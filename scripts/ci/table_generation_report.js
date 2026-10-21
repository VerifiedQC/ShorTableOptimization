'use strict';

const childProcess = require('child_process');
const fs = require('fs');

const RESULTS_BRANCH = 'submission-results';
const RESULT_MARKER = '<!-- table-generation-submission-result -->';

// The base branch a submission PR must target. A `pull_request` run checks out
// the workflow from the PR's own merge commit, so a fork could ship a verify
// workflow that skips the verifier and uploads a forged result artifact. This
// trusted job must not take the submission's identity from that artifact. It
// derives the policy commit from the verification run itself and resolves the
// pull request from the GitHub API, then confirms the run could only have used
// the base branch's workflow: the PR targets `submission/template` and changes
// nothing outside the submission surface.
const SUBMISSION_BASE_REF = 'submission/template';
const SUBMISSION_POLICY_FILE = 'TableGeneration/Submission/Policy.lean';
const SUBMISSION_HELPER_PREFIX = 'TableGeneration/Submission/Policy/';

function isAdmittedSubmissionPath(path) {
  return (
    path === SUBMISSION_POLICY_FILE ||
    (path.startsWith(SUBMISSION_HELPER_PREFIX) && path.endsWith('.lean'))
  );
}

// Resolve, and vouch for, the pull request behind a verification run. Returns
// { number, headSha } or throws. Everything here comes from the API and the
// run, never from the uploaded artifact.
async function resolveTrustedPullRequest(github, context, workflowRun) {
  const headSha = String(workflowRun.head_sha || '').toLowerCase().trim();
  if (!/^[0-9a-f]{40}$/.test(headSha)) {
    throw new Error('The verification run does not identify a head commit.');
  }
  const { owner, repo } = context.repo;
  const associated = await github.paginate(
    github.rest.repos.listPullRequestsAssociatedWithCommit,
    { owner, repo, commit_sha: headSha }
  );
  const candidates = associated.filter(
    (pr) =>
      pr.base &&
      pr.base.ref === SUBMISSION_BASE_REF &&
      String(pr.head && pr.head.sha).toLowerCase() === headSha
  );
  if (candidates.length !== 1) {
    throw new Error(
      `Expected exactly one ${SUBMISSION_BASE_REF} pull request at ${headSha}; ` +
        `found ${candidates.length}. Refusing to archive.`
    );
  }
  const pr = candidates[0];
  const files = await github.paginate(github.rest.pulls.listFiles, {
    owner,
    repo,
    pull_number: pr.number,
  });
  // The file list is the control that proves the run used the base workflow, so
  // it must be complete and non-empty. GitHub caps a pull request's file list at
  // 3000 even through pagination, so at that size a foreign file could be hidden
  // past the cap -- fail closed. A real submission always changes Policy.lean, so
  // it is neither empty nor anywhere near the cap.
  if (files.length === 0) {
    throw new Error(
      `Pull request #${pr.number} reports no changed files; refusing to archive.`
    );
  }
  if (files.length >= 3000) {
    throw new Error(
      `Pull request #${pr.number} changes ${files.length} files; the list may be ` +
        'truncated at the API cap, so a file outside the submission surface could ' +
        'be hidden. Refusing to archive.'
    );
  }
  const names = files.map((file) => file.filename);
  const foreign = names.filter((path) => !isAdmittedSubmissionPath(path));
  if (foreign.length) {
    throw new Error(
      `Pull request #${pr.number} changes files outside the submission surface ` +
        `(${foreign.join(', ')}). The verification run cannot be trusted to have ` +
        'used the base workflow; refusing to archive.'
    );
  }
  if (!names.includes(SUBMISSION_POLICY_FILE)) {
    throw new Error(
      `Pull request #${pr.number} does not change ${SUBMISSION_POLICY_FILE}; ` +
        'a submission must replace the policy implementation. Refusing to archive.'
    );
  }
  return { number: pr.number, headSha };
}

function sourceRunId() {
  const runId = Number(process.env.SOURCE_RUN_ID || 0);
  if (!Number.isSafeInteger(runId) || runId <= 0) {
    throw new Error('Source workflow run ID is invalid.');
  }
  return runId;
}

async function sourceWorkflowRun(github, context) {
  const response = await github.rest.actions.getWorkflowRun({
    ...context.repo,
    run_id: sourceRunId(),
  });
  return response.data;
}

async function ensureResultsBranch(github, context) {
  const { owner, repo } = context.repo;
  try {
    const existing = await github.rest.git.getRef({
      owner,
      repo,
      ref: `heads/${RESULTS_BRANCH}`,
    });
    return existing.data.object.sha;
  } catch (error) {
    if (error.status !== 404) throw error;
  }

  const tree = await github.rest.git.createTree({ owner, repo, tree: [] });
  const commit = await github.rest.git.createCommit({
    owner,
    repo,
    message: 'chore(results): initialize generated archive',
    tree: tree.data.sha,
    parents: [],
  });
  try {
    await github.rest.git.createRef({
      owner,
      repo,
      ref: `refs/heads/${RESULTS_BRANCH}`,
      sha: commit.data.sha,
    });
    return commit.data.sha;
  } catch (error) {
    if (error.status !== 422) throw error;
    const existing = await github.rest.git.getRef({
      owner,
      repo,
      ref: `heads/${RESULTS_BRANCH}`,
    });
    return existing.data.object.sha;
  }
}

const PERSIST_ATTEMPTS = 5;

async function persistFiles(github, context, files, message) {
  const { owner, repo } = context.repo;

  // Blobs are content-addressed and say nothing about the branch head, so they
  // are uploaded once and reused by every attempt below.
  const entries = [];
  for (const [storedPath, localPath] of files) {
    const blob = await github.rest.git.createBlob({
      owner,
      repo,
      content: fs.readFileSync(localPath).toString('base64'),
      encoding: 'base64',
    });
    entries.push({
      path: storedPath,
      mode: '100644',
      type: 'blob',
      sha: blob.data.sha,
    });
  }

  // Two submissions finishing together both persist to the same branch, and
  // `updateRef` without force refuses the second with 422. Re-read the head and
  // rebuild on top of it rather than losing that submission's archive: the
  // concurrency group that used to serialise this dropped queued runs outright,
  // which lost the archive, the PR comment and the close.
  for (let attempt = 1; attempt <= PERSIST_ATTEMPTS; attempt += 1) {
    const headSha = await ensureResultsBranch(github, context);
    const head = await github.rest.git.getCommit({
      owner,
      repo,
      commit_sha: headSha,
    });

    const tree = await github.rest.git.createTree({
      owner,
      repo,
      base_tree: head.data.tree.sha,
      tree: entries,
    });
    if (tree.data.sha === head.data.tree.sha) return;

    const commit = await github.rest.git.createCommit({
      owner,
      repo,
      message,
      tree: tree.data.sha,
      parents: [headSha],
    });
    try {
      await github.rest.git.updateRef({
        owner,
        repo,
        ref: `heads/${RESULTS_BRANCH}`,
        sha: commit.data.sha,
      });
      return;
    } catch (error) {
      if (error.status !== 422 || attempt === PERSIST_ATTEMPTS) throw error;
      await new Promise((resolve) => setTimeout(resolve, 500 * attempt));
    }
  }
}

async function downloadExistingIndex(github, context) {
  const { owner, repo } = context.repo;
  try {
    const existing = await github.rest.repos.getContent({
      owner,
      repo,
      path: 'leaderboard/results.json',
      ref: RESULTS_BRANCH,
    });
    if (Array.isArray(existing.data) || existing.data.encoding !== 'base64') {
      throw new Error('Existing benchmark index is not a base64-encoded file.');
    }
    const localPath = 'artifacts/existing-benchmark-results.json';
    fs.writeFileSync(localPath, Buffer.from(existing.data.content, 'base64'));
    return localPath;
  } catch (error) {
    if (error.status === 404) return '';
    throw error;
  }
}

function buildBenchmarkIndex(existingPath) {
  const args = [
    'scripts/leaderboard.py',
    '--artifact',
    'artifacts/table-generation-submission-result.json',
    '--config',
    'leaderboard/config.json',
    '--out',
    'artifacts/benchmark-results.json',
    '--operations-out',
    'artifacts/benchmark-operations.json',
  ];
  if (existingPath) args.push('--existing', existingPath);
  childProcess.execFileSync('python3', args, { stdio: 'inherit' });
}

function repositoryFileUrl(context, storedPath) {
  const serverUrl = process.env.GITHUB_SERVER_URL || 'https://github.com';
  const encodedPath = storedPath.split('/').map(encodeURIComponent).join('/');
  const { owner, repo } = context.repo;
  return `${serverUrl}/${owner}/${repo}/blob/${RESULTS_BRANCH}/${encodedPath}`;
}

async function persistBenchmarkResults({ github, context, core }) {
  const resultPath = 'artifacts/table-generation-results.json';
  const reportPath = 'artifacts/table-generation-results.md';
  const sourcePath = 'artifacts/table-generation-submission-source.zip';
  const operationsPath = 'artifacts/benchmark-operations.json';
  const result = JSON.parse(fs.readFileSync(resultPath, 'utf8'));
  const workflowRun = await sourceWorkflowRun(github, context);
  if (workflowRun.conclusion !== 'success') {
    throw new Error('Benchmark results may only be persisted for successful workflows.');
  }

  // Identity comes from the run and the API, not from the artifact: the policy
  // commit is the run's head SHA, and the pull request is resolved and vouched
  // for by resolveTrustedPullRequest. The artifact's own pr_number / head_sha
  // are ignored. Binding the archive directory to the real head SHA also means
  // a forged run cannot address, and so cannot overwrite, another policy's
  // directory -- that directory is named by that policy's own commit.
  const pr = await resolveTrustedPullRequest(github, context, workflowRun);
  const prNumber = String(pr.number);
  const policyId = pr.headSha;
  core.setOutput('pr_number', prNumber);
  const storedDirectory = `results/policies/${policyId}`;
  const storedResultPath = `${storedDirectory}/results.json`;
  const storedReportPath = `${storedDirectory}/results.md`;
  const storedSourcePath = `${storedDirectory}/source.zip`;
  const storedOperationsPath = `${storedDirectory}/operations.json`;
  const storedIndexPath = 'leaderboard/results.json';
  const message = `chore(results): persist policy ${policyId.slice(0, 12)}`;

  const existingIndexPath = await downloadExistingIndex(github, context);
  buildBenchmarkIndex(existingIndexPath);
  await persistFiles(
    github,
    context,
    [
      [storedResultPath, resultPath],
      [storedReportPath, reportPath],
      [storedSourcePath, sourcePath],
      [storedOperationsPath, operationsPath],
      [storedIndexPath, 'artifacts/benchmark-results.json'],
    ],
    message
  );

  core.setOutput('results_json_url', repositoryFileUrl(context, storedResultPath));
  core.setOutput('results_report_url', repositoryFileUrl(context, storedReportPath));
  core.setOutput('source_archive_url', repositoryFileUrl(context, storedSourcePath));
  core.setOutput('operations_json_url', repositoryFileUrl(context, storedOperationsPath));
  core.setOutput('benchmark_index_url', repositoryFileUrl(context, storedIndexPath));
}

function readVerifierResult(core) {
  const resultPath = 'artifacts/table-generation-submission-result.json';
  if (!fs.existsSync(resultPath)) return null;
  try {
    return JSON.parse(fs.readFileSync(resultPath, 'utf8'));
  } catch (error) {
    core.warning(`Could not parse verifier result JSON: ${error.message}`);
    return null;
  }
}

function reportBody(result, workflowRun) {
  const benchmarkPath = 'artifacts/table-generation-results.md';
  const verifierSummaryPath = 'artifacts/table-generation-summary.md';
  const fallback = [
    RESULT_MARKER,
    '### Table generation submission',
    '',
    'Status: **FAILURE**',
    '',
    'The verifier did not produce a summary artifact. Check the workflow run.',
  ].join('\n');
  let body = fs.existsSync(benchmarkPath)
    ? fs.readFileSync(benchmarkPath, 'utf8')
    : fs.existsSync(verifierSummaryPath)
      ? fs.readFileSync(verifierSummaryPath, 'utf8')
      : fallback;

  if (
    result?.phase === 'preflight' &&
    result.status === 'success' &&
    workflowRun.conclusion !== 'success'
  ) {
    body = [
      RESULT_MARKER,
      '### Table generation submission',
      '',
      'Status: **FAILURE**',
      '',
      'Preflight checks passed, but full Lean verification did not complete.',
      'Check the workflow run.',
    ].join('\n');
  }
  return body;
}

async function upsertResultComment(github, context, prNumber, body) {
  const { owner, repo } = context.repo;
  const comments = await github.paginate(github.rest.issues.listComments, {
    owner,
    repo,
    issue_number: prNumber,
    per_page: 100,
  });
  const existing = comments.find(
    comment => comment.user.type === 'Bot' && comment.body.includes(RESULT_MARKER)
  );
  if (existing) {
    await github.rest.issues.updateComment({
      owner,
      repo,
      comment_id: existing.id,
      body,
    });
    return;
  }
  await github.rest.issues.createComment({ owner, repo, issue_number: prNumber, body });
}

async function reportPullRequestResult({ github, context, core }) {
  const workflowRun = await sourceWorkflowRun(github, context);
  const result = readVerifierResult(core);
  const serverUrl = process.env.GITHUB_SERVER_URL || 'https://github.com';
  const repositoryUrl = `${serverUrl}/${context.repo.owner}/${context.repo.repo}`;
  const workflowUrl = `${repositoryUrl}/actions/runs/${workflowRun.id}`;
  const links = [`[Workflow run](${workflowUrl})`];
  if (process.env.RESULTS_REPORT_URL) {
    links.push(`[Results report](${process.env.RESULTS_REPORT_URL})`);
  }
  if (process.env.RESULTS_JSON_URL) {
    links.push(`[Results JSON](${process.env.RESULTS_JSON_URL})`);
  }
  if (process.env.OPERATIONS_JSON_URL) {
    links.push(`[Operations JSON](${process.env.OPERATIONS_JSON_URL})`);
  }
  if (process.env.BENCHMARK_INDEX_URL) {
    links.push(`[Benchmark JSON](${process.env.BENCHMARK_INDEX_URL})`);
  }
  if (process.env.SOURCE_ARCHIVE_URL) {
    links.push(`[Source archive](${process.env.SOURCE_ARCHIVE_URL})`);
  }
  let body = reportBody(result, workflowRun).trimEnd();
  const verifiedSuccessfully =
    workflowRun.conclusion === 'success' &&
    result?.phase === 'full' &&
    result.status === 'success';
  if (verifiedSuccessfully && process.env.PERSIST_OUTCOME !== 'success') {
    body += '\n\nBenchmark results could not be archived; the PR has been left open.';
  }
  body = `${body}\n\n${links.join(' · ')}\n`;

  // Resolve the pull request the same trusted way persistBenchmarkResults does,
  // rather than trusting the artifact's metadata. A run that cannot be vouched
  // for (a forged or mismatched artifact) gets no comment and no close.
  let trustedPr;
  try {
    trustedPr = await resolveTrustedPullRequest(github, context, workflowRun);
  } catch (error) {
    core.warning(
      `Could not resolve a trusted pull request; no comment was posted. ${error.message}`
    );
    return;
  }
  const prNumber = trustedPr.number;

  await upsertResultComment(github, context, prNumber, body);
  if (!result) {
    core.info('No result JSON found; leaving PR open.');
    return;
  }
  if (workflowRun.conclusion !== 'success') {
    core.info(
      `Verification workflow conclusion is ${workflowRun.conclusion}; leaving PR open.`
    );
    return;
  }
  if (result.phase !== 'full') {
    core.info(`Verifier phase is ${result.phase}; leaving PR open.`);
    return;
  }
  if (result.status !== 'success') {
    core.info(`Submission status is ${result.status}; leaving PR open.`);
    return;
  }
  if (process.env.PERSIST_OUTCOME !== 'success') {
    core.info('Benchmark persistence did not succeed; leaving PR open.');
    return;
  }

  await github.rest.pulls.update({
    ...context.repo,
    pull_number: prNumber,
    state: 'closed',
  });
}

module.exports = {
  persistBenchmarkResults,
  reportPullRequestResult,
  resolveTrustedPullRequest,
  isAdmittedSubmissionPath,
};
