'use strict';

// Regression tests for the Report job's trusted pull-request resolution.
//
// A `pull_request` run uses the workflow file from the PR's own merge commit, so
// a fork can ship a verify workflow that skips the verifier and uploads a forged
// result artifact. The trusted Report job must derive the policy commit from the
// verification run and resolve the PR from the API, never from the artifact, and
// must confirm the run could only have used the base branch's workflow.
//
// Run: node scripts/test_report_trust.js

const assert = require('assert');
const reporting = require('./ci/table_generation_report.js');

const HEAD = 'a'.repeat(40);
const OTHER = 'b'.repeat(40);

function fakeGithub({ associated = [], files = [] } = {}) {
  return {
    // github.paginate(method, params) just calls the method and returns its
    // array payload here; the real one concatenates pages.
    paginate: async (method, params) => method(params),
    rest: {
      repos: {
        listPullRequestsAssociatedWithCommit: async () => associated,
      },
      pulls: {
        listFiles: async () => files,
      },
    },
  };
}

const context = { repo: { owner: 'o', repo: 'r' } };

function run(name, fn) {
  return fn().then(
    () => console.log(`ok  ${name}`),
    (error) => {
      console.error(`FAIL ${name}: ${error.message}`);
      process.exitCode = 1;
    }
  );
}

async function expectThrows(promise, re) {
  try {
    await promise;
  } catch (error) {
    assert.match(error.message, re, `wrong error: ${error.message}`);
    return;
  }
  assert.fail('expected a rejection');
}

async function main() {
  await run('happy path returns the PR number and head SHA', async () => {
    const github = fakeGithub({
      associated: [
        { number: 7, base: { ref: 'submission/template' }, head: { sha: HEAD } },
      ],
      files: [{ filename: 'TableGeneration/Submission/Policy.lean' }],
    });
    const pr = await reporting.resolveTrustedPullRequest(
      github,
      context,
      { head_sha: HEAD }
    );
    assert.deepStrictEqual(pr, { number: 7, headSha: HEAD });
  });

  await run('helper files under Policy/ are admitted', async () => {
    const github = fakeGithub({
      associated: [
        { number: 8, base: { ref: 'submission/template' }, head: { sha: HEAD } },
      ],
      files: [
        { filename: 'TableGeneration/Submission/Policy.lean' },
        { filename: 'TableGeneration/Submission/Policy/Deep/Aux.lean' },
      ],
    });
    const pr = await reporting.resolveTrustedPullRequest(github, context, {
      head_sha: HEAD,
    });
    assert.strictEqual(pr.number, 8);
  });

  await run('a PR that edits the workflow is refused', async () => {
    const github = fakeGithub({
      associated: [
        { number: 9, base: { ref: 'submission/template' }, head: { sha: HEAD } },
      ],
      files: [
        { filename: 'TableGeneration/Submission/Policy.lean' },
        { filename: '.github/workflows/table-generation-submission.yml' },
      ],
    });
    await expectThrows(
      reporting.resolveTrustedPullRequest(github, context, { head_sha: HEAD }),
      /outside the submission surface/
    );
  });

  await run('a PR with no changed files is refused', async () => {
    const github = fakeGithub({
      associated: [
        { number: 20, base: { ref: 'submission/template' }, head: { sha: HEAD } },
      ],
      files: [],
    });
    await expectThrows(
      reporting.resolveTrustedPullRequest(github, context, { head_sha: HEAD }),
      /no changed files/
    );
  });

  await run('a PR at the file-list cap is refused', async () => {
    const files = [];
    for (let n = 0; n < 3000; n += 1) {
      files.push({ filename: `TableGeneration/Submission/Policy/H${n}.lean` });
    }
    const github = fakeGithub({
      associated: [
        { number: 21, base: { ref: 'submission/template' }, head: { sha: HEAD } },
      ],
      files,
    });
    await expectThrows(
      reporting.resolveTrustedPullRequest(github, context, { head_sha: HEAD }),
      /may be ?\n?.*truncated|truncated/
    );
  });

  await run('a PR that does not touch Policy.lean is refused', async () => {
    const github = fakeGithub({
      associated: [
        { number: 22, base: { ref: 'submission/template' }, head: { sha: HEAD } },
      ],
      files: [{ filename: 'TableGeneration/Submission/Policy/Helper.lean' }],
    });
    await expectThrows(
      reporting.resolveTrustedPullRequest(github, context, { head_sha: HEAD }),
      /does not change/
    );
  });

  await run('a PR against the wrong base is refused', async () => {
    const github = fakeGithub({
      associated: [{ number: 10, base: { ref: 'main' }, head: { sha: HEAD } }],
      files: [{ filename: 'TableGeneration/Submission/Policy.lean' }],
    });
    await expectThrows(
      reporting.resolveTrustedPullRequest(github, context, { head_sha: HEAD }),
      /Expected exactly one/
    );
  });

  await run('a head SHA that matches no PR is refused', async () => {
    const github = fakeGithub({ associated: [] });
    await expectThrows(
      reporting.resolveTrustedPullRequest(github, context, { head_sha: HEAD }),
      /Expected exactly one/
    );
  });

  await run('two PRs at the same head SHA are refused', async () => {
    const github = fakeGithub({
      associated: [
        { number: 11, base: { ref: 'submission/template' }, head: { sha: HEAD } },
        { number: 12, base: { ref: 'submission/template' }, head: { sha: HEAD } },
      ],
    });
    await expectThrows(
      reporting.resolveTrustedPullRequest(github, context, { head_sha: HEAD }),
      /found 2/
    );
  });

  await run('a non-hex head SHA is refused', async () => {
    await expectThrows(
      reporting.resolveTrustedPullRequest(fakeGithub(), context, {
        head_sha: 'not-a-sha',
      }),
      /does not identify a head commit/
    );
  });

  await run('a PR associated by commit but with a different head is refused', async () => {
    // listPullRequestsAssociatedWithCommit can return a PR that merely contains
    // the commit; its head must still be exactly the run's head.
    const github = fakeGithub({
      associated: [
        { number: 13, base: { ref: 'submission/template' }, head: { sha: OTHER } },
      ],
    });
    await expectThrows(
      reporting.resolveTrustedPullRequest(github, context, { head_sha: HEAD }),
      /Expected exactly one/
    );
  });

  await run('path admission matches the submission surface', async () => {
    assert.ok(
      reporting.isAdmittedSubmissionPath('TableGeneration/Submission/Policy.lean')
    );
    assert.ok(
      reporting.isAdmittedSubmissionPath(
        'TableGeneration/Submission/Policy/Helper.lean'
      )
    );
    assert.ok(
      !reporting.isAdmittedSubmissionPath('TableGeneration/Submission/Defs.lean')
    );
    assert.ok(
      !reporting.isAdmittedSubmissionPath(
        'TableGeneration/Submission/Policy/notes.md'
      )
    );
    assert.ok(!reporting.isAdmittedSubmissionPath('scripts/verifier.py'));
  });
}

main().then(() => {
  if (process.exitCode) {
    console.error('\nsome checks failed');
  } else {
    console.log('\nall checks passed');
  }
});
