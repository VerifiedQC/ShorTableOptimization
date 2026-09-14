#!/usr/bin/env node
// Investigation-only reporter: prints the full per-level plan for a list of
// widths under a chosen cost-model version.
//
// Candidate sources:
//   --archive <results-root>   the published archive (leaderboard/results.json
//                              plus each policy's operations.json); this is the
//                              catalogue the website planner uses.
//   --catalog <catalog.tsv>    output of
//                              `lake env lean --run scripts/tests/RecursiveCostOracle.lean --catalog`
//
// Usage:
//   node scripts/experiments/plan_report.js --archive <root> <v2|v3|v3-loose4kw> w1 w2 ...
//   node scripts/experiments/plan_report.js --catalog <file> <v2|v3|v3-loose4kw> w1 w2 ...
//
// Columns: model  n  gates  depth  k-per-level  childWidth-per-level  calls  arithmeticOps
"use strict";

const fs = require("node:fs");
const path = require("node:path");
const RecursiveCost = require("../../leaderboard/site/recursive-cost.js");

const [, , source, sourceArg, version, ...rawWidths] = process.argv;
const widths = rawWidths.map(Number);

function catalogCandidates(catalogPath) {
  return fs.readFileSync(catalogPath, "utf8")
    .split("\n").filter(Boolean).map(line => {
      const [marker, policyId, rawK, rawOperations] = line.split("\t");
      if (marker !== "candidate") throw new Error(`bad catalog line: ${line}`);
      const operations = rawOperations === "" ? [] : rawOperations.split(";").map(encoded => {
        const [name, ...values] = encoded.split(",");
        return [name, ...values.map(Number)];
      });
      return { policyId, k: Number(rawK), operations };
    });
}

function archiveCandidates(root) {
  const data = JSON.parse(
    fs.readFileSync(path.join(root, "leaderboard/results.json"), "utf8"));
  return RecursiveCost.archivedPhaseProductCandidates(data, operationsPath =>
    JSON.parse(fs.readFileSync(path.join(root, operationsPath), "utf8")));
}

async function main() {
  let candidates;
  if (source === "--archive") candidates = await archiveCandidates(sourceArg);
  else if (source === "--catalog") candidates = catalogCandidates(sourceArg);
  else throw new Error("expected --archive <root> or --catalog <file>");

  const model = RecursiveCost.selectModel(version);
  for (const plan of model.bestPlans(candidates, widths)) {
    const levels = model.planLevels(plan).filter(level => level.type === "recursive");
    console.log([
      model.modelVersion,
      plan.width,
      plan.gateCount.toString(),
      plan.recursionHeight,
      levels.map(level => level.k).join(","),
      levels.map(level => level.childWidth).join(","),
      plan.totalRecursiveCallCount.toString(),
      plan.totalArithmeticOperationCount.toString(),
    ].join("\t"));
  }
}

main().catch(error => { console.error(error); process.exitCode = 1; });
