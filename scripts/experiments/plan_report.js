#!/usr/bin/env node
// Investigation-only reporter: prints the full per-level plan for a list of
// widths under a chosen cost-model version, using the promoted best-known
// catalog exported by scripts/tests/RecursiveCostOracle.lean --catalog.
//
// Usage: node scripts/experiments/plan_report.js <catalog.tsv> <v2|v3|v3-4kW> w1 w2 ...
"use strict";

const fs = require("node:fs");
const RecursiveCost = require("../../leaderboard/site/recursive-cost.js");

const [, , catalogPath, version, ...rawWidths] = process.argv;
const widths = rawWidths.map(Number);

const candidates = fs.readFileSync(catalogPath, "utf8")
  .split("\n").filter(Boolean).map(line => {
    const [marker, policyId, rawK, rawOperations] = line.split("\t");
    if (marker !== "candidate") throw new Error(`bad catalog line: ${line}`);
    const operations = rawOperations === "" ? [] : rawOperations.split(";").map(encoded => {
      const [name, ...values] = encoded.split(",");
      return [name, ...values.map(Number)];
    });
    return { policyId, k: Number(rawK), operations };
  });

const model = RecursiveCost.selectModel ? RecursiveCost.selectModel(version) : RecursiveCost;
const plans = model.bestPlans(candidates, widths);
for (const plan of plans) {
  const levels = model.planLevels(plan);
  const ks = levels.filter(l => l.type === "recursive").map(l => l.k);
  const childWidths = levels.filter(l => l.type === "recursive").map(l => l.childWidth);
  console.log([
    model.modelVersion,
    plan.width,
    plan.gateCount.toString(),
    plan.recursionHeight,
    ks.join(","),
    childWidths.join(","),
    plan.totalRecursiveCallCount.toString(),
    plan.totalArithmeticOperationCount.toString(),
  ].join("\t"));
}
