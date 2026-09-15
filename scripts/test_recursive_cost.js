#!/usr/bin/env node
"use strict";

const assert = require("node:assert/strict");
const childProcess = require("node:child_process");
const fs = require("node:fs");
const path = require("node:path");
const RecursiveCost = require("../leaderboard/site/recursive-cost.js");

const binaryCandidate = {
  policyId: "test-binary",
  k: 2,
  operations: [
    ["phaseProduct", 0],
    ["phaseProduct", 1],
  ],
};

const transitionCandidate = {
  policyId: "test-transitions",
  k: 3,
  operations: [
    ["shiftL", 0, 3],
    ["shiftR", 1, 2],
    ["negate", 2],
    ["addScaled", 0, 2, 1, 4],
    ["addScaled", 2, 1, -1, 1],
    ["phaseProduct", 0],
  ],
};

let leanModulesBuilt = false;

function ensureLeanModulesBuilt(repository) {
  if (leanModulesBuilt) return;
  const result = childProcess.spawnSync(
    "lake",
    ["build", "TableGeneration.RecursiveCost.Correctness"],
    { cwd: repository, encoding: "utf8", maxBuffer: 8 * 1024 * 1024 },
  );
  if (result.status !== 0) {
    throw new Error(`Lean build failed:\n${result.stdout}\n${result.stderr}`);
  }
  leanModulesBuilt = true;
}

function testWidthModel() {
  assert.equal(RecursiveCost.phaseLimbWidth(10, 8, 3), 2);
  assert.deepEqual(RecursiveCost.initWidthState(10, 8, 3), {
    xw: [2, 2, 6],
    zw: [2, 2, 4],
  });

  const initial = RecursiveCost.initWidthState(8, 8, 2);
  const shifted = RecursiveCost.updateWidthState(initial, ["shiftL", 0, 1], 2);
  assert.deepEqual(shifted, { xw: [5, 4], zw: [5, 4] });
  const negated = RecursiveCost.updateWidthState(shifted, ["negate", 1], 2);
  assert.deepEqual(negated, { xw: [5, 5], zw: [5, 5] });
  const added = RecursiveCost.updateWidthState(
    negated,
    ["addScaled", 0, 1, -1, 2],
    2,
  );
  assert.deepEqual(added, { xw: [8, 5], zw: [8, 5] });
  assert.equal(
    RecursiveCost.nextSignedWidth(8, 8, 2, [
      ["shiftL", 0, 1],
      ["negate", 1],
      ["addScaled", 0, 1, -1, 2],
      ["phaseProduct", 0],
    ]),
    9,
  );
}

const MODELS = ["v3"];

function modelApi(version) {
  return RecursiveCost.selectModel(version);
}

function testGateModel() {
  assert.equal(RecursiveCost.rippleAdderGateBound(7), 65n);
  assert.equal(RecursiveCost.negateGateBound(7), 72n);
  assert.equal(RecursiveCost.directSignedPhaseProductGateCount(7, 9), 315n);

  // v3 primitives, against ResourceModel.lean at companion commit d5a165b.
  // Cuccaro: x = 2w - 6, cnot = 5w - 7, toffoli = 2w - 3; totalGates = 9w - 16.
  assert.equal(RecursiveCost.cuccaroModAddGateCount(7), 47n);
  assert.equal(RecursiveCost.cuccaroModAddGateCount(7), 9n * 7n - 16n);
  assert.equal(RecursiveCost.cuccaroModAddGateCount(3), 9n * 3n - 16n);
  // negate = (w + (2w - 6) + 2) + (5w - 7) + (2w - 3) = 10w - 14 for w >= 3.
  assert.equal(RecursiveCost.cuccaroNegateGateCount(7), 56n);
  assert.equal(RecursiveCost.cuccaroNegateGateCount(7), 10n * 7n - 14n);
  // Truncated Nat subtraction below the published w >= 3 regime.
  assert.equal(RecursiveCost.cuccaroModAddGateCount(2), 4n);
  assert.equal(RecursiveCost.cuccaroModAddGateCount(1), 0n);
  // Only the top limb is sign-extended; each is extended once and deallocated
  // once. k = 5, width 2048: limb = 409, top limb = 2048 - 4 * 409 = 412.
  assert.equal(RecursiveCost.topLimbWidth(2048, 409, 5), 412);
  assert.equal(
    RecursiveCost.signExtensionAllocationGateCount(2048, 2048, 5, 440),
    2n * ((440n - 412n) + (440n - 412n)),
  );

  // Pin this to a named model rather than to whatever the default is. That
  // lesson came from a real break: the default moved and silently changed the
  // expected value. v2 and v3-loose4kw have since been retired -- they mirrored
  // a model the companion deleted and a bound it never defined as a model.
  const arithmeticProbe = {
    policyId: "arithmetic-test",
    k: 2,
    operations: [
      ["shiftL", 0, 1],
      ["negate", 1],
      ["addScaled", 0, 1, 1, 2],
      ["phaseProduct", 0],
    ],
  };
  for (const [model, expectedGates] of [["v3", 302n]]) {
    assert.deepEqual(
      RecursiveCost.selectModel(model).analyzeProgram(8, 8, arithmeticProbe),
      {
        childWidth: 9,
        arithmeticGateCount: expectedGates,
        arithmeticOperationCount: 3,
        recursiveCallCount: 1,
      },
      `arithmetic probe under ${model}`,
    );
  }
}

function testPlanner() {
  // Pin the model rather than inherit the default.
  const RC = RecursiveCost.selectModel("v3");
  const width8 = RC.bestPlan([binaryCandidate], 8);
  assert.equal(width8.gateCount, 254n);
  assert.equal(width8.recursionHeight, 1);
  assert.equal(width8.totalRecursiveCallCount, 2n);
  assert.equal(width8.choice.k, 2);
  assert.equal(width8.choice.childWidth, 5);

  const width16 = RC.bestPlan([binaryCandidate], 16);
  assert.equal(width16.gateCount, 668n);
  assert.equal(width16.recursionHeight, 3);
  assert.equal(width16.totalRecursiveCallCount, 14n);
  assert.deepEqual(RC.compactPlan(width16), {
    model_version: "forshor-phase-product-gates-v3",
    objective: RC.objective,
    width: 16,
    gate_count: "668",
    recursion_height: 3,
    recursive_call_count: "14",
    arithmetic_operation_count: "0",
    steps: [
      {
        type: "recursive",
        level: 0,
        input_width: 16,
        instances: "1",
        policy_id: "test-binary",
        k: 2,
        child_width: 9,
        recursive_products_per_node: 2,
        local_gate_count_per_node: "4",
        expanded_local_gate_count: "4",
        local_arithmetic_operations_per_node: 0,
        expanded_arithmetic_operations: "0",
      },
      {
        type: "recursive",
        level: 1,
        input_width: 9,
        instances: "2",
        policy_id: "test-binary",
        k: 2,
        child_width: 6,
        recursive_products_per_node: 2,
        local_gate_count_per_node: "4",
        expanded_local_gate_count: "8",
        local_arithmetic_operations_per_node: 0,
        expanded_arithmetic_operations: "0",
      },
      {
        type: "recursive",
        level: 2,
        input_width: 6,
        instances: "4",
        policy_id: "test-binary",
        k: 2,
        child_width: 4,
        recursive_products_per_node: 2,
        local_gate_count_per_node: "4",
        expanded_local_gate_count: "16",
        local_arithmetic_operations_per_node: 0,
        expanded_arithmetic_operations: "0",
      },
      {
        type: "direct",
        level: 3,
        input_width: 4,
        instances: "8",
        gate_count_per_node: "80",
        expanded_gate_count: "640",
      },
    ],
  });
  const contributions = RecursiveCost.planLevels(width16).reduce(
    (total, level) => total + (level.type === "direct"
      ? level.expandedGateCount
      : level.expandedLocalGateCount),
    0n,
  );
  assert.equal(contributions, width16.gateCount);
}

async function testArchivedCatalog() {
  const policyA = "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
  const policyB = "bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb";
  const data = {
    policies: [
      {
        policy_id: policyB,
        operations_path: "b/operations.json",
        results: [
          {
            mode: "PhaseProduct",
            k: 3,
            total_operation_count: 2,
            phase_product_count: 1,
            arithmetic_operation_count: 1,
          },
          { mode: "PhaseTripleProduct", k: 2 },
        ],
      },
      {
        policy_id: policyA,
        operations_path: "a/operations.json",
        results: [
          {
            mode: "PhaseProduct",
            k: 3,
            total_operation_count: 1,
            phase_product_count: 1,
            arithmetic_operation_count: 0,
          },
          {
            mode: "PhaseProduct",
            k: 2,
            total_operation_count: 2,
            phase_product_count: 1,
            arithmetic_operation_count: 1,
          },
        ],
      },
    ],
  };
  const operationData = {
    "a/operations.json": {
      schema_version: 1,
      policy_id: policyA,
      targets: [
        { mode: "PhaseProduct", k: 2, operations: [["negate", 0], ["phaseProduct", 0]] },
        { mode: "PhaseProduct", k: 3, operations: [["phaseProduct", 1]] },
      ],
    },
    "b/operations.json": {
      schema_version: 1,
      policy_id: policyB,
      targets: [
        { mode: "PhaseProduct", k: 3, operations: [["shiftL", 0, 1], ["phaseProduct", 0]] },
      ],
    },
  };
  const loads = [];
  const candidates = await RecursiveCost.archivedPhaseProductCandidates(data, path_ => {
    loads.push(path_);
    return operationData[path_];
  });
  assert.deepEqual(candidates.map(candidate => [candidate.k, candidate.policyId]), [
    [2, policyA],
    [3, policyA],
    [3, policyB],
  ]);
  assert.deepEqual(loads.sort(), ["a/operations.json", "b/operations.json"]);
}

async function testPublishedArchive() {
  const configuredRoot = process.env.TABLE_GEN_RESULTS_ROOT;
  if (!configuredRoot) return;
  const resultsRoot = path.resolve(process.cwd(), configuredRoot);
  const data = JSON.parse(
    fs.readFileSync(path.join(resultsRoot, "leaderboard/results.json"), "utf8"),
  );
  const expectedCount = RecursiveCost.phaseProductResultDescriptors(data).length;
  const candidates = await RecursiveCost.archivedPhaseProductCandidates(data, operationsPath =>
    JSON.parse(fs.readFileSync(path.join(resultsRoot, operationsPath), "utf8")));
  assert(expectedCount > 0);
  assert.equal(candidates.length, expectedCount);
  const plans = RecursiveCost.bestPlans(candidates, [2048, 4096]);
  assert.deepEqual(plans.map(plan => plan.width), [2048, 4096]);
  assert(plans.every(plan => plan.gateCount > 0n));
}

function deterministicWidths() {
  const widths = Array.from({ length: 257 }, (_, index) => index);
  widths.push(511, 512, 513, 2048, 4096);
  let state = 0x5eed1234;
  for (let index = 0; index < 64; index += 1) {
    state = (Math.imul(state, 1664525) + 1013904223) >>> 0;
    widths.push(1 + (state % 4096));
  }
  return [...new Set(widths)];
}

function runLeanOracle(arguments_, model = "v3") {
  const repository = path.resolve(__dirname, "..");
  ensureLeanModulesBuilt(repository);
  const oracle = path.join(repository, "scripts/tests/RecursiveCostOracle.lean");
  const result = childProcess.spawnSync(
    "lake",
    ["env", "lean", "--run", oracle, `--model=${model}`, ...arguments_],
    { cwd: repository, encoding: "utf8", maxBuffer: 8 * 1024 * 1024 },
  );
  if (result.status !== 0) {
    throw new Error(`Lean oracle failed:\n${result.stdout}\n${result.stderr}`);
  }
  return result.stdout.trim().split("\n").filter(Boolean);
}

function leanPlans(widths, mode = null, model = "v3") {
  const arguments_ = mode === null
    ? widths.map(String)
    : [mode, ...widths.map(String)];
  return runLeanOracle(arguments_, model).map(line => {
    const [width, gates, height, calls, arithmetic, choice] = line.split("\t");
    return { width, gates, height, calls, arithmetic, choice };
  });
}

function bestKnownCatalog() {
  return runLeanOracle(["--catalog"]).map(line => {
    const [marker, policyId, rawK, rawOperations] = line.split("\t");
    assert.equal(marker, "candidate");
    const operations = rawOperations === "" ? [] : rawOperations.split(";").map(encoded => {
      const [name, ...values] = encoded.split(",");
      return [name, ...values.map(Number)];
    });
    return { policyId, k: Number(rawK), operations };
  });
}

function testBalancedReferenceAgreement() {
  const widths = Array.from({ length: 65 }, (_, index) => index);
  const lines = runLeanOracle(["--reference", ...widths.map(String)]);
  assert.equal(lines.length, widths.length * 2);
  for (const line of lines) {
    const [marker, policyId, width, fast, reference] = line.split("\t");
    assert.equal(marker, "reference");
    assert(["test-binary", "test-transitions"].includes(policyId));
    assert(Number.isSafeInteger(Number(width)));
    assert.equal(fast, reference);
  }
}

// The Lean planner evaluates an array-based width scan, not the companion's
// Function.update scan. Nothing types them together, so the oracle checks them
// against each other over the promoted catalogue.
function testWidthScanAgreement(model = "v3") {
  const output = runLeanOracle(
    ["--width-scan", "8", "16", "64", "128", "512", "1024", "2048", "4096"],
    model,
  );
  assert(
    output.includes("width scan agreement passed"),
    `width scan agreement failed under ${model}: ${output}`,
  );
}

function testDenseSparseAgreement(model = "v3") {
  const api = modelApi(model);
  const widths = [
    ...Array.from({ length: 33 }, (_, index) => index),
    63, 64, 65, 127, 128,
  ];
  for (const candidates of [
    [binaryCandidate],
    [transitionCandidate],
    [binaryCandidate, transitionCandidate],
  ]) {
    const dense = api.buildPlanTable(candidates, Math.max(...widths));
    const memoized = api.bestPlans(candidates, widths);
    memoized.forEach((plan, index) => assert.deepEqual(plan, dense[widths[index]]));
  }
  assert.deepEqual(
    runLeanOracle(["--dense-sparse", ...widths.map(String)], model),
    ["dense/sparse agreement passed"],
  );
}

function testLeanDifferential(model = "v3") {
  const api = modelApi(model);
  const widths = deterministicWidths();
  const lean = leanPlans(widths, null, model);
  assert.equal(lean.length, widths.length);
  lean.forEach((expected, index) => {
    const width = widths[index];
    const actual = api.bestPlan([binaryCandidate], width);
    const choice = actual.choice === null
      ? "base"
      : `${actual.choice.k}:${actual.choice.childWidth}:${actual.choice.policyId}`;
    assert.deepEqual(expected, {
      width: String(width),
      gates: String(actual.gateCount),
      height: String(actual.recursionHeight),
      calls: String(actual.totalRecursiveCallCount),
      arithmetic: String(actual.totalArithmeticOperationCount),
      choice,
    });
  });
}

function testBestKnownDifferential(model = "v3") {
  const api = modelApi(model);
  const candidates = bestKnownCatalog();
  assert.deepEqual(candidates.map(candidate => candidate.k), [
    2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
  ]);
  const widths = [
    ...Array.from({ length: 65 }, (_, index) => index),
    127, 128, 129, 2048, 4096,
  ];
  const lean = leanPlans(widths, "--best-known", model);
  const plans = api.bestPlans(candidates, widths);
  const dense = api.buildPlanTable(candidates, 129);
  lean.forEach((expected, index) => {
    const width = widths[index];
    const actual = plans[index];
    const choice = actual.choice === null
      ? "base"
      : `${actual.choice.k}:${actual.choice.childWidth}:${actual.choice.policyId}`;
    assert.deepEqual(expected, {
      width: String(width),
      gates: String(actual.gateCount),
      height: String(actual.recursionHeight),
      calls: String(actual.totalRecursiveCallCount),
      arithmetic: String(actual.totalArithmeticOperationCount),
      choice,
    });
    if (width <= 129) assert.deepEqual(actual, dense[width]);
  });

}

async function main() {
  testWidthModel();
  testGateModel();
  testPlanner();
  await testArchivedCatalog();
  await testPublishedArchive();
  testBalancedReferenceAgreement();
  for (const model of MODELS) {
    testWidthScanAgreement(model);
    testDenseSparseAgreement(model);
    testLeanDifferential(model);
    testBestKnownDifferential(model);
  }
  console.log(`recursive cost tests passed (${MODELS.join(", ")})`);
}

main().catch(error => {
  console.error(error);
  process.exitCode = 1;
});
