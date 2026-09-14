(function attachRecursiveCost(root, factory) {
  const api = factory();
  if (typeof module === "object" && module.exports) {
    module.exports = api;
  } else {
    root.RecursiveCost = api;
  }
}(typeof globalThis === "undefined" ? this : globalThis, function recursiveCostFactory() {
  "use strict";

  const objective = "logical_gate_count";

  function requireNatural(value, name) {
    if (!Number.isSafeInteger(value) || value < 0) {
      throw new TypeError(`${name} must be a nonnegative safe integer.`);
    }
  }

  function requireK(k) {
    requireNatural(k, "k");
    if (k < 2) throw new RangeError("k must be at least 2.");
  }

  function phaseLimbWidthOfWidth(width, k) {
    requireNatural(width, "width");
    requireK(k);
    return Math.floor(width / k);
  }

  function phaseLimbWidth(xWidth, zWidth, k) {
    return Math.min(
      phaseLimbWidthOfWidth(xWidth, k),
      phaseLimbWidthOfWidth(zWidth, k),
    );
  }

  function phaseSplitLogicalWidth(width, commonWidth, k, index) {
    requireNatural(width, "width");
    requireNatural(commonWidth, "commonWidth");
    requireK(k);
    requireNatural(index, "index");
    if (index >= k) throw new RangeError("index must be less than k.");
    return index + 1 === k ? width - index * commonWidth : commonWidth;
  }

  function initWidthState(xWidth, zWidth, k) {
    const commonWidth = phaseLimbWidth(xWidth, zWidth, k);
    return {
      xw: Array.from(
        { length: k },
        (_, index) => phaseSplitLogicalWidth(xWidth, commonWidth, k, index),
      ),
      zw: Array.from(
        { length: k },
        (_, index) => phaseSplitLogicalWidth(zWidth, commonWidth, k, index),
      ),
    };
  }

  function operationIndex(value, k, name) {
    requireNatural(value, name);
    if (value >= k) throw new RangeError(`${name} must be less than k.`);
    return value;
  }

  function cloneState(state) {
    return { xw: [...state.xw], zw: [...state.zw] };
  }

  function updateWidthState(state, operation, k) {
    if (!Array.isArray(operation) || typeof operation[0] !== "string") {
      throw new TypeError("operation must be a compact operation array.");
    }

    const next = cloneState(state);
    const name = operation[0];
    if (name === "phaseProduct") {
      operationIndex(operation[1], k, "phaseProduct index");
      return next;
    }

    if (name === "shiftL" || name === "shiftR") {
      const index = operationIndex(operation[1], k, `${name} index`);
      const amount = operation[2];
      requireNatural(amount, `${name} amount`);
      for (const widths of [next.xw, next.zw]) {
        widths[index] = name === "shiftL"
          ? widths[index] + amount
          : Math.max(0, widths[index] - amount);
      }
      return next;
    }

    if (name === "negate") {
      const index = operationIndex(operation[1], k, "negate index");
      next.xw[index] += 1;
      next.zw[index] += 1;
      return next;
    }

    if (name === "addScaled") {
      const destination = operationIndex(operation[1], k, "addScaled destination");
      const source = operationIndex(operation[2], k, "addScaled source");
      if (operation[3] !== 1 && operation[3] !== -1) {
        throw new RangeError("addScaled sign must be 1 or -1.");
      }
      const shift = operation[4];
      requireNatural(shift, "addScaled shift");
      next.xw[destination] = 1 + Math.max(
        next.xw[destination],
        next.xw[source] + shift,
      );
      next.zw[destination] = 1 + Math.max(
        next.zw[destination],
        next.zw[source] + shift,
      );
      return next;
    }

    throw new RangeError(`unknown operation: ${name}`);
  }

  function mergeNeededWidths(needed, state) {
    for (let index = 0; index < needed.xneed.length; index += 1) {
      needed.xneed[index] = Math.max(needed.xneed[index], state.xw[index]);
      needed.zneed[index] = Math.max(needed.zneed[index], state.zw[index]);
    }
  }

  function scanNeededWidths(xWidth, zWidth, k, operations) {
    if (!Array.isArray(operations)) throw new TypeError("operations must be an array.");
    let state = initWidthState(xWidth, zWidth, k);
    const needed = { xneed: [...state.xw], zneed: [...state.zw] };
    for (const operation of operations) {
      state = updateWidthState(state, operation, k);
      mergeNeededWidths(needed, state);
    }
    return needed;
  }

  function maximumNeededWidth(needed) {
    let maximum = 0;
    for (let index = 0; index < needed.xneed.length; index += 1) {
      maximum = Math.max(maximum, needed.xneed[index], needed.zneed[index]);
    }
    return maximum;
  }

  function nextSignedWidth(xWidth, zWidth, k, operations) {
    return 1 + maximumNeededWidth(scanNeededWidths(xWidth, zWidth, k, operations));
  }

  // ---------------------------------------------------------------------
  // Cost-model versions.
  //
  // v2 is the model transcribed from the companion development at cb0fa12:
  // rippleAdderGateBound(w) = 9w + 2 (a bound), free sign extension, and no
  // allocation bookkeeping.
  //
  // v3 transcribes the operative model at companion commit d5a165b, namely
  // shorGateCostModel = shorGateResourceModel.toCostModel in
  // Framework/Gatecount/ResourceModel.lean:
  //   * addScaled is the exact Cuccaro modulo adder,
  //     (2w - 6) + (5w - 7) + (2w - 3) = 9w - 16 for w >= 3;
  //   * negate is complement + constant-one register + that adder,
  //     (w + (2w - 6) + 2) + (5w - 7) + (2w - 3) = 10w - 14 for w >= 3;
  //   * shiftL / shiftR / zeroExtend / zeroDealloc are free;
  //   * signExtend / signDealloc cost n CNOTs each.
  // Truncated subtraction matches the companion's Nat arithmetic.
  // ---------------------------------------------------------------------

  function truncatedSub(left, right) {
    return left > right ? left - right : 0n;
  }

  function rippleAdderGateBound(width) {
    requireNatural(width, "width");
    return 9n * BigInt(width) + 2n;
  }

  function negateGateBound(width) {
    return BigInt(width) + rippleAdderGateBound(width);
  }

  function cuccaroModAddGateCount(width) {
    requireNatural(width, "width");
    const w = BigInt(width);
    return truncatedSub(2n * w, 6n) + truncatedSub(5n * w, 7n) + truncatedSub(2n * w, 3n);
  }

  function cuccaroNegateGateCount(width) {
    requireNatural(width, "width");
    const w = BigInt(width);
    return (w + truncatedSub(2n * w, 6n) + 2n) +
      truncatedSub(5n * w, 7n) + truncatedSub(2n * w, 3n);
  }

  function topLimbWidth(width, limbWidth, k) {
    return Math.max(0, width - (k - 1) * limbWidth);
  }

  // The companion's allocChunkGate sign-extends only the top limb and
  // zero-extends the other k - 1 limbs, and zeroExtend / zeroDealloc are free.
  // Each of the two top limbs is extended once and deallocated once.
  function signExtensionAllocationGateCount(xWidth, zWidth, k, childWidth) {
    const limbWidth = phaseLimbWidth(xWidth, zWidth, k);
    return 2n * (
      truncatedSub(BigInt(childWidth), BigInt(topLimbWidth(xWidth, limbWidth, k))) +
      truncatedSub(BigInt(childWidth), BigInt(topLimbWidth(zWidth, limbWidth, k)))
    );
  }

  // The 4kW allocation bound from the companion's one-level recurrence lemma.
  // A bound used by the asymptotic proof layer, not a cost the operative model
  // charges. Retained only as a sensitivity comparison.
  function looseAllocationGateBound(xWidth, zWidth, k, childWidth) {
    return 4n * BigInt(k) * BigInt(childWidth);
  }

  function directSignedPhaseProductGateCount(xWidth, zWidth) {
    requireNatural(xWidth, "xWidth");
    requireNatural(zWidth, "zWidth");
    return 5n * BigInt(xWidth) * BigInt(zWidth);
  }

  const COST_MODELS = {
    "forshor-phase-product-gates-v2": {
      modelVersion: "forshor-phase-product-gates-v2",
      rippleAdder: rippleAdderGateBound,
      negate: negateGateBound,
      allocation: () => 0n,
    },
    "forshor-phase-product-gates-v3": {
      modelVersion: "forshor-phase-product-gates-v3",
      rippleAdder: cuccaroModAddGateCount,
      negate: cuccaroNegateGateCount,
      allocation: signExtensionAllocationGateCount,
    },
    "forshor-phase-product-gates-v3-loose4kw": {
      modelVersion: "forshor-phase-product-gates-v3-loose4kw",
      rippleAdder: cuccaroModAddGateCount,
      negate: cuccaroNegateGateCount,
      allocation: looseAllocationGateBound,
    },
  };

  const MODEL_ALIASES = {
    v2: "forshor-phase-product-gates-v2",
    v3: "forshor-phase-product-gates-v3",
    "v3-loose4kw": "forshor-phase-product-gates-v3-loose4kw",
  };

  function costsFor(version) {
    const resolved = MODEL_ALIASES[version] || version;
    const costs = COST_MODELS[resolved];
    if (!costs) throw new RangeError(`unknown cost model: ${version}`);
    return costs;
  }

  function plannerFor(costs) {
    function phaseArithmeticOpCost(workingWidth, operation) {
      const name = operation[0];
      if (name === "shiftL" || name === "shiftR" || name === "phaseProduct") return 0n;
      if (name === "negate") return 2n * costs.negate(workingWidth);
      if (name === "addScaled") return 2n * costs.rippleAdder(workingWidth);
      throw new RangeError(`unknown operation: ${name}`);
    }

    function analyzeProgram(xWidth, zWidth, candidate) {
      requireK(candidate.k);
      if (typeof candidate.policyId !== "string" || !candidate.policyId) {
        throw new TypeError("candidate policyId must be a nonempty string.");
      }
      const childWidth = nextSignedWidth(xWidth, zWidth, candidate.k, candidate.operations);
      let arithmeticGateCount = 0n;
      let arithmeticOperationCount = 0;
      let recursiveCallCount = 0;
      for (const operation of candidate.operations) {
        arithmeticGateCount += phaseArithmeticOpCost(childWidth, operation);
        if (operation[0] === "phaseProduct") recursiveCallCount += 1;
        else arithmeticOperationCount += 1;
      }
      arithmeticGateCount +=
        costs.allocation(xWidth, zWidth, candidate.k, childWidth);
      return {
        childWidth,
        arithmeticGateCount,
        arithmeticOperationCount,
        recursiveCallCount,
      };
    }

    function basePlan(width) {
      return {
        width,
        gateCount: directSignedPhaseProductGateCount(width, width),
        recursionHeight: 0,
        totalRecursiveCallCount: 0n,
        totalArithmeticOperationCount: 0n,
        choice: null,
        childPlan: null,
      };
    }

    function stepPlan(width, candidate, analysis, child) {
      const calls = BigInt(analysis.recursiveCallCount);
      return {
        width,
        gateCount: analysis.arithmeticGateCount + calls * child.gateCount,
        recursionHeight: child.recursionHeight + 1,
        totalRecursiveCallCount: calls * (child.totalRecursiveCallCount + 1n),
        totalArithmeticOperationCount:
          BigInt(analysis.arithmeticOperationCount) +
          calls * child.totalArithmeticOperationCount,
        choice: {
          policyId: candidate.policyId,
          k: candidate.k,
          childWidth: analysis.childWidth,
          localArithmeticGateCount: analysis.arithmeticGateCount,
          localArithmeticOperationCount: analysis.arithmeticOperationCount,
          recursiveCallCount: analysis.recursiveCallCount,
        },
        childPlan: child,
      };
    }

    function lowerGateCount(candidate, current) {
      return candidate.gateCount < current.gateCount ? candidate : current;
    }

    function chooseAtWidth(candidates, plans, width) {
      let current = basePlan(width);
      for (const candidate of candidates) {
        const analysis = analyzeProgram(width, width, candidate);
        if (analysis.childWidth < width && plans[analysis.childWidth] !== undefined) {
          current = lowerGateCount(
            stepPlan(width, candidate, analysis, plans[analysis.childWidth]),
            current,
          );
        }
      }
      return current;
    }

    // Readable dense reference retained for bounded equivalence tests.
    function buildPlanTable(candidates, maxWidth) {
      requireNatural(maxWidth, "maxWidth");
      if (!Array.isArray(candidates)) throw new TypeError("candidates must be an array.");
      const plans = [];
      for (let width = 0; width <= maxWidth; width += 1) {
        plans.push(chooseAtWidth(candidates, plans, width));
      }
      return plans;
    }

    // Production planner: memoize only widths reachable from the requested roots.
    function bestPlans(candidates, widths) {
      if (!Array.isArray(candidates)) throw new TypeError("candidates must be an array.");
      if (!Array.isArray(widths)) throw new TypeError("widths must be an array.");
      widths.forEach(width => requireNatural(width, "width"));
      const memo = new Map();

      function solve(width) {
        if (memo.has(width)) return memo.get(width);
        let current = basePlan(width);
        for (const candidate of candidates) {
          const analysis = analyzeProgram(width, width, candidate);
          if (analysis.childWidth < width) {
            current = lowerGateCount(
              stepPlan(width, candidate, analysis, solve(analysis.childWidth)),
              current,
            );
          }
        }
        memo.set(width, current);
        return current;
      }

      return widths.map(solve);
    }

    function bestPlan(candidates, width) {
      return bestPlans(candidates, [width])[0];
    }

    return {
      modelVersion: costs.modelVersion,
      phaseArithmeticOpCost,
      analyzeProgram,
      basePlan,
      stepPlan,
      lowerGateCount,
      chooseAtWidth,
      buildPlanTable,
      bestPlans,
      bestPlan,
    };
  }

  const PLANNERS = Object.fromEntries(
    Object.keys(COST_MODELS).map(version => [version, plannerFor(COST_MODELS[version])]),
  );

  const defaultPlanner = PLANNERS["forshor-phase-product-gates-v2"];
  const modelVersion = defaultPlanner.modelVersion;
  const {
    phaseArithmeticOpCost,
    analyzeProgram,
    basePlan,
    stepPlan,
    lowerGateCount,
    chooseAtWidth,
    buildPlanTable,
    bestPlans,
    bestPlan,
  } = defaultPlanner;

  function phaseProductResultDescriptors(data) {
    if (!data || !Array.isArray(data.policies)) {
      throw new TypeError("leaderboard policies must be an array.");
    }
    const descriptors = [];
    for (const policy of data.policies) {
      if (typeof policy.policy_id !== "string" || !policy.policy_id) {
        throw new TypeError("archived policy ID must be a nonempty string.");
      }
      if (!Array.isArray(policy.results)) {
        throw new TypeError(`policy ${policy.policy_id} results must be an array.`);
      }
      for (const result of policy.results) {
        if (result.mode !== "PhaseProduct") continue;
        requireK(result.k);
        if (typeof policy.operations_path !== "string" || !policy.operations_path) {
          throw new TypeError(`policy ${policy.policy_id} operations are unavailable.`);
        }
        descriptors.push({
          policyId: policy.policy_id,
          operationsPath: policy.operations_path,
          result,
        });
      }
    }
    return descriptors.sort(
      (left, right) => left.result.k - right.result.k ||
        left.policyId.localeCompare(right.policyId),
    );
  }

  function validateArchivedTarget(descriptor, operationData) {
    if (!operationData || operationData.schema_version !== 1) {
      throw new Error("Unsupported operations schema.");
    }
    if (operationData.policy_id !== descriptor.policyId) {
      throw new Error(`Operations policy ID does not match ${descriptor.policyId}.`);
    }
    const target = operationData.targets.find(
      item => item.mode === "PhaseProduct" && item.k === descriptor.result.k,
    );
    if (!target || !Array.isArray(target.operations)) {
      throw new Error(
        `PhaseProduct k=${descriptor.result.k} operations are missing for ${descriptor.policyId}.`,
      );
    }
    const phaseProducts = target.operations.filter(
      operation => operation[0] === "phaseProduct",
    ).length;
    const arithmetic = target.operations.length - phaseProducts;
    if (target.operations.length !== descriptor.result.total_operation_count ||
        phaseProducts !== descriptor.result.phase_product_count ||
        arithmetic !== descriptor.result.arithmetic_operation_count) {
      throw new Error(
        `Archived operation counts do not match PhaseProduct k=${descriptor.result.k} results.`,
      );
    }
    return {
      policyId: descriptor.policyId,
      k: descriptor.result.k,
      operations: target.operations,
    };
  }

  async function archivedPhaseProductCandidates(data, loadOperations) {
    if (typeof loadOperations !== "function") {
      throw new TypeError("loadOperations must be a function.");
    }
    const cache = new Map();
    function load(path) {
      if (!cache.has(path)) cache.set(path, Promise.resolve(loadOperations(path)));
      return cache.get(path);
    }
    return Promise.all(
      phaseProductResultDescriptors(data).map(async descriptor =>
        validateArchivedTarget(descriptor, await load(descriptor.operationsPath))),
    );
  }

  function decimal(value) {
    return typeof value === "bigint" ? value.toString() : value;
  }

  function planLevels(plan) {
    const levels = [];
    let current = plan;
    let instances = 1n;
    let level = 0;
    while (current.choice !== null) {
      if (current.childPlan === null) {
        throw new Error("recursive plan is missing its selected child.");
      }
      const choice = current.choice;
      levels.push({
        type: "recursive",
        level,
        inputWidth: current.width,
        instances,
        policyId: choice.policyId,
        k: choice.k,
        childWidth: choice.childWidth,
        recursiveProductsPerNode: choice.recursiveCallCount,
        localGateCountPerNode: choice.localArithmeticGateCount,
        expandedLocalGateCount: instances * choice.localArithmeticGateCount,
        localArithmeticOperationsPerNode: choice.localArithmeticOperationCount,
        expandedArithmeticOperations:
          instances * BigInt(choice.localArithmeticOperationCount),
      });
      instances *= BigInt(choice.recursiveCallCount);
      current = current.childPlan;
      level += 1;
    }
    levels.push({
      type: "direct",
      level,
      inputWidth: current.width,
      instances,
      gateCountPerNode: current.gateCount,
      expandedGateCount: instances * current.gateCount,
    });
    return levels;
  }

  function compactLevel(level) {
    if (level.type === "direct") {
      return {
        type: "direct",
        level: level.level,
        input_width: level.inputWidth,
        instances: decimal(level.instances),
        gate_count_per_node: decimal(level.gateCountPerNode),
        expanded_gate_count: decimal(level.expandedGateCount),
      };
    }
    return {
      type: "recursive",
      level: level.level,
      input_width: level.inputWidth,
      instances: decimal(level.instances),
      policy_id: level.policyId,
      k: level.k,
      child_width: level.childWidth,
      recursive_products_per_node: level.recursiveProductsPerNode,
      local_gate_count_per_node: decimal(level.localGateCountPerNode),
      expanded_local_gate_count: decimal(level.expandedLocalGateCount),
      local_arithmetic_operations_per_node: level.localArithmeticOperationsPerNode,
      expanded_arithmetic_operations: decimal(level.expandedArithmeticOperations),
    };
  }

  function compactPlan(plan, version = modelVersion) {
    return {
      model_version: version,
      objective,
      width: plan.width,
      gate_count: decimal(plan.gateCount),
      recursion_height: plan.recursionHeight,
      recursive_call_count: decimal(plan.totalRecursiveCallCount),
      arithmetic_operation_count: decimal(plan.totalArithmeticOperationCount),
      steps: planLevels(plan).map(compactLevel),
    };
  }

  function selectModel(version) {
    const costs = costsFor(version);
    const planner = PLANNERS[costs.modelVersion];
    return Object.freeze(Object.assign({}, planner, {
      objective,
      planLevels,
      compactPlan: plan => compactPlan(plan, costs.modelVersion),
    }));
  }

  return Object.freeze({
    modelVersion,
    objective,
    modelVersions: Object.freeze(Object.keys(COST_MODELS)),
    selectModel,
    truncatedSub,
    cuccaroModAddGateCount,
    cuccaroNegateGateCount,
    topLimbWidth,
    signExtensionAllocationGateCount,
    looseAllocationGateBound,
    phaseLimbWidthOfWidth,
    phaseLimbWidth,
    phaseSplitLogicalWidth,
    initWidthState,
    updateWidthState,
    scanNeededWidths,
    maximumNeededWidth,
    nextSignedWidth,
    rippleAdderGateBound,
    negateGateBound,
    directSignedPhaseProductGateCount,
    phaseArithmeticOpCost,
    analyzeProgram,
    basePlan,
    stepPlan,
    lowerGateCount,
    chooseAtWidth,
    buildPlanTable,
    bestPlans,
    bestPlan,
    phaseProductResultDescriptors,
    archivedPhaseProductCandidates,
    planLevels,
    compactPlan,
  });
}));
