# Independent review: policy V–Q Bellman fixed-point bridge

**Verdict: PASS for the policy-averaging and Bellman identities between the project's two independently constructed fixed points; the source's infinite-trajectory interpretation remains OPEN.** No implementation defect or extra hypothesis was found. This is a scoped ordinary source/code review, not an author-approved frozen-declaration audit or a claim that `V^π`, `Q^π`, or Chapter 2 is complete.

The reviewer did not author `Formalization/MDP/PolicyValueQ.lean` or its `Basic.lean`, `FixedPoint.lean`, and `DiscountedFiniteTrajectory.lean` dependencies. I reconstructed the source obligation before inspecting the target code. The separate prior dependency reviews cited below are supporting evidence; this review does not repeat every proof in their import closures.

## Source-first reconstruction

- `source/upstream/tex/chapters/prelim.tex` lines 31–52 specifies finite state and action spaces, stationary normalized transition distributions, deterministic rewards in `[0,1]`, and discount `0 ≤ γ < 1`. Lines 63–74 define a stationary policy as a probability distribution on actions at each state and define `P_π` by averaging the original transition kernels under that policy.
- Lines 89–102 define the **infinite trajectory expectation** `V^π`. Lines 114–123 define `Q^π(s,a)` with the first action fixed and subsequent actions drawn from the policy; this meaning applies to every action, including one given zero mass by π. The policy-average identity at 123–128 is `V^π(s) = Σ_a π(a|s) Q^π(s,a)` for every s.
- Lines 190–209 define `T^π Q(s,a) = r(s,a) + γ Σ_t P(t|s,a) Σ_b π(b|t) Q(t,b)` and state that the source's trajectory Q is its unique fixed point. Lines 210–223 give `T_π V(s) = Σ_a π(a|s)r(s,a) + γ Σ_t P_π(t|s)V(t)` and state that the source trajectory value is a fixed point. A valid fixed-point-only bridge can prove the average of the unique Q-Bellman fixed point is the unique state-Bellman fixed point, but source trajectory identification is a further theorem.

Source SHA-256 matches `source/provenance.json`: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.

## Expanded model and binder review

`Basic.lean` defines `FiniteDistribution` by a mass function, nonnegativity at each point and total mass one; its `expectation` is the finite weighted sum. `DiscountedMDP` contains nonempty finite state and action carriers, the per-state/action normalized transition distributions, reward table and its lower and upper bounds, and γ with `0 ≤ γ < 1`. `StationaryPolicy` is a function from states to actual normalized finite action distributions. `policyTransition` binds the policy law to `M.transition s`; it does not reuse a transition distribution from a different action or state.

| Binder / expanded field | Classification and scope |
| --- | --- |
| `State`, `Action`, their `Fintype` instances | TYPING/source finite carriers; prelim lines 33–38. |
| `M.state_nonempty`, `M.action_nonempty` | STANDING, nonempty MDP state/action carriers, consistent with source finite probability distributions and available actions. |
| `M.transition s a` and its mass, nonnegativity, normalization | SOURCE/STANDING: the actual kernel `P(·|s,a)` and probability laws, lines 38 and 68–74. |
| `M.reward`, `M.reward_nonneg`, `M.reward_le_one` | SOURCE/STANDING: deterministic reward and `[0,1]`, line 42. |
| `M.discount`, `M.discount_nonneg`, `M.discount_lt_one` | SOURCE/STANDING: γ and exact interval, line 45, including γ=0. |
| `π : StationaryPolicy` and each action probability vector's mass, nonnegativity, normalization | SOURCE/STANDING: arbitrary stationary randomized policy, lines 66–67. |
| `Q : State → Action → ℝ` in `policyAverageQ_is_value_fixed` | SOURCE: any real array, lines 193–196; no reward-range restriction. |
| `hQ : M.qBellman π Q = Q` in `policyAverageQ_is_value_fixed` | An explicit conditional premise for the helper's *fixed-point implication*, not a purported unconditional source theorem. It is discharged from the proved `policyFixedPoint_spec` when deriving the public fixed-point identity. |
| `s : State`, `a : Action` in `policyFixedPoint_eq_reward_add_value` | SOURCE universal coordinates. No positivity of `π(a|s)` is required. |

The two final results have no extra fixed-point hypothesis, bridge assumption, measurability assumption, or optimality premise. All discount, reward, transition and policy data are from the one model/policy. The conditional helper's `hQ` is consumed rather than added to the final signatures. Known reward is relevant to the paper's learning access, but is not a mathematical premise of these Bellman equalities.

## Code and proof inspection

1. `policyAverageQ` (target lines 16–18) is exactly `s ↦ (π s).expectation (Q s)`, i.e. the true finite policy-weighted average; it has no default action, fallback or assumption of equality to a value function.
2. `qBellman` in `Basic.lean:176–180` expands to the correct immediate reward plus `γ` times the transition expectation of the **next-state** policy expectation. `valueBellman` at 182–185 uses the reward average and the policy-induced mixture; `FiniteDistribution.expectation_bind` proves the relevant iterated-expectation equality. Applying it in `policyAverageQ_is_value_fixed` (target lines 20–33) correctly rearranges finite sums. The equation is valid for every state and general randomized policy; it has the correct action/next-state order.
3. `FixedPoint.lean:51–69,82–90` constructs the unique policy Q-Bellman fixed point from a contraction on all finite real Q arrays and proves its equation. `DiscountedFiniteTrajectory.lean:117–154` independently proves the state Bellman map is a contraction on the full state-function space and selects its fixed point from proved unique existence. There is no choice from mere existence and no definition of either as the other. Target lines 37–42 supply the Q fixed-point equation to the conditional helper and the resulting state equation to the state fixed-point characterization. Therefore `valueFixedPoint_eq_policyAverageQ` asserts an unconditional equality of the two already-defined solutions.
4. `policyFixedPoint_eq_reward_add_value` (46–55) evaluates the proved Q fixed-point equation at arbitrary `(s,a)` and substitutes the proved averaged-Q/state equality. Its output is exactly `Q_fixed(s,a) = r(s,a) + γ Σ_t P(t|s,a) V_fixed(t)`. No `π(a|s) > 0` assumption is inserted, and the initial action is not averaged. Combining this with the previous equality gives the nested action/transition Bellman expression from the source at the Bellman-solution level.

`docs/critic-fixedpoint-review.md` separately reviews the full Q contraction/selection and axioms; `docs/critic-discounted-finite.md` separately reviews the state contraction, finite discounted paths, and convergence to the state fixed point. This target consumes their actual proved interfaces, not a bundled hypothesis that the desired result holds.

## Checks and identity

Reviewed SHA-256 digests:

| File | SHA-256 |
| --- | --- |
| `Formalization/MDP/PolicyValueQ.lean` | `3f1c5c812a7b60a8f99aecce5d7ce02cc3bab92c8335186feccf7e8fbc9b6369` |
| `Formalization/MDP/Basic.lean` | `ecf28ee04a78405be352f5453d957f34a7883d33304b21255a9f7f444e0bc088` |
| `Formalization/MDP/FixedPoint.lean` | `b7c7b6338d1ec5005942e3b0f80676ed8e0e2dfb650a2cb01638642fe65f642e` |
| `Formalization/MDP/DiscountedFiniteTrajectory.lean` | `c6b25ae5dfc3dc38f1d4ae654524764e10474ba04d94a0925242de5d88ccbdd6` |

`bash scripts/lean-local.sh Formalization/MDP/PolicyValueQ.lean` passed with no diagnostics. A temporary probe imported the built `Formalization.MDP.PolicyValueQ` export, expanded both final claims to literal finite weighted sums at arbitrary `s` and `a`, and passed. The same probe reported exactly `propext`, `Classical.choice`, and `Quot.sound` via `#print axioms` for `policyAverageQ_is_value_fixed`, `valueFixedPoint_eq_policyAverageQ`, and `policyFixedPoint_eq_reward_add_value`. The existing target `.olean` was newer than the target source; the source compiler check and exported-module probe were separate checks. The probe was deleted. No full integration build was run for this review.

## Boundary

These results say that the project's Bellman fixed-point objects obey the proper algebraic equations. They **do not** define the source's expectation over an infinite path or prove that `M.valueFixedPoint π` and `M.policyFixedPoint π` equal the source's `V^π` and `Q^π`. The finite-discounted module supplies finite sampled state returns and their limit, but does not by itself justify passing to an expectation on an infinite path or construct the conditioned infinite Q law. Completing the paper's trajectory-defined assertions requires those independently defined infinite objects, their measurability/summability, and proved identifications (including first-action conditioning for all actions). No such source-semantic closure is claimed here.
