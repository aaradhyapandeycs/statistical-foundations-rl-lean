# Independent one-state generative-experiment review

Reviewed 2026-11-02. Verdict: **PASS for the displayed uniform Q-estimation obstruction under the printed source’s known-reward model; source-level formal negation remains unencoded.** The construction is substantive and supplies the missing statistical experiment and estimator quantifier order. It is not an author-approved correction, an integrated export, or a theorem literally named as the negation of a formalized source statement.

## Identity and source

- `.local/OneStateExperiment.lean`: SHA-256 `e7b4220fab2b6495905667e1530e1f32d2e8ce564ac7bdc31f0299cf088ecc8f`.
- `.local/OneStateTrajectory.lean`: SHA-256 `091d881d496d1709115cb088a749d708633513c45bf84154ac534c93a02133d1`.
- `Formalization/Obstructions/OneStateParameters.lean`: SHA-256 `2be78dda039c300ebcc4455658994b8b0495c7f5da6ef31c1db20fb27b1586ba`.
- `prelim.tex`: SHA-256 `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.
- `generative_model_model_based.tex`: SHA-256 `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

The source defines finite carriers with `S` states and `A` actions and fully known deterministic rewards in `[0,1]` (`prelim.tex:31–45`). Stationary randomized policies are the policy carrier (`prelim.tex:66–76`); Q* is the Q of a simultaneously optimal deterministic policy (`prelim.tex:136–141`). The generative model supplies independent next-state observations (`generative_model_model_based.tex:15–23`). Known reward is reiterated at line 31; lines 74–75 describe the transition kernel as the only unknown model component, supporting known discount as well. Theorem `theorem:azar`, lines 1444–1464, permits `SA ≥ 16`, `γ ∈ [2/3,1)`, `0 < ε < 1/(32(1−γ))`, and `N ≤ c_N log(SA)/((1−γ)^3 ε²)`. Part (ii) asserts a model with strict-error probability at least 1/4 for every Q estimator.

The literal printed assumptions permit `S=1`, `A=16`, `γ=2/3`, and `N=1`. No `S ≥ 2` hypothesis was found in this theorem or the quoted source carrier conventions. Sixteen actions also meet a possible `A ≥ 2` policy-learning convention. Any intended additional restriction excluding this instance would need to be explicit and documented; it cannot silently repair the reviewed printed statement.

## Quantifier and binder audit

Main target: `StatisticalRL.Obstructions.oneState_theorem37_ii_obstruction`.

| Actual theorem input | Bin | Reason |
|---|---|---|
| `c : ℝ` | SOURCE | candidate universal positive lower-bound constant |
| `hc : 0 < c` | SOURCE | source universal constant is positive |

Counts: SOURCE 2, STANDING 0, TYPING 0, RULED 0, EXCESS 0. All parameter feasibility, model inhabitation, estimator existence, measurability, and uniform success are conclusions proved in the body, not assumptions. Fixed carriers and known-input estimator types are explicit in the conclusion. The underlying `DiscountedMDP` validity predicates require nonempty finite carriers, normalized nonnegative transition rows, rewards in `[0,1]`, and discount in `[0,1)`; these match the source standing model.

The actual order is `∀ c>0, ∃ ε>0, feasible-parameters ∧ inhabited-model-class ∧ ∃ estimator, measurable ∧ ∀ M, M.discount=2/3 → P_M(error>ε)<1/4`. Crucially the estimator is chosen before the unknown model. It takes only the known reward, discount, and sample data; it does not take M, its transition kernel, Q*, or a proof of its conclusion. It is a single explicit formula, in fact independent of c, ε, and data. Supplying `M.reward` to a fixed rule under the model quantifier is legitimate because reward is known. Even if reward were fixed before the unknown-transition quantifier, this same proof is stronger: its success is uniform over every valid reward table, and hence over each fixed known table.

For the intermediate `oneStateExperimentEstimator_failure`, the inputs are `M` (SOURCE model), `ε : ℝ` (SOURCE accuracy), and `hε : 0 ≤ ε` (SOURCE accuracy range, weakened validly to include zero). It has no external exactness or concentration hypothesis. `oneStateKnownRewardEstimator_exact` uses equality proofs connecting the supplied known reward and discount to the model; the final failure theorem supplies both with `rfl`, so these are not unknown-input access or assumed estimates.

## Genuine experiment and estimator

`OneSampleIndex = (Fin 1 × Fin 16) × Fin 1` provides exactly one observation per state-action row. `OneSampleData` stores its next-state value. `oneStateGenerativeLaw M` is the actual finite product of those rows’ PMF-derived measures. The probability instance, exact coordinate marginal theorem, and joint independence theorem are all proved. The degeneracy of singleton-state samples is a mathematical feature of this permitted model, not a replacement of the generative law by an unspecified or convenient probability measure. `oneStateExampleMDP` supplies a concrete admissible zero-reward model with discount 2/3, preventing vacuity of the quantified class.

The rule is `Qhat(r,γ,data)(s,a) = r(s,a) + γ max_b r(s,b)/(1−γ)`. The finite maximum is an actual maximum of the known reward table. Data measurability follows because the rule ignores data. The stronger joint Borel measurability in known reward, discount, and data is proved by finite maxima and measurable arithmetic. Total real division at γ=1 only extends the estimator’s ambient known-input domain; no theorem evaluates an admissible MDP there, and no off-domain value is used to discharge source mathematics. This is an estimator rule, not a source characterization-defined object with a hidden default branch.

Every transition distribution on a singleton state is necessarily the self-loop law. The imported one-state result proves the displayed formula solves the actual optimality Bellman equation. The trajectory bridge then identifies it with the optimal policy’s actual forced-first-action infinite-return expectation, including actions with zero policy mass. The constructed policy dominates all stationary randomized policies, which matches the source policy convention. Thus the error norm is the finite sup norm of the entire actual Q-array, not merely a Bellman residual or a stipulated target.

Exact equality holds for every possible data value and every admissible one-state model. Subtraction yields norm error zero. For ε≥0 the event `ε < 0` is empty, so its measure, and therefore its `Measure.real`, is exactly zero. The strict event matches the source’s `‖Qhat−Q*‖∞ > ε`. No a.e. exception, probability conversion, conditioning-on-null-event issue, or arbitrary-measure premise survives in the actual experiment theorem.

## Parameter feasibility

For each c>0, `oneState_parameter_feasible` chooses `ε = min(1/64, 27 c log 16)`. Positivity of log 16 makes ε positive; ε≤1/64 gives the required strict upper bound ε<3/32. With x=27c log16, ε≤x and ε≤1 imply ε²≤x, hence `1 ≤ x/ε²`, exactly the N=1 sample bound at γ=2/3. `oneState_theorem37_hypotheses_feasible` also proves the discount endpoints and `1·16 ≥16`. Consequently arbitrarily small proposed universal constants cannot avoid the counterexample merely by making the allowed sample range empty.

## Formal-negation boundary

Mathematically, under the explicit printed conventions, the construction excludes every proposed positive universal c_N: choose its feasible ε and the displayed single estimator; then every candidate model has failure probability zero, contradicting the claimed existence of a model with probability at least 1/4. The quantifier reversal is the correct one and the known-input and statistical requirements are now represented explicitly.

However, this file does **not** define the entire source claim as a Lean proposition and prove its literal negation. There is no general formal `Theorem37ii` binding S, A, γ, N, ε, the full estimator class, the model class and the exact experiment, followed by `¬ Theorem37ii`. The present positive obstruction supplies the ingredients for that final logical composition, but that source-level formal-negation declaration and its exact source correspondence remain to be written and independently checked before claiming a fully encoded refutation. The source theorem itself must not be rewritten or marked proved with an added `S ≥ 2` assumption without a visible correction process.

## Independent validation and remaining work

The exact staged source and an exact copied-source probe with eight appended `#print axioms` were compiled using the pinned `.local/lean`, with `.local`, project build, and all existing package build-library paths in `LEAN_PATH`. The copied-source probe was deleted afterwards. The first attempted probe omitted package paths and failed only with `unknown module prefix Mathlib`; correcting the search path resolved it.

All eight checks report exactly `[propext, Classical.choice, Quot.sound]`: `oneStateGenerativeLaw_probability`, `oneStateGenerativeLaw_marginal`, `oneStateGenerativeLaw_independent`, `oneStateExampleMDP_discount`, `oneStateExperimentEstimator_measurable`, `oneStateExperimentEstimator_joint_measurable`, `oneStateExperimentEstimator_failure`, and `oneState_theorem37_ii_obstruction`. No custom axiom, placeholder, or unfinished statistical premise was found. One compiler was used sequentially, coordinated within the shared two-compiler limit.

Remaining work: integrate the independently reviewed one-state trajectory dependency, replace its staged import with the real project module, compile/audit actual production exports, and (if full formal refutation is claimed) add the exact source-level lower-bound proposition and formal negation/composition. This review does not infer author approval, resolve unprinted author intent, or certify the original cited lower-bound paper. The staged source and its trajectory dependency remain unchanged.

## Integrated-source recheck

The integrated `Formalization/Obstructions/OneStateExperiment.lean` has SHA-256 `9e0edf146a203da6be3f7c7d2a2e77f69725d592e26ce844d08f99a38a3c2099`. A byte comparison verified that its complete difference from the reviewed staged source is exactly `import OneStateTrajectory` becoming `import Formalization.Obstructions.OneStateTrajectory`. No definition, theorem signature, proof or comment changed.

`bash scripts/lean-local.sh Formalization/Obstructions/OneStateExperiment.lean` independently compiled the actual integrated source with exit 0 and no diagnostics. An initial import-only axiom probe found that this new module’s production `.olean` had not yet been generated; source compilation without `-o` does not generate that artifact. I therefore audited an exact copy of the integrated source with the same eight appended `#print axioms` commands using `bash scripts/lean-local.sh .local/OneStateIntegratedCriticAudit.lean`. It compiled successfully, and every axiom list again contains exactly `propext`, `Classical.choice`, and `Quot.sound`. The probe was deleted. This confirms the import-only integration preserves the reviewed result and its axiom closure; production artifact generation and import-closure checking remain part of the lead’s integration check. The formal-negation boundary above is unchanged.
