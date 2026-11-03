# Independent one-state policy experiment review

Reviewed 2026-11-02. **PASS for the displayed staged policy obstruction, with the source-level formal-negation and integration boundaries below.** This is an independent mathematical and Lean audit of the fixed source, not an author-approved correction or a completed formalization of Theorem 3.7(i).

## Identity and source

- `.local/OneStatePolicyExperiment.lean`: SHA-256 `ac9fd551a5fb69f537745ec4b89874e52fa26649deed2e8e583f556146046fd3`.
- `.local/OneStateExperiment.lean`: `e7b4220fab2b6495905667e1530e1f32d2e8ce564ac7bdc31f0299cf088ecc8f`.
- `.local/OneStateTrajectory.lean`: `091d881d496d1709115cb088a749d708633513c45bf84154ac534c93a02133d1`.
- `Formalization/Obstructions/OneStateParameters.lean`: `2be78dda039c300ebcc4455658994b8b0495c7f5da6ef31c1db20fb27b1586ba`.
- `source/upstream/tex/chapters/prelim.tex`: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.
- `source/upstream/tex/chapters/generative_model_model_based.tex`: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

The source gives known deterministic bounded rewards and finite common state and action spaces (prelim lines 31–45), stationary randomized policies (66–76), and Q by a forced initial action and policy actions thereafter (114–123). It defines Q* using a simultaneous deterministic optimum (136–141). The generative model supplies independent row samples (model-based lines 15–31). Theorem `theorem:azar` (1443–1464), part (i), claims for every deterministic policy estimator a model where strict Q loss exceeds ε with probability at least 1/4, when `SA≥16`, `γ∈[2/3,1)`, `0<ε<1/[32(1−γ)]`, and `N≤c_N log(SA)/[(1−γ)^3 ε²]`. The printed hypotheses do not exclude `S=1, A=16`; this choice also meets the earlier `A≥2` convention.

## Quantifiers and semantic review

The displayed obstruction has inputs `c : ℝ` and `hc : 0 < c`, both SOURCE (candidate positive universal constant); STANDING 0, TYPING 0, RULED 0, EXCESS 0. Its conclusion produces ε and all feasibility assertions, an inhabited model class, and one jointly measurable deterministic policy estimator **before** quantifying over every admissible model with discount 2/3. It proves zero loss for every data outcome and probability strictly below 1/4 for every such model. The rule accepts the model's known reward and discount and its samples; it does not receive the unknown transition kernel or target Q. Uniformity in the known reward is stronger than fixing one known reward before varying transitions.

The imported sample data is indexed by `(state, action, sample-index)` with one sample per row. `oneStateGenerativeLaw` is the finite product of the actual transition row measures, and its probability, coordinate marginal and joint-independence results are proved. Since the state carrier is singleton, all data values are necessarily the self-loop; this is the genuine product experiment. A concrete admissible MDP witnesses nonemptiness.

The rule chooses the least index in the finite nonempty set of reward maxima. The exact selection-event equivalence correctly handles all ties, including multiple equal maxima, and its finite measurable comparisons establish measurability in the reward table. The estimator ignores discount and samples, and the proved joint measurability covers the reward, discount and data product and the state-indexed deterministic policy output. Its point-mass embedding produces a stationary deterministic policy.

For every one-state model, the policy's selected reward is maximal. The proof shows the explicit one-state Q satisfies its policy fixed-point equation and uses the forced-first-action trajectory bridge to identify actual trajectory Q on the entire state-action array. The comparison is the actual trajectory Q of the constructed optimal greedy policy, whose imported result establishes dominance over stationary randomized policies. Consequently equality holds even at first actions the selected policy never takes, and the finite sup norm is zero pointwise for every data value. The strict error event is empty for ε≥0, so its actual product probability is zero. No assumed error bound, exceptional data set, or arbitrary experiment measure is used.

For each c>0, the imported feasibility proof constructs a positive ε sufficiently small that N=1 satisfies the sample upper bound, while ε is strictly below 3/32, γ=2/3 is in the permitted interval, and `1·16≥16`. Thus reducing the proposed universal constant does not exclude the instance.

## Validation and limits

Using the pinned `.local/lean`, I compiled fresh temporary copies of the exact staged trajectory and experiment sources to temporary `.olean` files, then compiled a copy of the exact policy source with nine appended axiom inspections, with that temporary directory and the project/package build-library directories on `LEAN_PATH`. The first attempt from the project directory failed because Lean requires input files under its root; rerunning from the temporary directory succeeded. The probe was deleted. All nine inspected declarations (`rewardMaximizers_nonempty`, `measurableRewardGreedy_max`, `measurableRewardGreedy_eq_iff`, `measurableRewardGreedy_measurable`, `oneStatePolicyEstimator_joint_measurable`, `oneStatePolicyEstimator_actualQ`, `oneStatePolicyEstimator_loss`, `oneStatePolicyEstimator_failure`, and `oneState_theorem37_i_obstruction`) depend only on `propext`, `Classical.choice`, and `Quot.sound`. Compilation was coordinated under the two-compiler limit.

This establishes the displayed positive obstruction under the printed known-reward conventions, not a Lean theorem literally negating a fully encoded general statement of Theorem 3.7(i). The latter would need an exact source-facing proposition for all parameter, estimator, model and experiment quantifiers, a formal negation/composition, and independent review. The staged import also needs replacement by the production module path on integration, followed by compilation and axiom checks of the actual integrated export. No author intent, correction, or broader theorem completion is inferred.

## Integrated export recheck

The integrated source `Formalization/Obstructions/OneStatePolicyExperiment.lean` has SHA-256 `edbf5df9b2fd4025c3ae22bc509cfb180ce5a455982ddedc808e4e6cb6c78a45`. A direct unified diff against the reviewed staged source showed exactly one change: the import `OneStateExperiment` became `Formalization.Obstructions.OneStateExperiment`. The integrated `Formalization/Obstructions/OneStateExperiment.lean` has SHA-256 `9e0edf146a203da6be3f7c7d2a2e77f69725d592e26ce844d08f99a38a3c2099` and likewise differs from its staged source only in the trajectory import path.

After the project check built the integrated dependency, I compiled a temporary copy of the exact integrated policy source with the same nine appended `#print axioms` commands using `bash scripts/lean-local.sh` and the actual project build path. It compiled successfully; all nine declarations again depend only on `propext`, `Classical.choice`, and `Quot.sound`. The temporary probe was deleted. The project check separately compiled the actual integrated policy module. The remaining source-level formal-negation and author-correction boundaries above still apply.
