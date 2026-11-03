# Staged source-facing proposition and negation for Theorem 3.7(ii)

`.local/Theorem37Negation.lean` defines a quantified proposition `printedTheorem37ii` for the printed lower bound in an explicit known-reward, fixed-row generative experiment, and proves its literal Lean negation `not_printedTheorem37ii`. The proof instantiates the proposition at `S=1`, `A=16`, `γ=2/3`, `N=1` using the independently reviewed exact known-reward one-state estimator and the reviewed feasibility theorem. This is a staged formalization and requires an independent source/binder/axiom audit and project integration. It is **not yet a claim of an author-approved or fully certified negation of the manuscript's theorem**; the semantic choices and remaining correspondence boundaries are stated below.

## Source and statement encoded

The target is `source/upstream/tex/chapters/generative_model_model_based.tex:1438–1464`, label `theorem:azar`, part (ii). The source's MDP, known reward, trajectory Q and stationary-policy definitions are `prelim.tex:31–45,63–76,114–141`; the independent generative query and known-reward model is repeated at model-based chapter lines 15–31. The source gives `SA≥16`, `2/3≤γ<1`, `0<ε<1/[32(1−γ)]`, and `N≤c_N log(SA)/[(1−γ)^3 ε²]`, then claims for every Q estimator the existence of a fixed-size MDP with error probability `≥1/4`.

The staged `printedTheorem37ii` makes the following quantifier order explicit:

```text
∃ c>0,
  ∀ S A N γ ε satisfying the displayed source restrictions,
    ∀ measurable estimator and every model-independent random seed law,
      ∃ admissible S-state/A-action MDP M with M.discount = γ,
        P_M(‖Qhat−Q*‖∞ > ε) ≥ 1/4.
```

`S`, `A`, `N` range over natural numbers; `Fin S` and `Fin A` implement the source's labeled finite carriers. The proposition imposes **no extra N>0 premise**: the printed theorem does not explicitly display one. Its counterexample uses N=1, so the result does not rely on any possible N=0 interpretation. `DiscountedMDP` stores nonempty carriers, normalized nonnegative transition rows, deterministic rewards in `[0,1]` and `0≤discount<1`. The MDP's discount is required to equal the universally quantified γ. The estimator may depend on `(S,A,N,γ,ε,c)` in the usual lower-bound order, since it is quantified after those choices; the one-state witness happens not to depend on c or ε.

`Theorem37Samples S A N` is the full array of next-state observations indexed by `(s,a,i)` with `i : Fin N`. `theorem37GenerativeLaw M N` is the finite product of the actual transition-row measures for these indices. Its probability, true-coordinate-marginal and full joint independence theorems are proved; it is not an abstract or assumed law. Independent randomized procedures are represented using an arbitrary seed carrier, probability law and measurable estimator, with the actual sample law multiplied by the seed law. The source does not formalize randomization or estimator measurability, so `Theorem37QEstimator` spells out one standard interpretation: a measurable map of data and seed for each known reward table and known discount. The model's reward and discount are supplied as known observable inputs; the hidden transition kernel is not an estimator input. This includes all deterministic measurable estimators and independently seeded randomized estimators within the represented universe. No general representation theorem for every conceivable probability-kernel formulation or higher-universe seed is asserted.

The target Q is `M.trajectoryExpectedQ M.optimalGreedyPolicy`, evaluated under the actual forced-first-action infinite trajectory law, and the error is the finite sup norm of the entire Q array. Existing reviewed results prove that this greedy policy simultaneously dominates all stationary randomized policies and attains the optimal Bellman Q. The manuscript's stationary policy carrier supports that representation; an independently stated unrestricted history-dependent-policy equivalence is not proved by this module. A source auditor must assess these estimator and optimal-policy interpretations before treating `printedTheorem37ii` as an exact authoritative transcription. The source does not itself supply a Lean declaration, so this is not an author-frozen theorem.

## Negation and dependencies

For arbitrary proposed `c>0`, `oneState_theorem37_hypotheses_feasible` supplies an ε satisfying the printed bound with S=1, A=16, γ=2/3 and N=1. `theorem37OneStateEstimator` is the fixed known-reward rule

```text
Qhat(r, γ, data, seed)(s,a) = r(s,a) + γ max_b r(s,b)/(1−γ).
```

It is measurable, ignores data and seed, and takes no unknown transition kernel as input. `theorem37OneStateEstimator_error` applies the previously reviewed actual-trajectory one-state result to show that its full-array error is zero for **every** admissible one-state model and **every** observation and seed. The formal negation assumes `printedTheorem37ii`, instantiates its universal estimator quantifier with this fixed estimator and the deterministic `Unit` seed, and obtains the source's claimed M. Its strict-error event is empty, so its real probability is zero, contradicting `≥1/4`. It does not assume the conclusion, the error bound, source failure, or a model-specific estimator. The underlying one-state exactness is stronger than required: it holds for all discounts and rewards, not just γ=2/3.

The source's formal quantification over arbitrary estimators is under-specified mathematically, so this result proves `¬ printedTheorem37ii` **for the explicit estimator/seed interface above**. Because the counterexample is a conventional deterministic measurable estimator, a broader source estimator class would still contain that witness, but the formal inclusion or a complete equivalence with every unstated source interpretation is not separately proved here. No unprinted `S≥2` restriction is introduced. Any intended restriction excluding the one-state instance requires explicit source/author clarification rather than silently changing the proposition.

## Verification and identity

The exact staged source, copied unchanged to a temporary file with five appended `#print axioms`, compiled without diagnostics via `bash scripts/lean-local.sh` against the existing integrated project artifacts. `theorem37GenerativeLaw_probability`, `theorem37GenerativeLaw_marginal`, `theorem37GenerativeLaw_independent`, `theorem37OneStateEstimator_error`, and `not_printedTheorem37ii` each use only `propext`, `Classical.choice`, and `Quot.sound`. This is a staged source/axiom check, not an integrated project build or independent review of this proposed source statement.

SHA-256:

- `.local/Theorem37Negation.lean`: `d9ae884a0ec7245a3acaae1f07d02a67a0443ce268a2f63facbe215d7368dd12`.
- `Formalization/Obstructions/OneStateExperiment.lean`: `9e0edf146a203da6be3f7c7d2a2e77f69725d592e26ce844d08f99a38a3c2099`.
- `Formalization/Obstructions/OneStateTrajectory.lean`: `091d881d496d1709115cb088a749d708633513c45bf84154ac534c93a02133d1`.
- `Formalization/Obstructions/OneStateParameters.lean`: `2be78dda039c300ebcc4455658994b8b0495c7f5da6ef31c1db20fb27b1586ba`.
- Source `prelim.tex`: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.
- Source `generative_model_model_based.tex`: `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.
