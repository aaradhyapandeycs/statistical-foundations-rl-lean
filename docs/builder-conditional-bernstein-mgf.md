# Conditional bounded-increment quadratic MGF

Stable source `.local/ConditionalBernsteinMGF.lean`, SHA-256 `b8680a852d7e27875ae277481959efffbcb570c0421ac9fcc1252f615fdffa8d`.

## Completed bounded lemma

`StatisticalRL.conditional_mgf_le_exp_secondMoment` proves, for an arbitrary probability space with ambient measurable structure m₀, a sub-sigma-algebra m≤m₀, an ambient-measurable real X, an almost-everywhere bound |X|≤B, real t with |t|B≤1, and actual conditional mean E[X|m]=0 almost everywhere,

`E[exp(tX)|m] ≤ exp(t² E[X²|m])` almost everywhere.

The theorem derives integrability of X, X², exp(tX) and its quadratic envelope from measurable boundedness on a probability space. It assumes no independent samples, conditional exponential estimate, target tail bound, or integrability conclusion. The explicit ambient measurability annotation is intentional: the conditioning sigma-algebra m must not accidentally replace m₀ in X's measurability assumption. Requiring X to be measurable already at m plus conditional centering would trivialize the lemma; that is not the declaration here. B need not be separately constrained nonnegative since its almost-everywhere absolute bound on a probability space enforces that. Both signs of t and t=0 are included, as are zero increments and zero variance.

The proof uses `Real.norm_exp_sub_one_sub_id_le` on |tX|≤1 to dominate exp(tX) by 1+tX+t²X². `Integrable.of_bound` derives all integrability. `condExp_mono`, `condExp_add`, `condExp_smul` and `condExp_const` transport the pointwise bound through actual conditional expectation; conditional mean zero removes the linear term, and 1+u≤exp(u) completes the claim. Function expressions are explicitly folded to lambdas before rewriting conditional linearity, avoiding Pi addition/smul matching failures.

## Source fidelity and limitation

This is a useful conditional counterpart of the existing iid-row quadratic MGF ingredient, not a duplicate of its iid factorization theorem: X may depend arbitrarily on the past and only its actual conditional centering is required. It supplies a variance-sensitive one-step input for adapted TD/Q-learning increments.

It is deliberately a **weaker preliminary MGF bound**, with coefficient t² and restricted domain |t|B≤1. It is not the sharp conditional Bernstein bound `exp(t²V/(2(1−|t|B/3)))`, not the full source `lem:Freedman-prelim`, and not a proof of its exact √8 and4/3 tail constants. It neither claims nor assumes a supermartingale or a tail inequality. See `docs/builder-freedman-variance-peeling.md` for the exact printed source and missing stochastic layer. Do not silently substitute this preliminary bound into a proof requiring sharp Bernstein constants.

## Source-first supermartingale construction plan

For filtration ℱ and adapted Xₖ with E[Xₖ|ℱₖ₋₁]=0, define the actual predictable variance Vₖ=E[Xₖ²|ℱₖ₋₁] and cumulative Wₙ=ΣVₖ. Conditional expectation supplies a strongly ℱₖ₋₁-measurable version of Vₖ and a.e. nonnegativity (`condExp_nonneg`). For each fixed real t in the proved restricted domain, candidate `Zₙ=exp(tΣXₖ−t²Wₙ)` has one-step factor exp(tXₖ−t²Vₖ). Prove its conditional expectation≤1 by pulling out the predictable compensator, then pull out Zₙ₋₁. Relevant pinned APIs are `condExp_mul_of_stronglyMeasurable_left` and `condExp_mul_of_aestronglyMeasurable_left` in ConditionalExpectation/PullOut. They require actual integrability of the product and non-predictable factor; bounded finite-time increments and a.e. nonnegative V provide these bounds, but those proofs must be supplied. Adaptedness and the actual filtration inclusions must also be proved.

Mathlib `Probability/Martingale/Basic.lean` defines Supermartingale as adaptedness, conditional ordering for every earlier/later pair, and integrability at every time. Its natural-number one-step construction APIs include `supermartingale_of_setIntegral_succ_le`; the conditional subtraction variant has a sign-oriented name, so inspect its precise statement before use. A direct one-step inequality alone is not yet an inhabitant of the full structure without the required construction/induction. Once an actual nonnegative exponential supermartingale is available, derive a variance-restricted tail via Markov/stopping arguments, optimize a legal t with all zero endpoints explicit, and use K-bin/two-tail union. Obtaining the printed constants may require the sharper one-step Bernstein envelope rather than the present preliminary coefficient.

## Validation

The exact source compiled successfully. An exact-source-copy probe `.local/ConditionalBernsteinMGFAudit.lean` appended its axiom check and full declaration print; compilation exited0 with no diagnostics, and transitive axioms are only `propext`, `Classical.choice`, `Quot.sound`. The signature confirms X is ambient-measurable and m≤m₀. No custom axioms or placeholders occur. Compiler slot is idle/released. Independent source review and actual integrated-export checks remain separate requirements.
