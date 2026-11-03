# Independent review: auxiliary-value growth

**Verdict: pass for the source's true auxiliary growth estimate and its separately stated zero-discount identity.** This is a deterministic ingredient, not the complete statistical policy-evaluation theorem.

The source `generative_model_model_based.tex:413–455`, especially `eq:Vl-inf-norm-bound-0` and `eq:Vl-inf-norm-bound`, defines `r⁰=rπ`, `V⁰=(I−γPπ)⁻¹r⁰`, and for each successor `rˡ⁺¹=√Var_Pπ(Vˡ)`, `Vˡ⁺¹=(I−γPπ)⁻¹rˡ⁺¹`. The imported independently reviewed auxiliary module implements these objects with true policy transition rows, current-state-by-next-state matrix orientation, and the actual infinite-trajectory policy value at level zero; `auxiliaryValue_eq_inverse` proves the literal inverse representation also at zero. Its rewards are nonnegative at every level, including policy-averaged reward at zero.

For arbitrary finite state and action carriers, an admissible discounted MDP M, stationary randomized π, and every natural l, `auxiliaryValue_succ_scaled_bound` specializes the reviewed general-forcing bound to the actual `auxiliaryReward M π l`. Its use of `auxiliaryValue_eq_inverse` identifies the bound's W=Rrˡ with exactly Vˡ; the next vector is definitionally R√Var_Pπ(Vˡ). Thus it obtains `γ‖Vˡ⁺¹‖∞ ≤ ‖Vˡ‖∞/√(1−γ)` with no upper bound on auxiliary rewards and no probabilistic-event premise.

For γ>0, the one-step factor is `1/(γ√(1−γ))`. The induction starts at l=0 with the actual trajectory value, multiplies the induction hypothesis by this nonnegative factor, and uses the successor power law, so the exponent is exactly l. The source-factor theorem compares this factor to `√2/(γ√(1−γ))`, using positive denominator and `1≤√2`, and preserves the nonnegative norm multiplier. The uniform theorem then applies the actual trajectory bound `‖Vπ‖∞≤1/(1−γ)` with the correct factor and orientation. Consequently the source's precise √2 geometric constant and horizon factor are proved; the constant-one estimate is a stronger intermediate claim. No hidden sample-size assumption is introduced.

The scaled successor estimate covers γ=0. The positive-discount estimates explicitly require `0<γ`, as needed for the source's `1/γ` expression. Independently, `auxiliaryValue_empirical_eq_of_zero` proves true and empirical auxiliary vectors equal at every level, for any sample size N>0 and every actual data realization, because both literal resolvents become the identity while using the same true auxiliary reward. This does not assert that the row variance itself vanishes.

The result depends on the reviewed general-forcing variance-resolvent estimate and on the reviewed auxiliary construction. It does not establish the empirical residual recursion, a simultaneous Bernstein event, its terminal bound, or the source's H³ sample complexity. The stochastic interpretation of the initial policy value and the shared true auxiliary reward are inherited from those already reviewed dependencies.

## Verification

Reviewed `.local/PolicyEvaluationAuxiliaryGrowth.lean` SHA-256 `48162a77942e7c9faa58efd70452c0700f00107f6ce47aa36f93028e262c7b0a`. Its staged dependencies were rebuilt sequentially from sources SHA-256 `082412791d8577add90e6a97cd74f286a0d7bbfde6c2f0ae11dfc51b4ddb3323` (general forcing) and `68a6bc19097ecc84a93583a39230b92b58b4a3ab8a2c0971ab50d084923bbb95` (auxiliary, byte-identical to the integrated module). The pinned source TeX SHA-256 is `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

An exact unchanged copy of the growth source with its original imports and six appended `#print axioms` commands compiled in the staged import environment, exit 0. All six exports (`auxiliaryValue_succ_scaled_bound`, `auxiliaryValue_succ_bound`, `auxiliaryValue_norm_growth_sharp`, `auxiliaryValue_norm_growth_source`, `auxiliaryValue_norm_growth_source_uniform`, and `auxiliaryValue_empirical_eq_of_zero`) use only `propext`, `Classical.choice`, and `Quot.sound`. This audit covers the staged source; integration and the actual integrated import path require separate verification.

## Integrated export verification

The production `Formalization/Generative/PolicyEvaluationAuxiliaryGrowth.lean` SHA-256 is `e3e5892d32d3fa4d3b3eb42c212f24e3e2972ed8728f17f82cb32ad5d161114f`. Comparison against the independently reviewed staged source found only qualification of its two project import paths. The actual production module was built after the integrated general-forcing module, and an import-only probe of all six exports compiled with only `propext`, `Classical.choice`, and `Quot.sound`.
