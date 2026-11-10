import Formalization.Probability.AdaptiveProduct
import Batteries.Tactic.Alias

/-!
# Corrected Theorem 7.12: adaptive product lemma (L8)

The adaptive product lemma, its Markov consequence and the finite union bound are proved in
`Formalization/Probability/AdaptiveProduct.lean` (namespace `StatisticalRL.AdaptiveKL`). This file
keeps the names used by the Theorem 7.12 proofs as aliases with identical statements.
-/

namespace StatisticalRL.Ch7Rest.Rlhf

/-- Adaptive product lemma (L8); alias of `StatisticalRL.AdaptiveKL.adaptive_prod_le`. -/
alias adaptive_prod_le := StatisticalRL.AdaptiveKL.adaptive_prod_le

/-- Total mass one of the adaptive product law; alias of
`StatisticalRL.AdaptiveKL.adaptive_prod_sum_eq_one`. -/
alias adaptive_prod_sum_eq_one := StatisticalRL.AdaptiveKL.adaptive_prod_sum_eq_one

/-- Markov consequence `P(∏ Y ≥ c) ≤ 1/c`; alias of `StatisticalRL.AdaptiveKL.adaptive_markov`. -/
alias adaptive_markov := StatisticalRL.AdaptiveKL.adaptive_markov

/-- Finite union bound; alias of `StatisticalRL.AdaptiveKL.union_bound_sum`. -/
alias union_bound_sum := StatisticalRL.AdaptiveKL.union_bound_sum

end StatisticalRL.Ch7Rest.Rlhf
