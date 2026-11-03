# Scalar Bernoulli KL-expression bound

Staged source `.local/GenerativeLowerBoundBernoulli.lean`, SHA-256 `e448cc57b89ace8b91fd65d0cd2a7999c17970e7c58381ff78de073488fe74f1`; source plan `docs/builder-generative-lower-bound-bernoulli-plan.md`. Source reference: generative-model chapter lines 1694–1710.

For 0<p,q<1, `bernoulliKLExpression_le_quadratic` proves the exact scalar inequality `q log(q/p)+(1−q)log((1−q)/(1−p)) ≤ (q−p)²/(p(1−p))`. It derives both logarithmic estimates from pinned Mathlib's `Real.log_le_sub_one_of_pos` and proves the algebra, with no desired inequality in its hypotheses. `bernoulliKLExpression_increment_le` specializes to 1/2≤p<p+α<1 and proves the source bound ≤2α²/(1−p). The source N factor can be applied separately once an actual product-law KL identity is established.

The definition is explicitly a scalar expression, and its measure-theoretic KL identity, finite-product tensorization, actual hard MDP observation laws, and Fano/testing lower bound remain unproved. The proof makes no claim about these results or disputed policy-learning statements. Exact staged compilation succeeded with no diagnostics; axiom probes for the definition and both theorems report only `propext`, `Classical.choice`, and `Quot.sound`. Independent review and actual production integration remain.
