# Measure-theoretic Bernoulli KL bridge

Exact staged source `.local/GenerativeLowerBoundBernoulliMeasure.lean`, SHA-256 `4294f718f543bf6f08abf60ec66f12f3486919a4a157bccc8f3231b855dfee66`. It imports the reviewed-pending staged scalar file `.local/GenerativeLowerBoundBernoulli.lean`, SHA `e448cc57b89ace8b91fd65d0cd2a7999c17970e7c58381ff78de073488fe74f1`, and pinned Mathlib KL and PMF integral APIs. Source motivation: generative-model chapter lines 1694–1710.

For actual `PMF.bernoulli` probability measures on Bool, the file proves full support of the reference law for 0<p<1; absolute continuity of every Bernoulli law with respect to it; and the pointwise Radon–Nikodym ratio for general Bool PMFs with full-support reference. It then derives `klDiv(Bern(q),Bern(p)).toReal = q log(q/p)+(1−q)log((1−q)/(1−p))` for 0≤q<1 and 0<p<1, and the scalar quadratic bound for 0<q<1. Parameters are Mathlib nonnegative reals with real coercions, preserving the source's interior domain. The strict lower bound q>0 is not required for the equality; q=1 is not included in its present signature.

Crucially, `bernoulli_klDiv_ne_top` independently proves the actual extended-real KL is finite using absolute continuity and finite-space integrability, and `bernoulli_klDiv_eq_expression` proves the ℝ≥0∞ identity itself. Thus no conclusion relies on `ENNReal.toReal ∞ = 0` hiding an infinite KL. No product tensorization, actual hard-MDP sampling law, testing inequality, or minimax theorem is claimed.

Focused exact-source compilation succeeded without diagnostics, using `.local` on `LEAN_PATH`; seven exports' `#print axioms` use only `propext`, `Classical.choice`, and `Quot.sound`. Independent refute-first review, import qualification, and actual production-export build/axiom checks remain.
