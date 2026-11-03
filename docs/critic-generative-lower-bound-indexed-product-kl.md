# Independent review: heterogeneous Bernoulli KL and swapped rows

Reviewed `.local/GenerativeLowerBoundIndexedProductKL.lean` SHA `401482aa222acf69f09611e41f00828de93f45cd774215dd1521a5ffeb363000`, its builder handoff, and source `generative_model_model_based.tex:1991–2036`. The staged source proves the stated actual finite product-law ingredient, with both KL orientations and the source constant; it does not yet identify this auxiliary experiment with full indexed-MDP sampling laws or prove Fano/minimax results.

`indexedBernoulliLaw` is the actual `Measure.pi` on all Bernoulli coordinates, not merely prescribed marginals. With both parameter vectors interior, all atoms are positive and the log-likelihood identity has first vector `q` and reference vector `p`. The KL tensorization integrates the coordinate log ratios under the first law, using its true projection marginals. The separate non-top theorem requires only interior reference parameters, allowing endpoints in the first law; it rules out hiding infinity through `.toReal`. Product coordinates can have different probabilities, and an empty finite index is included.

`twoRowSwapLaw` makes the Boolean row index select q in one row and p in the other, with N genuinely independent samples in each. Comparing `alternate=true` to `alternate=false` therefore yields exactly `N[KL(Bern(q)||Bern(p))+KL(Bern(p)||Bern(q))]`; the two nonidentical directions are preserved. Under `1/2≤p<q<1` and `2(q−p)≤1−p`, denominator comparisons yield respective bounds `2(q−p)²/(1−p)` and `4(q−p)²/(1−p)`. Their sum is at most the stated weaker source bound `8N(q−p)²/(1−p)`; all denominators are positive. `N=0` is allowed. No target inequality, decoder success, or testing bound is assumed.

The complete source family additionally contains other unchanged rows and deterministic absorber rows; these are not silently treated as full-support Bernoulli coordinates. A separate actual-law encoding/pushforward result and KL transport/common-coordinate cancellation is required, as are finite-family testing/Fano and estimation or policy-loss composition. This module asserts none of them.

## Independent staged compiler and axiom audit

Freshly compiled staged scalar Bernoulli, measure identity, Bernoulli product and heterogeneous-product sources in an isolated project-local directory. A separate importing probe inspected all nine exports including the probability instance. Every compilation/probe exited zero and each export depends only on `propext`, `Classical.choice`, and `Quot.sound`. The reviewed source emits one nonsemantic unused simp-argument warning. Production qualification and actual imported-export checks remain separate.

## Integrated production audit

Actual production `Formalization/Generative/GenerativeLowerBoundIndexedProductKL.lean` SHA `e1108ee825297c5c828f91e10adeb4c3692ebdcef30d5a391fedc3371758b5f5`: only its staged import qualified; the expected unused simp-argument warning persists. The seven production modules compiled sequentially and a separate importing probe inspected all 70 exports. Every command exited zero; each declaration uses only `propext`, `Classical.choice`, and `Quot.sound` or fewer. The staged source scope and remaining gaps above are unchanged.
