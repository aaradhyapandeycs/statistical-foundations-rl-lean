# Independent source review: synchronous Q-learning sampling

Reviewed `QLearningSynchronousSampling.lean` (private staged draft, not shipped), SHA-256 `70dccffe5af0e7f824226c1d235257f4b0ea8e4ff7a5f9aaf8d9d1e06a830937`, against the source algorithm in `source/upstream/tex/chapters/generative_model_model_free.tex:794–870` and the compiled iterate module `QLearningIterateBounds.lean` (private staged draft, not shipped) / `Formalization/ModelFree/QLearningIterateBounds.lean`, both SHA-256 `594b96eede407a268bad69041146728a7456478c39c53990c53bef006a5b207e`. The later independent compile audit verified this same hash; there were no changes after source review.

## Verdict

PASS for the staged finite-product sampling interface and its pathwise output bounds.

`QSamples State Action T` is exactly `((State × Action) × Fin T) → State`, so the experiment contains T draws for every state/action row: `S·A·T` total coordinates. `qSamplingLaw` is the existing model-based product law. Its marginal theorem identifies every coordinate with the actual `M.transition s a` row measure, and its independence theorem gives mutual independence across all state/action/time coordinates. This matches the source algorithm's fresh independent next-state draw for every `(s,a)` at every iteration.

The source iterate applies its first update at time `t+1` using `samples (t+1) s a`. The helper's correspondence theorem sends that call to coordinate `⟨t, ht⟩` for `t<T`; thus iterations 1 through T use exactly the Fin T coordinates, with no time-zero draw. `qSampledIterate` runs the compiled synchronous Q recursion for exactly T steps. The staged and production iterate source files are byte-identical at the hash above.

For T=0, the coordinate type `Fin 0` is empty and the sample array is the unique function from an empty index set. The iterate performs zero updates, so the extension's arbitrary fallback state is never queried. For positive T, its fallback applies only outside update indices 1 through T. State nonemptiness is supplied by `DiscountedMDP` for that fallback.

The measurable output claim is sound on the finite sample domain. The Q and V bounds and the sup-norm error against the actual `M.trajectoryExpectedQ M.optimalGreedyPolicy` are inherited from the already reviewed compiled pathwise iterate theorem. Since those bounds hold for every data array, the stated almost-sure bounds under the actual product sampling law are valid.

## Scope

The module does not itself prove a prefix-independence/causality interface for the iterates or conditional centering/variance statements. It also proves no concentration or rate result. The `qSamplesExtend` values outside queried update times are an implementation extension only.

## Independent compiler and axiom audit

Verified the exact staged source hash above and compiled it into `QLearningSynchronousSampling.olean` (in an isolated local audit directory, not shipped) with the already audited Q-iterate artifact first on the isolated search path. Compilation exited successfully without diagnostics. The import probe checked all ten public declarations, from `qSamplingLaw` through `qSampledIterate_error_ae`; each depends only on `propext`, `Classical.choice`, and `Quot.sound`. Production integration and a production import/export audit remain separate.

Production integration: the reviewed source body compiles in the project export with qualified imports; the Q-learning causality file has been given the production module name `QLearningCausality`. The full project check audited 2,755 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
