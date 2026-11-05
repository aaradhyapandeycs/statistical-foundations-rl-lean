# Independent review: Q-learning finite-prefix causality bridge

Reviewed `QLearningCausalityDraft.lean` (private staged draft, not shipped), SHA-256 `3eade75e34d1dc7c5a2f6e809e0fe2f8e7fe197ca2b288761df2078067276d37`, against `docs/builder-q-learning-causality.md`, the synchronous update in `source/upstream/tex/chapters/generative_model_model_free.tex:794–870`, and the exact staged sampling/iterate dependencies (hashes `70dccffe5af0e7f824226c1d235257f4b0ea8e4ff7a5f9aaf8d9d1e06a830937` and `594b96eede407a268bad69041146728a7456478c39c53990c53bef006a5b207e`). The handoff SHA matches the current source.

## Source and semantic review

PASS for finite-prefix factorization and independence of Q_t from one current-row draw. `qPastIndices T t` contains exactly product coordinates whose zero-based layer is `<t`; `qPastData` restricts the complete sample array to that finite prefix, and `qCompletePast` fills all other coordinates with the fixed nonempty state. The pathwise agreement theorem identifies iterates whenever all update-time samples through t agree. Its prefix specialization therefore shows that Q_t is a function only of the first t sample layers. The history/code space is finite with the local discrete measurable structure, so this factorization is measurable and supports the independence composition.

The source update at step `t+1` uses its fresh draw `samples (t+1)`. The sampling bridge maps that to the array coordinate with index `t`, provided `t<T`. Hence the past set `<t` and the current singleton coordinate are disjoint; independence of all product coordinates yields independence of the complete past block from that fresh draw, and measurable composition yields independence of Q_t from the draw. `qSamplingLaw_marginal` separately supplies the actual `(M.transition s a).rowMeasure` law. The statement correctly does not assert independence of Q_{t+1} from the draw used to update it.

At `T=0`, `Fin 0` and the past index set are empty, Q₀ depends on no samples, and there is no `t<T`; thus no fresh-draw claim is made. At `t=T`, the prefix contains all T coordinates and no future draw is asserted. The implementation's fill value only affects coordinates outside the queried prefix.

## Fresh exact-source compile and axiom audit

Verified the three exact staged hashes and ran the private audit script `audit-q-learning-causality-independent.sh` (not shipped), which rebuilt Q-iterate bounds, synchronous sampling, then the causality source in an isolated local audit directory (not shipped). All compiled successfully without diagnostics. The import probe covered 25 declarations across the three modules; every declaration used only `propext`, `Classical.choice`, and `Quot.sound` (the singleton-index definition used a subset). This independently confirms the builder's focused staged compile claim.

## Remaining scope

The bridge does not define a named filtration/sigma-algebra interface or state an explicit theorem that the whole current time layer is independent of the past block; it proves independence for one current row coordinate, while `qSamplingLaw_independent` gives mutual coordinate independence from which a layer-block result may be derived. The past factorization supplies the requisite measurability argument at finite horizon, but conditional expectation/centering, conditional variance, martingale properties, concentration, and learning rates remain unproved. Production import qualification and integrated export checks remain separate.

Production integration: the reviewed source body compiles in the project export with qualified imports; the Q-learning causality file has been given the production module name `QLearningCausality`. The full project check audited 2,755 declarations, allowing only `propext`, `Classical.choice`, and `Quot.sound`.
