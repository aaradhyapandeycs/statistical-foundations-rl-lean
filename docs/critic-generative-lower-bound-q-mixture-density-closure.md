# Independent source review: Q-mixture atom and density closure

Reviewed the exact staged sources named in the latest density/cross and χ²-expansion handoffs. This review is source-only; no compiler was run.

| Module | SHA-256 |
|---|---|
| `.local/GenerativeLowerBoundQMixtureLaw.lean` | `47fd378b9e8226896e8c6bdee1c90a69f8abc81b9426d2d79f029c0d4ebae775` |
| `.local/GenerativeLowerBoundQMixtureRowDensity.lean` | `55d72a31c512860509fc4dbb9c7194ff9efe85f37203724594607796b6fbcbd5` |
| `.local/GenerativeLowerBoundQMixtureProductFactors.lean` | `1e549e73ffe7dff4e37dcf332ba733eced15e4f9ee6b8626a50b703c637d2d95` |
| `.local/GenerativeLowerBoundQMixtureAtomRatio.lean` | `73ee3a99811f42bbceff36454d8514772cafe80e097b0b89f0823dffcf164607` |
| `.local/GenerativeLowerBoundQMixtureActiveDiagonal.lean` | `58afef5b3e6e7159e43edc27ee1639b53c774ffc467b1d95c832af4f6fc88db9` |
| `.local/GenerativeLowerBoundQMixtureDensity.lean` | `d8fd7d8701f9c6e250a2b37cc49c63b59f60aeb465de7f687701fdd7b6ca368a` |

## Actual laws, positivity, and endpoints

The law module defines an actual product Bernoulli law for each `θ : Fin m × Fin A`, the all-p baseline product, and the equally weighted alternative mixture as the observation marginal of the actual uniform-prior joint measure. The `[NeZero m]` and `[NeZero A]` binders make the prior space nonempty and `K=mA` strictly positive, so normalization never divides by zero. The baseline atom-positive lemma uses `0<p<1` at every coordinate; at `N=0` there are no coordinates and the unique empty-array atom has mass one. The pointwise RN theorem is the actual finite-measure atom ratio with the baseline as reference.

The atom-ratio module proves the orientation `alternative atom / baseline atom`, i.e. the density of the selected alternative with respect to the baseline. In the product ratio, the selected row contributes its actual Bernoulli atom ratio at each sample; every other coordinate has the same Bernoulli(p) law in numerator and denominator and cancels using baseline positivity. The resulting ratio is exactly the defined N-fold changed-row likelihood. Parameters are NNReal; `0<p<1` protects both denominator masses and `q≤1` makes q a legal Bernoulli parameter. No `p≤q` assumption is required for the identity. At `N=0`, both finite products are empty and the likelihood is one.

The full-active-product diagonal theorem integrates the square of this exact likelihood under the actual baseline product. Each selected-row coordinate contributes `1+d`, with `d=(q−p)²/[p(1−p)]`; every unchanged coordinate integrates to one. The product integral is therefore `(1+d)^N`. The proof uses product integration, not a scalar surrogate. It includes `N=0`, yielding one. Its `[NeZero m] [NeZero A]` assumptions ensure there is a selected row, although the algebraic diagonal formula itself does not depend on cardinality beyond that row's existence.

The mixture law is the marginal of a genuine uniform-prior joint law, not a normalized formal sum assumed to be a probability measure. The singleton theorem computes its mass as `K⁻¹ ∑θ Pθ{x}`. Dividing by the strictly positive baseline atom and applying the proved alternative atom ratio gives the actual RN derivative's `toReal` value as the uniform sum of row likelihoods, exactly the `qMixtureLikelihood` definition. Since `K>0` is enforced by the nonempty Fin indices, the normalization matches. For `N=0`, all alternative laws equal the unique empty-array baseline law, all row likelihoods equal one, and the normalized mixture density equals one.

## Scope and remaining gaps

These results concern the encoded active-coordinate Bernoulli product experiment. The earlier observation-law source proves that the actual complete generative sample array is the common reconstruction pushforward of that experiment, including deterministic absorber rows; this review does not derive an additional full-array RN identity. The distinct-row cross moment is a separate result in the density/cross handoff. Even with the diagonal, cross, and normalized density pieces, the finite double-sum χ² expansion, overlap/testing bound, common Q-estimator risk transfer, and final lower-bound conclusion remain open according to the current χ²-expansion handoff.

The latest builder handoffs report successful focused compilation and standard-only axioms for the newly staged atom ratio, active diagonal, mixture singleton, and density modules. This independent review confirms the intended orientation, law normalization, positivity hypotheses, and zero-sample behavior by source inspection only; it does not reproduce those compiler results.

**Verdict:** the actual product atom ratio, active diagonal moment, normalized mixture atom law, and baseline RN-density identity are coherent under their stated nonempty/interior hypotheses and include `N=0`. The claims stop at the encoded active product and the stated local moments/density; they do not close the χ² or statistical risk argument.

Production integration: the corresponding production module bodies match the independently reviewed staged sources, with qualified imports. The full project export compiled and audited 2,522 declarations, permitting only `propext`, `Classical.choice`, and `Quot.sound`.
