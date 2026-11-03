# Independent review: Borel finite-family representation and Hoeffding

**Verdict: PASS for the explicitly defined quotient measurable space of unordered finite vector families and the resulting source-radius, strict Hoeffding bound on that space.** The source does not itself specify a σ-algebra for random finite sets; this implementation supplies a precise natural finite-enumeration interpretation. Equality with a separately defined hyperspace or other random-set σ-algebra is not proved or claimed. This is a scoped ordinary review, not an author-approved frozen-declaration audit or a whole-paper certification.

The reviewer did not author `.local/RandomFamilyBorel.lean` but did author its imported `EmpiricalHoeffdingRandomFamily.lean`; that dependency has a separate independent review in `docs/critic-empirical-hoeffding-random-family.md`, which must be retained. I reconstructed the source and the earlier test-σ-algebra boundary before inspecting this module.

## Source-first reconstruction

`source/upstream/tex/chapters/prelim.tex:916–927` takes N iid observations from a finite transition row and forms its empirical-frequency row. The Hoeffding lemma at 939–949, `lem:Hoeffding-prelim`, takes a finite family `𝒱 ⊆ ℝ_+^S` independent of that empirical row, `0<δ<1`, and asserts, **simultaneously for every family member**, probability strictly greater than `1−δ` for

```text
|(\hat P−P)V| ≤ sqrt(‖V‖∞² log(2|𝒱|/δ)/(2N)).
```

For a random family the family-valued map and joint event require a measurable-space interpretation, which the source does not make explicit. Independence must be imposed on the unordered family and the empirical row; requiring an independently chosen enumeration, or independence from the full ordered sample, would be stronger. The displayed empirical row requires positive N; the theorem makes `N>0` explicit. A zero vector has zero deviation and radius. The empty-family event is vacuous, though the source does not explicitly set a mathematical convention for `log |𝒱|` at cardinality zero.

## Finite-enumeration measurable space

- `FamilyEnumeration n` (staged lines 22–24) is the subtype of **injective** functions `Fin n → (State → ℝ)`. Thus the indexing preserves every distinct vector and contains no duplicate padding. `enumerationFamily` forgets the order by taking the image of the actual finite tuple; `enumerationFamily_card` proves its cardinality is n. `enumerationFamily_surjective` constructs an injective enumeration of **every** finite family using its cardinality, including the empty family at n=0. No global fixed family-size bound or a selected enumeration is added to the main theorem.
- `measurableSet_injectiveEnumeration` proves injectivity is measurable as a finite/countable intersection of coordinate-equality or inequality tests. The tuple uses the usual finite product measurable spaces of the real coordinate vectors; the subtype carries the corresponding inherited σ-algebra. Equality of two vectors is tested by the entire vector, not by one coordinate.
- `finiteFamilyBorel` (80–99) is the intersection of the measurable spaces induced by mapping each injective n-tuple to its unordered image. The checked `finiteFamilyBorel_measurableSet_iff` characterizes its events **exactly** by measurable preimages under every n enumeration; `measurable_enumerationFamily` verifies each enumeration map. Along with surjectivity this is the final/quotient σ-algebra of the disjoint union of those finite Borel tuple spaces. Its definition is independent of d, N and δ. A separately constructed Hausdorff/hyperspace topology or equality with its Borel σ-algebra is outside the module; no such equality is needed for the stated quotient-space theorem.
- An independent compiled probe reindexed an arbitrary injective tuple by an arbitrary permutation of `Fin n` and proved the unordered family is unchanged. This checks the order-forgetting map without assuming a canonical enumeration.

## Tests, independence, and theorem scope

`enumerationFamily_nonneg_measurable` expresses source nonnegativity as a finite intersection over tuple positions and state coordinates. `enumerationFamily_bad_measurable` expresses the failure test as a finite union over positions; `enumerationFamily_card` substitutes the **actual** family cardinality n into the same radius. Vector norms and finite weighted row evaluations are measurable, with the genuine row and true expectation. This covers n=0 as the empty union and does not invent a representative on the empty carrier.

`familyTestSpace_le_finiteFamilyBorel` proves the earlier source-test σ-algebra is contained in this quotient σ-algebra. The final theorem transfers measurability to the smaller source-test σ-algebra and uses `IndepFun.comp` with the measurable **identity on unordered finite families**. It preserves independence from the empirical row under `rowVectorSpace`, the usual real-coordinate row σ-algebra; it does not assume independence of an enumeration or of raw samples. The imported finite-range theorem justifies using the discrete row internally without strengthening this coordinate-row hypothesis. The resulting conclusion comes from the already reviewed actual joint-law random-family theorem, including its strict product-integration argument, rather than being supplied as a premise.

`randomBorelFamily_empiricalRow_success_gt` quantifies over an arbitrary joint probability space, true iid sample law, Borel-quotient-measurable unordered finite family, actual-row independence, a.e. source nonnegativity, `N>0`, and `0<δ<1`. It has no input of a tail bound, measurable failure conclusion, or successful event. It uses the exact source threshold and strict `>` success probability, with potentially outcome-dependent finite cardinality; empty and zero-vector cases are inherited from the reviewed source-test theorem. The almost-everywhere nonnegativity condition is no stronger than the source's almost-sure random-family reading.

## Independent probes and identity

A temporary copy of the exact staged file compiled without diagnostics via `bash scripts/lean-local.sh <temporary-file>`, with two appended checks:

1. Arbitrary permutation of an injective enumeration leaves its unordered family unchanged.
2. A fair Bernoulli coin chooses either the empty family or the singleton zero-vector family, on the actual product with `d.sampleMeasure N`. The probe proves the two families differ, supplies the product-law iid sample marginal and **unordered family/empirical-row independence**, and instantiates the final strict source-radius theorem. This is a nonconstant random family with varying cardinality, not a deterministic-family specialization.

In the same successful run, `#print axioms` for `enumerationFamily_surjective`, `measurableSet_injectiveEnumeration`, `finiteFamilyBorel_measurableSet_iff`, `enumerationFamily_bad_measurable`, `familyTestSpace_le_finiteFamilyBorel`, and `randomBorelFamily_empiricalRow_success_gt` reported only `propext`, `Classical.choice`, and `Quot.sound`. The temporary probe was removed. This checks the exact staged source and imported compiled artifacts; a future integrated export and full project build need separate checks.

Reviewed SHA-256 values:

| File | SHA-256 |
| --- | --- |
| `.local/RandomFamilyBorel.lean` | `1bda21b0bac900dc0dec5db6cef949dfc99a745dff4cce14f2a1a0732c57d335` |
| `Formalization/Probability/EmpiricalHoeffdingRandomFamily.lean` | `d5434c422e8535a134cedf7a5ff66c8ad8db0f49c77c3c018b26ec52b26f5fa6` |
| `Formalization/Probability/EmpiricalHoeffdingFamily.lean` | `0b8bf547984a749623012f9a6a19ffe92ffa9c10f8a69d6b4abf139c794dc12d` |
| `Formalization/Probability/EmpiricalRow.lean` | `6e87c90ff1150f7053845acff92d60a5c35035c7a78adcd394e0da5f3d9dc154` |
| `source/upstream/tex/chapters/prelim.tex` | `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5` |
