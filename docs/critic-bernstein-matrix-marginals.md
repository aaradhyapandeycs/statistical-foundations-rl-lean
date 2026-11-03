# Independent review: whole-matrix Bernstein under rowwise iid marginals

**Verdict: PASS for the whole-matrix assertion of Lemma 2.5 under the explicit quotient-Borel random-family interpretation and positive-N convention.** The new staged declaration removes the previous excess cross-row product-law assumption. It assumes the source's iid N-sample law separately at every row, permits arbitrary dependence between rows, requires independence of the random family from the **full empirical matrix**, and proves the literal source radius with strict probability. This is a scoped source/semantic/code review, not author approval or whole-paper completion.

The authoritative source is `source/upstream/tex/chapters/prelim.tex:916–927` for the row samples/frequencies, `:427–443` for population variance and `:956–977` for Lemma `lem:Bernstein-prelim`, particularly `eq:Bernstein-P-whole-prelim`. The source first states simultaneous vector-family control for one row and then gives the whole-matrix expression under independence from `P̂`; this audit uses the natural simultaneous-family reading. The preliminary sampling text says iid **within each row** and does not explicitly require independence between different rows. The later simulator chapter's independent-query assumption is a separate stronger context. My earlier review `docs/critic-bernstein-matrix.md` identifies why the former staged theorem's joint product-of-rows premise was too strong; the present result directly addresses that gap.

## Assumptions and quantifiers

`randomBorelFamily_matrixBernstein_of_rowMarginals` has finite nonempty State and Action carriers, an arbitrary valid `FiniteDistribution State` at every state-action index, a probability space with measurable matrix-sample draw, positive N, and `0<δ<1`. Its decisive sampling input is

```text
∀ i : State × Action,
  μ.map (fun ω => draw ω i) = (d i).sampleMeasure N.
```

`sampleMeasure N` is the N-fold iid product of the actual row's probability measure. Thus each entire sequence has the correct joint iid distribution; merely correct one-sample marginals would not suffice. No hypothesis equates the joint matrix-sample law to a product across rows or asks for cross-row independence. An independent compiled probe derived the exact displayed row-law hypothesis from within-row `iIndepFun`, coordinate a.e. measurability, and the correct individual marginals, with no independence assumption involving distinct rows. Measurable coordinates provide measurable matrix draw under the product σ-algebra.

`family : Ω→Finset (State→ℝ)` is a genuinely random unordered finite family; `hfamily` makes it measurable in `finiteFamilyBorel`, the final σ-algebra of injective finite Borel enumerations. No fixed family size, measurable ordering, or raw-sample independence is imposed. `hV` permits coordinatewise nonnegativity almost everywhere. `hindep` states independence of the family and the **complete empirical matrix** in the product of the row real-coordinate σ-algebras. `marginalMatrixVectorSpace_eval` proves each row projection measurable, so `hindep.comp` derives exactly the single-row independence consumed by the existing random-family theorem. Independence from every row separately would be weaker than full-matrix independence and is not substituted for the source input.

As in the single-row formalization, the source leaves its random-set σ-algebra implicit; no equality with a separately defined hyperspace Borel σ-algebra or author ruling is claimed. N=1 is allowed. N=0 is excluded because source frequencies and radius divide by N; the manuscript does not specify a zero-sample convention. Empty families are admitted, giving a vacuous simultaneous event on those outcomes. Lean uses total `Real.log`, while the manuscript does not specify `log 0`; no member of an empty family requires evaluating the bound. Zero vectors and zero variance are inherited from the reviewed sharp family result. δ endpoints remain excluded exactly as in source.

## Bound and proof check

The output quantifies over every row and every vector in the actual outcome-dependent family. The empirical matrix uses each row's actual frequency vector; subtracting `d i` expectations is the source matrix-vector deviation. The variance is the actual row population variance `E[V²]−E[V]²`; the finite Pi norm is the source `‖V‖∞`. The printed radius is exactly

```text
sqrt(2 log(4·S·A·|𝒱|/δ)/N) sqrt(Var_{P_i}(V))
  + 2‖V‖∞ log(4·S·A·|𝒱|/δ)/(3N).
```

The proof puts `m=card(State×Action)=SA` and applies the reviewed single-row strict success theorem at `η=δ/m`; nonemptiness gives `0<η<1`. Each bad event is measurable, has probability `<η`, and the finite union bound gives total bad probability `<mη=δ` without needing any independence between rows. `hlog` establishes the exact `4SA|𝒱|/δ` argument, and complementing the union produces the simultaneous non-strict row inequalities with probability **strictly greater** than `1−δ`. The target probability or any tail bound is not a premise.

## Shared-sequence witness

`diagonalMatrixSamples N ω` copies the same N observations into every row. `diagonalMatrixSamples_row_marginal` proves the shared construction's row laws agree with `d.sampleMeasure N` when all true rows share d; `diagonalMatrixSamples_rows_equal` proves the row sequences equal pointwise. For a nondegenerate d and at least two rows, this is a genuinely correlated coupling: e.g. the event that the first observations in two rows agree has probability 1 under this coupling, versus strictly less than 1 under the independent product. The staged declarations prove equal rows and their marginal laws; they do not themselves export a formal non-independence theorem.

A separate compiled probe went further and instantiated `randomBorelFamily_matrixBernstein_of_rowMarginals` directly with `μ=d.sampleMeasure N`, this shared-sequence draw, and an **arbitrary deterministic nonnegative finite family**. It proved the required empirical-matrix independence using constant-family independence, and obtained the exact whole-matrix conclusion. This verifies that the final theorem is usable on the correlated construction, rather than merely defining an unrelated witness. This probe does not prove a random correlated-family specialization, which is already covered by the general theorem's hypotheses.

## Independent verification and identity

The exact staged source was copied unchanged to a temporary probe and compiled against the integrated `Formalization.Probability.BernsteinFamily` dependency via `bash scripts/lean-local.sh`, with the iid-to-row-law probe, shared-sequence application, and five `#print axioms` commands appended. Compilation passed. The only diagnostic was the builder-disclosed unused `[Fintype Action]` linter warning in `diagonalMatrixSamples_row_marginal`, an optional witness; no Lean errors occurred. The exact `diagonalMatrixSamples_row_marginal`, `marginalMatrixVectorSpace_eval`, `marginalBernsteinBad_measurable`, and `randomBorelFamily_matrixBernstein_of_rowMarginals` use only `propext`, `Classical.choice`, and `Quot.sound`; `diagonalMatrixSamples_rows_equal` uses no axioms. The probe compiled the staged source against the integrated family artifact; integrated matrix-module compilation remains a separate step.

SHA-256:

- `.local/BernsteinMatrixMarginals.lean`: `70cefdb4775c8dc406b61e22fa41f0a80e3689d13e98e2a272a19380e500f321`.
- `Formalization/Probability/BernsteinFamily.lean`: `3f3d25c0953b629e7a8fba0921edf9a689a9818606e99e8eca7e64306299bcfe`.
- Source `prelim.tex`: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.

This supersedes the source-scope limitation recorded for the earlier *stronger* product-row statement, without altering that earlier statement or its review. Independent integration, actual export/axiom checks, and any author-facing or whole-paper correspondence process remain separate.
