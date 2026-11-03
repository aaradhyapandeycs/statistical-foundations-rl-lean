# Source correspondence: Lemma 2.5, single-row Bernstein inequality

**Scoped verdict.** The integrated `StatisticalRL.FiniteDistribution.randomBorelFamily_bernstein_source` has the source's single-row Bernstein conclusion, including its exact constants and strict success probability, for the explicitly constructed finite-enumeration measurable model of a random unordered family. The source leaves that random-family σ-algebra implicit. `N>0` is made explicit because the source's empirical frequencies and radius divide by N. This is an ordinary source comparison, not an author-approved frozen declaration, a formal assertion about all possible random-set σ-algebras, or a whole-Lemma-2.5 completion claim.

This auditor previously authored an earlier imported random-family infrastructure module and the separate whole-matrix review, but did not author `BernsteinFamily.lean`. The independent source/code/axiom review of the family module is `docs/critic-bernstein-family.md`; the independently reviewed sharp fixed-vector component is `docs/critic-sharp-empirical-bernstein.md`. This report independently checks the integrated declaration's source correspondence and makes the representation boundary explicit.

## Authoritative source and displayed conclusion

`source/upstream/tex/chapters/prelim.tex:916–927` fixes a transition row and N iid observations and defines empirical frequencies. At lines 956–965, Lemma `lem:Bernstein-prelim`, equation `eq:Bernstein-Psa-prelim`, takes a finite set `𝒱⊆ℝ₊^S`, independent of `P̂_{s,a}`, and `0<δ<1`. It asserts that, simultaneously for all `V∈𝒱`, with probability **greater than** `1−δ`,

```text
|(P̂_{s,a}−P_{s,a})V|
 ≤ √(2 log(4|𝒱|/δ)/N) √Var_{P_{s,a}}(V)
   + 2‖V‖∞ log(4|𝒱|/δ)/(3N).
```

The true population variance is `E_P[V²]−(E_P[V])²` (`prelim.tex:427–443`). The subsequent empirical-Bernstein lemma at lines 985–997 is different: it uses empirical variance, N−1, and coefficient 7; it is not covered by this theorem.

## Expanded statement correspondence

| Source ingredient | Integrated declaration and precise interpretation |
| --- | --- |
| One fixed state-action row; finite states | Arbitrary `[Fintype State]` and `d : FiniteDistribution State` represent the chosen normalized row: its nonnegative masses sum to one. Any fixed MDP transition row can instantiate d. No action or global matrix carrier is needed for a one-row statement, and no matrix-wide conclusion follows. If State is empty, a normalized `d` cannot be constructed. |
| Underlying probability experiment | Arbitrary measurable `Ω`, probability measure `μ`, and measurable `draw : Ω→Fin N→State` provide a joint realization. Index `Fin N` differs from source indices 1,…,N only by relabeling. |
| N iid samples from the row | `hlaw : μ.map draw = d.sampleMeasure N`, with `sampleMeasure` the actual product of N copies of `d.rowMeasure`. `sampleMeasure_coordinate` and `sampleMeasure_independent` establish its correct marginals and mutual independence. Conversely, iid coordinates with the same row law imply this product law by Mathlib `iIndepFun_iff_map_fun_eq_pi_map` (finite-coordinate measurability supplies `hdraw`). The source's row iid assumption is therefore represented as a joint-law equality, not a concentration premise. |
| Empirical row and expectation | `empiricalRow N hN` uses normalized state counts, and `empiricalRow_expectation` identifies evaluation with the average of sampled values. `(empiricalRow ...).expectation V − d.expectation V` is precisely `(P̂−P)V`. |
| Family and nonnegativity | `family : Ω→Finset(State→ℝ)` may depend on the outcome and may have any finite, outcome-dependent cardinality. `hV` requires coordinatewise nonnegativity almost everywhere; this is no stronger than the usual almost-sure reading of a random family in `ℝ₊^S`. A fixed deterministic family is included. |
| Random-family measurable model | `finiteFamilyBorel` is the final σ-algebra for unordered finite sets under all injective finite Borel enumerations; every finite family, including the empty set, has such a representation. `hfamily` asks that the family itself be measurable in that space. It does **not** require a separately chosen measurable ordering. The source does not specify a σ-algebra for random sets; equivalence to a separately defined hyperspace Borel σ-algebra has not been established. |
| Independence | `hindep` is `IndepFun family (fun ω ↦ empiricalRow N hN (draw ω)) μ`, using the quotient family σ-algebra and the empirical row's real-coordinate pullback `rowVectorSpace`. The dependency's finite-support lemma justifies temporarily using a discrete row σ-algebra internally. The theorem does **not** require the family to be independent of the ordered raw sample vector. |
| Population variance and norm | `d.variance V` is the source `E_d[V²]−(E_d[V])²`, proved nonnegative via its centered-square form; `‖V‖` is the finite Pi supremum norm. `bernsteinRadius_eq_source` proves the exact product-of-square-roots source form. No positive-variance, positive-norm, or support-positivity hypothesis is added. |
| Probability, quantification, constants | The final target has `1−δ < μ.real {ω | ∀ V∈family ω, … ≤ …}`. Its radius prints the source factor 2 under the square root, `log(4·card/δ)`, and `2/(3N)` norm term with actual cardinality. The event's vector inequality is non-strict; its success probability is strict. |
| Sample and confidence endpoints | The Lean inputs are `N : ℕ`, `0<N`, `0<δ`, `δ<1`. Thus N=1 is included, N=0 is excluded, and neither δ endpoint is asserted. The source does not give an N=0 convention for division. |
| Empty family | Lean admits it and the simultaneous event is vacuous; the deterministic-family proof has an explicit empty branch and the random transfer includes empty outcomes. Although Lean's real logarithm is total, the source does not explicitly specify `log 0`; no bound is evaluated for a member when the family is empty. This is a conventional boundary, not an attributed author ruling. |

## Why the strict conclusion follows

For nonempty fixed family of size k, `bernsteinViolation_le` instantiates the independently reviewed sharp fixed-vector theorem at `B=‖V‖∞` and `L=log(4k/δ)`, bounding each strict violation by `δ/(2k)`. The finite union bound gives total failure at most δ/2, so the complement has probability at least `1−δ/2 > 1−δ`. Zero variance and zero norm are handled by the sharp theorem, not positive-range assumptions; the empty family has its own case.

For random families, `supportedBernsteinBad` constructs an actual measurable family/empirical-row bad event using finitely many attainable empirical rows. `product_supportedBernsteinBad_lt` and `randomFamily_bernstein_success_gt` use the joint law and the stated independence to integrate the fixed-family bounds. The Borel enumeration machinery proves the necessary family tests measurable; the final literal-radius theorem is derived with `bernsteinRadius_eq_source`. No desired event probability or tail estimate is a final theorem input.

## Scope and source identity

This finding concerns only the first, single-row inequality. A separate whole-matrix result must handle all rows and the `SA` logarithmic factor; the staged matrix theorem at the time of its audit requires a full product law across raw rows, stronger than the preliminary chapter's explicit per-row iid statement. See `docs/critic-bernstein-matrix.md` for that unresolved boundary. No empirical-variance Bernstein result follows.

SHA-256 of the exact compared files:

- `Formalization/Probability/BernsteinFamily.lean`: `3f3d25c0953b629e7a8fba0921edf9a689a9818606e99e8eca7e64306299bcfe`.
- `Formalization/Probability/SharpEmpiricalBernstein.lean`: `f47b57d451b8ee49c8b702a834ee99747ec5cca36288bf9344dd08c11a596e67`.
- `Formalization/Probability/EmpiricalRow.lean`: `6e87c90ff1150f7053845acff92d60a5c35035c7a78adcd394e0da5f3d9dc154`.
- `Formalization/Probability/RandomFamilyBorel.lean`: `1bda21b0bac900dc0dec5db6cef949dfc99a745dff4cce14f2a1a0732c57d335`.
- `Formalization/Probability/Variance.lean`: `541714ed6173402131bece633476308c1c832f31d0cbb46534cc55f48dcd9553`.
- Source `prelim.tex`: `2d27bb720d49020ce1d3ea362b1678a90c6208882accca90fef21c25e42031a5`.

For this correspondence audit, a temporary probe imported the **integrated** `Formalization.Probability.BernsteinFamily` export and compiled successfully. It independently derived the exact joint product-law hypothesis from mutually independent coordinates with the correct marginals, checked the finite Pi sup-norm characterization, and printed the axioms of `bernsteinRadius_eq_source` and `randomBorelFamily_bernstein_source`: both report only `propext`, `Classical.choice`, and `Quot.sound`. This is an integrated-export probe against the existing compiled artifacts; the independent full-source review is recorded separately in `docs/critic-bernstein-family.md`.
