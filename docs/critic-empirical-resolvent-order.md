# Independent review: empirical policy-resolvent order

**Verdict: PASS for the four deterministic order and normalization properties of the actual empirical policy-transition resolvent.** They supply the positivity, monotonicity, all-ones normalization and absolute-value domination used in the source proof; they do not prove a concentration event, recursive auxiliary-error bound, or sharp policy-evaluation theorem. This is a staged-source review, not author approval or whole-paper certification.

Reviewed `.local/EmpiricalResolventOrder.lean`, SHA-256 `bed62174679d0a11f0778702e29f77a004d144a26d5e8f5b4661644ffafd0bf5`, and `docs/builder-empirical-resolvent-order.md`. The source is `source/upstream/tex/chapters/generative_model_model_based.tex:234–250`, especially `eq:sum-I-minu-gammaP-expand`, and lines 480–495, `eq:upper-bound-Vl-Vhatl-00`. Source SHA-256 is `b7e7abfb2c2cb2c0dd82470db5ecac3a67d7163682246d499935d9130214ac4d`.

## Actual matrix and assumptions

`empiricalMatrix N hN data` is the integrated direct policy-evaluation empirical transition matrix: row s is the finite probability distribution of N observed next states at s, current state indexes rows and next state columns. Its `mulVec` evaluates the corresponding empirical row. The theorem inputs an arbitrary *actual data realization*, not an arbitrary matrix with hidden positivity assumptions. Each row is normalized by the existing `empiricalPolicyRow` construction, and `empiricalResolvent_isUnit` has already established invertibility of `A=I−γP̂` from its stochastic rows and the admissible discount.

The source's conditions `0≤γ<1` and finite nonempty state/action sets follow from the actual `DiscountedMDP`; N>0 is explicit because empirical frequency rows require it. Results include γ=0. Since these are pointwise deterministic statements, no sampling probability or cross-row independence premise is required.

## Four exports

1. `empiricalResolvent_mulVec_nonneg` takes a genuinely nonnegative input vector f and proves every coordinate of `A⁻¹ f` nonnegative. Its proof sets u to the actual inverse image, obtains `Au=f` from proved invertibility, and chooses a minimum coordinate t. Stochastic averaging gives `P̂u(t)≥u(t)`; with f(t)≥0 and 0≤γ<1, a negative minimum would make `u(t)−γP̂u(t)<0`, contradiction. It does not assume inverse positivity. An independent compiled probe applied this theorem to each standard basis vector and verified every actual inverse matrix entry is nonnegative; no separate formal matrix-entry theorem is claimed in the staged file.
2. `empiricalResolvent_mulVec_mono` applies positivity to `g−f` and actual matrix linearity, preserving the input order `f≤g`. This works for arbitrary real vectors, with no extra nonnegativity requirement on f or g individually.
3. `empiricalResolvent_mulVec_one` proves `A⁻¹ 1 = (1/(1−γ))1`, using the empirical row's exact expectation of a constant and the independently proved invertibility. This is equality, not merely an upper bound, and includes γ=0. It is the source's all-one-vector/row-sum identity.
4. `empiricalResolvent_abs_le` applies monotonicity to `f≤|f|` and `−f≤|f|`, then matrix linearity under negation, giving `|(A⁻¹ f)(s)|≤(A⁻¹ |f|)(s)` for every coordinate. Absolute values are entrywise and the inverse remains the empirical one, exactly as in source Step (i).

The four statements have no probability-of-success, Bernstein, estimated-value equality, or future recursion result as a premise. Combined with a separate valid entrywise concentration event and nonnegative coefficients, monotonicity and the ones identity can support source Step (ii), but that application is not proved here.

## Independent verification and scope

A temporary copy of the exact staged source, with an entrywise matrix-positivity probe and four `#print axioms` commands appended, compiled successfully against the integrated `Formalization.Generative.PolicyEvaluationInverse` import via `bash scripts/lean-local.sh`. The first optional probe attempt needed an explicit `Pi.single` codomain annotation; the corrected probe and unchanged staged source compiled without diagnostics. All four exports `empiricalResolvent_mulVec_nonneg`, `empiricalResolvent_mulVec_mono`, `empiricalResolvent_mulVec_one`, and `empiricalResolvent_abs_le` have axiom closure exactly `propext`, `Classical.choice`, and `Quot.sound`.

This review did not change Lean source. Actual integrated-export compilation and axiom checks remain separate, as do the source's Bernstein event application, recursive value inequalities, terminal bound and final sample theorem.

## Integrated export recheck

`Formalization/Generative/EmpiricalResolventOrder.lean` is byte-identical to the reviewed staged source at SHA-256 `bed62174679d0a11f0778702e29f77a004d144a26d5e8f5b4661644ffafd0bf5`. The actual integrated source compiled cleanly to its previously absent project-owned `.olean` using `bash scripts/lean-local.sh -o .lake/build/lib/lean/Formalization/Generative/EmpiricalResolventOrder.olean Formalization/Generative/EmpiricalResolventOrder.lean`. A separate import-only probe checked all four reviewed exports; each again reports only `propext`, `Classical.choice`, and `Quot.sound`. Whole-project validation and the unproved source steps remain separate.
