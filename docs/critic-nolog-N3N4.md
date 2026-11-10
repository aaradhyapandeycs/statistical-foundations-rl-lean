# Critic review: N3 (ConvexNonlinearTransfer.lean) and N4 (TDInferenceConvexSharp711.lean)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent review of N3 `Formalization/Probability/ConvexNonlinearTransfer.lean` (nonlinear transfer of the polyhedral Stein bound to all convex sets; sha256 75ffbbd9f429c38f9ed894a5b9668958777d5616d0564095d2f1e6e402091ab8) and N4 `Formalization/Ch7Rest/TDInferenceConvexSharp711.lean` (assembly of the corrected Theorem 7.11 over all convex sets at T^(-1/3); sha256 b3a0201a1e9d8aa86101ead71ed507fa91da9f2034be386a7fca70e9f8c765bd). Probes are local scratch files (`<local probe>`).

Integration note: both ACCEPT. I1 applied (`TDInferenceConvexSharp711.lean` imported from `Formalization.lean` and `Formalization/Statements/Ch7Proofs.lean`). I2 applied: entry `Thm7_11_corrected` in `Formalization/Statements/Ch7.lean` with wrapper `Thm7_11_corrected_holds`; COVERAGE Theorem 7.11 row, the `Thm7_11_corrected_halfspace` docstring and the stale "rate without log(2T) open" items updated (the oracle confidence-region corollaries are not re-derived at the sharper rate). I3: the printed coefficient remains open and is disclosed. The end-to-end statement audit is [critic-711-sharp.md](critic-711-sharp.md).

Reviewer: independent critic (read-only on Formalization/, docs/, Formalization.lean). Date 2026-11-10.

## Verdicts
- N3 `Formalization/Probability/ConvexNonlinearTransfer.lean`: **ACCEPT**.
- N4 `Formalization/Ch7Rest/TDInferenceConvexSharp711.lean`: **ACCEPT** (file); integration items I1-I3 are for the lead, not file fixes.

## Evidence
- No stale/missing project oleans (every Formalization/*.lean older than its olean, checked 07:10 EST).
- `bash scripts/lean-local.sh Formalization/Probability/ConvexNonlinearTransfer.lean`: rc=0, no output (local log).
- `bash scripts/lean-local.sh Formalization/Ch7Rest/TDInferenceConvexSharp711.lean`: rc=0, no output (local log).
- `<local probe>`: `abs_pexp_convex_add_sub_le`, `_update`, `abs_lawProb_sub_linLaw_le_third_of_burnIn`,
  `abs_lawProb_convex_sub_gaussCov_le_third_sharp` all depend on [propext, Classical.choice, Quot.sound] only.
  Same file #print's lawProb/scaledError/linPart/pathWeight/gaussCov and #check's every upstream lemma used.
- No sorry/admit/axiom/set_option in either file.

## N3 findings
1. Upper sandwich correct: w+d∈C, w∉C ⇒ φ(w)>0, φ(w+d)≤0, and 1-Lipschitz (sup norm, unit-ℓ¹ forms, `abs_polyPhi_sub_le`) gives φ(w)≤‖d‖, so φ(w)∈[0,‖d‖]. Lower sandwich symmetric: φ(w)∈[−‖d‖,0]. Other cases trivial by nonnegativity of intervalInd/indicator.
2. Exact representation used only on P = image W ∪ image (W+D), which contains both points of every ω (hWP, hWDP); `polyPhi_eq_sup'` is rfl (dotProduct unfolds). All-in-C case: indicators equal pathwise, bound ≥ 0 via hR0. Otherwise a point y₀∉C exists as `exists_polyhedral_repr` requires. No closedness/measurability needed; correct for finite Ω.
3. Theorem A instances: (a,b)=(0,‖D‖), (ai,bi)=(0,‖Dᵢ‖); (a,b)=(−‖D‖,0), (ai,bi)=(−‖Dᵢ‖,0). a≤b discharged by norm_nonneg / simp; update invariance by rfl or hDi. Endpoint terms simplify to |‖D‖−‖Dᵢ‖| (|−x−−y|=|x−y|) and b−a=‖D‖, giving exactly R. Division by λ uses hlam0. `_update` discharges hDi with `Function.update_idem`.
4. λ hypothesis is the uncentred directional second moment over unit-ℓ¹ v, identical to Theorem A's (H-λ); satisfiable, not vacuous.

## N4 findings
5. λ: ReservoirCond e L c 1 at r=n=T gives c·T/T·v⬝v ≤ ∑_{all m} v⬝(L(e m)L(e m)ᵀ)v; filter is univ, Equiv.sum_comp reindexes, `sum_mul_sq_dotProduct_eq` + `sum_tupleProb_mul_linSummand_mul` turn each term into ∑ₓp⟨v,ξ⟩². Cauchy–Schwarz 1=|v|₁² ≤ S v⬝v. λ = diagMin Γ_true/(32S)/S = diagMin/(32S²), independent of T and v, valid for T ≥ linReservoirBurnIn.
6. δ = T^{-1/2}K_βB from `norm_linSummand_le_inv_sqrt`; δ ≤ T^{-1/3}K_βB for T≥1 (`inv_sqrt_le_rpow_neg_third`, correct). Per-coordinate variance ≤ Tδ² = B², hence ∑√ ≤ SB, E‖W‖ ≤ SB, E m ≤ δS·SB.
7. Identifications: pexp p F = ∑ pathWeight·F by rfl (pathWeight = ∏ tupleProb); vsum = linPart via `linPart_eq_sum`; W + D = scaledError by add_sub_cancel; e1 matches `lawProb` definition exactly; E‖W‖‖D‖ and leave-one-out sums match upstream signatures verbatim (D = scaledError − linPart). xs = arbitrary tuple is legitimate: upstream lemma is ∀ xs.
8. Final arithmetic: λ⁻¹((4/3)(S²BK_E t + 2tB·SB + S K_CS t) + tB·S·SB) = convexNonlinConst·t by ring; constant depends only on (M,π,μ,V₀,μmin,η₀), μmin = diagMin μ — independent of T and C.
9. T < N: `abs_sum_pathWeight_indicator_sub_gaussCov_le_one` (≤1) and 1 ≤ N^{1/3}T^{-1/3}; K = |K₁|+|K₂|+N^{1/3}+1 > 0 dominates both branches. ∃K before ∀T ∀C: uniform.
10. No hidden hypotheses: same binders as `abs_lawProb_convex_sub_gaussCov_le_third_log` (0<η₀≤1, full-support μ, Γ_true≻0, any V₀); η₀≤1 is weaker than the printed 0<η₀<1/4.

## Integration items (lead)
- I1. Neither file is imported from Formalization.lean yet; add so the axiom audit covers them.
- I2. If recorded as proved, add a `Thm7_11_corrected` (all convex, corrected Γ, instance constant) entry in Statements/Ch7.lean + Ch7Proofs.lean (printed hypotheses η₀<1/4 follow from η₀≤1), and update COVERAGE row 30, the `Thm7_11_corrected_halfspace` docstring ("all-convex ... remains open") and the C47/conf-region "rate without log(2T)" open items, which this result now closes for the oracle shapes only after corollaries are re-derived.
- I3. Printed coefficient remains open; constant is an instance constant (docstrings say so).
