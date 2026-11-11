# CHECK: the private corrected-theorem plan (independent plan check)

Public copy of the independent plan check; local paths removed.

Date: 2026-11-09. Checker: independent plan critic (did not write the plan). Read-only. I ran no Lean or lake, edited
nothing except this report, changed no git state and fetched no paper.

Read: `AGENTS.md`; `source/upstream/tex/chapters/inference.tex:100–146`; the plan (417 lines);
the private M4 plan check §1–§2; `docs/critic-thm7-11-m4.md` (header, calibration);
`Formalization/TDInference/Definitions.lean` (defs 50–160), `TDInferencePrinted711.lean` (the `Thm7_11_printed*`
Props), `TDInferenceNoise711.lean` (header, `tdSecondMoment_le`), `TDInferenceOperator711.lean`
(`mul_norm_le_norm_tdA_mulVec`, `norm_tdA_inv_mulVec_le`), `TDInferencePRRemainder711.lean`
(`weightedL2_scaledError_sub_prGaussPart_le_rpow`); the declaration lists of `GaussianAntiConcentration.lean`,
`LindebergFinite.lean`, `TDInferenceStepSize711.lean` and `TDInferenceZeroNoise711.lean`; `SOURCE-ISSUES.md` C47
header. All mathematics below was re-derived by hand.

## Verdicts

| Item | Verdict |
| --- | --- |
| §1 statement candidates (1.2, 1.3) | **GO WITH FIXES** (S1–S3) |
| M5 (D′, B1–B5) | **GO WITH FIXES** (F1–F3); recommended first brief |
| M5c G1 (convex shell, the key lemma) | **GO**: the lemma is **true**, and the proof sketch is correct (§2) |
| M5c G2/G3 (smoothing; P1 at T^{-1/9}) | **GO, low priority**: not on the counted path |
| M6 (B6, B7, P2) | **GO, deferred**: not on the counted path |
| M7 (1-D Stein Berry–Esseen) | **GO WITH FIXES** (F4) |
| M8 (Chen–Shao + TD leave-one-out) | **GO WITH FIXES** (F5–F7) |
| M9 (half-space assembly + index entry) | **GO WITH FIXES** (F8, S1); counting is a lead decision |
| Estimates | plausible overall; H2 is under-estimated (§5) |

**Key-lemma verdict (G1): TRUE.** For standard ν = ΠN(0,1) on `ι → ℝ` with |ι| = S, the sup norm, every convex K and
every r ≥ 0, ν(cthick_r K ∩ cthick_r (int K)ᶜ) ≤ 4S²r/√(2π). I found no counterexample among thin slabs, cones,
sets near the origin, unbounded sets, empty-interior sets, ∅ or univ. The earlier "no elementary route" remark
concerned covering along the set's own direction. Classifying by the large coordinate of the separating normal avoids
it.

## 1. Statement candidates

**Readings.**
- **d = S.** This is correct: √TΔ̄_T ∈ ℝ^S, so the class 𝒞_d can only mean convex subsets of ℝ^S (C47(3)).
- **R-inst** (both c and C̃ per instance). This reading is **exactly** equivalent to d_cvx(T) ≤ K′T^{-1/3} for all
  T ≥ 1 with an instance constant K′:
  - one direction is cK·T^{-1/3} + C̃T^{-1/2} ≤ (cK+C̃)T^{-1/3};
  - the other uses K′ = (K′/K)·K, which needs K > 0.

  So 1.2 = the C43-corrected `Thm7_11_printed_instWise` over all convex sets. This is right.
- **R-univ.** The plan's sentence in §0 is slightly wrong for a *fixed* c:
  - "≤ cKT^{-1/3} + C̃T^{-1/2} ∀T" implies limsup T^{1/3}d ≤ cK;
  - but limsup ≤ cK does not give back the bound with the same c, because convergence to cK from above can be
    slower than T^{-1/6}.

  The ∃-universal-c readings are nevertheless equivalent, because the bound with c gives limsup ≤ cK < 2cK, which
  gives the bound with 2c (K > 0, finite prefix into C̃). Fix S2.
- **Instance C̃.** C̃ per instance, including V₀, drops the printed "polynomial in salient parameters". That cannot be
  formalized without the cited paper. It is already disclosed in the `Thm7_11_printed*` docstrings and must be repeated
  in the new entries (S1).

**1.3 `Thm7_11_restricted_halfspace`: honest, and meets the §2 threshold.** It checks each of the four threshold
conditions:

| Threshold condition | Met by 1.3 |
| --- | --- |
| Convex subclass | closed half-spaces, a disclosed scope restriction |
| Covariance | true Γ (C43) |
| Rate | the printed rate T^{-1/3} |
| Coefficient | a changed coefficient, which the docstring states |

Notes:
- **Closed only.** Closed half-spaces suffice for all half-spaces. P(uᵀX < b) = lim_n P(uᵀX ≤ b − 1/n) on both sides,
  so the bound passes to open half-spaces with the same K. Recording this in COVERAGE is optional.
- **Not a weak smooth metric.** Half-space distance is the sup over u of the Kolmogorov distance of the 1-D
  projections. This is a genuine set-probability statement, unlike the M4 smooth metric. It still does **not** give the
  convex confidence regions of :144/:185ff (ellipsoids and rectangles are not half-spaces), and COVERAGE must say so
  (S3).
- **Hypothesis `∀ s, 0 < trueGamma`.** This is not a hidden hypothesis. The printed coefficient uses ‖Γ⁻¹‖ and κ(Γ),
  so the printed bound is meaningless unless Γ ≻ 0. The Γ is the corrected one (C43).
- **Definitions.** The sketches use real definitions. `lawProb`, `gaussCov`, `tdA`, `trueGamma`, `DiscountedMDP`,
  `StationaryPolicy` and `FiniteDistribution` all exist (`TDInference711Defs.lean:96,133,108,121`). The binders match
  `TDInferencePrinted711.lean:37–49`. The Props are self-contained and do not refer to any theorem's type.
- **u = 0 case.** The set is univ or ∅. `lawProb_univ` and the probability-measure property of `gaussCov` close it.
- **Index file import.** `Formalization/Statements/Ch7.lean` does not yet import `TDInference711Defs`, so M9 must add
  it. `TDInference711Defs` contains only definitions plus basic facts. It imports `ModelFree.TDIterateBounds`, which
  is acceptable under the project's existing "definition module" practice; the lead should confirm.

**1.2 `Thm7_11_restricted_instConst`.** This is honest; it is the corrected covariance plus the R-inst reading. It is
research-scale and deferred, as the plan says.

**Required statement fixes:**

- **S1 (the 1.3 docstring lacks the issue pointer and the C̃ disclosure; AGENTS requires both).** Replace the 1.3
  docstring with:

  > Theorem 7.11 (`thm:Berry-Esseen-linear`, `chapters/inference.tex:132–141`), corrected covariance and restricted
  > class and constant. Differs from the printed result in three ways: (1) `Γ` is the true per-sample TD-noise
  > covariance `trueGamma` (printed `Γ` uses `r_π`; SOURCE-ISSUES C43); (2) the sets are closed half-spaces
  > `{x | ∑ s, u s * x s ≤ b}` only, not all convex sets in `ℝ^S`; (3) the `T^{-1/3}` constant `K` depends on the
  > instance, `η₀` and `V₀` and is not shown to be a universal multiple of the printed
  > `√(η₀/((1−γ)λ₀))Tr Γ‖Γ⁻¹‖ + √(Sκ(Γ))/((1−γ)λ₀η₀)`; `C̃T^{-1/2}` is absorbed into `K` and is not shown polynomial.
  > Kept: printed rate `T^{-1/3}`, printed `η_t = η₀t^{-2/3}` with `0 < η₀ < 1/4`, i.i.d. full-support μ-sampling,
  > every `V₀`, `d = S`. See SOURCE-ISSUES C43 and C47(3).

- **S2 (§0 R-univ wording).** Replace "is equivalent to limsup_T T^{1/3}·d_cvx(T) ≤ c·K" with:

  > implies limsup_T T^{1/3}·d_cvx(T) ≤ c·K, and conversely limsup ≤ c·K implies the bound with 2c (K > 0; the finite
  > prefix goes into C̃). Hence the readings "for some universal c" coincide.

- **S3 (COVERAGE/C43 text at M9).** The status line must read:

  > restricted variant: closed half-spaces only (1-D projections), corrected Γ, instance/V₀ constant at the printed
  > rate; the all-convex statement (1.2) and the printed coefficient (1.1) remain open; implies no convex
  > confidence-region guarantee beyond half-spaces.

  Whether this counts toward the named-result ledger is the lead's or user's decision. The M4 threshold text admits
  it.

## 2. KEY LEMMA G1: re-derivation and break attempts

Notation: ⟨u,x⟩ = Σ u_i x_i; ‖·‖ is the sup norm, so |⟨u,x−y⟩| ≤ ‖u‖₁‖x−y‖.

**Step 1 (a functional for each shell point).** Let x ∈ cthick_r K ∩ cthick_r (int K)ᶜ.
- (int K)ᶜ is closed and nonempty (else the shell is empty), and the space is proper. So some y ∉ int K has
  ‖x−y‖ ≤ r (`IsClosed.exists_infDist_eq_dist`, or the infEdist version).
- **Case int K ≠ ∅.** `geometric_hahn_banach_open_point` gives f ≠ 0 with f(z) < f(y) on int K. Then f(z) ≤ f(y) on
  closure(int K) ⊇ K (`Convex.closure_interior_eq_closure_of_nonempty_interior`). Write f = ⟨u,·⟩ and normalize
  ‖u‖₁ = 1. Then ⟨u,z⟩ ≤ ⟨u,y⟩ ≤ ⟨u,x⟩ + r for all z ∈ K.
- **Case int K = ∅, K ≠ ∅.** The affine span is proper (`Convex.interior_nonempty_iff_affineSpan_eq_top`), so a
  nonzero u, with ‖u‖₁ = 1, is constant (= c) on K. Since x is within r of closure K, |⟨u,x⟩ − c| ≤ r, so again
  ⟨u,z⟩ ≤ ⟨u,x⟩ + r on K.
- **Case K = ∅.** Then cthick_r K = ∅.
- **Case K = univ.** Then (int K)ᶜ = ∅ and the shell is empty.

Correct.

**Step 2.** ‖u‖₁ = 1 forces some |u_i| ≥ 1/S. Correct.

**Step 3 (the crux).** Define B_i^+ := {p ∈ cthick_r K : ∃u, ‖u‖₁ = 1, u_i ≥ 1/S, ∀z∈K, ⟨u,z⟩ ≤ ⟨u,p⟩ + r}. Take
p and p + s·e_i in B_i^+ with s > 0, and use **p's** u.
- First, sup_K⟨u,·⟩ ≤ ⟨u,p⟩ + r. The sup is finite even for unbounded K, because the inequality itself bounds it.
- So ⟨u,p+se_i⟩ ≥ sup_K⟨u,·⟩ − r + s/S.
- Second, p + se_i ∈ cthick_r K gives ⟨u,p+se_i⟩ ≤ sup_K⟨u,·⟩ + ‖u‖₁r.
- Hence s ≤ 2Sr. Only p's membership in B_i^+ and the other point's membership in cthick_r K are used.

Every e_i-line section of B_i^+ therefore has diameter ≤ 2Sr. B_i^- is symmetric, using p + se_i's functional, or by
reflecting.

**Step 4 (closedness).** {(p,u) : ∀z∈K, ⟨u,z−p⟩ ≤ r} is an intersection of closed sets. Intersect it with
ℝ^S × U_i^±, where U_i^± = {‖u‖₁ = 1, ±u_i ≥ 1/S} is compact. The projection is closed
(`isClosedMap_fst_of_compactSpace` on the compact subtype). Intersecting with the closed cthick_r K gives B_i^±
closed. Correct.

**Step 5 (Fubini).** ν(B_i^±) ≤ (1/√(2π))·sup over sections of λ(section) ≤ 2Sr/√(2π). Summing over the 2S pieces
gives 4S²r/√(2π). The repo already has the slicing lemma `measure_pi_le_of_slice_le` and `gaussianPDFReal_le_inv_sqrt`
(`GaussianAntiConcentration.lean:26,65`); use them instead of a new Fubini.

**Break attempts (all fail):**
- **Thin slab** K = {|x₁| ≤ ε}.
  - If ε ≤ r, the shell is {|x₁| ≤ ε+r}, with mass ≤ 2(ε+r)/√(2π) ≤ 4r/√(2π).
  - If ε > r, the shell is {ε−r ≤ |x₁| ≤ ε+r}, with mass ≤ 4r/√(2π).

  Both are within the bound. These points are classified by their **normal** e₁, so the slab's thinness is
  irrelevant.
- **Segment or hyperplane** (int K = ∅). The bound gives cthick_r K ⊆ {|⟨u,x⟩ − c| ≤ r}, a slab of Euclidean width
  2r/‖u‖₂ ≤ 2r√S, with Gaussian mass ≤ 2r√S/√(2π). Consistent.
- **Cone near the apex, or a set at the origin.** Nothing in Steps 1–5 uses distance to the origin or the curvature of
  ∂K. The apex region is covered by B_i for whichever normal is chosen.
- **Unbounded K, and K with interior but non-closed.** Handled in Steps 1 and 3 (closure(int K) ⊇ K).
- **Dimension sanity check.** The sharp Euclidean bound is O(S^{1/4}·ρ) (Nazarov). A sup-norm r-shell lies inside a
  Euclidean (r√S)-shell, giving O(S^{3/4}r). This is consistent with S², so there is no contradiction. The lower-bound
  examples (Nazarov's polytopes) have mass ≍ S^{1/4}ρ ≤ S² r. As the plan says, S² is useless for R-univ but fine for
  instance constants.

**Consequences, which I checked.**
- **Shell transfer.** K\K_{−r} and cthick_r K \ int K both lie in the shell.
- **Change of variables.** For Z = Lz with L = A⁻¹diag(√Γ):
  - L⁻¹ = diag(1/√Γ)A;
  - ‖A‖_{∞→∞} = max_s μ(s)(1 − γP_ss + γ(1−P_ss)) ≤ 1+γ ≤ 2, so ‖L⁻¹‖ ≤ 2/√(minΓ);
  - L⁻¹ is a linear homeomorphism, so L⁻¹((int K)ᶜ) = (int L⁻¹K)ᶜ.
- **Frontier and outer measure.**
  - Letting r → 0 gives gaussCov(frontier K) = 0.
  - `.real` of a non-measurable convex C is the outer measure of the pushforward, which is sandwiched between
    interior C and closure C.
  - Since the frontier is null, it equals the measure of the closure. The data side (`lawProb`) is a finite sum and
    has no measurability issue.

All correct.

## 3. D′ (route B, M5)

**B1.**
- Row s of I − ηA has diagonal 1 − ημ(s)(1 − γP_ss) and off-diagonal entries ημ(s)γP_ss′ ≥ 0.
- If ημ(s) ≤ 1 the diagonal is ≥ 0, and the absolute row sum is exactly 1 − ημ(s)(1−γ).
- Hence ‖I−ηA‖_∞ = max_s(1 − ημ(s)(1−γ)) = 1 − η(1−γ)λ₀ for 0 ≤ η ≤ 1.
- Under the printed range η_t ≤ η₀ < 1/4 ≤ 1.

This holds for every full-support μ, with no stationarity. It matches `mul_norm_le_norm_tdA_mulVec`. The random
I − ηA_k are also ∞-nonexpansive for η ≤ 1 (row s_k sum = 1 − η + ηγ·[s′≠s] + …).

**Recursion check.**
- `tdStep_sub_value_apply` gives Δ_t = (I − η_tA_t)Δ_{t−1} − η_tξ_te_{s_t}, with A_t = e_s(e_s − γe_{s′})ᵀ.
- E[A_t] = A, E[ξ_te_{s_t}] = 0 (Bellman, `tupleCondExp_tdNoise`), and Cov(ξe) = diag(trueGamma).
- Hence D_t := Δ_t − Δ^lin_t satisfies D_t = (I−η_tA)D_{t−1} − η_t(A_t − A)Δ_{t−1}, with D_0 = Δ_0.
- Summing: E_T = T^{-1/2}Σ_t G_{0,t}Δ_0 (deterministic) + T^{-1/2}Σ_k β_{k,T}(A_k−A)Δ_{k−1}.

This is the plan's B3.

**B4 order (L² remainder): O(T^{-1/3}) confirmed.**
- The ζ_k = (A_k−A)Δ_{k−1} are martingale differences. Coordinatewise orthogonality gives
  E[E_T(s)²] ≤ T⁻¹Σ_k‖β_k‖²_∞ E‖ζ_k‖²_∞ + transient.
- E‖ζ_k‖² ≲ Σ_s E Δ_{k−1}(s)² ≲ Sη_k by `tdSecondMoment_le` (proved in M3 for non-stationary μ via the max-coordinate
  recursion; no stationarity).
- Σ_k η_k ≍ 3η₀T^{1/3}, so E[E_T(s)²] ≲ T^{-2/3} and the L² norm is ≲ T^{-1/3}.
- The transient is ≤ T^{-1/2}‖Δ_0‖·Σ_t e^{−aΣ_{i≤t}η_i}, which is a finite instance constant.

**B5 order (covariance error): O(T^{-1/3}) confirmed. Recommended proof device** (add to the brief, F2).
- All the G_{k,t} are polynomials in A, so they commute with A.
- From G_{k,t+1} = (I − η_{t+1}A)G_{k,t}: Σ_{t=k}^{T} η_{t+1}G_{k,t} = A⁻¹(I − G_{k,T+1}).
- Hence −β_{k,T} − A⁻¹ = Σ_{t=k}^{T}(η_k − η_{t+1})G_{k,t} − A⁻¹G_{k,T+1}. The two pieces:
  - The first is ≲ η_k/k · Σ_t (t−k)e^{−aη_t(t−k)} ≲ k^{-1/3}/(a²η₀) (bulk), plus a summable early-k part.
  - The second sums to Σ_k‖G_{k,T+1}‖ ≲ 1/(aη_T) ≍ T^{2/3}.
- Then ‖Λ_T − Λ‖ ≤ T⁻¹Σ_k(‖β_k‖ + ‖A⁻¹‖)‖Γ‖‖β_k + A⁻¹‖ ≲ T⁻¹(T^{2/3} + T^{2/3}) = T^{-1/3}.
- The sign varies (CHECK-M4 R3); the bound is on a norm, so no sign is needed.
- This also matches the CHECK-M4 numerics.

**Hidden assumptions: none beyond full support, 0 < η₀ ≤ 1, T ≥ 1.** Γ ≻ 0 is **not** needed for B4 or B5.

**Required M5 fixes:**

- **F1 (B2 wording).** "uniform bound ‖β_{k,T}‖ ≤ C′/a" is not right with C′ universal.
  - For small k, η_kΣ_t e^{−3aη₀(t^{1/3}−k^{1/3})} ≈ 1/a + O(1/(a²η₀ k^{1/3})) + O(1/(a³η₀²k^{2/3})).
  - Replace it with: "‖β_{k,T}‖_∞ ≤ K_β for all 1 ≤ k ≤ T, with K_β explicit in a = (1−γ)λ₀ and η₀, and free of k
    and T (≍ 1/a + 1/(a³η₀²))".
  - Only T-freeness matters.
- **F2.** Add the commutation/telescoping identity above to the B5 brief, as the route for β_{k,T} → −A⁻¹.
- **F3 (M5 must also export the independence structure M8 needs).**
  - `linPart ω = ∑ k, linSummand T k (ω k)`: each summand depends only on tuple k, with deterministic weights.
  - Its exact covariance identity Σ_ω pathWeight·linPart(s)·linPart(s′) = linCov T s s′.
  - Lean indexing: `tdIter` uses `stepSize η₀ (t+1)` with `ω t`, so β must be indexed to match. The pair
    `prAverage` / `range T` / `t+1` must be reconciled once, here.

## 4. M7/M8: the half-space route

**Reduction to 1-D (correct).**
- Fix u ≠ 0. Then uᵀX = c_T + uᵀX^lin + uᵀE′_T, where c_T is the deterministic transient. It only shifts b, and the
  Kolmogorov sup absorbs it.
- Set σ²_{u,T} = uᵀΛ_Tu, W = uᵀX^lin/σ_{u,T} = Σ_k w_k(ω_k) and Δ = uᵀE′_T/σ_{u,T}.
- The w_k are independent, mean 0 and non-identically distributed, with Σ Ew_k² = 1 exactly.
- **Positivity for all T ≥ 1.** Λ_T ⪰ T⁻¹β_TΓβ_Tᵀ = T⁻¹η_T²Γ ≻ 0, since β_{T,T} = −η_T I. So σ_{u,T} > 0, and no
  large-T assumption is needed for the normalization.
- **Uniform lower bound.**
  - σ²_u := uᵀΛu = ‖Γ^{1/2}A⁻ᵀu‖₂² ≥ minΓ·‖A⁻ᵀu‖²_∞ ≥ minΓ‖u‖²_∞/‖Aᵀ‖²_∞.
  - ‖Aᵀ‖_∞ = max column sum ≤ μ(s′) + γΣ_sμ(s)P_ss′ ≤ 1 + γ ≤ 2.
  - H4's σ_u ≥ √minΓ‖u‖_∞/2 is correct. For T ≥ T₀, B5 gives σ_{u,T} ≥ σ_u/2.
- **Lyapunov ratio, uniform over u (correct, with an S factor).**
  - |w_k| ≤ T^{-1/2}|(β_kᵀu)_{s_k}|·B/σ_{u,T} ≤ T^{-1/2}‖u‖₁K_βB/σ_{u,T} ≤ T^{-1/2}·2SK_βB/(√minΓ/2).
  - Note that ‖β_kᵀ‖_∞ = ‖β_k‖_{1→1} is **not** controlled by the sup-norm contraction directly. Go through
    |uᵀβ_ke_s| ≤ ‖u‖₁‖β_k‖_∞ and ‖u‖₁ ≤ S‖u‖_∞ (F7).
  - Hence Σ_k E|w_k|³ ≤ max|w_k| ≲_inst T^{-1/2}.

**Chen–Shao terms (rate T^{-1/3}, no log: confirmed).**
- β₂ + β₃ ≲ T^{-1/2}.
- E|WΔ| ≤ ‖Δ‖₂ ≲ T^{-1/3}, by B4.
- Σ_i E|w_i(Δ − Δ^{(i)})| ≤ Σ_i ‖w_i‖₂‖Δ−Δ^{(i)}‖₂ ≲ Σ_i T^{-1/2}·T^{-1/2}√η_i = T⁻¹√η₀Σ i^{-1/3} ≍ T^{-1/3}.
- Variance step |Φ(z/σ_T) − Φ(z/σ)| ≤ C|σ_T²/σ² − 1| ≲ S²K_Λ T^{-1/3}/(minΓ/4), uniformly in z and u.

The total is T^{-1/3}; there is no tail argument, hence no log.

**Leave-one-out bound H3 (re-derived; correct, but the brief must name the mechanism).**
- Replace tuple i by a fixed x⋆; any tuple works, since |ξ(x⋆)| ≤ B holds for every tuple (`abs_tdNoise_le`). Let
  δ_k = Δ_k − Δ_k^{(i)}. Then:
  - δ_i = −η_i[(A_i − A⋆)Δ_{i−1} + ξ_ie_{s_i} − ξ⋆e⋆];
  - for k > i, δ_k = (I − η_kA_k)δ_{k−1}, a zero-noise TD recursion.
- Summing as in B3: X − X^{(i)} = T^{-1/2}[Σ_tG_{i,t}δ_i + Σ_{k>i}β_k(A_k−A)δ_{k−1}].
- The noise part of Σ_tG_{i,t}δ_i is exactly β_i(ξ_ie − ξ⋆e⋆) = the change in X^lin, so it **cancels** in E. What
  remains:
  - T^{-1/2}β_i(A_i − A⋆)Δ_{i−1}, of size T^{-1/2}K_β·O(√η_i);
  - plus the martingale sum, of size T^{-1/2}K_β(Σ_{k>i}E‖δ_{k−1}‖²)^{1/2}.
- **This needs a second-moment decay for the zero-noise recursion:** max_s Eδ_k(s)² ≤ Π_{i<j≤k}(1 − aη_j)·max_s
  Eδ_i(s)². That is M3's `tdSecondMoment_succ_le` mechanism (max-coordinate, Jensen on the convex combination) with
  noise 0. It is **not** the sup-norm contraction B1, which is pathwise and only nonexpansive for random A_k.
- With it, Σ_{k>i}E‖δ_k‖² ≲ η_i²/(aη_i) = η_i/a, so ‖Δ−Δ^{(i)}‖₂ ≲_inst T^{-1/2}√η_i.
- **Independence.** Δ^{(i)} and W − w_i are functions of tuples ≠ i, hence independent of tuple i under the product
  `pathWeight`. That is exactly the Chen–Shao (2007, Thm 2.1) hypothesis.

**Required M7/M8 fixes:**

- **F4 (M7 scope).** The Stein solution f_z has f_z′ discontinuous at z. The brief must say:
  - the Stein identity E[w f(W)] = Σ_i E∫K_i(t)f′(W^{(i)}+t)dt is proved for Lipschitz f with a derivative off a
    finite set (FTC with countable exceptions: `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` or the
    off-countable variants);
  - the concentration inequality P(a ≤ W^{(i)} ≤ b) ≤ √2(b−a) + 2(√2+1)β₃ (or the repo's chosen constant) is part of
    M7, not M8.
- **F5 (M8 H2 scope and estimate).** H2 needs the **randomized** concentration inequality P(Δ₁ ≤ W ≤ Δ₂) for random
  Δ₁, Δ₂ (Chen–Shao 2007, Prop./Lemma 5.1). This is a separate multi-page argument. Re-estimate H2 at 1500–2500
  lines, not 800–1500. The generic export must take an arbitrary finite product of finite laws, with no TD imports.
- **F6 (M8 H3 brief).** Name the zero-noise second-moment decay lemma (above) as a deliverable, for example
  `max_secondMoment_zeroNoise_le`. Also state the cancellation of the β_i noise term explicitly, so the builder does not
  bound it crudely: a crude O(T^{-1/2}) per-i bound would give Σ_i T^{-1}·O(1) = O(1).
- **F7 (H4).** Use ‖u‖₁ ≤ S‖u‖_∞ for the β_kᵀ bound. Use the trivial bound |·| ≤ 1 ≤ K·T^{-1/3} for T < T₀, with
  K ≥ T₀^{1/3}, where T₀ is the B5 threshold for σ_{u,T} ≥ σ_u/2.
- **F8 (M9).** The wrapper must use the `gaussCov` projection lemma (uᵀL z ~ N(0, uᵀΛu)), which is to be proved from
  `StdGaussianPi`. The u = 0 case goes through `lawProb_univ` / `lawProb` of ∅ and `IsProbabilityMeasure` of the map.

## 5. Estimates against history

- **Calibration.** M3 was 1755 lines and M4 1250 lines (`critic-thm7-11-m4.md` hashes; 156+297+453+344), each from
  precise plans. At that pace the counted path (6.3–11.3k lines) would be about 4–8 builder-hours. The plan's 20–45
  builder-hours applies a 3–5× novelty factor for Stein, Chen–Shao and leave-one-out. That is reasonable, not inflated.
- **Per-milestone.**
  - H2: low (F5).
  - H1: plausible.
  - M5 (1.7–3k): plausible. B4 is coordinatewise scalar orthogonality, so it may come in at the low end.
  - M5c (2–3.4k): plausible.
- **Total.** 32–67 agent-hours over 4–8 windows is plausible. I would quote the counted path as **7–12k lines**
  (H2 raised).
- **Gating.** M5c, M6 and G2/G3 are **not** prerequisites of the counted path. They should get slots only after M5,
  M7 and M8 are staffed.

## 6. Candidate notes N1–N6

| Note | Assessment | Action |
| --- | --- | --- |
| N1 | **Open candidate, not established.** My B5 calculation shows the leading covariance mismatch is ≍ T^{-1/3}/(aη₀) in sup norms. Whitening with Γ^{-1/2} and moving between sup and Euclidean norms can add factors of S or κ(Γ) beyond the printed √(Sκ). Neither direction is shown. The diagonal-Lyapunov-weight paper calculation in §2 of the plan is correct: ν_βP ≤ ν_β/β; constant (1−γ)/(1+γ)·λ₀; κ(Q) ≤ 4/(3(1−γ)λ₀). | Do not record unless numerics show limsup T^{1/3}d / K unbounded along a family. |
| N2 | **Real but trivial** wording slip ("standard Gaussian … with the asymptotic covariance"). | Optional one-line note in C43; not a separate issue. |
| N3 | **Not a source issue.** Convex sets are Lebesgue-measurable. With the completed Gaussian and the atomic data law, any convex A can be replaced by a Borel A′ (A minus the null boundary part, plus the finitely many atoms) with the same two probabilities, so d_cvx ≤ TV holds. TV = 1 makes the remark uninformative but not false. | None. |
| N4 | Presentation only; already implied by C43/C47's C̃ reading. | None. |
| N5 | Open risk, relevant only to R-univ. | None now. |
| N6 | Already recorded. | None. |

## 7. Recommended first builder brief: M5 (lane 1)

- **Goal.** Library infrastructure for the linearised process (D′). Partial infrastructure only: **no**
  `Statements/` entry, no COVERAGE or ledger change.
- **Source locators.**
  - `inference.tex:52–64` (sampling);
  - :72 (update);
  - :82, :88 (PR average, Δ̄_T);
  - :104–117 (A, Λ⋆, Γ);
  - :134 (η_t = η₀t^{-2/3});
  - C43 (Γ := trueGamma).
- **Imports.** `Formalization.TDInference.Noise`, `TDInferenceOperator711`, `TDInferenceStepSize711`,
  `TDInferencePRRemainder711` (for `WeightedL2` and orthogonality patterns), `Formalization.Probability.WeightedL2`.
- **Owned files (new only).**
  - `Formalization/Analysis/MatrixContractionSup.lean`: B1. Generic statement: a matrix with nonnegative diagonal and
    absolute row sums ≤ 1 − c contracts the sup norm by 1 − c. TD instance: ‖(1 − η•tdA)v‖ ≤ (1 − η(1−γ)μmin)‖v‖ for
    0 ≤ η ≤ 1.
  - `Formalization/TDInference/Linearised.lean`: definitions `linKernel` (G_{k,t}), `linWeight` (β_{k,T}),
    `linSummand`, `linPart` (X^lin_T), `linCov` (Λ_T), and the pathwise decomposition B3 of
    `scaledError − linPart`. Lean indexing must match `tdIter` (tuple `ω t` uses `stepSize η₀ (t+1)`).
  - `Formalization/TDInference/Kernel.lean`: B2 (kernel decay, a k- and T-free K_β), the commutation and
    telescoping identity Σ_{t} η_{t+1}G_{k,t} = A⁻¹(I − G_{k,T+1}).
  - `Formalization/TDInference/LinearisationRemainder.lean`: B4.
  - `Formalization/TDInference/LinearisedCovariance.lean`: B5, plus the covariance identity of `linPart` (F3).
- **Exports (signatures fixed up front; constants explicit and T-free).** The hypotheses throughout are
  `0 < η₀`, `η₀ ≤ 1`, `0 < μmin`, `∀ s, μmin ≤ μ.prob s`, `1 ≤ T`, and every `V₀`. No Γ hypothesis, no stationarity.
  - `weightedL2_scaledError_sub_linPart_le`: ∀ s, `weightedL2 (pathWeight M π μ) (fun ω ↦ scaledError M π η₀ V₀ ω s
    − linPart … ω s) ≤ K_E * T^(-(1/3))`.
  - `abs_linCov_sub_le`: ∀ s s′, `|linCov … T s s′ − ((tdA)⁻¹ * diagonal (trueGamma) * (tdA)⁻¹ᵀ) s s′| ≤
    K_Λ * T^(-(1/3))`.
  - `linPart_eq_sum` (each summand depends only on `ω k`) and `sum_pathWeight_linPart_mul_linPart` (equals
    `linCov`).
  - `linWeight_last` (β_{T,T} = −η_T•1), for M8's positivity.
- **Validation.** Focused compiles only: `bash scripts/lean-local.sh` per file, at most one compiler (the lead holds
  the other slot). A probe file with `#print axioms` on every export must show only
  `propext, Classical.choice, Quot.sound`, and must instantiate the exports on the `zMDP` instance
  (`TDInferenceZeroNoise711`) and on one instance with Γ ≻ 0 (non-vacuity). No `sorry`, `admit` or `axiom`; no edits
  to existing files or signatures.
- **Stop condition.** Stop when all exports compile axiom-clean with the probe. Report file sha256s, line counts and
  compile times. If either T^{-1/3} order fails to close, **stop and report the obstruction**. Do not weaken it to
  T^{-1/6} or add hypotheses.

**Parallel lane (one slot, if available): M5c-a = G1 only.**
- Owned file: `Formalization/Probability/GaussianConvexShell.lean`.
- Exports:
  - `stdGaussianPi_convexShell_le`: all convex K, r ≥ 0, ≤ 4S²r/√(2π), sup-norm `Metric.cthickening`;
  - `gaussCov_frontier_eq_zero` (∀ convex K, under ∀ s, 0 < Γ s and invertible A).
- Reuse `measure_pi_le_of_slice_le` and `gaussianPDFReal_le_inv_sqrt`.
- Follow §2 Steps 1–5 exactly: classify by the separating normal's large coordinate; handle the int K = ∅ case with a
  functional constant on the affine span.
- Same validation and stop rules. G2/G3 wait.
