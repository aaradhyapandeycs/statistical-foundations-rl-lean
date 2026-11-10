# Plan check (gate P0): all-convex route to Theorem 7.11

Public copy, scrubbed (local paths and the builder brief of the original §11 removed). This is a
**paper-level plan check** of the route to an all-convex-sets Berry–Esseen bound for the corrected Theorem 7.11
(`thm:Berry-Esseen-linear`, `chapters/inference.tex:132–141`). It concerns **route infrastructure, not a source
result**: nothing here is a Lean proof, and no COVERAGE row, statement entry or named-result count depends on it.
Milestone and section numbers of the plan (M1–M8, "§4.M5", ...) refer to the unpublished route plan; F1–F7 are
this check's fixes. Milestones M1 and M2 have been built as Lean infrastructure and reviewed
([critic-allconvex-m1.md](critic-allconvex-m1.md), [critic-allconvex-m2.md](critic-allconvex-m2.md)); the later
milestones are open.

Date: 2026-11-09. Checker: independent paper critic. I did not write the plan.

Scope and method:
- Read-only. No Lean, no lake, no git changes, no downloads. The only file written is this one.
- Plan sha256: `14a004e26b6d068888d78662cf3bcb0ee603247ac4bbaa083dd0ddb82cc52327` (446 lines; the plan itself is not published).
- Also read:
  - [critic-thm7-11-corrected-plan-check.md](critic-thm7-11-corrected-plan-check.md) §1–§3 (G1 re-derivation);
  - `docs/critic-thm7-11-m5.md` (the M5 exports);
  - declaration heads of `TDInferenceKernel711.lean` (`sum_linWeightGap_le`, `norm_linWeight_sub_inv_mulVec_le`),
    `TDInferenceLinearised711.lean`, `TDInferenceLinRemainder711.lean` (`linMartTerm`),
    `ConvexDistanceTV711.lean`, `GaussianAntiConcentration.lean` and `MatrixContractionSup.lean`;
  - the repo's Azuma/Freedman files (`Formalization/Probability/Azuma*.lean`, `Freedman*.lean`,
    `BoundedIncrementFixedTimeTail.lean`).
- Literature comparisons are from memory; nothing was fetched.

All mathematics below was re-derived by hand. Notation:
- n summands, b ≍ n^{-1/2} the a.s. bound, Σ ≥ λI;
- j = the number of not-yet-swapped indices, with reservoir covariance v_j ≳ j/n;
- s̄ = the shell-probability factor.

## Verdicts

| # | Claim | Verdict |
| --- | --- | --- |
| 1a | Reservoir swap; the tail where the reservoir vanishes | **CONFIRMED.** Bound (c) handles the last ≈ nε² swaps. |
| 1b | Third-order remainder, with derivatives in the ε-shell, factored as E‖Y‖³·s̄ | **FIXABLE (F2)** |
| 1c | Closure of the hybrid class ("drop k, halve reservoir"), with pass 1 uniform over it | **FIXABLE (F1).** True for the concrete prefix class; not proved for the class as written. |
| 1d | Convex-set operations: translates, thickening, interior, inner parallel set, A∖B shells | **CONFIRMED.** Measurability: F3. |
| 1e | Dimension and constants (G1 S², Hermite S-polynomial, b√n) | **CONFIRMED** (instance-level only) |
| 2 | Pass 1 = n^{-1/4}; pass 2 = n^{-3/8} log n; crossovers j₁, j₂; pass 3 = n^{-7/16} | **CONFIRMED** (arithmetic) |
| 3 | Non-identical weights; Markov count; reservoir with r₀ = O(1) | **CONFIRMED**, with a norm detail (F7) |
| 4 | Chebyshev on B4 gives all-convex T^{-2/9} | **CONFIRMED.** Pass 1 alone suffices (F5). |
| 5 | Smoothing caps T^{-1/12} / T^{-1/9} / T^{-1/8} | **CONFIRMED** as arithmetic of the stated cost templates. "Impossible" means only "for this template". |
| 6a | Doob differences d_k = linSummand_k + T^{-1/2}β_k(A_k−A)Δ_{k−1}; transient deterministic | **CONFIRMED on paper**, modulo index and sign conventions |
| 6b | M8a (martingale reservoir Lindeberg) is the route to T^{-1/3}(1+log T) | **Plausible but superseded (F6).** A far shorter route gives the same rate. |
| 6c | Exact T^{-1/3} needs research (shell-local leave-one-out or Shao–Zhang) | **CONFIRMED** (agree) |
| — | "Pass-2 bootstrap is the planner's construction" | Fair, if worded as "a two-step truncation of the Bentkus-style recursive smoothing argument". Not from a cited paper. |

**Overall for Phase 1: GO WITH FIXES (F1–F7).** I found no false rate claim. The two substantive gaps are F1
(the hybrid class) and F2 (the factoring of the remainder). Both have concrete fixes. F5 and F6 are not
corrections; they are cheaper paths.

## 1. Reservoir swap

**Setup re-derived.**
- Order e(1..n). Hybrid at step k: U_k = Σ_{m<k} Y_{e(m)} + Σ_{m>k} G_{e(m)}.
- The Gaussian twins G_i are independent, with Cov G_i = Cov Y_i = L_iL_iᵀ.
- The reservoir is the twins of e(k+1..n), so r = j = n−k, and ReservoirCond gives v_j ≥ cj/n.
- Y_k and G_k are independent of U_k with equal first two moments. So for any C³ test F with bounded
  derivatives, the zeroth, first and second Taylor orders cancel exactly.

**(a)** F = φ ⋆ N(0, Cov R), with v ≥ cj/n.
- The three derivatives fall on the Gaussian (Hermite degree 3, direction trick u = Lᵀ(LLᵀ)⁻¹h).
- So ‖D³F‖ ≤ C_S v^{-3/2}·sup|φ|.
- With E|G_k|³ ≤ C_S‖L_k‖³ ≲ b³, the cost per step is ≲ b³(n/j)^{3/2} = j^{-3/2}. ✓

**(c)** F = φ with no smoothing: ‖D³φ‖ ≤ C ε^{-3}. Cost per step b³ε^{-3}. ✓

**The tail (reservoir → 0).**
- (a) alone gives Σ_j j^{-3/2} = O(1), which is useless. The last j < j* = nε² swaps use (c) instead.
- Pass 1 sum:
  - j < nε²: nε²·n^{-3/2}ε^{-3} = n^{-1/2}ε^{-1};
  - j ≥ nε²: Σ j^{-3/2} ≤ 2(nε²)^{-1/2} = 2n^{-1/2}ε^{-1};
  - total 3n^{-1/2}/ε. ✓
- So the shrinking reservoir is handled correctly, and it is exactly what drives the rate. 1a CONFIRMED.

**(b)** Split each twin as G_i = 2^{-1/2}(L_iw_i + L_iw′_i), with w and w′ independent. This is what the scales
a_i = ½ mean; it is better than splitting the index set.
- R₁ = Σ 2^{-1/2}L_iw_i is the smoothing half, with Cov R₁ = v/2 ≥ cj/(2n).
- R₂ stays in U′.
- F(x) = Eφ(x + Mz), with MMᵀ = Cov R₁:
  - D_hF = E[Dφ(x+Mz)h];
  - D²_hF = E[Dφ(x+Mz)h·⟨z,u⟩];
  - D³_hF = E[Dφ(x+Mz)h·(⟨z,u⟩² − ‖u‖²)], with ‖u‖² ≤ C_S‖h‖²/v.
- Dφ ≤ Cε^{-1}, and Dφ is supported in the ε-shell. Hence |D³F(x)[h³]| ≤ Cε^{-1}v^{-1}‖h‖³·E[1{x+Mz ∈ shell}(1+‖z‖²)]. ✓

**1b. Factoring the remainder: the gap.** The plan writes the remainder as E‖Y‖³·(shell factor). The Lagrange form
has the intermediate point t*(ω), which depends on (U, Y), so E[‖Y‖³ sup_t 1{U+tY ∈ shell}] does not factor. The
plan's "U ∈ K^{ε+b}∖K_{−b}" enlargement repairs this for the bounded Y_k, but **not for the Gaussian twin G_k,
which is unbounded**. The plan's (b)/(c) apply to both sides of the swap.

**Fix F2** (choose one):
- **(i, recommended)** Use the integral form along the segment, g(t) = F(U+tY):
  g(1) = g(0) + g′(0) + ½g″(0) + ∫₀¹ ½(1−t)²g‴(t)dt.
  - For fixed t, condition on (Y, z). Then U′ is independent of them, and E_{U′}1{U′ + tY + Mz ∈ A∖B} ≤ s̄ :=
    sup_w P(U′ + w ∈ A∖B), where A = closure(K^ε) and B = int K for the upper sandwich.
  - The same works for (c) with U and φ.
  - This needs no b-enlargement, treats G_k and Y_k identically, and removes the "segment-local Taylor" lemma
    (+150 lines) from M5's risk list.
  - The integral-form remainder is about 100–200 Lean lines via FTC (`intervalIntegral.integral_eq_sub_of_hasDerivAt`)
    applied three times.
- **(ii)** Keep Lagrange with the enlarged shell for Y_k. For G_k, condition on g = ‖G_k‖ and use
  P(U ∈ K^{ε+g}∖K_{−g}) ≤ C(ε+2g)/√λ + 2β(U). This is linear in g, so the extra factor is E‖G‖³(ε+‖G‖) ≲ b³(ε+b).

**Shell probability.** s̄ ≤ N_{U′}(A∖B) + 2β(U′). This holds because B ⊆ A are both convex: P(A) − P(B) ≤ [N(A)+β] −
[N(B)−β].
- A∖B ⊆ cthick_ε K ∩ cthick_ε(int K)ᶜ, so G1 for N(0, Cov U′) with Cov U′ ≥ λ/4 gives s̄ ≤ Cε/√λ + 2β(U′).
- Lower sandwich: K∖int K_{−ε} also lies in the ε-shell. A point of K_{−ε}∖int K_{−ε} is a limit of points within ε
  of Kᶜ, so it is within ε (closed) of (int K)ᶜ. ✓
- The Hermite weight is harmless: E_z[(1+‖z‖²)·P_{U′}(…)] ≤ (1+S′)s̄, by independence of U′ from (z, Y). ✓

**1c. Hybrid-class closure: the gap and the fix.**
- §4.M5 defines the class by an arbitrary J, scales a_i ∈ {0,½,1} and Cov ≥ λ/4. It then asserts
  "β₀ ≤ Cn^{-1/4} uniformly over the hybrid class".
- Pass 1 for a hybrid H runs an inner swap over J and **needs its own reservoir condition** (inner v_j ≳ j/n).
  Cov H ≥ λ/4 does not supply it.
  - Example: S = 2 and J ordered so that its last ≍ √n indices carry covariance only along e₁.
  - Take the fixed Gaussian part ≍ λ e₂e₂ᵀ. Then the inner reservoir is degenerate along e₂ for the last swaps.
  - Pass 1 then loses its gain: (c)-only on n^{1/2}·(…) steps yields n^{-1/8}-type rates.
- So the uniform claim is unproved for the class as written.

**Fix F1.** Restrict the class to the hybrids that pass 2 actually uses, for a fixed order e and step k:
- U_k^{(1)} = Σ_{m<k}Y_{e(m)} + Σ_{m>k}G_{e(m)}, used in (c);
- U_k^{(½)} = Σ_{m<k}Y_{e(m)} + Σ_{m>k}2^{-1/2}L_{e(m)}w′_{e(m)}, which is U′ in (b);
- the full sum X.

Pass 1 for U_k^{(a)} uses the inner order e restricted to e(1..k−1). At inner step r the reservoir is the full-scale
twins of e(k−r..k−1) plus the fixed a-scaled twins of e(k+1..n). That is ≥ ½·Σ over the suffix e(k−r..n) minus
index k. By ReservoirCond it is ≥ (c/2)(n−k+r+1)/n − C_S b² ≥ (c/4)r/n for r ≥ r₀′.
- Pass 1 needs no β of sub-hybrids, so the recursion has **depth one**. The class is closed in the only sense
  needed.
- Also Cov U_k^{(½)} = Σ − ½·Cov(reservoir) − L_kL_kᵀ ≥ λ/2 − C_S b² ≥ λ/4 for n ≥ n₀. Small n is absorbed
  (β ≤ 1 ≤ K n^{-1/3} for n ≤ n₀).
- Lean consequence: define the class as an explicit function of (e, k, a ∈ {½,1}), not as a predicate over
  arbitrary (J, a). This also simplifies the measure bookkeeping, which was the plan's "high-medium" risk.

**1d. Convexity.** The following sets are all convex:
- translates K − w;
- thickening and cthickening (sup norm);
- interior and closure;
- K_{−ε} = {x | closedBall x ε ⊆ K};
- C^δ and C_{−δ}.

The shells are differences A∖B with B ⊆ A convex. CONFIRMED.

**F3 (measurability).** Inside M5, take β as a sup over **Borel** convex sets. All the sets above can be chosen open
or closed. Pass to arbitrary convex C only at the end:
- the pexp side is a finite sum;
- P(X ∈ int C) ≤ P(X ∈ C) ≤ P(X ∈ closure C);
- the Gaussian frontier is null by M1.

This avoids outer-measure reasoning for the hybrid measure pexp ⊗ Gaussian, which is not finite-support.

**1e. Constants.**
- G1 gives 4S²·‖L⁻¹‖_{∞→∞}·r/√(2π).
- The Hermite constants are polynomial in S; the sup-norm to Euclidean conversions cost √S.
- Everything is instance-level, consistent with plan §7.3.

## 2. Bootstrap arithmetic

**Pass 1.** β ≤ Cε + 3Cn^{-1/2}/ε, so ε = n^{-1/4} gives β₀ ≲ n^{-1/4}. ✓

**Pass 2.** The per-step bounds are:
- (a) j^{-3/2};
- (b) n^{-1/2}(s/ε)/j, using n^{-3/2}ε^{-1}(n/j)s;
- (c) n^{-3/2}ε^{-3}s;

with s = C(ε+b) + 2β₀ ≤ 1.

Comparisons:
- (b) ≤ (c) iff j ≥ nε² = j₂;
- (a) ≤ (b) iff j ≥ nε²/s² = j₁ ≥ j₂.

So (c) on j < j₂, (b) on [j₂, j₁], (a) on j > j₁. The sums are n^{-1/2}s/ε, 2n^{-1/2}(s/ε)log(1/s) and
2n^{-1/2}s/ε. The plan's label "j₁ = nε²/s², j₂ = nε²" is consistent; note that the (b)-window is [j₂, j₁].

Total: n^{-1/2}(s/ε)(1+log(1/s)) ✓, and s ≥ b gives log(1/s) ≤ ½ log n.

Then ε = n^{-3/8}:
- n^{-1/2}·β₀/ε = n^{-1/2+1/8} = n^{-3/8};
- n^{-1/2}·(1 + b/ε) ≤ 2n^{-1/2};
- so β ≲ n^{-3/8} log n ≤ C n^{-1/3}. ✓

**Recursion.** In general β′ ≈ ε + n^{-1/2}(β/ε)log n, so ε* = (n^{-1/2}β log n)^{1/2}. The exponents are 1/4 →
3/8 → 7/16 → … → 1/2, with fixed point n^{-1/2} log n. The plan's pass 3 = n^{-7/16} is correct, and two passes
are the minimum to beat 1/3. CONFIRMED.

## 3. TD instantiation (M6.1, M6.2)

**The reservoir.**
- `sum_linWeightGap_le` bounds Σ_k e_k ≤ C·T^{2/3}, where e_k is the contrDrift + contrProd/a coefficient.
  `norm_linWeight_sub_inv_mulVec_le` says ‖(β_k − A⁻¹)v‖_∞ ≤ e_k‖v‖_∞.
- Markov: #{e_k > θ} ≤ C T^{2/3}/θ ≤ T/2 for T ≥ T₀.
- Good k: write E_k = β_k − A⁻¹, so ‖E_k‖_{∞→∞} ≤ θ and ‖E_kᵀ‖_{2→2} ≤ √(‖E_k‖_{1}‖E_k‖_{∞}) ≤ √S·θ.
  - Then ‖β_kᵀu‖₂ ≥ ‖A^{-ᵀ}u‖₂ − √Sθ‖u‖₂ ≥ ‖u‖₂/(2‖A‖₂) once θ ≤ 1/(2√S‖A‖₂).
  - Hence uᵀ(T^{-1}β_k diag(Γ) β_kᵀ)u ≥ (minΓ/(4‖A‖₂²T))‖u‖₂².
- **F7:** the plan's θ = 1/(2‖A‖S) is fine if ‖A‖ means ‖A‖_{∞→∞}, because ‖A‖₂ ≤ √S‖A‖_∞. State which norm.
- Order: bad indices first, good last.
  - For r ≤ n − |B| the last r are good, giving ≥ c r/T.
  - For r > n − |B| the reservoir is ≥ c(n−|B|)/T ≥ (c/2) ≥ (c/2)r/n.
  - So ReservoirCond holds with r₀ = 1 and constant c/2. CONFIRMED.
- Bad indices are swapped while the reservoir is ≥ c/2. Under (a) they cost ≲ |B|·T^{-3/2} = o(T^{-1/3}).

**Summands (M6.2).** These are given by the existing exports:
- the summands are independent with finite sample type `Tuple`;
- mean 0 and covariance T^{-1}β_k diag(Γ_true)β_kᵀ;
- ‖·‖ ≤ K_β B T^{-1/2}.

**Target (M6.3).** The Lindeberg endpoint is N(0, Λ_T). M4 against N(0, Λ) costs ≲ ‖Λ_T − Λ‖/λ ≲ T^{-1/3}.
- I re-derived the M4 interpolation. d/dt E h(Z_t) = ½E[D²h(Z_t)](Σ₁−Σ₂), and both derivatives can be put on the
  Gaussian Z_t through the Hermite identity. So the bound is C_S‖Σ₁−Σ₂‖/λ_min(Σ_t) for any bounded h, with no ε.
  CONFIRMED.
- Λ_T ≥ λ/2 for T ≥ T₀ follows from `abs_linCov_sub_le`.

## 4. Chebyshev step (M7)

X = X^lin + E_T, and B4 gives ‖E_T(s)‖_{L²} ≤ K_E T^{-1/3}, including the deterministic transient. So
P(‖E_T‖_∞ > δ) ≤ S K_E² T^{-2/3}/δ².

- **Upper:** P(X∈C) ≤ P(X^lin ∈ C^δ) + P(‖E‖>δ) ≤ N(C) + cδ + β_lin + S K_E²T^{-2/3}/δ².
- **Lower:** use C_{−δ}. Then C∖C_{−δ} lies in the δ-shell, by the same argument as in §1b.
- **Balance:** δ = T^{-2/3}/δ² gives δ = T^{-2/9}. CONFIRMED.

**F5 (important simplification).** Here β_lin only has to be ≤ T^{-2/9}. Pass 1 gives T^{-1/4} ≤ T^{-2/9}. So the
**all-convex T^{-2/9} result for the full statistic needs only pass 1**. That removes from its critical path:
- the hybrid class and the bootstrap;
- bound (b) and the M3 "mixed" lemma;
- the M2 derivative-support clause.

Pass 2 is needed only for the uncounted linear-part statement at T^{-1/3} and for any T^{-1/3}·polylog result.

## 5. Smoothing caps (§2 of the plan)

All rows re-derived:

| Error terms | Optimum | Rate |
| --- | --- | --- |
| ε + T^{-1/6}/ε (+ T^{-1/2}/ε³ = T^{-1/4}) | ε = T^{-1/12} | T^{-1/12} |
| δ + T^{-1/3}/δ², with ε + T^{-1/2}/ε³ | δ = T^{-1/9}, ε = T^{-1/8} | T^{-1/9} |
| ε + T^{-1/3}/ε² | ε = T^{-1/9} | T^{-1/9} |
| ε + T^{-1/2}/ε³ | ε = T^{-1/8} | T^{-1/8} |

The "T^{-1/18}" contradiction is right: T^{-1/2}ε^{-3} ≤ T^{-1/3} requires ε ≥ T^{-1/18}.

These are correct statements about the cost template "global ‖D³‖ ≲ ε^{-3} times a T^{-1/2} Lyapunov sum". They
are not impossibility theorems. Wording fix: "capped at T^{-1/8} *within this template*".

## 6. Phase 2

**6a. Doob decomposition** (re-derived).
- E[Δ_t | F_{t−1}] = (I−η_tA)Δ_{t−1}, because tuple t is independent of F_{t−1}, E A_t = A and E ξe = 0.
- So E[Δ_t|F_k] = G_{k,t}Δ_k, and M_k = Σ_{t<k}Δ_t + Σ_{t≥k}G_{k,t}Δ_k.
- d_k = M_k − M_{k−1} = Σ_{t≥k}G_{k,t}(Δ_k − (I−η_kA)Δ_{k−1}) = −β_k[ξ_ke_{s_k} + (A_k−A)Δ_{k−1}].
- M_0 is deterministic.

So the linear part plus `linMartTerm` (= Σ_u linWeight·prMartingaleTerm) is the Doob decomposition, up to the
repo's sign and step-index conventions (η′_k = stepSize(k+1)). The builder must check these in Lean. CONFIRMED on
paper.

**6b. The log source** (M8a plausibility).
- The second-order term ½E[D²F(S_{k−1})(V_k − C_k)] has E‖V_k−C_k‖ ≍ T^{-1}√η_k·‖β_k‖².
- Weighted by min(v^{-1}, ε^{-2}), it gives Σ_j √η·min(1/j, ε^{-2}/T) ≈ T^{-1/3}(1 + log(1/ε²)).
- Near the end, both V − C and v scale like β_{k,T}², so the ratio is again √η/j.
- So T^{-1/3} log T from this term is **plausible**.

Additional obstacles M8a would face, which the plan does not list:
- d_k depends on S_{k−1}, so F2(i) fails. It needs the b-enlarged shell together with the pathwise bound.
- It needs its own martingale hybrid class with a pass 1.
- Bolthausen-type martingale lower bounds (n^{-1/4}) show that the conditional-variance term is where generic
  martingale BE fails. Here it is saved only by V_k − C_k being spread evenly.

**F6 (much shorter route to the same T^{-1/3}·log T, replacing M8a).** Do not run a martingale Lindeberg. Instead,
combine pass 2 for X^lin with an exponential tail for E_T, using bounded-increment Azuma twice:

1. **Δ_k with high probability.** By variation of constants,
   Δ_k = G_{0,k}Δ_0 − Σ_{j≤k}η_jG_{j+1,k}[ξ_je_{s_j} + (A_j−A)Δ_{j−1}].
   - This is a deterministic transient plus a martingale with deterministic weights.
   - Its increments are bounded pathwise by Cη_j·Π_{i∈(j,k]}(1−aη_i), using `tdPathBound` and B1.
   - Azuma per coordinate gives P(|Δ_k(s)| > C√(η_k log T)) ≤ T^{-3}. The variance proxy is Ση_j²Π² ≲ η_k, a
     squared version of `mul_contrSum_le_of_ge`.
   - The transient Π(1−aη) ≈ exp(−c k^{1/3}) is summable.
2. **E_T with high probability.** E_T = deterministic O(T^{-1/2}) + T^{-1/2}Σ_kW_k(A_k−A)Δ_{k−1}.
   - Truncate the increments by 1{|Δ_{k−1}| ≤ C√(η_k log T) + transient}. The indicator is F_{k−1}-measurable,
     so the truncated sequence is still a martingale difference.
   - Azuma with Σc_k² ≲ T^{-1}Σ_kη_k log T ≲ T^{-2/3} log T gives P(‖E_T‖_∞ > C T^{-1/3} log T) ≤ C/T.
3. **Assembly** as in §4: β_lin (T^{-3/8} log T) + cδ + C/T ≲ T^{-1/3} log T.
   - With Freedman and a high-probability bound Σ|Δ_k|² ≲ T^{1/3}, this improves to T^{-1/3}√(log T).

The repo already has Azuma, Freedman and bounded-increment tails (`AzumaStrictTwoSided`, `AzumaSumMGF`,
`BoundedIncrementFixedTimeTail`, `FreedmanExactAssembly`). They are stated for `Measure Ω` with filtrations. The
work is a bridge to `pathWeight`, either through `PMF.toMeasure` or a finite-sum MGF induction like
`sum_pathWeight_mul_sum_mul_sum`.

Estimate: 1000–2000 lines and 20–35 h, against M8a's 2500–4000 lines and 40–70 h at medium-high risk. This also
corrects §2's row "L^{2q} moments of E_T (not available)": they are available from (1)–(2).

**6c. Exact T^{-1/3}.** Any tail-plus-sandwich route pays δ with P(‖E_T‖>δ) ≤ T^{-1/3}, which forces
δ ≳ T^{-1/3}√(log T). So removing the log does need decoupling at the shell level. I agree it is research. The
Shao–Zhang route (ii) is the standard one for nonlinear statistics, and I expect that the source relies on a
result of this kind.

## 7. Known results and whether a simpler route exists

Known results, from memory, not re-verified:
- **Bentkus (2003, JSPI; 2005, Theory Probab. Appl.)** gets n^{-1/2} with d^{1/4} for convex sets, i.i.d. and
  non-identical (Lyapunov ratio). The method is Lindeberg-type composition plus Gaussian smoothing plus
  **induction on n**, in which the recursion inequality is closed at the fixed point.
- **Raič (2019, Bernoulli)** is the same scheme with explicit constants.
- **Fang–Röllin (2015, Bernoulli)** uses Stein's method plus smoothing plus a similar recursion, at n^{-1/2} with
  polynomial dimension dependence.
- **Zhilova** (non-classical BE, higher-moment matching) gets better-than-n^{-1/2} rates for smooth classes; it is
  not needed here.

Assessment:
- The plan's construction is a **two-step truncation of the Bentkus recursion**. Pass 1 is the classical
  "Lindeberg with the Gaussian part as smoother" bound, which is folklore. Pass 2 is one iteration of the recursion
  with the shell factor.
- For the n^{-1/3} target, the truncation is **shorter** than a full Bentkus induction. The full induction needs:
  - strong induction over sample size, or over index subsets in the non-identical case;
  - closing a constant fixed point K ≥ C(1 + K/K′)…;
  - Bentkus's log-free refinement to reach n^{-1/2}.

  None of these is needed at n^{-1/3}.
- Stein in ℝ^S needs Ornstein–Uhlenbeck semigroup solution bounds on top of M3. That is longer.
- **Recommendation:** keep the plan's route, with F1/F2, and stop at pass 2.

## 8. Required fixes (summary)

- **F1.** Replace the abstract hybrid class with the concrete family U_k^{(a)}, a ∈ {½, 1}, built from (e, k).
  Prove pass 1 for it from ReservoirCond via the suffix argument in §1c, at depth one. Drop "uniform over arbitrary
  (J, a)".
- **F2.** Use integral-form third-order Taylor along the segment, and condition on (Y, z) before taking the shell
  probability. This removes the b-enlargement and covers the unbounded twin G_k. Alternatively use (ii) of §1b.
- **F3.** In M5, take the sup in β over Borel convex sets (open or closed suffice). Extend to arbitrary convex C
  only in the final export, using the interior/closure sandwich and the M1 frontier-null result.
- **F4.** Record the n ≥ n₀ conditions (Cov U ≥ λ/4; the inner reservoir loses L_kL_kᵀ ≲ b²) and absorb small n
  into the constant.
- **F5.** Re-order Phase 1 so that **T^{-2/9} needs only pass 1** (see §9).
- **F6.** Replace M8a with the Azuma-tail route (§6b). Keep the martingale Lindeberg only as background for M8b, if
  ever.
- **F7.** M6.1: state the norms (‖·‖_{∞→∞} from `norm_linWeight_sub_inv_mulVec_le`) and θ ≤ 1/(2√S‖A‖₂). Wording
  in plan §2: "capped within this template".

## 9. Recommended milestone order

1. **M1, G1 shell** (generic, Probability).
2. **M2 without the support clause**, and **M3 with the pure Gaussian D^k bounds (k ≤ 3) only**. Run these in
   parallel with M1.
3. **M4**, the Gaussian law identity and the convex comparison. It uses the M3 k = 2 bound.
4. **M5a, pass 1** (n^{-1/4}). The swap uses bounds (a) and (c) only, with no hybrid class.
5. **M6** (reservoir counting, summands, target), then **M7 at T^{-2/9}**. This is the first all-convex,
   true-Γ result for the full statistic. It is uncounted (partial in COVERAGE).
   - **M7₀ (T^{-1/9}) becomes optional.** It saves little once M5a exists, because M5a needs only (a)+(c).
6. **M2 support clause, M3 mixed bound, M5b pass 2** (concrete class F1, integral Taylor F2). This gives the linear
   part at T^{-1/3}.
7. **M8a′, the Azuma tail** (F6), giving the full statistic at T^{-1/3} log T. A second P0 is needed only for the
   truncation bookkeeping.
8. **M8b** (research, separate gate). It is the only step that would give a counted `Thm7_11_restricted_instConst`.

## 10. Honest estimate

My estimates differ from the plan's §5 as follows:

| Work | Lines | Agent-hours |
| --- | --- | --- |
| M1 | 700–1200 | 12–20 |
| M2 without support | 800–1300 | — |
| M3 pure only | 500–900 | — |
| M4 | 600–1100 | — |
| M5a | 1200–2000 | 20–35 |
| M6 + M7 | 900–1500 | — |
| **Subtotal to T^{-2/9}** | **4700–8000** | **90–150** |
| M5b (with M2 support and M3 mixed) | +1500–2500 | +30–50 |
| M8a′ | +1000–2000 | +20–35 |

Notes:
- The plan's 35–60 h for M5 is optimistic. The pexp ⊗ Gaussian measure layer alone is likely 500+ lines; I'd budget
  ×1.3–1.5.
- M8b remains research with unbounded risk.
- **No milestone here yields a counted Statements entry.** The counted target needs M8b. AGENTS.md is respected by
  the plan's §6 table: no `_restricted` entries for weaker rates.
