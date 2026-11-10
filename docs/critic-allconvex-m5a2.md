# CRITIC: M5a-2 (reservoir Lindeberg pass 1, multivariate convex Berry–Esseen at n^{-1/4})

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Infrastructure review for the all-convex Theorem 7.11 route, not a source result: no COVERAGE row, statement-index entry or named-result change follows from it. Reviewed: M5a-2 (reservoir Lindeberg pass 1), `Formalization/Probability/ConvexLindebergReservoirBase.lean`, `Formalization/Probability/ConvexLindebergReservoir.lean`. Planning notes cited below (route plan, M5a design and design check, M6a interface note) are local and not published; the route plan check is public as [critic-allconvex-p0.md](critic-allconvex-p0.md). Probes are local scratch files (`<local probe>`).

Integration (2026-11-09): I1 applied. `ReservoirCond` and `matrixMaxRowAbsSum_le_of_forall` are now declared only in `ConvexLindebergReservoirBase.lean`; `TDInferenceConvexReservoir711.lean` imports it, and all three modules are imported from `Formalization.lean`. N1 applied (Base header wording). The sha256 and line counts below refer to the reviewed version.

Date: 2026-11-09. Independent critic, not the builder. I edited nothing in the repository except this file and
`<local critic folder>`. No git commands.

Under review (sha256 matches builder status note):
- `Formalization/Probability/ConvexLindebergReservoirBase.lean` (738 lines), `21557f4b…0f0d`
- `Formalization/Probability/ConvexLindebergReservoir.lean` (324 lines), `cd84de63…28bc`

Spec: the M5a design (not published), as amended by the M5a design check (not published) (R1–R12) and [critic-allconvex-p0.md](critic-allconvex-p0.md) (F1–F5).

## Verdict: **ACCEPT** (one integration fix is required at landing: I1)

Both files compile from source in my own runs, the axiom closure is clean, and the main statement is the honest
one. The proof chain matches my independent reconstruction of pass 1.

There is no defect in either file. The one blocking item, **I1**, is for the lead's integration commit: a second
name collision with the M6a file that the builder's notes do not mention.

## Commands and evidence (all mine; one Lean process at a time, started only when `pgrep -x lean | wc -l` < 2)

| Command | Exit | Time | Output |
|---|---|---|---|
| `bash scripts/lean-local.sh Formalization/Probability/ConvexLindebergReservoirBase.lean` | 0 | 29 s | empty: no errors, no warnings (`<local log>`) |
| `bash scripts/lean-local.sh Formalization/Probability/ConvexLindebergReservoir.lean` | 0 | 25 s | empty (`<local log>`) |
| `bash scripts/lean-local.sh <local probe>` | 0 | 99 s | see below (`CriticProbe.log`) |
| `bash scripts/lean-local.sh <local probe>` | 1 | — | expected collision (I1) |

`CriticProbe.lean` imports `Formalization` plus both modules.
- `#print axioms` gives exactly `[propext, Classical.choice, Quot.sound]` for:
  - `abs_pexp_convex_sub_twinLaw_le_quarter`, `cvxDist_lawPexp_twinLaw_le_quarter`, `rad_convex_le_quarter`;
  - `abs_pexp_sub_twinLaw_le_smooth`, `abs_pexp_indicator_sub_le_of_smooth`, `twinLaw_convexShell_le`;
  - `abs_step_le_of_reservoir`, `abs_step_le_of_sandwich`, `hexp_eq_integral_block`, `abs_hexp_succ_sub_le`;
  - `reservoirCond_rad`, `le_cvxDist`.
- `example : ((⊤ : ℕ∞) : WithTop ℕ∞) = ∞ := rfl` and `≠ ω` (by `decide`) both pass.
- `#print` of `reservoirQuarterConst`, `twinLaw`, `twinMat`, `ReservoirCond`, `cvxDist`, `lawPexp` and `Stein.pexp`
  matches the reading below.

Grep over both files for `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by` and `extern`: no hits.

## (1) The theorem is the honest statement

`abs_pexp_convex_sub_twinLaw_le_quarter` takes `e : Fin n ≃ κ`, `0 < n`, `hp0`, `hp1`, `hmean`,
`hcov : E[Y_a Y_b] = (L Lᵀ)_ab`, `0 ≤ B`, `‖Y i x‖_∞ ≤ B/√n`, `0 < c`, `r₀ ≤ n`, `ReservoirCond e L c r₀`, and
`Convex ℝ K`. It concludes

`|pexp p (1_K(∑ Y)) − (twinLaw L).real K| ≤ reservoirQuarterConst ι c r₀ B · n^{-1/4}`.

- **The model is genuinely independent.** `Stein.pexp p F = ∑_ω (∏ p_i(ω_i)) F ω` is the product law of the
  coordinates.
- **The target is the right Gaussian.** `twinLaw L = (stdGaussianPi (κ×ι)).map (twinMat L univ *ᵥ ·)`, and
  `twinMat_mul_transpose` (re-checked in the probe) gives covariance `∑ L_i L_iᵀ`. By `hcov` and independence this
  is `Cov(∑ Y)`, so twinLaw is N(0, Cov ∑Y) with no change of target.
- **Constants depend on S = |ι|, c, r₀ and B only.** They are `4S²(S/√c)/√(2π) + A₃B³/6 · (c₃(2+r₀) + 4·8S³·(c√c)⁻¹)`:
  - `A₃ = lindebergMomentConst ι`;
  - `c₃ = sandwichConst ι 3`, an integral of the fixed mollifier on ι;
  - `gaussDerivConst 3` is numeric.

  There is no n, no κ (forced to |κ| = n by `e`) and no n₀: the bound holds at every n ≥ 1.
- **K is arbitrary.** There is no `MeasurableSet K` binder (the probe instantiates it for an arbitrary convex
  `K : Set (Fin 1 → ℝ)`). `(twinLaw L).real K` is the outer-measure value. Every step of L29 uses only
  `measureReal_mono` and `measureReal_union_le` (valid for arbitrary sets under a finite measure) and integrals
  against the open sets `thickening ε K` and `(cthickening ε (interior K)ᶜ)ᶜ`.
- **cvxDist (F3).** `cvxDist` takes the sup over Borel convex sets. `le_cvxDist` proves boundedness (≤ μ(univ) +
  ν(univ)) instead of relying on the junk value of `ciSup`. `lawPexp_real_eq` identifies the finite law on measurable
  K.
- **Remaining hypotheses are honest.** `r₀ ≤ n` is needed so that ReservoirCond at r = n gives Σ ⪰ cI. `0 < c` is
  needed for the shell bound. `DecidableEq ι` is a harmless instance.

## (2) Hybrid and swap bookkeeping (L7–L18, F1)

- **Swap sets.**
  - `gaussSet e k = e''{m ≥ k}`, `resSet e k = e''{m > k}`, `prefixSum = ∑_{m<k} Y_{e m}`.
  - `hybrid = prefix + twinMat(gaussSet) w`.
  - `hybrid_eq` / `hybrid_succ_eq` split off block `e k` correctly, via `gaussSet_eq_insert`, `not_mem_resSet` and
    `twinMat_insert_mulVec`.
- **Endpoints.**
  - `hexp_zero` is ∫φ d twinLaw, by `integral_map` with a continuous map.
  - `hexp_n` is pexp φ(∑Y), by `gaussSet_n = ∅`, `prefixSum_n` (`Equiv.sum_comp`) and the probability mass.
- **Data side.** `hexp_succ_eq` uses `pexp_comp_coord` with `prefixSum_update`: the prefix does not depend on
  coordinate e k, by injectivity of e.
- **Gaussian side.** `hexp_eq_integral_block` applies M5a-1's `integral_comp_blockOf_indep` (R5 signature, verified
  in GaussianBlock.lean:188):
  - G is bounded by 1 and continuous;
  - independence of block e k is shown by `twinMat_mulVec_congr` together with `e k ∉ resSet e k`.
- **Step reduction.** `abs_hexp_succ_sub_le` reduces the step to a pointwise-in-U bound through `pexp_sub`,
  `abs_pexp_le`, `pexp_mono` and `pexp_const`.
- **F1 respected.** Only the fixed-order prefix hybrids H_k occur. No convex distance of a hybrid is used, and the
  recursion depth is 0.

## (3) Per-step bounds

- **Reservoir step (`abs_step_le_of_reservoir`).**
  - The reservoir covariance is `twinMat(resSet)·ᵀ = ∑_{m>k} L L ᵀ ≥ c(n−1−k)/n · I`, by `reservoir_quadForm`.
    I re-checked the ReservoirCond filter `n − r ≤ m ↔ k < m` at r = n−1−k (omega). Its use requires
    r₀ ≤ n−1−k, which is implied by the telescope case `r₀ + ⌈√n⌉ ≤ n−1−k`.
  - The Euclidean bound is converted to sup form by `sq_norm_le_dotProduct_self`, as R2/L31b require.
  - M3's `norm_iteratedFDeriv_gaussSmooth_le` gives `‖D³‖ ≤ 8S³ (v√v)⁻¹`, using only ‖φ‖ ≤ 1, so it is independent
    of ε. It also gives `‖D¹‖ ≤ 2S/√v`. The rpow conversion is correct.
  - Then Taylor (L19 → LindebergFinite's `abs_sum_sub_integral_le_of_moments`) with the budget A₃b³.
  - `reservoir_step_const_eq` turns `(v√v)⁻¹ b³` into `(c√c)⁻¹ B³ (j√j)⁻¹`. ✓
- **Sandwich step (`abs_step_le_of_sandwich`).**
  - It undoes the smoothing: Fubini swap (`integral_integral_swap`), Σ moved inside ∫_w, then the pointwise swap at
    the base `U + R w` with M2 `c₃ ε^{-3}` (and `c₁ ε^{-1}` for the L₁ input).
  - Every integrability side goal is discharged from continuity and [0,1] bounds.
- **Third order.**
  - `norm_fderiv_fderiv_sub_le_of_iteratedFDeriv` turns ‖D³F‖ ≤ M into a Lipschitz bound on D²F (mean value on
    `univ`).
  - The moment budget `sum_cube_add_integral_cube_le` gives E‖Y‖³ ≤ b³ and
    E‖Lz‖³ ≤ (S√S b)³ · S·12e^{1/2}, via `matrixAbsSum_le_of_cov` (Cauchy–Schwarz on rows) and
    `integral_norm_pow_three_stdGaussianPi_le`.
  - So A₃ = 1 + (S√S)³·S·12e^{1/2}. This matches CHECK §1. ✓

## (4) Telescoping and smoothing

- **L26b `abs_pexp_sub_twinLaw_le_smooth`.**
  - `Finset.sum_range_sub` with hexp_n/hexp_zero, then `sum_range_le_quarter` (M5a-1, accepted).
  - Case a (j ≥ r₀ + ⌈√n⌉) is the reservoir bound. Case c is the sandwich bound with
    `c₃ (√√n)³/6 · A₃ (B/√n)³`.
  - The final form is `A₃B³/6 (c₃(2+r₀) + 4C_H(c√c)⁻¹)/√√n`, exactly the M5a-1 export.
- **L27–L29 `abs_pexp_indicator_sub_le_of_smooth`.**
  - Upper: 1_K ≤ φ⁺ ≤ 1_{thick}, and thick ⊆ K ∪ shell (`thickening_diff_subset_convexShell`).
  - Lower: φ⁻ = 1 on the open set M = (cthick (int K)ᶜ)ᶜ (closed ε-ball ⊆ K by `closedBall_subset_of_mem_inner`), and
    K ⊆ M ∪ shell.
  - Convexity enters only through `hsh`. ✓
- **L33 `twinLaw_convexShell_le`.**
  - T Tᵀ is PSD, so there is a square Q with QQᵀ = TTᵀ (`exists_mul_transpose_eq_of_posSemidef`).
  - M4.1 `map_mulVec_stdGaussianPi_eq` gives twinLaw = ν.map(Q·).
  - `total_quadForm` (r = n) gives Σ ⪰ cI, hence Q is surjective, hence `IsUnit Q.det`.
  - M1 `map_mulVec_convexShell_le` applies.
  - `matrixMaxRowAbsSum_inv_le_of_quadForm` uses the R6(ii) sign-vector route and gives `‖Q⁻¹‖_∞ ≤ S/√c`. The
    constant is consistently S/√c, not mixed with √(S/c). ✓
- **Main.** ε = (√√n)⁻¹ and `rpow_neg_quarter_eq` give `n^{-1/4} = (√√n)⁻¹`, and `ring` closes it.

## (5) ContDiff exponent

All smoothness hypotheses are `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)`. The probe confirms this is `∞` (`rfl`) and is not
`ω`, so R1 is satisfied. `.of_le (WithTop.coe_le_coe.2 le_top)` and `contDiff_infty.1 hφ 3` lower it to orders 3
and 2.

## (6) Hidden hypotheses and non-vacuity

- No hidden hypotheses (§1).
- `rad_convex_le_quarter` instantiates the main theorem at every n ≥ 1 with `κ = Fin n`, `ι = Fin 1`, `X = Bool`,
  `p = 1/2`, `Y = ±(√n)⁻¹`, `L = (√n)⁻¹ • 1`, `e = refl`, `c = 1`, `r₀ = 0`, `B = 1`.
- `reservoirCond_rad` proves ReservoirCond with equality (card of the last-r filter = r via `Nat.card_Ico`). This
  meets R10.

## Findings

- **I1 (BLOCKING for integration, not for these files).** `Formalization/Ch7Rest/TDInferenceConvexReservoir711.lean`
  defines two declarations that collide with Base, both in namespace `StatisticalRL.Probability`:
  - `ReservoirCond` (line 65). This one is already known (R8). The bodies are textually identical.
  - **`matrixMaxRowAbsSum_le_of_forall` (line 252).** This collision is new and absent from the builder's notes. The
    statement types coincide: `{A : Matrix ι ι ℝ} {c} (hc : 0 ≤ c) (h : ∀ i, ∑ j, |A i j| ≤ c)`, with no
    `DecidableEq ι` in either.

  `CollisionProbe.lean` (imports both files) fails with
  `environment already contains 'StatisticalRL.Probability.ReservoirCond'`. The second collision would surface next.

  **Fix:** in the integration commit, delete both declarations from the M6a file, add
  `import Formalization.Probability.ConvexLindebergReservoirBase` there, and keep every other M6a use unchanged (the
  names resolve to the Base copies). Then compile the M6a file and run `python3 scripts/check.py`. The M6a file is
  not currently imported by `Formalization.lean`.
- **N1 (nit, non-blocking).** The Base header says ReservoirCond is "the interface consumed by the TD reservoir
  construction". The TD construction *produces* it, and M5a consumes it. Suggested wording: "the interface supplied
  by the TD reservoir construction".
- **N2 (record only).** The constant grows linearly in r₀. Consumers must supply r₀ independent of n. M6a gives
  r₀ = 1, so this is fine.

R1–R12 status: all addressed.
- R1, R2, R3 (`hexp`), R4 (L26b), R5 (block lemma used), R6 (M4.1 used; S/√c), R9 (ℕ cast `n - 1 - k`) and R10 are
  done.
- R7 and R12 are text-only items in the design.
- R8 and R11 are integration and consumer notes; see I1 and below.

F1–F5:
- F1 ✓ (prefix hybrids only).
- F2 ✓ (deterministic Taylor with an unbounded Gaussian twin, no shell localisation).
- F3 ✓ (Borel sup for cvxDist; arbitrary K pointwise).
- F4 is vacuous in pass 1, since no n₀.
- F5 ✓ (n^{-1/4} ≤ n^{-2/9} is left to M7).

## Notes for M6.3 and M7

- **M6.3 (TD instance).** Supply `ReservoirCond e (linFactor …) c 1` with `c = γmin/(32 S)`.
  - `hc : 0 < c` needs **`0 < γmin`** (R11). `exists_linFactor_reservoirCond` only assumes `0 ≤ γmin`.
  - Also supply `r₀ = 1 ≤ n` (T ≥ 1).
  - The sup-norm bound must be `‖Y_i‖_∞ ≤ B/√T`, with B independent of T.
  - `hcov` must be stated with exactly the same square factor `L i` as ReservoirCond.
- **M7 (Chebyshev / final).**
  - The target here is `twinLaw L` = N(0, ∑ L_i L_iᵀ). To reach the book's Gaussian, use M4.1
    `map_mulVec_stdGaussianPi_eq` or a GaussianCovCompare step, plus a covariance-comparison error term if ∑ L_iL_iᵀ
    differs from the limiting Σ.
  - Use the pointwise theorem (all convex K) when the downstream sets are not known to be measurable. Use `cvxDist`
    only for Borel sets.
  - n^{-1/4} ≤ n^{-2/9} for n ≥ 1 (F5).
- **Statement index.** Infrastructure only. No `Statements/Ch7.lean` entry and no COVERAGE change is warranted by
  this milestone.
