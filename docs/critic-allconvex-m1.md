# Critic report: M1 (G1 Gaussian convex shell), all-convex Theorem 7.11 route

Public copy, scrubbed (local paths removed). Route infrastructure for Theorem 7.11, not a source result: no
COVERAGE row or statement entry. Fixes F1 (import in `Formalization.lean`), F2 (ownership row in
`docs/PROGRESS.md`) and F3 (`map_affine_measure_apply`, `map_affine_measureReal_apply`) were applied after this
review, as were R1 (helpers moved to the `GaussianConvexShell` sub-namespace) and R2
(`matrixMaxRowAbsSum_eq_linfty_opNorm`); line counts below refer to the reviewed version. The consumer
inclusions of (1) for the M2 sandwiches are now in `Formalization/Probability/ConvexSandwichShell.lean`.

Critic: independent (not the builder). Date: 2026-11-09.
Under review: `Formalization/Probability/GaussianConvexShell.lean` (621 lines, mtime Nov 9 12:57).
Brief: the M1 builder brief derived from [critic-allconvex-p0.md](critic-allconvex-p0.md) (not published); paper proof: [critic-thm7-11-corrected-plan-check.md](critic-thm7-11-corrected-plan-check.md) §2 (G1 Steps 1–5).

## Verdict: ACCEPT WITH FIXES

The mathematics is correct. The constant is not weakened. There are no hidden hypotheses and the file compiles cleanly
with the allowed axioms. The fixes are integration and bookkeeping (F1, F2) plus one consumer-convenience bridge (F3).
None of them changes a signature.

## Compile evidence (run by the critic)

- Probe (a local scratch file, not published). It contains `import Formalization`, then the module's own
  imports and the **full module body copied verbatim**. This compiles the current source rather than trusting the
  olean, and it tests for name collisions with everything in `Formalization`.
- Appended to the probe: `#print axioms` for all 9 exports, `#check`s, and an independent empty-interior sanity
  example.
- Command: `bash scripts/lean-local.sh` on the probe, run with `pgrep -x lean`
  showing 1 process.
- Result: 0 errors, 0 warnings, no name collisions.
- Axioms: `stdGaussianPi_convexShell_le`, `_ofReal`, `stdGaussianPi_frontier_convex_eq_zero`,
  `map_affine_convexShell_le`, `map_affine_frontier_convex_eq_zero`, `map_affine_real_convex_eq_interior/_closure`
  and `stdGaussianPi_real_convex_eq_interior/_closure` all depend only on `[propext, Classical.choice, Quot.sound]`.
- `grep sorry|admit|axiom` on the file: no hits. The only match for the pattern is the word "admits" in the module
  docstring.
- Every new name is unique repo-wide. `sum_mul_update_eq` is reused from `GaussianAntiConcentration`, not redefined.

## (1) Is the shell the right object for M5/M7?

Shell_r(K) := cthickening r K ∩ cthickening r (interior K)ᶜ, using the sup metric that `ι → ℝ` carries by default.

Inclusions that consumers need. Each was re-derived by the critic; the general form holds for every convex C and
ε ≥ 0.
- **C^ε \ C^{-ε} ⊆ Shell_ε(C).** C^ε is any of {dist(·,C) ≤ ε}, {dist(·,C) < ε} or cthickening. C^{-ε} is any
  inner parallel set with x ∉ C^{-ε} ⇒ there is y ∉ C with dist(x,y) ≤ ε; this covers {B̄(x,ε) ⊆ C},
  {B(x,ε) ⊆ C} and {infDist(x,Cᶜ) > ε}. Since y ∉ C implies y ∉ int C, x ∈ cthickening ε (int C)ᶜ.
- C \ C^{-ε}, C^ε \ C and cthickening ε C \ int C all lie in Shell_ε(C). The last one holds because
  x ∉ int C ⇒ x ∈ (int C)ᶜ.
- **Euclidean shells.** dist_∞ ≤ dist_2, so Euclidean ε-neighbourhoods lie inside sup-ε neighbourhoods, in both
  thickenings. Hence the Euclidean ε-shell ⊆ Shell_ε (sup) **with the same ε**, and the sup-norm bound applies
  unchanged. The converse direction would cost √S; do not use it.
  - Lean caveat: Euclidean consumers live on `EuclideanSpace ℝ ι` (a different type). They must transport through
    `WithLp.equiv` / `PiLp` and prove the inclusion. M1 does not provide this bridge, so M5/M7 own it if they need it
    (see the notes below).

## (2) Constant and norm

- **Pieces.** 2S pieces, indexed by `ι × Bool`, with card = 2S (`Fintype.card_prod`, `card_bool`).
- **Each piece.** `measure_pi_le_of_slice_le` bounds each piece by the `gaussianReal 0 1` mass of a 1-D section
  whose points are pairwise within 2Sr. `gaussianReal_le_of_abs_sub_le` gives ≤ 2Sr/√(2π), via Icc(inf, inf+2Sr)
  and `gaussianReal_Icc_le`.
- **Total.** 2S · 2Sr/√(2π) = 4S²r/√(2π), exactly as in the brief. The `.real` form uses `toReal_le_of_le_ofReal`
  with no loss.
- **Norm consistency.** The sup norm is used throughout:
  - `abs_sum_mul_le_sum_abs_mul_norm` is ‖u‖₁·‖w‖∞;
  - `matrixMaxRowAbsSum` is max_i Σ_j|A_ij|, the correct ℓ∞→ℓ∞ operator norm;
  - `norm_mulVec_le_matrixMaxRowAbsSum` is proved directly.
  - The affine bound 4S²·‖L⁻¹‖_{∞→∞}·r/√(2π) matches brief target 3.

## (3) Re-derivation of the proof

**Step 1 (`exists_functional_of_mem_convexShell`).**
- **int K ≠ ∅.**
  - Take y ∈ closure((int K)ᶜ) = (int K)ᶜ (closed), with dist(x,y) ≤ r.
  - `geometric_hahn_banach_open_point` gives f with f < f(y) on int K. f ≠ 0, shown by evaluating at a point of
    int K.
  - f ≤ f(y) on closure(int K) = closure K ⊇ K.
  - Coefficients c_j = f(e_j); c ≠ 0 by `linearMap_coeffs_ne_zero`.
  - ⟨c,z⟩ ≤ ⟨c,y⟩ ≤ ⟨c,x⟩ + ‖c‖₁ r. Correct.
- **int K = ∅.**
  - K ≠ ∅, because cthickening r ∅ = ∅.
  - The affine span is proper (`interior_nonempty_iff_affineSpan_eq_top`), so its direction is proper.
  - Some g ≠ 0 vanishes on the direction, so g is constant on K, hence on closure K. Take w ∈ closure K with
    dist(x,w) ≤ r.
  - g z = g w ≤ g x + ‖c‖₁ r. Correct.
  - The critic's probe also instantiates this case: a line in ℝ³, which has empty interior.
- **K = univ.** int K ≠ ∅, and y ∈ (int K)ᶜ = ∅ is impossible, so the case is closed automatically. **K = ∅** falls
  into the empty-interior branch and is closed by K.Nonempty. **S = 0** is consistent: c ≠ 0 is impossible, but the
  shell is also empty.

**Step 2.**
- Normalize by L = ‖c‖₁ > 0 and take i = argmax |c_i|. Then L ≤ S|c_i|, so S·σ·u_i ≥ 1 with σ = sign(c_i).
- r·‖c‖₁/L = r gives ⟨u,z⟩ ≤ ⟨u,x⟩ + r.
- Pieces need only ‖u‖₁ ≤ 1, which is weaker and therefore harmless.
- Correct.

**Step 3.**
- Let p = update x i y be in the piece with normal u, and q = update x i y' ∈ cthickening r K, with w ∈ closure K
  and dist(q,w) ≤ r.
- Then ⟨u,q⟩ ≤ ⟨u,w⟩ + ‖u‖₁r ≤ ⟨u,p⟩ + 2r, so u_i(y'−y) ≤ 2r.
- Hence σ(y'−y) ≤ S·σu_i·σ(y'−y) = S·u_i(y'−y) ≤ 2Sr. When σ(y'−y) ≤ 0 the bound is trivial.
- The symmetric call gives the other side, so |y'−y| ≤ 2Sr. This matches the paper. It uses only p's piece
  membership and q's thickening membership.

**Step 4.**
- Directions: {‖u‖₁ ≤ 1, S·σu_i ≥ 1} is closed and bounded, hence compact.
- F ⊆ ℝ^ι × dirs is an intersection of closed sets.
- `isClosedMap_fst_of_compactSpace` makes the projection closed, and intersecting with the closed cthickening keeps
  it closed. Correct.

**Step 5.** As in (2). Measurability comes from closedness.

**Affine transfer.**
- f(z) = c + Lz is a homeomorphism (`affineHomeomorph`).
- f⁻¹(cthickening r A) ⊆ cthickening(‖L⁻¹‖r)(f⁻¹A): pull back the nearest point through closure and use
  ‖L⁻¹v‖ ≤ ‖L⁻¹‖‖v‖.
- f⁻¹((int K)ᶜ) = (int f⁻¹K)ᶜ (`preimage_interior` of the homeomorphism).
- f⁻¹K is convex.
- The shell is closed, so `map_measureReal_apply` is legitimate.
- Correct.

## (4) Interior/closure for non-measurable convex K

- `measure_eq_interior_of_frontier_null` and `measure_closure_eq_interior_of_frontier_null` use only
  `measure_mono` and `measure_union_le`, with closure = int ∪ frontier. Both hold for arbitrary sets: a `Measure`
  evaluated on a non-measurable set is its (trimmed) outer measure, which is monotone and subadditive.
- The frontier is closed, so its nullity is a genuine measurable statement (`Measure.map_apply`).
- So `.real K = .real (int K) = .real (closure K)` is valid for every convex K. The docstring wording "(outer) mass"
  is accurate.
- Caveat for consumers: the statement is about `(μ.map f).real K`, **not** `μ.real (f ⁻¹' K)`. For the
  homeomorphism f the two agree for every set (`MeasurableEquiv.map_apply`), but M1 does not export that bridge.
  See F3.

## (5) Hidden hypotheses and non-vacuity

- **Hypotheses.** Only `Convex ℝ K`, `0 ≤ r` (needed: for r < 0, cthickening is the closure and the bound would
  turn negative) and `IsUnit L.det` (needed for L⁻¹).
- The typeclasses `[Fintype ι]` and `[DecidableEq ι]` are only needed for `L⁻¹`/`update`.
- No measurability assumption on K.
- **Non-vacuity examples.** The file's own: a half-plane in ℝ², and L = 1. The critic's: a codimension-2 line in ℝ³.
  The conclusions are nontrivial, because the bound 4S²r/√(2π) is < 1 for small r.

## Required fixes

- **F1 (integration, lead).** Add `import Formalization.Probability.GaussianConvexShell` to `Formalization.lean`, so
  the axiom audit and `scripts/check.py` cover it. Also add it to any gate list that enumerates modules, if
  applicable. It is currently not imported.
- **F2 (bookkeeping).** Record M1 ownership and status in `docs/PROGRESS.md`. The brief requires this, and there is
  currently no entry. Label it infrastructure, not a source result. The docstrings already do so.
- **F3 (consumer bridge, small).** Add `map_affine_measure_apply`: `(μ.map f) s = μ (f ⁻¹' s)` for **all** s, via
  `(affineHomeomorph L hL c).toMeasurableEquiv.map_apply`, or a `.real` version. Alternatively, M7 must prove it
  locally. Without it, a consumer that writes P(c + LZ ∈ K) as a preimage cannot use the interior/closure lemmas for
  non-measurable K.

## Recommendations (optional, non-blocking)

- **R1.** Generic names in `StatisticalRL.Probability` (`boolSign`, `measurable_affine`, `continuous_sum_mul`,
  `affineHomeomorph`, `convex_preimage_affine`) risk future collisions. Consider a `GaussianConvexShell`
  sub-namespace or `private` for the helpers. There are no collisions today.
- **R2.** A lemma `matrixMaxRowAbsSum A = ‖A‖` under `Matrix.linftyOpNormedRing` would let M6 reuse Mathlib's
  ‖·‖_∞ bounds. The docstring asserts the correspondence but does not prove it.
- **R3.** A `c = 0` / `L`-only corollary would spare consumers rewriting `fun z ↦ 0 + L *ᵥ z`.

## Notes for consumers

- **M5 (smoothing / d_cvx transfer).**
  - Use C^ε \ C^{-ε} ⊆ Shell_ε(C) (see (1)). The inclusion is not in the file, and it is a two-line proof per
    variant of C^{-ε}.
  - If the smoothing is Euclidean, the sup-norm bound applies with the same ε (Euclidean shell ⊆ sup shell). The
    type transport from `EuclideanSpace` is the consumer's.
  - Do not route sup → Euclidean, which loses √S.
- **M6 (gaussCov).**
  - Instantiate L = A⁻¹ diag(√Γ). The bound needs ‖L⁻¹‖_{∞→∞} = `matrixMaxRowAbsSum (diag(1/√Γ) A)`, which is
    ≤ 2/√(min Γ) by the plan's row-sum computation.
  - Keep gaussCov-specific corollaries in M6, as the brief requires. M1 correctly has none.
  - IsUnit det must be discharged there.
- **M7 (Chebyshev / assembly).**
  - The frontier-null and interior/closure equalities are stated for `μ.map f`. Bridge to preimage form via F3.
  - `lawProb` (finite sum) needs none of this.
  - The S² constant is per-instance: acceptable for instance constants, useless for a universal one. This is
    consistent with the plan.
