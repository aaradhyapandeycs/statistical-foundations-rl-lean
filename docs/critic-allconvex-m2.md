# Critic report: M2 (smooth sandwich, no support clause), all-convex Theorem 7.11 route

Public copy, scrubbed (local paths removed). Route infrastructure for Theorem 7.11, not a source result: no
COVERAGE row or statement entry. After this review the module was moved into the
`StatisticalRL.Analysis.ConvexSmoothIndicator` namespace (so the axiom audit covers it), imported from
`Formalization.lean` (N4), and note N1/N3 was addressed by an addendum (`convex_setOf_closedBall_subset`,
`isClosed_setOf_closedBall_subset`, `measurableSet_setOf_closedBall_subset`, `measurable_of_contDiff_top`,
`measurable_smoothIndicator`); the two shell inclusions of (1) are in
`Formalization/Probability/ConvexSandwichShell.lean`. The sha256 and line count below refer to the reviewed
version.

Reviewed: `Formalization/Analysis/ConvexSmoothIndicator.lean`, sha256
`6ebe2c40029bf00eee141f5320418b8923214acf9be488bdaeecea804c1e787a`, 379 lines (matches the builder's status report).
Brief: milestone M2 of the all-convex route plan (not published) as amended by [critic-allconvex-p0.md](critic-allconvex-p0.md) (F2, F3, F5).

## Verdict: ACCEPT

No required fixes. Optional notes for M5 below.

## Evidence (commands run by the critic)

- Fresh compile of a byte copy of the source:
  `bash scripts/lean-local.sh` on a local scratch copy -> no errors, no warnings (24 s).
- A local probe (not published; imports `Formalization` and the module; module olean
  newer than source): compiles, so no name collisions with the current library. `#print axioms` for
  `exists_smooth_sandwich_upper/lower`, `sandwichConst_zero`, `norm_iteratedFDeriv_smoothIndicator_le`,
  `iteratedFDeriv_lsmul_convolution`, `contDiff_smoothIndicator`, `smoothIndicator_mem_Icc`:
  only `propext, Classical.choice, Quot.sound`.
- grep: no `sorry`, `admit`, `axiom`, `set_option`, `native_decide`, `implemented_by` in the module.
- Only one Lean process run at a time (pgrep count was 0 before each run). No repo edits outside
  the critic's scratch directory and this report; no git changes.

## (1) Fit for M5 pass 1

Exports (as elaborated):
- upper: any `K`, `0 < ε` -> exists `φ`, `ContDiff ℝ ⊤ φ`, values in `[0,1]`, `φ = 1` on `K`, `φ = 0` off
  `thickening ε K`, `‖D^k φ x‖ ≤ sandwichConst ι k / ε^k` for all `k : ℕ`, all `x`.
- lower: same, with `φ x = 1` whenever `closedBall x ε ⊆ K`, `φ = 0` off `K`.

This is what the reservoir swap (pass 1, bounds (a)+(c), integral-form Taylor F2) consumes: C^∞ (so C^3 for
the FTC-based Taylor), sup bounds on D^1..D^3 of the form c_k ε^{-k} with c_k independent of K and ε.
Borel measurability of the witnesses follows from continuity (`h.continuous.measurable`); not stated
separately, not needed.

Shell compatibility with M1 (`cthickening r K ∩ cthickening r (interior K)ᶜ`, default sup metric on both
sides): verified in the probe, for every set K:
- `thickening ε K \ K ⊆ cthickening ε K ∩ cthickening ε (interior K)ᶜ` (upper excess region);
- `K \ {x | closedBall x ε ⊆ K} ⊆ cthickening ε K ∩ cthickening ε (interior K)ᶜ` (lower deficit region).
So `φ_hi − φ_lo` (upper at K, lower at K) is supported in `thickening ε K \ {x | closedBall x ε ⊆ K}`, which
is inside the M1 shell of width ε. Norms agree (sup norm on `ι → ℝ` throughout; M1 also uses the default metric).

## (2) Re-derivation of the convolution argument

- φ = 1_A ⋆ ρ_δ with ρ_δ(x) = δ^{-d} ρ₁(x/δ), ρ₁ = normed `ContDiffBump` (rIn 1/2, rOut 1), support = open
  unit ball, ∫ρ₁ = 1 (`integral_normed`); ∫ρ_δ = 1 via `integral_comp_inv_smul_of_nonneg` (factor δ^d). Correct.
- Derivatives pass onto the kernel: `iteratedFDeriv_lsmul_convolution` by induction using
  `HasCompactSupport.hasFDerivAt_convolution_right` with 1_A locally integrable (needs A measurable; the
  witnesses use an open set and the complement of an open set). Correct.
- Scaling: ‖D^kρ_δ(x)‖ ≤ δ^{-d} δ^{-k} ‖D^kρ₁(x/δ)‖ (composition with δ⁻¹·id, operator norm ≤ δ⁻¹),
  integrated -> δ^{-k} ∫‖D^kρ₁‖. With δ = ε/2: 2^k ε^{-k} ∫‖D^kρ₁‖ = sandwichConst ι k / ε^k. Correct.
- [0,1]: 0 ≤ 1_A ≤ 1, ρ_δ ≥ 0, ∫ρ_δ = 1. Correct.
- φ(x) = 1 needs x − t ∈ A for all ‖t‖ < δ (open ball, matching the open support of ρ₁); φ(x) = 0 when the
  open δ-ball misses A. Upper: A = thickening (ε/2) K, so x ∈ K gives the ball inside A; x ∉ thickening ε K
  gives the ball disjoint from A (triangle inequality, strict). Lower: A = (thickening (ε/2) Kᶜ)ᶜ; if
  closedBall x ε ⊆ K, every x − t (‖t‖<ε/2) is at distance ≥ ε/2 from Kᶜ; if x ∉ K, every x − t lies in
  thickening (ε/2) Kᶜ. Checked line by line.

## (3) Constants

`sandwichConst ι k = 2^k ∫ ‖iteratedFDeriv ℝ k ρ₁‖` depends only on ι, k (fixed bump). The integrand is
continuous with compact support (integrability proved), so the constant is genuine, not a junk value.
`sandwichConst_zero : sandwichConst ι 0 = 1` holds (= ∫ρ₁) and is proved. `sandwichConst_nonneg` proved.

## (4) Hidden hypotheses / non-vacuity

- Exports assume only `0 < ε` and `Fintype ι`; no convexity, measurability or nonemptiness of K required
  (stronger than the plan's convex statement). No support clause, as F5 allows.
- Non-vacuity example in the file: on `Fin 1 → ℝ`, the upper sandwich of `{0}` at scale 1 is 1 at 0 and 0 at
  the constant 2. Checked.
- Plan deviation: k ranges over all ℕ and φ is C^∞ rather than C^3 with k ≤ 3; this is strictly stronger.

## Notes for M5 (not required fixes for M2)

- N1. M5 needs the inner parallel set B = {x | closedBall x ε ⊆ K} convex and Borel (CHECK §1b: B ⊆ A both
  convex). Neither is in this module. The probe proves both in ~30 lines: convex if K convex; closed if K closed.
  (For K open it is also open since closedBall is compact; not proved.) Place these in M5 or a small M2 addendum.
- N2. Upper set A = thickening ε K is open (Borel) and convex for convex K (`Convex.thickening`).
- N3. Measurability of the witnesses: use `ContDiff.continuous.measurable`.
- N4. The module is not yet imported from `Formalization.lean`; the lead must add it (and to any gate import
  list) when integrating. It states no source result, so no `Statements/ChN` entry.
