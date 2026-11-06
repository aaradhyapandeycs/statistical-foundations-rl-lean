import Mathlib

/-!
# Signed stage recursion unroll (generic algebra)

If `d h ≤ c · d (h+1) + b h + r h` for all `h < H` with `c ≥ 0` and arbitrary signed `b, r`,
then `d 0 ≤ c^H · d H + ∑_{h<H} c^h (b h + r h)`. Induction on `H` (including `H = 0`), keeping the
exact geometric weight on every signed residual. Not the actual Q algorithm or a martingale bound.
-/

open scoped BigOperators

namespace StatisticalRL.OnlineQStageAlgebraPrivate

theorem signedStageRecursionUnroll (H : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (d b r : ℕ → ℝ)
    (hstep : ∀ h < H, d h ≤ c * d (h + 1) + b h + r h) :
    d 0 ≤ c ^ H * d H + ∑ h ∈ Finset.range H, c ^ h * (b h + r h) := by
  induction H with
  | zero => simp
  | succ H ih =>
    have ih' := ih (fun h hh => hstep h (Nat.lt_succ_of_lt hh))
    have hH := hstep H (Nat.lt_succ_self H)
    have hscaled := mul_le_mul_of_nonneg_left hH (pow_nonneg hc H)
    rw [Finset.sum_range_succ, pow_succ]
    nlinarith
end StatisticalRL.OnlineQStageAlgebraPrivate
