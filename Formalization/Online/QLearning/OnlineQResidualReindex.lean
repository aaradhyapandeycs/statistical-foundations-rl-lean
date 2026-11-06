import Mathlib

/-!
# Chronological reindexing of stage-weighted residuals

`∑_{h<H} c^h ∑_{k<K} r k h = ∑_{t<KH} c^{t mod H} r (t / H) (t mod H)` (episode-major order
`t = kH + h`), by induction on `K` with `range ((K+1)H) = range (KH) ⊔ (KH + range H)`.
No sign conditions on `c` or `r`.
-/

open scoped BigOperators

namespace StatisticalRL.OnlineQResidualReindexPrivate

theorem stageWeightedResidual_chronological (H K : ℕ) (hH : 0 < H)
    (c : ℝ) (r : ℕ → ℕ → ℝ) :
    (∑ h ∈ Finset.range H, c ^ h * ∑ k ∈ Finset.range K, r k h) =
      ∑ t ∈ Finset.range (K * H), c ^ (t % H) * r (t / H) (t % H) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [add_mul, one_mul, Finset.sum_range_add, ← ih]
    have hblock : ∀ x ∈ Finset.range H,
        c ^ ((K * H + x) % H) * r ((K * H + x) / H) ((K * H + x) % H) = c ^ x * r K x := by
      intro x hx
      have hx' : x < H := Finset.mem_range.mp hx
      have h1 : (K * H + x) % H = x := by
        rw [Nat.mul_add_mod']; exact Nat.mod_eq_of_lt hx'
      have h2 : (K * H + x) / H = K := by
        rw [Nat.mul_comm K H, Nat.mul_add_div hH, Nat.div_eq_of_lt hx', add_zero]
      rw [h1, h2]
    rw [Finset.sum_congr rfl hblock, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _
    rw [Finset.sum_range_succ, mul_add]
end StatisticalRL.OnlineQResidualReindexPrivate
