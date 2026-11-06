import Formalization.Online.QLearning.RateWeights

/-! Deterministic source bonus domination and residual bound; positive visit count and nonnegative source log are explicit. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem qLearning_bonus_weighted_bounds (H n : ℕ) (hH : 0 < H) (hn : 0 < n)
    (L cb : ℝ) (hL : 0 ≤ L) (hcb : 2 ≤ cb) :
    let A := (H:ℝ)^3*L
    2*Real.sqrt (A/(n:ℝ)) ≤
      ∑ i ∈ Finset.Icc 1 n, onlineQRateWeight H n i * (cb*Real.sqrt (A/(i:ℝ))) ∧
    2*(∑ i ∈ Finset.Icc 1 n, onlineQRateWeight H n i * (cb*Real.sqrt (A/(i:ℝ)))) ≤
      4*cb*Real.sqrt (A/(n:ℝ)) := by
  let A : ℝ := (H:ℝ)^3*L
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hn0
  have hcb0 : 0 ≤ cb := by linarith
  have hroot : 0 ≤ Real.sqrt A := Real.sqrt_nonneg _
  have hsum := onlineQRateWeight_sqrt_sum_bounds H n hH hn
  have heq : (∑ i ∈ Finset.Icc 1 n, onlineQRateWeight H n i * (cb*Real.sqrt (A/(i:ℝ)))) =
      cb*Real.sqrt A * (∑ i ∈ Finset.Icc 1 n, onlineQRateWeight H n i / Real.sqrt (i:ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Real.sqrt_div hA]
    ring
  have hlower := mul_le_mul_of_nonneg_left hsum.1 (mul_nonneg hcb0 hroot)
  have hupper := mul_le_mul_of_nonneg_left hsum.2 (mul_nonneg hcb0 hroot)
  change 2*Real.sqrt (A/(n:ℝ)) ≤
      (∑ i ∈ Finset.Icc 1 n, onlineQRateWeight H n i * (cb*Real.sqrt (A/(i:ℝ)))) ∧
    2*(∑ i ∈ Finset.Icc 1 n, onlineQRateWeight H n i * (cb*Real.sqrt (A/(i:ℝ)))) ≤
      4*cb*Real.sqrt (A/(n:ℝ))
  rw [heq]
  rw [Real.sqrt_div hA]
  have hmul : 2*Real.sqrt A ≤ cb*Real.sqrt A := mul_le_mul_of_nonneg_right hcb hroot
  have hdiv := div_le_div_of_nonneg_right hmul hs.le
  constructor
  · calc
      2*(Real.sqrt A / Real.sqrt (n:ℝ)) = (2*Real.sqrt A)/Real.sqrt (n:ℝ) := by ring
      _ ≤ (cb*Real.sqrt A)/Real.sqrt (n:ℝ) := hdiv
      _ = cb*Real.sqrt A*(1/Real.sqrt (n:ℝ)) := by ring
      _ ≤ _ := hlower
  · calc
      2*(cb*Real.sqrt A*(∑ i ∈ Finset.Icc 1 n, onlineQRateWeight H n i / Real.sqrt (i:ℝ))) ≤
          2*(cb*Real.sqrt A*(2/Real.sqrt (n:ℝ))) := mul_le_mul_of_nonneg_left hupper (by norm_num)
      _ = 4*cb*(Real.sqrt A / Real.sqrt (n:ℝ)) := by ring
end StatisticalRL.OnlineRL
