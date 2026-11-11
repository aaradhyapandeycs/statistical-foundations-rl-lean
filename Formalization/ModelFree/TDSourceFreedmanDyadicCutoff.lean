import Formalization.ModelFree.TDSourceFreedmanLogComparison

/-!

Derive the source dyadic cutoff `K=2⌈log₂ H⌉`, with `H=1/(1−γ)`. No sample-size or probability premise is used.
-/

namespace StatisticalRL.TemporalDifference

/-- The same source level also covers the squared horizon, as required by
the first-Freedman deterministic variance floor `σ_w²/2^K`. The factor two
in `K=2⌈log₂ H⌉` is used here: if `m=⌈log₂H⌉`, then `H≤2^m` and
`(2^m)^2=2^(2m)=2^K`. -/
theorem tdSourceFreedmanLevel_covers_effectiveHorizon_sq
    (γ : ℝ) (hγhalf : 1 / 2 ≤ γ) (hγ1 : γ < 1) :
    (1 / (1 - γ)) ^ 2 ≤ (2 : ℝ) ^ tdSourceFreedmanLevel γ := by
  have hgap : 0 < 1 - γ := by linarith
  have hHpos : 0 < 1 / (1 - γ) := by positivity
  have hHge2 : 2 ≤ 1 / (1 - γ) := by
    rw [le_div_iff₀ hgap]
    linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let m : ℕ := Nat.ceil
    (Real.log (1 / (1 - γ)) / Real.log 2)
  have hceil :
      Real.log (1 / (1 - γ)) / Real.log 2 ≤ (m : ℝ) := by
    exact Nat.le_ceil _
  have hlogH : Real.log (1 / (1 - γ)) ≤ Real.log ((2 : ℝ) ^ m) := by
    have hmul := mul_le_mul_of_nonneg_right hceil hlog2pos.le
    calc
      Real.log (1 / (1 - γ)) =
          (Real.log (1 / (1 - γ)) / Real.log 2) * Real.log 2 := by
        field_simp [ne_of_gt hlog2pos]
      _ ≤ (m : ℝ) * Real.log 2 := hmul
      _ = Real.log ((2 : ℝ) ^ m) := by rw [Real.log_pow]
  have hpowPos : 0 < (2 : ℝ) ^ m := pow_pos (by norm_num) m
  have hHpow : 1 / (1 - γ) ≤ (2 : ℝ) ^ m :=
    (Real.log_le_log_iff hHpos hpowPos).mp hlogH
  have hmul1 := mul_le_mul_of_nonneg_left hHpow hHpos.le
  have hmul2 := mul_le_mul_of_nonneg_right hHpow hpowPos.le
  have hpowSq : ((2 : ℝ) ^ m) ^ 2 = (2 : ℝ) ^ (2 * m) := by
    calc
      ((2 : ℝ) ^ m) ^ 2 = (2 : ℝ) ^ (m * 2) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (2 * m) := by rw [Nat.mul_comm m 2]
  calc
    (1 / (1 - γ)) ^ 2 =
        (1 / (1 - γ)) * (1 / (1 - γ)) := by ring
    _ ≤ (1 / (1 - γ)) * (2 : ℝ) ^ m := hmul1
    _ ≤ (2 : ℝ) ^ m * (2 : ℝ) ^ m := hmul2
    _ = ((2 : ℝ) ^ m) ^ 2 := by ring
    _ = (2 : ℝ) ^ (2 * m) := hpowSq
    _ = (2 : ℝ) ^ tdSourceFreedmanLevel γ := by
      simp [tdSourceFreedmanLevel, m]

end StatisticalRL.TemporalDifference
