import Formalization.ModelFree.QLearningStoppedPrefixKLAtomBase

/-! Geometric stopping weights and stopped-prefix atomic KL identities. -/

namespace StatisticalRL.QLearning.CountablePinsker

/-- KL atom scaling when both laws receive the same nonnegative mass. KL
orientation is numerator `a`, reference `b`; support inclusion and all zero
cases are explicit. -/
theorem qStoppedPrefixKLAtom_common_nonneg_scale
    (w a b : ℝ) (hw : 0 ≤ w) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hsupport : a ≠ 0 → b ≠ 0) :
    qStoppedPrefixKLAtom (w * a) (w * b) = w * qStoppedPrefixKLAtom a b := by
  by_cases hw0 : w = 0
  · simp [qStoppedPrefixKLAtom, hw0]
  have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  by_cases ha0 : a = 0
  · simp [qStoppedPrefixKLAtom, ha0]
  have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb0 := hsupport ha0
  have hbPos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have hwa : w * a ≠ 0 := ne_of_gt (mul_pos hwpos haPos)
  have hwb : w * b ≠ 0 := ne_of_gt (mul_pos hwpos hbPos)
  have hratio : (w * a) / (w * b) = a / b := by
    field_simp [ne_of_gt hwpos, ne_of_gt haPos, ne_of_gt hbPos]
  simp only [qStoppedPrefixKLAtom, if_neg hwa, if_neg ha0, hratio]
  ring

/-- The common mass of stop time `k` for the source independent geometric
stopping time. The zero-discount value is specified directly to avoid a
`0^0` convention. -/
noncomputable def qGeometricStopWeight (γ : ℝ) (k : ℕ) : ℝ :=
  if γ = 0 then (if k = 0 then 1 else 0) else (1 - γ) * γ ^ k

theorem qGeometricStopWeight_nonneg (γ : ℝ) (k : ℕ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    0 ≤ qGeometricStopWeight γ k := by
  by_cases hγ0 : γ = 0
  · simp [qGeometricStopWeight, hγ0]
    split_ifs <;> norm_num
  · simp [qGeometricStopWeight, hγ0]
    exact mul_nonneg (by linarith) (pow_nonneg hγ k)

/-- At zero discount the stop is exactly the common point mass at horizon
zero, with every positive horizon assigned zero mass. -/
theorem qGeometricStopWeight_zero (k : ℕ) :
    qGeometricStopWeight 0 k = if k = 0 then 1 else 0 := by
  simp [qGeometricStopWeight]

/-- Atomwise KL cancellation for the source geometric stopped-prefix
mixture. In particular all positive-horizon atoms vanish at `γ=0`; no
positive-weight assumption is imposed, and impossible nominal paths retain
the zero-numerator convention. -/
theorem qStoppedPrefixKLAtom_geometric_scale
    (γ : ℝ) (k : ℕ) (a b : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsupport : a ≠ 0 → b ≠ 0) :
    qStoppedPrefixKLAtom (qGeometricStopWeight γ k * a)
      (qGeometricStopWeight γ k * b) =
      qGeometricStopWeight γ k * qStoppedPrefixKLAtom a b := by
  exact qStoppedPrefixKLAtom_common_nonneg_scale _ a b
    (qGeometricStopWeight_nonneg γ k hγ hγ1) ha hb hsupport

end StatisticalRL.QLearning.CountablePinsker
