import Formalization.ModelFree.QLearningChiUpper

/-! Actual support-preserving affine tilt for the
lower side of Q-comparison-facts (i). No optimizer or target lower estimate is
a premise. Source parameter selection is separate from this generic witness. -/
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State : Type*} [Fintype State]

/-- The actual centered nominal value has mean zero, including zero variance. -/
theorem qChi_centered_expectation_zero (p : FiniteDistribution State) (v : State → ℝ) :
    p.expectation (fun x ↦ v x - p.expectation v) = 0 := by
  rw [p.expectation_sub, p.expectation_const]
  ring

/-- Pairwise span suffices; no absolute location restriction on values is imposed. -/
theorem qChi_abs_centered_le_of_pairwise (p : FiniteDistribution State) (v : State → ℝ)
    (H : ℝ) (hspan : ∀ x y, |v x - v y| ≤ H) (x : State) :
    |v x - p.expectation v| ≤ H := by
  have he : v x - p.expectation v = p.expectation (fun y ↦ v x - v y) := by
    rw [p.expectation_sub, p.expectation_const]
  rw [he]
  exact p.abs_expectation_le (hspan x)

/-- An actual finite probability vector, built from the nominal row. The
centered-span and cH≤1 conditions prove its coordinate nonnegativity. -/
noncomputable def qChiTilt (p : FiniteDistribution State) (v : State → ℝ)
    (H c : ℝ) (hc : 0 ≤ c) (hspan : ∀ x, |v x - p.expectation v| ≤ H)
    (hsmall : c * H ≤ 1) : FiniteDistribution State where
  prob x := p.prob x * (1 + c * (v x - p.expectation v))
  prob_nonneg x := by
    apply mul_nonneg (p.prob_nonneg x)
    have hx := (abs_le.mp (hspan x)).1
    have hh := mul_le_mul_of_nonneg_left hx hc
    nlinarith
  sum_prob := by
    have hz := qChi_centered_expectation_zero p v
    have he : (fun x ↦ p.prob x * (1 + c * (v x - p.expectation v))) =
        fun x ↦ p.prob x + c * (p.prob x * (v x - p.expectation v)) := by
      funext x; ring
    rw [he, Finset.sum_add_distrib, ← Finset.mul_sum, p.sum_prob]
    change 1 + c * p.expectation (fun x ↦ v x - p.expectation v) = 1
    rw [hz]
    ring

@[simp] theorem qChiTilt_prob (p : FiniteDistribution State) (v : State → ℝ)
    (H c : ℝ) (hc : 0 ≤ c) (hspan : ∀ x, |v x - p.expectation v| ≤ H)
    (hsmall : c * H ≤ 1) (x : State) :
    (qChiTilt p v H c hc hspan hsmall).prob x =
      p.prob x * (1 + c * (v x - p.expectation v)) := rfl

/-- No mass can be created at a nominal zero atom. -/
theorem qChiTilt_support (p : FiniteDistribution State) (v : State → ℝ)
    (H c : ℝ) (hc : 0 ≤ c) (hspan : ∀ x, |v x - p.expectation v| ≤ H)
    (hsmall : c * H ≤ 1) (x : State) (hx : p.prob x = 0) :
    (qChiTilt p v H c hc hspan hsmall).prob x = 0 := by
  simp [qChiTilt_prob, hx]

/-- Exact cost of the concrete tilt. Cancellation is restricted to positive
nominal atoms; the centered second moment remains the actual variance. -/
theorem qChiTilt_chiSquared (p : FiniteDistribution State) (v : State → ℝ)
    (H c : ℝ) (hc : 0 ≤ c) (hspan : ∀ x, |v x - p.expectation v| ≤ H)
    (hsmall : c * H ≤ 1) :
    qChiSquared p (qChiTilt p v H c hc hspan hsmall) = c ^ 2 * p.variance v := by
  classical
  have hv : (∑ x ∈ Finset.univ.filter (fun x ↦ 0 < p.prob x),
      p.prob x * (v x - p.expectation v) ^ 2) = p.variance v := by
    rw [p.variance_eq_expectation_centered_sq, FiniteDistribution.expectation]
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hx hnot
    have hz : p.prob x = 0 := by
      have hn : ¬ 0 < p.prob x := by simpa using hnot
      exact le_antisymm (le_of_not_gt hn) (p.prob_nonneg x)
    simp [hz]
  unfold qChiSquared
  calc
    _ = ∑ x ∈ Finset.univ.filter (fun x ↦ 0 < p.prob x),
        c ^ 2 * (p.prob x * (v x - p.expectation v) ^ 2) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hp : p.prob x ≠ 0 := ne_of_gt (Finset.mem_filter.mp hx).2
      rw [qChiTilt_prob]
      field_simp
      ring
    _ = c ^ 2 * (∑ x ∈ Finset.univ.filter (fun x ↦ 0 < p.prob x),
        p.prob x * (v x - p.expectation v) ^ 2) := by rw [Finset.mul_sum]
    _ = _ := by rw [hv]

/-- The concrete tilt's gain is exactly c times the nominal variance. -/
theorem qChiTilt_expectation_sub (p : FiniteDistribution State) (v : State → ℝ)
    (H c : ℝ) (hc : 0 ≤ c) (hspan : ∀ x, |v x - p.expectation v| ≤ H)
    (hsmall : c * H ≤ 1) :
    (qChiTilt p v H c hc hspan hsmall).expectation v - p.expectation v = c * p.variance v := by
  have he : (fun x ↦ (qChiTilt p v H c hc hspan hsmall).prob x * v x) =
      fun x ↦ p.prob x * v x + c * (p.prob x * v x ^ 2) -
        (c * p.expectation v) * (p.prob x * v x) := by
    funext x
    rw [qChiTilt_prob]
    ring
  unfold FiniteDistribution.expectation at he ⊢
  rw [he, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  unfold FiniteDistribution.variance FiniteDistribution.expectation
  ring

/-- The witness belongs to the actual support-aware ball whenever its proved
cost is within rho. No strict-positivity or nonzero-variance premise occurs. -/
theorem qChiTilt_mem_ball (p : FiniteDistribution State) (v : State → ℝ)
    (H c ρ : ℝ) (hc : 0 ≤ c) (hspan : ∀ x, |v x - p.expectation v| ≤ H)
    (hsmall : c * H ≤ 1) (hcost : c ^ 2 * p.variance v ≤ ρ) :
    qChiTilt p v H c hc hspan hsmall ∈ qChiBall p ρ := by
  constructor
  · exact qChiTilt_support p v H c hc hspan hsmall
  · rw [qChiTilt_chiSquared]
    exact hcost

/-- Source lower support-function radius, using the explicit nominal or tilted
row witness. The centered-span premise is supplied by the pairwise-span helper. -/
theorem qRobustExpectations_sSup_sub_ge_of_centered_span
    (p : FiniteDistribution State) (v : State → ℝ) (H ρ : ℝ)
    (hH : 0 < H) (hρ : 0 ≤ ρ)
    (hspan : ∀ x, |v x - p.expectation v| ≤ H) :
    Real.sqrt (ρ * p.variance v) - ρ * H ≤
      sSup (qRobustExpectations p ρ v) - p.expectation v := by
  have hb : BddAbove (qRobustExpectations p ρ v) := by
    refine ⟨p.expectation v + Real.sqrt (ρ * p.variance v), ?_⟩
    intro z hz
    obtain ⟨q, hq, rfl⟩ := hz
    have hh := (le_abs_self (q.expectation v - p.expectation v)).trans
      (qChiBall_abs_expectation_sub_le p q ρ v hq)
    linarith
  have hnom : p.expectation v ≤ sSup (qRobustExpectations p ρ v) :=
    le_csSup hb ⟨p, qChiBall_self p ρ hρ, rfl⟩
  have hv : 0 ≤ p.variance v := p.variance_nonneg v
  have hσsq : Real.sqrt (p.variance v) ^ 2 = p.variance v := Real.sq_sqrt hv
  have hrhosq : Real.sqrt ρ ^ 2 = ρ := Real.sq_sqrt hρ
  have hprod : Real.sqrt (ρ * p.variance v) = Real.sqrt ρ * Real.sqrt (p.variance v) :=
    Real.sqrt_mul hρ _
  by_cases hzero : ρ = 0
  · subst ρ
    simp only [zero_mul, Real.sqrt_zero, sub_zero]
    linarith
  have hρpos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hzero)
  by_cases hlarge : Real.sqrt ρ * H ≤ Real.sqrt (p.variance v)
  · have hσpos : 0 < Real.sqrt (p.variance v) :=
      lt_of_lt_of_le (mul_pos (Real.sqrt_pos.2 hρpos) hH) hlarge
    let c := Real.sqrt ρ / Real.sqrt (p.variance v)
    have hc : 0 ≤ c := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hsmall : c * H ≤ 1 := by
      dsimp [c]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hσpos).2
      simpa only [one_mul] using hlarge
    have hcost : c ^ 2 * p.variance v = ρ := by
      change (Real.sqrt ρ / Real.sqrt (p.variance v)) ^ 2 * p.variance v = ρ
      calc
        _ = (Real.sqrt ρ / Real.sqrt (p.variance v)) ^ 2 * Real.sqrt (p.variance v) ^ 2 :=
          congrArg (fun z : ℝ ↦ (Real.sqrt ρ / Real.sqrt (p.variance v)) ^ 2 * z) hσsq.symm
        _ = Real.sqrt ρ ^ 2 := by field_simp
        _ = ρ := hrhosq
    let q := qChiTilt p v H c hc hspan hsmall
    have hq : q ∈ qChiBall p ρ := qChiTilt_mem_ball p v H c ρ hc hspan hsmall hcost.le
    have hgain := qChiTilt_expectation_sub p v H c hc hspan hsmall
    have hgain' : c * p.variance v = Real.sqrt ρ * Real.sqrt (p.variance v) := by
      change (Real.sqrt ρ / Real.sqrt (p.variance v)) * p.variance v = _
      calc
        _ = (Real.sqrt ρ / Real.sqrt (p.variance v)) * Real.sqrt (p.variance v) ^ 2 :=
          congrArg (fun z : ℝ ↦ (Real.sqrt ρ / Real.sqrt (p.variance v)) * z) hσsq.symm
        _ = _ := by field_simp
    have hs := le_csSup hb (show q.expectation v ∈ qRobustExpectations p ρ v from ⟨q, hq, rfl⟩)
    rw [hprod]
    change q.expectation v - p.expectation v = _ at hgain
    rw [hgain'] at hgain
    nlinarith [mul_nonneg hρ hH.le]
  · have hsmall : Real.sqrt (p.variance v) < Real.sqrt ρ * H := lt_of_not_ge hlarge
    have hh := mul_le_mul_of_nonneg_left hsmall.le (Real.sqrt_nonneg ρ)
    rw [hprod]
    nlinarith

end StatisticalRL.QLearning
