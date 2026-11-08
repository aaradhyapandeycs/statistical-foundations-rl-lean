import Formalization.RobustRL.DRVI.VarianceTools

/-!
# Variance transfer to an admissible row (milestone 3, plan §3.4, "clos")

For `q` in the uncertainty ball around `p` and a vector `f` with span at most `S`:
* TV: `Var_p f ≤ Var_q f + σ S^2`;
* χ² (support-aware): `Var_p f ≤ Var_q f + (√σ/2) S^2`.
Consequently `std_p f ≤ std_q f + √clos`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7

variable {State : Type*} [Fintype State]

theorem sum_sub_mul_const (p q : FiniteDistribution State) (c : ℝ) :
    ∑ x, (p.prob x - q.prob x) * c = 0 := by
  rw [← Finset.sum_mul, Finset.sum_sub_distrib, p.sum_prob, q.sum_prob]; ring

/-- Common reduction: `Var_p f − Var_q f ≤ Σ (p−q)(h − S²/2)` with `h = (f − E_q f)^2`. -/
theorem variance_sub_le_sum (p q : FiniteDistribution State) (f : State → ℝ) (c : ℝ) :
    p.variance f - q.variance f ≤
      ∑ x, (p.prob x - q.prob x) * ((f x - q.expectation f) ^ 2 - c) := by
  have h1 := variance_le_sq_dev p f (q.expectation f)
  have h2 : q.variance f = q.expectation (fun x ↦ (f x - q.expectation f) ^ 2) :=
    FiniteDistribution.variance_eq_expectation_centered_sq q f
  have h3 : ∑ x, (p.prob x - q.prob x) * ((f x - q.expectation f) ^ 2 - c) =
      p.expectation (fun x ↦ (f x - q.expectation f) ^ 2) -
        q.expectation (fun x ↦ (f x - q.expectation f) ^ 2) := by
    have : ∀ x, (p.prob x - q.prob x) * ((f x - q.expectation f) ^ 2 - c) =
        (p.prob x * (f x - q.expectation f) ^ 2 - q.prob x * (f x - q.expectation f) ^ 2) -
          (p.prob x - q.prob x) * c := by intro x; ring
    simp_rw [this, Finset.sum_sub_distrib, sum_sub_mul_const p q c]
    simp [FiniteDistribution.expectation]
  linarith

theorem centered_sq_bound (q : FiniteDistribution State) {f : State → ℝ} {S : ℝ}
    (hspan : ∀ x y, f x - f y ≤ S) (x : State) :
    |(f x - q.expectation f) ^ 2 - S ^ 2 / 2| ≤ S ^ 2 / 2 := by
  have hlo : f x - S ≤ q.expectation f := by
    have := q.expectation_mono (f := fun _ ↦ f x - S) (g := f)
      (fun y ↦ by have := hspan x y; linarith)
    simpa using this
  have hhi : q.expectation f ≤ f x + S :=
    q.expectation_le_const (fun y ↦ by have := hspan y x; linarith)
  have hsq : (f x - q.expectation f) ^ 2 ≤ S ^ 2 := by
    have h1 : -S ≤ f x - q.expectation f := by linarith
    have h2 : f x - q.expectation f ≤ S := by linarith
    nlinarith
  rw [abs_le]; constructor <;> nlinarith [sq_nonneg (f x - q.expectation f)]

/-- TV variance transfer. -/
theorem tv_variance_transfer {p q : FiniteDistribution State} {σ : ℝ} (hq : q ∈ tvBall p σ)
    {f : State → ℝ} {S : ℝ} (hspan : ∀ x y, f x - f y ≤ S) :
    p.variance f ≤ q.variance f + σ * S ^ 2 := by
  have hred := variance_sub_le_sum p q f (S ^ 2 / 2)
  have hq' : (1 / 2 : ℝ) * ∑ x, |p.prob x - q.prob x| ≤ σ := hq
  have hbound : ∑ x, (p.prob x - q.prob x) * ((f x - q.expectation f) ^ 2 - S ^ 2 / 2) ≤
      ∑ x, |p.prob x - q.prob x| * (S ^ 2 / 2) := by
    apply Finset.sum_le_sum; intro x _
    calc (p.prob x - q.prob x) * ((f x - q.expectation f) ^ 2 - S ^ 2 / 2)
        ≤ |(p.prob x - q.prob x) * ((f x - q.expectation f) ^ 2 - S ^ 2 / 2)| := le_abs_self _
      _ = |p.prob x - q.prob x| * |(f x - q.expectation f) ^ 2 - S ^ 2 / 2| := abs_mul _ _
      _ ≤ |p.prob x - q.prob x| * (S ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (centered_sq_bound q hspan x) (abs_nonneg _)
  rw [← Finset.sum_mul] at hbound
  have : (∑ x, |p.prob x - q.prob x|) * (S ^ 2 / 2) ≤ σ * S ^ 2 := by
    have hS : 0 ≤ S ^ 2 / 2 := by positivity
    have := mul_le_mul_of_nonneg_right (show ∑ x, |p.prob x - q.prob x| ≤ 2 * σ by linarith) hS
    linarith
  linarith

/-- χ² variance transfer (support-aware ball). -/
theorem chi_variance_transfer {p q : FiniteDistribution State} {σ : ℝ} (hq : q ∈ chiBall p σ)
    {f : State → ℝ} {S : ℝ} (hspan : ∀ x y, f x - f y ≤ S) :
    p.variance f ≤ q.variance f + Real.sqrt σ / 2 * S ^ 2 := by
  classical
  have hred := variance_sub_le_sum p q f (S ^ 2 / 2)
  obtain ⟨hsupp, hchi⟩ := hq
  set F := Finset.univ.filter (fun x ↦ 0 < p.prob x)
  set h : State → ℝ := fun x ↦ (f x - q.expectation f) ^ 2 - S ^ 2 / 2
  -- restrict to the support of p
  have hrestrict : ∑ x, (p.prob x - q.prob x) * h x = ∑ x ∈ F, (p.prob x - q.prob x) * h x := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    have hp0 : p.prob x = 0 := by
      have : ¬ 0 < p.prob x := fun h' ↦ hx (Finset.mem_filter.mpr ⟨Finset.mem_univ x, h'⟩)
      exact le_antisymm (not_lt.mp this) (p.prob_nonneg x)
    rw [hp0, hsupp x hp0]; ring
  -- Cauchy–Schwarz
  set u : State → ℝ := fun x ↦ (p.prob x - q.prob x) / Real.sqrt (p.prob x)
  set v : State → ℝ := fun x ↦ Real.sqrt (p.prob x) * h x
  have huv : ∀ x ∈ F, (p.prob x - q.prob x) * h x = u x * v x := by
    intro x hx
    have hp : 0 < p.prob x := (Finset.mem_filter.mp hx).2
    have hs : 0 < Real.sqrt (p.prob x) := Real.sqrt_pos.mpr hp
    simp only [u, v]
    field_simp
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt F u v
  have hu2 : ∑ x ∈ F, u x ^ 2 ≤ σ := by
    have : ∀ x ∈ F, u x ^ 2 = (q.prob x - p.prob x) ^ 2 / p.prob x := by
      intro x hx
      have hp : 0 < p.prob x := (Finset.mem_filter.mp hx).2
      simp only [u]
      rw [div_pow, Real.sq_sqrt hp.le]; ring
    rw [Finset.sum_congr rfl this]
    exact hchi
  have hv2 : ∑ x ∈ F, v x ^ 2 ≤ (S ^ 2 / 2) ^ 2 := by
    have hv : ∀ x, v x ^ 2 = p.prob x * h x ^ 2 := by
      intro x; simp only [v]; rw [mul_pow, Real.sq_sqrt (p.prob_nonneg x)]
    calc ∑ x ∈ F, v x ^ 2 ≤ ∑ x, v x ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun x _ _ ↦ sq_nonneg _)
      _ = p.expectation (fun x ↦ h x ^ 2) := by simp only [hv]; rfl
      _ ≤ (S ^ 2 / 2) ^ 2 := by
          apply p.expectation_le_const
          intro x
          have hb : |h x| ≤ S ^ 2 / 2 := centered_sq_bound q hspan x
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  have hσ0 : 0 ≤ σ := le_trans (Finset.sum_nonneg (fun x _ ↦ sq_nonneg (u x))) hu2
  have hfinal : ∑ x ∈ F, u x * v x ≤ Real.sqrt σ * (S ^ 2 / 2) := by
    calc ∑ x ∈ F, u x * v x ≤ Real.sqrt (∑ x ∈ F, u x ^ 2) * Real.sqrt (∑ x ∈ F, v x ^ 2) := hcs
      _ ≤ Real.sqrt σ * Real.sqrt ((S ^ 2 / 2) ^ 2) := by
          apply mul_le_mul (Real.sqrt_le_sqrt hu2) (Real.sqrt_le_sqrt hv2)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt σ * (S ^ 2 / 2) := by rw [Real.sqrt_sq (by positivity)]
  rw [hrestrict, Finset.sum_congr rfl huv] at hred
  have : Real.sqrt σ * (S ^ 2 / 2) = Real.sqrt σ / 2 * S ^ 2 := by ring
  linarith

theorem sqrt_add_le_add_sqrt' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]

/-- Standard-deviation form: `Var_p f ≤ Var_q f + clos` gives `std_p f ≤ std_q f + √clos`. -/
theorem std_le_of_variance_le {p q : FiniteDistribution State} {f : State → ℝ} {clos : ℝ}
    (hclos : 0 ≤ clos) (h : p.variance f ≤ q.variance f + clos) :
    Real.sqrt (p.variance f) ≤ Real.sqrt (q.variance f) + Real.sqrt clos := by
  calc Real.sqrt (p.variance f) ≤ Real.sqrt (q.variance f + clos) := Real.sqrt_le_sqrt h
    _ ≤ Real.sqrt (q.variance f) + Real.sqrt clos := sqrt_add_le_add_sqrt'
        (FiniteDistribution.variance_nonneg q f) hclos

end StatisticalRL.RobustRL.DRVI
