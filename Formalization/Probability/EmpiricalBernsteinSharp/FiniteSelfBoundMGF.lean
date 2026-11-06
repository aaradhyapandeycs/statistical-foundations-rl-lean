import Formalization.Probability.EmpiricalBernsteinSharp.FiniteZeroMeanLaplace
import Formalization.Probability.EmpiricalBernsteinSharp.SelfBoundComparator

/-! Private uncompiled finite iid self-bounding lower-tail MGF candidate.
The empirical-variance and random-family consequences are separate. -/
open scoped BigOperators
namespace StatisticalRL.EmpiricalBernsteinEntropy

theorem finite_sample_self_bound_laplace (State : Type*) [Fintype State]
    (p : State → ℝ) (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (n : ℕ) (f : (Fin n → State) → ℝ)
    (fi : Fin n → (Fin n → State) → ℝ) (a theta : ℝ)
    (ha : 1 ≤ a) (htheta : 0 ≤ theta)
    (hind : ∀ j ω s, fi j (Function.update ω j s) = fi j ω)
    (hdec : ∀ j ω, 0 ≤ f ω-fi j ω ∧ f ω-fi j ω ≤ 1)
    (hsq : ∀ ω, (∑ j, (f ω-fi j ω)^2) ≤ a*f ω) :
    finiteSampleLaplace p n f theta ≤
      Real.exp (-theta*(∑ ω, (∏ i, p (ω i))*f ω) +
        a*(∑ ω, (∏ i, p (ω i))*f ω)*theta^2/2) := by
  classical
  let m : ℝ := ∑ ω : Fin n → State, (∏ i, p (ω i))*f ω
  have ha0 : 0 < a := by linarith
  have hf (ω : Fin n → State) : 0 ≤ f ω := by
    have hs : 0 ≤ ∑ j, (f ω-fi j ω)^2 := Finset.sum_nonneg (fun j hj ↦ sq_nonneg _)
    nlinarith [hsq ω]
  have hm : 0 ≤ m := Finset.sum_nonneg (fun ω hω ↦
    mul_nonneg (Finset.prod_nonneg (fun i hi ↦ hp _)) (hf ω))
  by_cases hm0 : m = 0
  · have hzero := finite_sample_laplace_eq_one_of_zero_mean p hp hp1 n f hf hm0 theta
    change finiteSampleLaplace p n f theta ≤ Real.exp (-theta*m+a*m*theta^2/2)
    rw [hzero, hm0]
    norm_num
  · have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
    let H : ℝ → ℝ := fun t ↦ Real.log (finiteSampleLaplace p n f t)
    let Hd : ℝ → ℝ := fun t ↦ -finiteSampleTiltedFirstMoment p n f t /
      finiteSampleLaplace p n f t
    have hMzero : finiteSampleLaplace p n f 0 = 1 := finite_sample_laplace_zero p hp1 n f
    have hAzero : finiteSampleTiltedFirstMoment p n f 0 = m := by
      simp [finiteSampleTiltedFirstMoment, m]
    have hH0 : H 0 = 0 := by simp [H, hMzero]
    have hHderiv0 : HasDerivAt H (-m) 0 := by
      have h := (finite_sample_laplace_derivative p n f 0).log (by rw [hMzero]; norm_num)
      simpa [H, hMzero, hAzero] using h
    have hderiv (t : ℝ) (ht : 0 < t) : HasDerivAt H (Hd t) t := by
      have h := finite_sample_log_laplace_differential p hp hp1 n f fi a t ha0 ht.le hind hdec hsq
      exact h.2.1
    have hnonpos (t : ℝ) (ht : 0 < t) : H t ≤ 0 := by
      have h := finite_sample_log_laplace_differential p hp hp1 n f fi a t ha0 ht.le hind hdec hsq
      exact Real.log_nonpos h.1.le (finite_sample_laplace_le_one p hp hp1 n f hf t ht.le)
    have hdiff (t : ℝ) (ht : 0 < t) : (t+a*(Real.exp t-1-t))*Hd t ≤ H t := by
      exact (finite_sample_log_laplace_differential p hp hp1 n f fi a t ha0 ht.le hind hdec hsq).2.2
    have hcomp := self_bound_differential_comparison H Hd a m ha hmpos hH0 hHderiv0
      hderiv hnonpos hdiff theta htheta
    have hquad := StatisticalRL.SharpBernstein.self_bound_comparison_quadratic a m theta ha hm htheta
    have hMpos : 0 < finiteSampleLaplace p n f theta :=
      (finite_sample_log_laplace_differential p hp hp1 n f fi a theta ha0 htheta hind hdec hsq).1
    change finiteSampleLaplace p n f theta ≤ Real.exp (-theta*m+a*m*theta^2/2)
    rw [← Real.exp_log hMpos]
    apply Real.exp_le_exp.mpr
    dsimp [H] at hcomp
    linarith

end StatisticalRL.EmpiricalBernsteinEntropy
