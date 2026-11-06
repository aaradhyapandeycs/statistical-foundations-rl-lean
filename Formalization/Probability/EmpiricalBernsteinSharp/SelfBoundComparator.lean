import Formalization.Probability.EmpiricalBernsteinSharp.SelfBoundRatioComparison
import Formalization.Probability.EmpiricalBernsteinSharp.SelfBoundComparison

/-! Private uncompiled specialization of the negative-ratio comparison to
the self-bounding Laplace differential inequality. -/
namespace StatisticalRL.EmpiricalBernsteinEntropy

theorem self_bound_differential_comparison (H Hd : ℝ → ℝ) (a m : ℝ)
    (ha : 1 ≤ a) (hm : 0 < m) (hH0 : H 0 = 0)
    (hHderiv0 : HasDerivAt H (-m) 0)
    (hHderiv : ∀ x, 0 < x → HasDerivAt H (Hd x) x)
    (hH : ∀ x, 0 < x → H x ≤ 0)
    (hHdiff : ∀ x, 0 < x →
      (x+a*(Real.exp x-1-x))*Hd x ≤ H x) :
    ∀ x, 0 ≤ x → H x ≤ -(m/a)*(1-Real.exp (-a*x)) := by
  let F : ℝ → ℝ := fun x ↦ -(m/a)*(1-Real.exp (-a*x))
  let Fd : ℝ → ℝ := fun x ↦ -m*Real.exp (-a*x)
  let D : ℝ → ℝ := fun x ↦ x+a*(Real.exp x-1-x)
  have ha0 : 0 < a := by linarith
  have hF0 : F 0 = 0 := by simp [F]
  have hFd (x : ℝ) : HasDerivAt F (Fd x) x := by
    dsimp [F, Fd]
    convert (((hasDerivAt_const x (1 : ℝ)).sub
      (((hasDerivAt_id x).const_mul (-a)).exp)).const_mul (-(m/a))) using 1 <;>
      simp only [id_eq] <;> field_simp [ne_of_gt ha0] <;> ring
  have hFderiv0 : HasDerivAt F (-m) 0 := by simpa [Fd] using hFd 0
  have hD (x : ℝ) (hx : 0 < x) : 0 < D x := by
    dsimp [D]
    have hψ : 0 ≤ Real.exp x-1-x := by linarith [Real.add_one_le_exp x]
    nlinarith [mul_nonneg ha0.le hψ]
  have hF (x : ℝ) (hx : 0 < x) : F x < 0 := by
    have hxexp : Real.exp (-a*x) < 1 := by
      rw [Real.exp_lt_one_iff]
      nlinarith [mul_pos ha0 hx]
    dsimp [F]
    have hmdiv : 0 < m/a := div_pos hm ha0
    exact mul_neg_of_neg_of_pos (by linarith) (by linarith)
  have hFdiff (x : ℝ) (hx : 0 < x) : F x ≤ D x*Fd x := by
    have h := StatisticalRL.SharpBernstein.self_bound_comparison_sign a m x ha hm.le hx.le
    dsimp [F, Fd, D]
    linarith
  exact negative_ratio_differential_comparison H F Hd Fd D m hm hH0 hF0
    hHderiv0 hFderiv0 hHderiv (fun x _ ↦ hFd x) hD hH hF hHdiff hFdiff

end StatisticalRL.EmpiricalBernsteinEntropy
