import Formalization.Online.QLearning.RateNormalization

/-! Exact finite weighted Bellman subtraction, independent of concentration. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem qLearning_weightedBellman_subtract {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (w0 H R P : ℝ) (v u b : ι → ℝ)
    (hnorm : w0 + ∑ i, w i = 1) :
    (w0*H + ∑ i, w i*(R+v i+b i)) - (R+P) =
      w0*(H-(R+P)) + ∑ i, w i*((v i-u i)+(u i-P)+b i) := by
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  have hmul := congrArg (fun z : ℝ => z*(R+P)) hnorm
  nlinarith [hmul]
end StatisticalRL.OnlineRL
