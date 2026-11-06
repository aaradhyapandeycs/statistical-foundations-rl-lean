import Formalization.Online.QLearning.RateWeights

/-! Fixed t deterministic learning-rate weight squared budget. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem qLearning_rate_fin_squared_le (H n : ℕ) (hH : 0 < H) (hn : 0 < n) :
    (∑ i : Fin n, (onlineQRateWeight H n (i.val+1))^2) ≤ 2*(H:ℝ)/(n:ℝ) := by
  have heq : (∑ i : Fin n, (onlineQRateWeight H n (i.val+1))^2) =
      ∑ j ∈ Finset.Icc 1 n, (onlineQRateWeight H n j)^2 := by
    apply Finset.sum_bij (fun i _ => i.val+1)
    · intro i hi
      simp only [Finset.mem_Icc]
      omega
    · intro i hi j hj hij
      apply Fin.ext
      omega
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      refine ⟨⟨j-1, by omega⟩, Finset.mem_univ _, ?_⟩
      simp only
      omega
    · intro i hi
      rfl
  rw [heq]
  exact onlineQRateWeight_sq_sum_le H n hH hn
end StatisticalRL.OnlineRL
