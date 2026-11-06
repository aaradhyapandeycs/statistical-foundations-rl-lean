import Formalization.Online.QLearning.EpisodeWeightedFin

/-! Source rate weights include the initial contribution at zero visits. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {H : ℕ}

theorem qLearning_rate_zero_eq (hH : 0 < H) (t : ℕ) :
    onlineQRateWeight H t 0 = if t=0 then 1 else 0 := by
  by_cases ht : t=0
  · simp [ht,onlineQRateWeight]
  · have ht1 : 1 ≤ t := by omega
    have hone : (1:ℕ) ∈ Finset.Icc 1 t := Finset.mem_Icc.mpr ⟨le_rfl,ht1⟩
    simp only [if_neg ht,onlineQRateWeight,if_pos rfl]
    apply Finset.prod_eq_zero hone
    rw [onlineQRate_one hH]
    ring

theorem qLearning_rate_fin_normalized (hH : 0 < H) (t : ℕ) :
    onlineQRateWeight H t 0 + ∑ i : Fin t, onlineQRateWeight H t (i.val+1) = 1 := by
  by_cases ht : t=0
  · subst t
    have hz : (∑ i : Fin 0, onlineQRateWeight H 0 (i.val+1)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      exact Fin.elim0 i
    rw [qLearning_rate_zero_eq hH, if_pos rfl, hz]
    norm_num
  · have hsum : (∑ i : Fin t, onlineQRateWeight H t (i.val+1)) =
        ∑ j ∈ Finset.Icc 1 t, onlineQRateWeight H t j := by
      apply Finset.sum_bij (fun i _ => i.val+1)
      · intro i hi; simp only [Finset.mem_Icc]; omega
      · intro i hi j hj hij; apply Fin.ext; omega
      · intro j hj
        have hj' := Finset.mem_Icc.mp hj
        refine ⟨⟨j-1,by omega⟩,Finset.mem_univ _,?_⟩
        simp only
        omega
      · intro i hi; rfl
    rw [qLearning_rate_zero_eq hH,if_neg ht, zero_add, hsum]
    exact onlineQRateWeight_sum_eq_one hH (by omega)
end StatisticalRL.OnlineRL
