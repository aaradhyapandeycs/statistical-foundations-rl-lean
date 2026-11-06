import Formalization.Online.QLearning.ActualBellmanError
import Formalization.Online.QLearning.BonusNoiseScalar

/-! The source bonus bound in the actual finite-visit indexing. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators

theorem qLearning_finBonus_bounds (H t : ℕ) (hH : 0 < H) (ht : 0 < t)
    (L cb : ℝ) (hL : 0 ≤ L) (hcb : 2 ≤ cb) :
    let A := (H:ℝ)^3*L
    2*Real.sqrt (A/(t:ℝ)) ≤
      ∑ i : Fin t, onlineQRateWeight H t (i.val+1) * (cb*Real.sqrt (A/((i.val+1):ℝ))) ∧
    2*(∑ i : Fin t, onlineQRateWeight H t (i.val+1) * (cb*Real.sqrt (A/((i.val+1):ℝ)))) ≤
      4*cb*Real.sqrt (A/(t:ℝ)) := by
  let A : ℝ := (H:ℝ)^3*L
  have heq : (∑ i : Fin t, onlineQRateWeight H t (i.val+1) * (cb*Real.sqrt (A/((i.val+1):ℝ)))) =
      ∑ j ∈ Finset.Icc 1 t, onlineQRateWeight H t j * (cb*Real.sqrt (A/(j:ℝ))) := by
    apply Finset.sum_bij (fun i _ => i.val+1)
    · intro i hi; simp only [Finset.mem_Icc]; omega
    · intro i hi j hj hij; apply Fin.ext; omega
    · intro j hj
      have hj' := Finset.mem_Icc.mp hj
      refine ⟨⟨j-1,by omega⟩,Finset.mem_univ _,?_⟩
      simp only
      omega
    · intro i hi; simp only [Nat.cast_add, Nat.cast_one]
  change 2*Real.sqrt (A/(t:ℝ)) ≤ _ ∧ 2*(∑ i : Fin t,
    onlineQRateWeight H t (i.val+1) * (cb*Real.sqrt (A/((i.val+1):ℝ)))) ≤ _
  rw [heq]
  exact qLearning_bonus_weighted_bounds H t hH ht L cb hL hcb
end StatisticalRL.OnlineRL
