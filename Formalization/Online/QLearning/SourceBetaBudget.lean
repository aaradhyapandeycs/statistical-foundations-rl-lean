import Formalization.Online.QLearning.VisitSqrtBudget
import Formalization.Online.QLearning.ActualErrorAll

/-! The source β budget on any realized stage-specific row sequence. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {Row : Type*} [Fintype Row] [DecidableEq Row]

theorem qLearning_sourceBeta_visitBudget (rowAt : ℕ → Row) (K H : ℕ)
    (L cb : ℝ) (hL : 0 ≤ L) (hcb : 0 ≤ cb) :
    (∑ k ∈ Finset.range K, qLearningSourceBeta H (onlineVisitCount rowAt k (rowAt k)) L cb) ≤
      8*cb*Real.sqrt ((H:ℝ)^3*L)*Real.sqrt (Fintype.card Row : ℝ)*Real.sqrt (K:ℝ) := by
  let A : ℝ := (H:ℝ)^3*L
  let C : ℝ := 4*cb*Real.sqrt A
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hz : qLearningSourceBeta H 0 L cb = 0 := by simp [qLearningSourceBeta]
  have hnonneg (n : ℕ) : 0 ≤ qLearningSourceBeta H n L cb := by
    unfold qLearningSourceBeta
    split_ifs <;> positivity
  have hbound (n : ℕ) (hn : 0<n) : qLearningSourceBeta H n L cb ≤ C/Real.sqrt (n:ℝ) := by
    rw [qLearningSourceBeta,if_neg (ne_of_gt hn)]
    dsimp [C,A]
    rw [Real.sqrt_div (by positivity)]
    ring_nf
    exact le_rfl
  have h := qLearning_visitCost_sqrt_budget rowAt K (fun n => qLearningSourceBeta H n L cb)
    C hz hC hnonneg hbound
  dsimp [C,A] at h
  nlinarith
end StatisticalRL.OnlineRL
