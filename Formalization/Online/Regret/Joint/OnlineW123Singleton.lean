import Formalization.Online.Regret.W3.OnlineW3RestrictedSource
import Formalization.Online.Regret.W2.OnlineW2RestrictedSourceBudget
import Formalization.Online.Regret.W1.OnlineW1RestrictedSourceBudget

/-! Single-state empirical and true row expectations agree even for the
corrected zero-count default. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance w123SingleStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance w123SingleActionDecidable : DecidableEq Action := Classical.decEq Action

theorem onlineSingleton_expectation_eq [Subsingleton State]
    (p q : FiniteDistribution State) (V : State → ℝ) : p.expectation V = q.expectation V := by
  unfold FiniteDistribution.expectation
  apply Finset.sum_congr rfl
  intro s hs
  rw [p.prob_eq_one_of_subsingleton s, q.prob_eq_one_of_subsingleton s]

theorem onlineSingleton_W123_zero [Subsingleton State]
    (H K : ℕ) (hH : 0 < H) (E : Fin H → EnvironmentStage State Action)
    (initial : Fin K → State) (fallback : State) (path : OnlineOutcomePath State (K * H))
    (δ c₁ c₂ : ℝ) :
    (∑ k : Fin K, onlineActualEpisodeW1 H K hH E initial fallback path k δ c₁ c₂) = 0 ∧
    (∑ k : Fin K, onlineActualEpisodeW2 H K hH E initial fallback path k δ c₁ c₂) = 0 ∧
    (∑ h : Fin H, ∑ k : Fin K, onlineActualW3Point H K hH E initial fallback path δ c₁ c₂ h k) = 0 := by
  have hdiff (p q : FiniteDistribution State) (V : State → ℝ) :
      p.expectation V - q.expectation V = 0 := sub_eq_zero.mpr (onlineSingleton_expectation_eq p q V)
  constructor
  · simp only [onlineActualEpisodeW1, onlineEpisodeFixedOptimalW1]
    simp [hdiff]
  constructor
  · simp only [onlineActualEpisodeW2, onlineEpisodeFixedOptimalW2]
    simp [hdiff]
  · simp only [onlineActualW3Point]
    simp [hdiff]
end StatisticalRL.OnlineRL
