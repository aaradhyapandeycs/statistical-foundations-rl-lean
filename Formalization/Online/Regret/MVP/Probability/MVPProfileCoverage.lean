import Formalization.Online.Regret.MVP.Probability.MVPProfileChoice

/-! Every admissible sample-dependent sequence is represented by one fixed
choice vector on each realization, after simultaneous finite-index control. -/
namespace StatisticalRL.FiniteHorizonGenerative
open MeasureTheory ProbabilityTheory StatisticalRL.OnlineRL
variable {State Action Profile Level : Type*} [Fintype State] [Fintype Action]
  [Fintype Profile] [Fintype Level]
local instance : MeasurableSpace State := ⊤

theorem mvpProfileChoice_covers_actualFamily {H : ℕ} (K : ℕ)
    (family : Profile → (h : Fin H) → FutureCode (State := State) (Action := Action) h K → Finset (State → ℝ))
    (hcard : ∀ p h code, (family p h code).card ≤ K+1)
    (p : Profile) (level : Level) (data : Samples State Action H K)
    (X : Fin H → State → Action → State → ℝ)
    (hX : ∀ h s a, X h s a ∈ family p h (futureData h K data)) :
    ∃ choice : Fin H → State → Action → Fin (K+1),
      ∀ h s a, mvpProfileSelectedTest K family
        (p,choice,level) h s a (futureData h K data) = X h s a := by
  classical
  let choice : Fin H → State → Action → Fin (K+1) := fun h s a =>
    Classical.choose (mvpProfileSelectedTest_covers K family hcard p h
      (futureData h K data) (X h s a) (hX h s a))
  refine ⟨choice, ?_⟩
  intro h s a
  exact Classical.choose_spec (mvpProfileSelectedTest_covers K family hcard p h
    (futureData h K data) (X h s a) (hX h s a))
end StatisticalRL.FiniteHorizonGenerative
