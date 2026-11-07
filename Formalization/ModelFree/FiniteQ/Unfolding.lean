import Formalization.ModelFree.FiniteQ.Definitions

/-! # Finite-horizon synchronous Q-learning: the source recursion

Unfolding lemmas for `Formalization.ModelFree.FiniteQ.Definitions`: initialization, the terminal
convention `Q_{t,H+1} ≡ 0`, and the update `eqn:q-learning-finite`
(`chapters/generative_model_model_free.tex:2176–2194`) read off the definitions. -/

namespace StatisticalRL.FiniteQLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

open FiniteHorizonGenerative


theorem sampledStages_length {H : ℕ} (E : Fin H → EnvironmentStage State Action) (T : ℕ)
    (Q₀ : Fin H → State → Action → ℝ) (data : Samples State Action H T) :
    (sampledStages E T Q₀ data).length = H := by
  simp [sampledStages]

theorem sampledStages_drop {H : ℕ} (E : Fin H → EnvironmentStage State Action) (T : ℕ)
    (Q₀ : Fin H → State → Action → ℝ) (data : Samples State Action H T) (h : Fin H) :
    (sampledStages E T Q₀ data).drop h.val =
      { env := E h
        sample := fun t s a ↦ if ht : t < T then data ((h, s, a), ⟨t, ht⟩) else s
        init := Q₀ h } :: (sampledStages E T Q₀ data).drop (h.val + 1) := by
  rw [List.drop_eq_getElem_cons (by simp [sampledStages])]
  simp [sampledStages]

/-- Initialization: `Q_{0,h} = Q₀ h`. -/
theorem sampledIterateAt_zero {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (η : ℕ → ℝ) (T : ℕ) (Q₀ : Fin H → State → Action → ℝ) (data : Samples State Action H T)
    (h : Fin H) : sampledIterateAt E η T Q₀ data 0 h.val = Q₀ h := by
  rw [sampledIterateAt, sampledStages_drop]
  rfl

/-- Terminal convention: `Q_{t,H+1} ≡ 0` (0-based stage `H`). -/
theorem sampledIterateAt_terminal {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (η : ℕ → ℝ) (T : ℕ) (Q₀ : Fin H → State → Action → ℝ) (data : Samples State Action H T)
    (t : ℕ) (s : State) (a : Action) : sampledIterateAt E η T Q₀ data t H s a = 0 := by
  have : (sampledStages E T Q₀ data).drop H = [] := by
    simp [sampledStages]
  rw [sampledIterateAt, this]
  rfl

/-- The update `eqn:q-learning-finite` at iteration `t + 1 ≤ T` and stage `h`, with the target
built from the fresh draw `data ((h,s,a), t)` and the current iterate at stage `h + 1`. -/
theorem sampledIterateAt_succ {H : ℕ} (E : Fin H → EnvironmentStage State Action)
    (η : ℕ → ℝ) (T : ℕ) (Q₀ : Fin H → State → Action → ℝ) (data : Samples State Action H T)
    (t : ℕ) (ht : t < T) (h : Fin H) (s : State) (a : Action) :
    sampledIterateAt E η T Q₀ data (t + 1) h.val s a =
      (1 - η (t + 1)) * sampledIterateAt E η T Q₀ data t h.val s a +
        η (t + 1) * ((E h).reward s a +
          letI : Nonempty Action := (E h).action_nonempty
          actionMaximum (sampledIterateAt E η T Q₀ data (t + 1) (h.val + 1)
            (data ((h, s, a), ⟨t, ht⟩)))) := by
  simp only [sampledIterateAt]
  rw [sampledStages_drop]
  simp [iterate, headIterate, ht]

end StatisticalRL.FiniteQLearning
