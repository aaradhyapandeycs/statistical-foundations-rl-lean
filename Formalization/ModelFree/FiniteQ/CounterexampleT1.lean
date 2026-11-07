import Formalization.ModelFree.FiniteQ.Unfolding

/-! # Theorem 4.13 needs `2 ≤ T`: a counterexample at `T = 1`

Source: `thm:finite-horizon-simple-Q-generative`,
`chapters/generative_model_model_free.tex:2215–2236`, schedule `eq:thm:finite-horizaon-eta`
(:2203–2209). Instance (`docs/SOURCE-ISSUES.md` C35 item (1)): `H = 2`, `State = Bool`,
`Action = Unit`, both transitions uniform, `r₁ ≡ 0`, `r₂(s) = [s]`, `η ≡ 1`, `Q₀ ≡ 0`, `δ = 1/2`,
`ε = 1/4`. Then `Q⋆₁ ≡ 1/2`, while the one-iteration output at stage 1 is `r₂(s') ∈ {0,1}` for every
draw, so the accuracy event is empty. Adapted from the independent critic's probe. -/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.FiniteQLearning

noncomputable def t1Unif : FiniteDistribution Bool where
  prob := fun _ ↦ 1 / 2
  prob_nonneg := fun _ ↦ by norm_num
  sum_prob := by simp

noncomputable def t1Stage0 : EnvironmentStage Bool Unit where
  state_nonempty := ⟨true⟩
  action_nonempty := ⟨()⟩
  transition := fun _ _ ↦ t1Unif
  reward := fun _ _ ↦ 0
  reward_nonneg := fun _ _ ↦ le_rfl
  reward_le_one := fun _ _ ↦ by norm_num

noncomputable def t1Stage1 : EnvironmentStage Bool Unit where
  state_nonempty := ⟨true⟩
  action_nonempty := ⟨()⟩
  transition := fun _ _ ↦ t1Unif
  reward := fun s _ ↦ if s then 1 else 0
  reward_nonneg := fun s _ ↦ by split_ifs <;> norm_num
  reward_le_one := fun s _ ↦ by split_ifs <;> norm_num

noncomputable def t1Env : Fin 2 → EnvironmentStage Bool Unit := ![t1Stage0, t1Stage1]

theorem t1_optimalQ_stage0 (s : Bool) :
    EnvironmentStage.optimalQ ((List.ofFn t1Env).drop 0) s () = 1 / 2 := by
  have hL : List.ofFn t1Env = [t1Stage0, t1Stage1] := by simp [List.ofFn_succ, t1Env]
  rw [hL]
  simp [EnvironmentStage.optimalQ, EnvironmentStage.optimalValue,
    EnvironmentStage.qBackup, FiniteDistribution.expectation, t1Stage0, t1Stage1, t1Unif, actionMaximum]

theorem t1_iterate_stage0 (η : ℕ → ℝ) (hη : η 1 = 1) (Q₀ : Fin 2 → Bool → Unit → ℝ)
    (data : FiniteHorizonGenerative.Samples Bool Unit 2 1) (s : Bool) :
    sampledIterate t1Env η 1 Q₀ data 0 s () =
      if data ((0, s, ()), 0) then 1 else 0 := by
  have h0 := sampledIterateAt_succ t1Env η 1 Q₀ data 0 (by norm_num) 0 s ()
  have h1 := sampledIterateAt_succ t1Env η 1 Q₀ data 0 (by norm_num) 1
    (data ((0, s, ()), 0)) ()
  have hterm := sampledIterateAt_terminal t1Env η 1 Q₀ data 1
  simp only [hη, sub_self, zero_mul, zero_add, one_mul] at h0 h1
  simp only [Fin.val_one, Fin.val_zero] at h0 h1
  unfold sampledIterate
  simp only [Fin.val_zero]
  rw [h0]
  simp only [actionMaximum, Finset.univ_unique, Finset.sup'_singleton] at h1 ⊢
  simp only [zero_add, show (default : Unit) = () from rfl] at h1 ⊢
  have hfin : (⟨0, by norm_num⟩ : Fin 1) = 0 := rfl
  simp only [hfin] at h1 ⊢
  erw [h1, hterm]
  simp [t1Env, t1Stage0, t1Stage1]

theorem t1_event_empty (η : ℕ → ℝ) (hη : η 1 = 1) (Q₀ : Fin 2 → Bool → Unit → ℝ) :
    {data : FiniteHorizonGenerative.Samples Bool Unit 2 1 | ∀ h s a,
      |sampledIterate t1Env η 1 Q₀ data h s a -
        EnvironmentStage.optimalQ ((List.ofFn t1Env).drop h.val) s a| ≤ 1 / 4} = ∅ := by
  ext data
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall, not_le]
  refine ⟨0, true, (), ?_⟩
  rw [t1_iterate_stage0 η hη Q₀ data true]
  have := t1_optimalQ_stage0 true
  simp only [Fin.val_zero] at this ⊢
  rw [this]
  split_ifs <;> norm_num [abs_of_pos, abs_of_neg]


universe u v

/-- The statement-index entry `Thm4_13_corrected` (`Formalization/Statements/Ch4.lean`), verbatim,
with its premise `2 ≤ T` replaced by `T₀ ≤ T`. `Thm4_13_from 2` is the corrected entry;
`Thm4_13_from 1` is the printed statement transcribed without the added premise. -/
def Thm4_13_from (T₀ : ℕ) : Prop :=
  ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c₁ c₂ : ℝ, 0 < c₂ → c₂ ≤ c₁ → c₁ ≤ c₀ → ∃ c₃ : ℝ, 0 < c₃ ∧
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (H : ℕ) (E : Fin H → EnvironmentStage State Action) (η : ℕ → ℝ) (δ ε : ℝ) (T : ℕ),
    T₀ ≤ T → 0 < δ → δ < 1 → 0 < ε → ε ≤ 1 →
    (∀ t, t ≤ T →
      1 / (1 + c₁ * T / (H * Real.log (T : ℝ) ^ 2)) ≤ η t ∧
      η t ≤ 1 / (1 + c₂ * t / (H * Real.log (T : ℝ) ^ 2))) →
    c₃ * (H : ℝ) ^ 4 * Real.log (T : ℝ) ^ 3 *
      Real.log ((Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * T / δ) / ε ^ 2 ≤ T →
    ∀ Q₀ : Fin H → State → Action → ℝ,
    (∀ h s a, 0 ≤ Q₀ h s a ∧ Q₀ h s a ≤ (H : ℝ) - h) →
    1 - δ < (FiniteHorizonGenerative.samplingLaw E T).real {data | ∀ h s a,
      |sampledIterate E η T Q₀ data h s a -
        EnvironmentStage.optimalQ ((List.ofFn E).drop h.val) s a| ≤ ε}

/-- Without the added premise (`1 ≤ T` in place of `2 ≤ T`) the Lean transcription of
Theorem 4.13 is false: at `T = 1`, `Real.log 1 = 0` and `x / 0 = 0` turn the schedule into
`η_1 = 1` and the sample-size condition into `0 ≤ 1`, while the instance below is never
`1/4`-accurate (`docs/SOURCE-ISSUES.md` C35). -/
theorem not_thm4_13_from_one : ¬ Thm4_13_from.{0, 0} 1 := by
  rintro ⟨c₀, hc₀, h⟩
  obtain ⟨c₃, -, hc₃⟩ := h c₀ c₀ hc₀ le_rfl le_rfl
  have key := hc₃ Bool Unit 2 t1Env (fun _ ↦ 1) (1 / 2) (1 / 4) 1 le_rfl (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (fun t _ ↦ by simp) (by simp) (fun _ _ _ ↦ 0)
    (fun h _ _ ↦ ⟨le_rfl, by have := h.isLt; simp⟩)
  rw [t1_event_empty (fun _ ↦ 1) rfl (fun _ _ _ ↦ 0)] at key
  simp at key
  linarith

end StatisticalRL.FiniteQLearning
