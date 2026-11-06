import Formalization.ModelFree.QLearningSourceLateCaps

/-!
# Source step-size weights for Q-learning (`lemma:Q-step-size`)

`qSourceStepWeight η t i` is the weight `η_i^{(t)}` of `def:eta-i-t-simple`
(`chapters/generative_model_model_free.tex:1075–1083`); the `i = 0` branch takes precedence
at `t = 0`. Under the source schedule `eq:thm:infinite-horizaon-eta` (lines 882–886) this
module assembles all claims of `lemma:Q-step-size` (lines 1093–1112) from the existing
late-cap and telescoping results.
-/

open scoped BigOperators
namespace StatisticalRL.QLearning

/-- The source weights `η_i^{(t)}` of `def:eta-i-t-simple`. -/
noncomputable def qSourceStepWeight (η : ℕ → ℝ) (t i : ℕ) : ℝ :=
  if i = 0 then ∏ j ∈ Finset.Icc 1 t, (1 - η j)
  else η i * ∏ j ∈ Finset.Icc (i + 1) t, (1 - η j)

theorem qSourceStepWeight_of_ne_zero (η : ℕ → ℝ) (t i : ℕ) (hi : i ≠ 0) :
    qSourceStepWeight η t i = qPositiveWeight η t i := by
  rw [qSourceStepWeight, if_neg hi]
  rfl

/-- All claims of `lemma:Q-step-size` under the source learning-rate schedule. -/
theorem qSource_step_size_weights (γ c₁ c₂ : ℝ) (T : ℕ) (η : ℕ → ℝ)
    (hT : 2 ≤ T) (hγ1 : γ < 1) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hs : qSourceRateSchedule γ c₁ c₂ T η) :
    (∀ i t : ℕ, T / 2 < i → i ≤ t → t ≤ T →
      0 ≤ qSourceStepWeight η t i ∧ qSourceStepWeight η t i ≤ η i ∧
        η i ≤ qSourceLateCap γ c₂ T) ∧
    (∀ t : ℕ, t ≤ T →
      (∑ i ∈ Finset.Icc (T / 2 + 1) t, (qSourceStepWeight η t i) ^ 2) ≤
        qSourceLateCap γ c₂ T) ∧
    (∀ τ t : ℕ, 1 ≤ τ → τ ≤ t →
      (∑ i ∈ Finset.Icc τ t, qSourceStepWeight η t i) =
        1 - ∏ j ∈ Finset.Icc τ t, (1 - η j)) ∧
    (∀ t : ℕ, (∑ i ∈ Finset.Icc 0 t, qSourceStepWeight η t i) = 1) := by
  have hunit : ∀ j, j ≤ T → 0 ≤ η j ∧ η j ≤ 1 :=
    fun j hj => qSourceRate_unit_interval γ c₁ c₂ T η hT hγ1 hc₁ hc₂ hs j hj
  have hsum : ∀ τ t : ℕ, 1 ≤ τ →
      (∑ i ∈ Finset.Icc τ t, qSourceStepWeight η t i) =
        1 - ∏ j ∈ Finset.Icc τ t, (1 - η j) := by
    intro τ t hτ
    rw [← qPositiveWeight_sum_telescope η τ t]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have : i ≠ 0 := by
      have := (Finset.mem_Icc.1 hi).1
      omega
    exact qSourceStepWeight_of_ne_zero η t i this
  refine ⟨?_, ?_, fun τ t hτ _ => hsum τ t hτ, ?_⟩
  · intro i t hi hit htT
    have hi0 : i ≠ 0 := by omega
    rw [qSourceStepWeight_of_ne_zero η t i hi0]
    obtain ⟨hη0, _⟩ := hunit i (by omega)
    have hp0 : 0 ≤ ∏ j ∈ Finset.Icc (i + 1) t, (1 - η j) :=
      Finset.prod_nonneg (fun j hj => by
        have := (hunit j (by have := (Finset.mem_Icc.1 hj).2; omega)).2
        linarith)
    have hp1 : ∏ j ∈ Finset.Icc (i + 1) t, (1 - η j) ≤ 1 :=
      Finset.prod_le_one
        (fun j hj => by
          have := (hunit j (by have := (Finset.mem_Icc.1 hj).2; omega)).2
          linarith)
        (fun j hj => by
          have := (hunit j (by have := (Finset.mem_Icc.1 hj).2; omega)).1
          linarith)
    refine ⟨mul_nonneg hη0 hp0, mul_le_of_le_one_right hη0 hp1, ?_⟩
    exact qSourceRate_late_le γ c₁ c₂ T η hT hγ1 hc₂ hs i hi (by omega)
  · intro t ht
    calc (∑ i ∈ Finset.Icc (T / 2 + 1) t, (qSourceStepWeight η t i) ^ 2)
        = ∑ i ∈ Finset.Icc (T / 2 + 1) t, (qPositiveWeight η t i) ^ 2 := by
          refine Finset.sum_congr rfl (fun i hi => ?_)
          have : i ≠ 0 := by
            have := (Finset.mem_Icc.1 hi).1
            omega
          rw [qSourceStepWeight_of_ne_zero η t i this]
      _ ≤ qSourceLateCap γ c₂ T :=
          qSourceLate_weight_squares_le γ c₁ c₂ T t η hT hγ1 hc₁ hc₂ ht hs
  · intro t
    have hsplit : Finset.Icc 0 t = insert 0 (Finset.Icc 1 t) := by
      ext x
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hsplit, Finset.sum_insert (by simp), hsum 1 t le_rfl, qSourceStepWeight, if_pos rfl]
    ring

end StatisticalRL.QLearning
