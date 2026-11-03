import Formalization.ModelFree.QLearningChiFixedValueFreedman

/-! common actual-law event for two deterministic
value families, all rows and late terminals. No inter-event independence. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qChiUnionStateMeasurable : MeasurableSpace State := ⊤
local instance qChiUnionActionMeasurable : MeasurableSpace Action := ⊤

noncomputable def qChiFixedFreedmanGood (M : DiscountedMDP State Action) (v : State → ℝ)
    (η : ℕ → ℝ) (c₂ : ℝ) (T u : ℕ) (s : State) (a : Action)
    (K : ℕ) (ε : ℝ) : Set (QSamples State Action T) := {data |
      |qChiFixedFluctuationSum M v η T u s a data| ≤ Real.sqrt (8 * max
        (historyPredictableVariance (qSamplingLaw M T) (qChiFixedFluctuationIncrement M v η T u s a) T data)
        (qChiFixedVarianceBudget M v c₂ T s a / (2 : ℝ)^K) * Real.log (2*K/ε)) +
        (4/3) * (M.discount * qSourceLateCap M.discount c₂ T * M.effectiveHorizon) * Real.log (2*K/ε)}

/-- Two signs receive delta/2 each through epsilon=delta/(2SAT). -/
theorem qChiFixedFreedman_twoFamilies_allRows (M : DiscountedMDP State Action)
    (vs : Bool → State → ℝ) (η : ℕ → ℝ) (c₁ c₂ : ℝ) (T : ℕ)
    (hT : 2 ≤ T) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hs : qSourceRateSchedule M.discount c₁ c₂ T η)
    (hspan : ∀ flag x y, |vs flag x - vs flag y| ≤ M.effectiveHorizon)
    (K : ℕ) (hK : 0 < K) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ (qSamplingLaw M T).real {data |
      ∀ (flag : Bool) (s : State) (a : Action) (j : Fin T), T/2 < j.val+1 →
        data ∈ qChiFixedFreedmanGood M (vs flag) η c₂ T (j.val+1) s a K
          (δ / (2 * (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * T))} := by
  classical
  letI : Nonempty State := M.state_nonempty
  letI : Nonempty Action := M.action_nonempty
  let μ := qSamplingLaw M T
  let S : ℝ := Fintype.card State
  let A : ℝ := Fintype.card Action
  let ε := δ / (2*S*A*T)
  have hS : 1 ≤ S := by dsimp [S]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hA : 1 ≤ A := by dsimp [A]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hTr : 1 ≤ (T : ℝ) := by exact_mod_cast (by omega : 1 ≤ T)
  have hden : 0 < 2*S*A*T := by positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε < 1 := by
    dsimp [ε]
    rw [div_lt_iff₀ hden]
    have hSA : 1 ≤ S*A := by nlinarith
    have hSAT : 1 ≤ S*A*T := by nlinarith
    nlinarith
  let bad (p : Bool × State × Action × Fin T) : Set (QSamples State Action T) :=
    if T/2 < p.2.2.2.val+1 then
      (qChiFixedFreedmanGood M (vs p.1) η c₂ T (p.2.2.2.val+1) p.2.1 p.2.2.1 K ε)ᶜ else ∅
  have hbad (p : Bool × State × Action × Fin T) : μ.real (bad p) ≤ ε := by
    by_cases hp : T/2 < p.2.2.2.val+1
    · have hgood := qChiFixedFluctuation_freedman M (vs p.1) η c₁ c₂ T (p.2.2.2.val+1)
        hT (by omega) hc₁ hc₂ hs (hspan p.1) p.2.1 p.2.2.1 K hK ε hε hε1
      have hc := measureReal_compl (μ := μ)
        ((Set.to_countable (qChiFixedFreedmanGood M (vs p.1) η c₂ T
          (p.2.2.2.val+1) p.2.1 p.2.2.1 K ε)).measurableSet)
      rw [probReal_univ] at hc
      simp only [bad, hp, if_pos]
      change 1 - ε ≤ μ.real (qChiFixedFreedmanGood M (vs p.1) η c₂ T
        (p.2.2.2.val+1) p.2.1 p.2.2.1 K ε) at hgood
      linarith
    · simp [bad, hp, hε.le]
  have hall : μ.real (⋃ p : Bool × State × Action × Fin T, bad p) ≤ δ := by
    calc
      _ ≤ ∑ p : Bool × State × Action × Fin T, μ.real (bad p) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _p : Bool × State × Action × Fin T, ε := Finset.sum_le_sum (fun p _ ↦ hbad p)
      _ = δ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
        change (2*(S*(A*T)))*ε = δ
        rw [show 2*(S*(A*T)) = 2*S*A*T by ring]
        dsimp [ε]
        field_simp [ne_of_gt hden]
  let target : Set (QSamples State Action T) := {data |
    ∀ (flag : Bool) (s : State) (a : Action) (j : Fin T), T/2 < j.val+1 →
      data ∈ qChiFixedFreedmanGood M (vs flag) η c₂ T (j.val+1) s a K ε}
  have hsub : (⋃ p : Bool × State × Action × Fin T, bad p)ᶜ ⊆ target := by
    intro data hd flag s a j hj
    by_contra hn
    exact hd (Set.mem_iUnion.mpr ⟨(flag,s,a,j), by simp [bad, hj, hn]⟩)
  have hmono := measureReal_mono hsub (measure_ne_top μ target)
  have hc := measureReal_compl (μ := μ)
    ((Set.to_countable (⋃ p : Bool × State × Action × Fin T, bad p)).measurableSet)
  rw [probReal_univ] at hc
  change 1 - δ ≤ μ.real target
  linarith

noncomputable def qChiComparatorValueFamily (M : DiscountedMDP State Action)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (flag : Bool) : State → ℝ :=
  if flag then qLearningValue M (qRobustPlusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ)
  else qLearningValue M (qRobustMinusFixedPoint M ρ (2 * ρ * M.effectiveHorizon) hρ)

theorem qChiComparatorValueFamily_span (M : DiscountedMDP State Action)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (flag : Bool) (x y : State) :
    |qChiComparatorValueFamily M ρ hρ flag x - qChiComparatorValueFamily M ρ hρ flag y| ≤ M.effectiveHorizon := by
  cases flag
  · simpa [qChiComparatorValueFamily] using
      (qRobustComparator_value_pairwise_span M ρ (2 * ρ * M.effectiveHorizon) hρ x y).2
  · simpa [qChiComparatorValueFamily] using
      (qRobustComparator_value_pairwise_span M ρ (2 * ρ * M.effectiveHorizon) hρ x y).1

/-- Actual constructed comparators are fixed before data and satisfy the
required span by proof. Their common event introduces no span premise. -/
theorem qChiComparatorFreedman_allRows (M : DiscountedMDP State Action)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (η : ℕ → ℝ) (c₁ c₂ : ℝ) (T : ℕ)
    (hT : 2 ≤ T) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hs : qSourceRateSchedule M.discount c₁ c₂ T η)
    (K : ℕ) (hK : 0 < K) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ (qSamplingLaw M T).real {data |
      ∀ (flag : Bool) (s : State) (a : Action) (j : Fin T), T/2 < j.val+1 →
        data ∈ qChiFixedFreedmanGood M (qChiComparatorValueFamily M ρ hρ flag)
          η c₂ T (j.val+1) s a K
          (δ / (2 * (Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * T))} := by
  exact qChiFixedFreedman_twoFamilies_allRows M (qChiComparatorValueFamily M ρ hρ) η c₁ c₂ T
    hT hc₁ hc₂ hs (qChiComparatorValueFamily_span M ρ hρ) K hK δ hδ hδ1

end StatisticalRL.QLearning
