import Formalization.ModelFree.QLearningOptimalFreedman

/-! Actual-law late-terminal and row union for V*.
The finite-cardinality product association is normalized explicitly. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.QLearning
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance qOptUnionStateMeasurable : MeasurableSpace State := ⊤
local instance qOptUnionActionMeasurable : MeasurableSpace Action := ⊤

/-- Fixed-row Freedman good event for one source terminal u, with arbitrary
positive failure budget. -/
noncomputable def qOptimalFreedmanGood (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (c₂ : ℝ) (T u : ℕ) (hu : u ≤ T) (s : State) (a : Action)
    (K : ℕ) (ε : ℝ) : Set (QSamples State Action T) := {data |
      |qSourceIndexedFluctuation M η T u hu s a data| ≤
        Real.sqrt (8 * max
          (historyPredictableVariance (qSamplingLaw M T) (qOptimalFluctuationIncrement M η T u s a) T data)
          (qOptimalVarianceBudget M c₂ T s a / (2 : ℝ)^K) * Real.log (2*K/ε)) +
        (4/3) * (M.discount * qSourceLateCap M.discount c₂ T * M.effectiveHorizon) * Real.log (2*K/ε)}

/-- One event for every row and every source late terminal. Confidence ε is
δ/(|S||A|T); all T positive terminal indices are included in the union count,
while only floor(T/2)<u contribute. -/
theorem qOptimalFreedman_late_allRows (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (c₁ c₂ : ℝ) (T : ℕ) (hT : 2 ≤ T) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hs : qSourceRateSchedule M.discount c₁ c₂ T η)
    (K : ℕ) (hK : 0 < K) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ (qSamplingLaw M T).real {data |
      ∀ (s : State) (a : Action) (j : Fin T), T/2 < j.1+1 →
        data ∈ qOptimalFreedmanGood M η c₂ T (j.1+1) (by omega) s a K
          (δ / ((Fintype.card State : ℝ) * (Fintype.card Action : ℝ) * T))} := by
  classical
  letI : Nonempty State := M.state_nonempty
  letI : Nonempty Action := M.action_nonempty
  let μ := qSamplingLaw M T
  let S : ℝ := Fintype.card State
  let A : ℝ := Fintype.card Action
  let ε := δ / (S*A*T)
  have hS : 1 ≤ S := by dsimp [S]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hA : 1 ≤ A := by dsimp [A]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hTr : 1 ≤ (T : ℝ) := by exact_mod_cast (by omega : 1 ≤ T)
  have hden : 0 < S*A*T := by positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε < 1 := by
    dsimp [ε]
    rw [div_lt_iff₀ hden]
    nlinarith [mul_nonneg (sub_nonneg.mpr hS) (sub_nonneg.mpr hA),
      mul_nonneg (sub_nonneg.mpr (show 1 ≤ S*A by nlinarith)) (sub_nonneg.mpr hTr)]
  let bad (p : State × Action × Fin T) : Set (QSamples State Action T) :=
    if T/2 < p.2.2.1+1 then (qOptimalFreedmanGood M η c₂ T (p.2.2.1+1) (by omega) p.1 p.2.1 K ε)ᶜ else ∅
  have hbad (p : State × Action × Fin T) : μ.real (bad p) ≤ ε := by
    by_cases hp : T/2 < p.2.2.1+1
    · have hgood := qOptimalFluctuation_freedman M η c₁ c₂ T (p.2.2.1+1) hT (by omega)
        hc₁ hc₂ hs p.1 p.2.1 K hK ε hε hε1
      have hc := measureReal_compl (μ := μ)
        ((Set.to_countable (qOptimalFreedmanGood M η c₂ T (p.2.2.1+1) (by omega) p.1 p.2.1 K ε)).measurableSet)
      rw [probReal_univ] at hc
      simp only [bad, hp, if_pos]
      change 1 - ε ≤ μ.real (qOptimalFreedmanGood M η c₂ T (p.2.2.1+1) (by omega) p.1 p.2.1 K ε) at hgood
      linarith
    · simp [bad, hp, hε.le]
  have hbadall : μ.real (⋃ p : State × Action × Fin T, bad p) ≤ δ := by
    calc
      _ ≤ ∑ p : State × Action × Fin T, μ.real (bad p) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _p : State × Action × Fin T, ε := Finset.sum_le_sum (fun p _ ↦ hbad p)
      _ = δ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
        change (S*(A*T))*ε = δ
        rw [show S*(A*T) = S*A*T by ring]
        dsimp [ε]
        field_simp [ne_of_gt hden]
  let target : Set (QSamples State Action T) := {data |
      ∀ (s : State) (a : Action) (j : Fin T), T/2 < j.1+1 →
        data ∈ qOptimalFreedmanGood M η c₂ T (j.1+1) (by omega) s a K ε}
  have hsub : (⋃ p : State × Action × Fin T, bad p)ᶜ ⊆ target := by
    intro data hd s a j hj
    by_contra hn
    exact hd (Set.mem_iUnion.mpr ⟨(s,a,j), by simp [bad, hj, hn]⟩)
  have hmono := measureReal_mono hsub (measure_ne_top μ target)
  have hc := measureReal_compl (μ := μ) ((Set.to_countable (⋃ p : State × Action × Fin T, bad p)).measurableSet)
  rw [probReal_univ] at hc
  change 1 - δ ≤ μ.real target
  linarith

end StatisticalRL.QLearning
