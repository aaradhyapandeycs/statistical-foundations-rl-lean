import Formalization.ModelFree.TDTerminalFreedman

/-! Finite-state union of actual fixed-terminal scalar Freedman events. Per-state
increment and variance caps and the comparisons to the chosen source scales
remain explicit inputs; the confidence allocation is `δ/(2ST)`, giving an
all-state failure bound of `δ/(2T)`. -/
namespace StatisticalRL.TemporalDifference
open MeasureTheory ProbabilityTheory
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdSourceFirstFreedmanUnionStateMeasurable : MeasurableSpace State := ⊤

/-- Finite state union of the actual fixed-terminal scalar Freedman events.
The per-state confidence is exactly `δ/(2ST)`, so the all-state failure is
exactly bounded by `δ/(2T)`. Comparisons from the source increment cap `B`,
variance floor `σ²/2^K`, and Freedman logarithm to their chosen source values
`Bsrc`, `σsrc²`, and `L` are explicit premises. -/
private theorem tdSource_firstFreedman_allStates_of_caps_of_pos
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (hTpos : 0 < T)
    (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (A Bsrc σsrcSq L δ : ℝ) (hA : 0 ≤ A)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1)
    (hcap : ∀ k, 1 ≤ k → k ≤ t → tdRateWeight M.discount η t k ≤ A)
    (hB : 2 * M.discount * M.effectiveHorizon * A ≤ Bsrc)
    (hSigma : M.discount ^ 2 * M.effectiveHorizon ^ 3 * A ≤ σsrcSq)
    (K : ℕ) (hK : 0 < K)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hLogCompare : Real.log
        (2 * (K : ℝ) / (δ / (2 * (Fintype.card State : ℝ) * T))) ≤ L) :
    1 - δ / (2 * (T : ℝ)) ≤ (tdSamplingLaw M π T).real
      {data | ∀ s : State,
        |∑ k ∈ Finset.Icc 1 t,
            tdSampledWeightedIncrement M π η T t k V₀ s data| ≤
          Real.sqrt (8 * max (tdTerminalVarianceSum M π η T t V₀ s data)
            (σsrcSq / (2 : ℝ) ^ K) * L) + (4 / 3) * Bsrc * L} := by
  classical
  letI : Nonempty State := M.state_nonempty
  let μ : Measure (TDSamples State T) := tdSamplingLaw M π T
  let S : ℝ := Fintype.card State
  let ε : ℝ := δ / (2 * S * T)
  have hS : 1 ≤ S := by
    dsimp [S]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hTreal : 1 ≤ (T : ℝ) := by exact_mod_cast hTpos
  have hST : 1 ≤ S * (T : ℝ) := by
    calc
      (1 : ℝ) ≤ (T : ℝ) := hTreal
      _ = 1 * (T : ℝ) := by ring
      _ ≤ S * (T : ℝ) := mul_le_mul_of_nonneg_right hS (by positivity)
  have hden : 0 < 2 * S * T := by positivity
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hε1 : ε < 1 := by
    dsimp [ε]
    rw [div_lt_iff₀ hden]
    nlinarith [hδ1, hST]
  have hLcoord : 0 ≤ Real.log (2 * (K : ℝ) / ε) := by
    apply Real.log_nonneg
    have harg : 1 ≤ 2 * (K : ℝ) / ε := by
      rw [le_div_iff₀ hε]
      have hKreal : 1 ≤ (K : ℝ) := by exact_mod_cast hK
      nlinarith [hε1]
    exact harg
  have hLnonneg : 0 ≤ L := hLcoord.trans hLogCompare
  have hB0 : 0 ≤ Bsrc := by
    have hcoeff : 0 ≤ 2 * M.discount * M.effectiveHorizon * A :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        M.discount_nonneg) M.effectiveHorizon_nonneg) hA
    exact hcoeff.trans hB
  have hSigma0 : 0 ≤ σsrcSq := by
    have hvar : 0 ≤ M.discount ^ 2 * M.effectiveHorizon ^ 3 * A :=
      mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg M.effectiveHorizon_nonneg 3)) hA
    exact hvar.trans hSigma
  have hvar0 : 0 ≤ M.discount ^ 2 * M.effectiveHorizon ^ 3 * A :=
    mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg M.effectiveHorizon_nonneg 3)) hA
  have hdenK : 0 < (2 : ℝ) ^ K := by positivity
  have hfloor : M.discount ^ 2 * M.effectiveHorizon ^ 3 * A / (2 : ℝ) ^ K ≤
      σsrcSq / (2 : ℝ) ^ K := div_le_div_of_nonneg_right hSigma (by positivity)
  have hlog : Real.log (2 * (K : ℝ) / ε) ≤ L := by
    simpa [ε, S, mul_assoc] using hLogCompare
  let rawGood (s : State) : Set (TDSamples State T) :=
    {data | |∑ k ∈ Finset.Icc 1 t,
      tdSampledWeightedIncrement M π η T t k V₀ s data| ≤
        Real.sqrt (8 * max (tdTerminalVarianceSum M π η T t V₀ s data)
          (M.discount ^ 2 * M.effectiveHorizon ^ 3 * A / (2 : ℝ) ^ K) *
            Real.log (2 * (K : ℝ) / ε)) +
          (4 / 3) * (2 * M.discount * M.effectiveHorizon * A) *
            Real.log (2 * (K : ℝ) / ε)}
  let good (s : State) : Set (TDSamples State T) :=
    {data | |∑ k ∈ Finset.Icc 1 t,
      tdSampledWeightedIncrement M π η T t k V₀ s data| ≤
        Real.sqrt (8 * max (tdTerminalVarianceSum M π η T t V₀ s data)
          (σsrcSq / (2 : ℝ) ^ K) * L) + (4 / 3) * Bsrc * L}
  have hRadius (s : State) (data : TDSamples State T) :
      Real.sqrt (8 * max (tdTerminalVarianceSum M π η T t V₀ s data)
        (M.discount ^ 2 * M.effectiveHorizon ^ 3 * A / (2 : ℝ) ^ K) *
          Real.log (2 * (K : ℝ) / ε)) +
        (4 / 3) * (2 * M.discount * M.effectiveHorizon * A) *
          Real.log (2 * (K : ℝ) / ε) ≤
      Real.sqrt (8 * max (tdTerminalVarianceSum M π η T t V₀ s data)
        (σsrcSq / (2 : ℝ) ^ K) * L) + (4 / 3) * Bsrc * L := by
    have hmax : max (tdTerminalVarianceSum M π η T t V₀ s data)
        (M.discount ^ 2 * M.effectiveHorizon ^ 3 * A / (2 : ℝ)^K) ≤
        max (tdTerminalVarianceSum M π η T t V₀ s data) (σsrcSq / (2 : ℝ)^K) :=
      max_le_max le_rfl hfloor
    have hmax0 : 0 ≤ max (tdTerminalVarianceSum M π η T t V₀ s data)
        (M.discount ^ 2 * M.effectiveHorizon ^ 3 * A / (2 : ℝ)^K) :=
      le_trans (div_nonneg hvar0 (by positivity)) (le_max_right _ _)
    have hmaxSrc0 : 0 ≤ max (tdTerminalVarianceSum M π η T t V₀ s data)
        (σsrcSq / (2 : ℝ)^K) :=
      le_trans (div_nonneg hSigma0 (by positivity)) (le_max_right _ _)
    have hrootArg :
        8 * max (tdTerminalVarianceSum M π η T t V₀ s data)
            (M.discount ^ 2 * M.effectiveHorizon ^ 3 * A / (2 : ℝ)^K) *
            Real.log (2 * (K : ℝ) / ε) ≤
        8 * max (tdTerminalVarianceSum M π η T t V₀ s data)
            (σsrcSq / (2 : ℝ)^K) * L := by
      calc
        _ ≤ 8 * max (tdTerminalVarianceSum M π η T t V₀ s data)
              (σsrcSq / (2 : ℝ)^K) * Real.log (2 * (K : ℝ) / ε) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hmax (by norm_num)) hLcoord
        _ ≤ _ := mul_le_mul_of_nonneg_left hlog (by positivity)
    have hroot := Real.sqrt_le_sqrt hrootArg
    have hlinear1 := mul_le_mul_of_nonneg_right hB hLcoord
    have hlinear2 := mul_le_mul_of_nonneg_left hlinear1 (by norm_num : (0 : ℝ) ≤ 4 / 3)
    have hlinear3 := mul_le_mul_of_nonneg_left hlog (by positivity :
      (0 : ℝ) ≤ (4 / 3) * Bsrc)
    nlinarith [hroot, hlinear2, hlinear3]
  have hgoodProb (s : State) : 1 - ε ≤ μ.real (good s) := by
    have hraw := tdTerminal_freedman_weightEnvelope M π η T t ht V₀ h₀ s A hA hη hcap
      K hK ε hε hε1
    have hrawProb : 1 - ε ≤ μ.real (rawGood s) := by
      simpa [μ, rawGood] using hraw
    have hsub : rawGood s ≤ᵐ[μ] good s := by
      filter_upwards with data hraw
      simpa only [Set.mem_setOf_eq] using hraw.trans (hRadius s data)
    have hmono := ENNReal.toReal_mono (measure_ne_top μ (good s)) (measure_mono_ae hsub)
    exact hrawProb.trans hmono
  let bad (s : State) : Set (TDSamples State T) := (good s)ᶜ
  have hbad (s : State) : μ.real (bad s) ≤ ε := by
    have hc := measureReal_compl (μ := μ) ((Set.to_countable (good s)).measurableSet)
    rw [probReal_univ] at hc
    simp only [bad]
    have hgp := hgoodProb s
    change 1 - ε ≤ μ.real (good s) at hgp
    linarith
  let badUnion : Set (TDSamples State T) := ⋃ s : State, bad s
  have hbadUnion : μ.real badUnion ≤ δ / (2 * (T : ℝ)) := by
    calc
      _ ≤ ∑ s : State, μ.real (bad s) := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _s : State, ε := Finset.sum_le_sum fun s _ ↦ hbad s
      _ = δ / (2 * (T : ℝ)) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        dsimp [ε, S]
        field_simp
  let target : Set (TDSamples State T) := {data | ∀ s : State, data ∈ good s}
  have hsub : badUnionᶜ ⊆ target := by
    intro data hnot s
    by_contra hbad'
    exact hnot (Set.mem_iUnion.mpr ⟨s, hbad'⟩)
  have hmono := measureReal_mono hsub (measure_ne_top μ target)
  have hc := measureReal_compl (μ := μ) ((Set.to_countable badUnion).measurableSet)
  rw [probReal_univ] at hc
  change 1 - δ / (2 * (T : ℝ)) ≤ μ.real target
  linarith

/-- The cap-union result also includes the degenerate zero-sample experiment:
both finite sums are empty there. For positive sample sizes the private
helper uses the strictly positive per-state confidence level. -/
theorem tdSource_firstFreedman_allStates_of_caps
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T)
    (V₀ : State → ℝ)
    (h₀ : ∀ s, 0 ≤ V₀ s ∧ V₀ s ≤ M.effectiveHorizon)
    (A Bsrc σsrcSq L δ : ℝ) (hA : 0 ≤ A)
    (hη : ∀ i, 1 ≤ i → i ≤ t → 0 ≤ η i ∧ η i ≤ 1)
    (hcap : ∀ k, 1 ≤ k → k ≤ t → tdRateWeight M.discount η t k ≤ A)
    (hB : 2 * M.discount * M.effectiveHorizon * A ≤ Bsrc)
    (hSigma : M.discount ^ 2 * M.effectiveHorizon ^ 3 * A ≤ σsrcSq)
    (K : ℕ) (hK : 0 < K)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hLogCompare : Real.log
        (2 * (K : ℝ) / (δ / (2 * (Fintype.card State : ℝ) * T))) ≤ L) :
    1 - δ / (2 * (T : ℝ)) ≤ (tdSamplingLaw M π T).real
      {data | ∀ s : State,
        |∑ k ∈ Finset.Icc 1 t,
            tdSampledWeightedIncrement M π η T t k V₀ s data| ≤
          Real.sqrt (8 * max (tdTerminalVarianceSum M π η T t V₀ s data)
            (σsrcSq / (2 : ℝ) ^ K) * L) + (4 / 3) * Bsrc * L} := by
  classical
  by_cases hTzero : T = 0
  · subst T
    have htzero : t = 0 := by omega
    have hL : 0 ≤ L := by simpa using hLogCompare
    have hB0 : 0 ≤ Bsrc := by
      have hcoeff : 0 ≤ 2 * M.discount * M.effectiveHorizon * A :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
          M.discount_nonneg) M.effectiveHorizon_nonneg) hA
      exact hcoeff.trans hB
    have hSigma0 : 0 ≤ σsrcSq := by
      have hcoeff : 0 ≤ M.discount ^ 2 * M.effectiveHorizon ^ 3 * A :=
        mul_nonneg (mul_nonneg (sq_nonneg _)
          (pow_nonneg M.effectiveHorizon_nonneg 3)) hA
      exact hcoeff.trans hSigma
    have htarget : {data | ∀ s : State,
        |∑ k ∈ Finset.Icc 1 t,
            tdSampledWeightedIncrement M π η 0 t k V₀ s data| ≤
          Real.sqrt (8 * max (tdTerminalVarianceSum M π η 0 t V₀ s data)
            (σsrcSq / (2 : ℝ) ^ K) * L) + (4 / 3) * Bsrc * L} = Set.univ := by
      ext data
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro s
      subst t
      have hsum : (∑ k ∈ Finset.Icc 1 0,
          tdSampledWeightedIncrement M π η 0 0 k V₀ s data) = 0 := by simp
      have hvar : tdTerminalVarianceSum M π η 0 0 V₀ s data = 0 := by
        simp [tdTerminalVarianceSum, StatisticalRL.predictableSecondMomentSum]
      have hfloor : 0 ≤ σsrcSq / (2 : ℝ) ^ K := div_nonneg hSigma0 (by positivity)
      have hmax : 0 ≤ max (0 : ℝ) (σsrcSq / (2 : ℝ) ^ K) := le_max_left _ _
      have harg : 0 ≤ 8 * max (0 : ℝ) (σsrcSq / (2 : ℝ) ^ K) * L := by positivity
      have hlinear : 0 ≤ (4 / 3 : ℝ) * Bsrc * L :=
        mul_nonneg (mul_nonneg (by norm_num) hB0) hL
      have hradius : 0 ≤ Real.sqrt
          (8 * max (0 : ℝ) (σsrcSq / (2 : ℝ) ^ K) * L) +
            (4 / 3 : ℝ) * Bsrc * L :=
        add_nonneg (Real.sqrt_nonneg _) hlinear
      simpa [hsum, hvar] using hradius
    rw [htarget, probReal_univ]
    simp
  · exact tdSource_firstFreedman_allStates_of_caps_of_pos
      M π η T t ht (Nat.pos_of_ne_zero hTzero) V₀ h₀ A Bsrc σsrcSq L δ hA
      hη hcap hB hSigma K hK δ hδ hδ1 hLogCompare

end StatisticalRL.TemporalDifference
