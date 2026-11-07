import Formalization.Generative.FiniteHorizonGenerativeSampling
import Formalization.Probability.FreedmanNaturalHistory
import Formalization.Probability.Variance
import Mathlib.Probability.ConditionalExpectation

/-! # Freedman's inequality for weighted one-row fluctuations of a fixed value vector

Under the finite-horizon generative-model law `FiniteHorizonGenerative.samplingLaw E T` (independent
draws `s_{t,h}(s,a) ~ P_h(·|s,a)`), fix a stage `h`, a pair `(s,a)`, a deterministic value vector `V`
and deterministic coefficients `c n`. The increments
`X_n = c_n (V(s_{n,h}(s,a)) - P_h(·|s,a) V)` (`n < T`) depend on distinct independent coordinates,
so they are conditionally centred given the prior increments with conditional second moment
`c_n² Var_{P_h(·|s,a)}(V)`. The source Freedman inequality (`lem:Freedman-prelim`,
`chapters/prelim.tex:1056–1076`, formalized as `freedman_natural_history`) with `K₀ = 1` then gives
the deterministic-radius bound below. -/

open MeasureTheory ProbabilityTheory Finset

namespace StatisticalRL.FiniteQLearning

open FiniteHorizonGenerative

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance coordFreedmanStateMeasurable : MeasurableSpace State := ⊤

/-- The increment `c_n (V(s_{n,h}(s,a)) - P V)` (zero for `n ≥ T`). -/
noncomputable def coordIncrement {H T : ℕ} (E : Fin H → EnvironmentStage State Action)
    (h : Fin H) (s : State) (a : Action) (V : State → ℝ) (c : ℕ → ℝ) (n : ℕ)
    (data : Samples State Action H T) : ℝ :=
  if hn : n < T then
    c n * (V (data ((h, s, a), ⟨n, hn⟩)) - ((E h).transition s a).expectation V)
  else 0

theorem coordIncrement_measurable {H T : ℕ} (E : Fin H → EnvironmentStage State Action)
    (h : Fin H) (s : State) (a : Action) (V : State → ℝ) (c : ℕ → ℝ) (n : ℕ) :
    Measurable (coordIncrement (T := T) E h s a V c n) :=
  measurable_of_countable _

/-- The sigma-algebra of a single coordinate. -/
abbrev coordSigma {H T : ℕ} (i : SampleIndex State Action H T) :
    MeasurableSpace (Samples State Action H T) :=
  MeasurableSpace.comap (fun data : Samples State Action H T ↦ data i) inferInstance

/-- The increment is a function of its own coordinate, and so are its powers. -/
theorem coordIncrement_measurable_own {H T : ℕ} (E : Fin H → EnvironmentStage State Action)
    (h : Fin H) (s : State) (a : Action) (V : State → ℝ) (c : ℕ → ℝ) (n : ℕ) (hn : n < T)
    (F : ℝ → ℝ) :
    Measurable[⨆ j ∈ ({((h, s, a), ⟨n, hn⟩)} : Set (SampleIndex State Action H T)), coordSigma j]
      (fun data ↦ F (coordIncrement (T := T) E h s a V c n data)) := by
  have hY : Measurable[⨆ j ∈ ({((h, s, a), ⟨n, hn⟩)} : Set (SampleIndex State Action H T)),
      coordSigma j] (fun data : Samples State Action H T ↦ data ((h, s, a), ⟨n, hn⟩)) :=
    (comap_measurable _).mono (le_iSup₂ (f := fun j (_ : j ∈ ({((h, s, a), ⟨n, hn⟩)} :
      Set (SampleIndex State Action H T))) ↦ coordSigma j) _ rfl) le_rfl
  have hF : Measurable (fun x : State ↦
      F (c n * (V x - ((E h).transition s a).expectation V))) := measurable_of_countable _
  have : (fun data ↦ F (coordIncrement (T := T) E h s a V c n data)) =
      (fun x : State ↦ F (c n * (V x - ((E h).transition s a).expectation V))) ∘
        (fun data : Samples State Action H T ↦ data ((h, s, a), ⟨n, hn⟩)) := by
    funext data
    simp [coordIncrement, hn]
  rw [this]
  exact hF.comp hY

/-- The strict prior increments only see the earlier coordinates of the same row. -/
theorem priorIncrementSigma_coord_le {H T : ℕ} (E : Fin H → EnvironmentStage State Action)
    (h : Fin H) (s : State) (a : Action) (V : State → ℝ) (c : ℕ → ℝ) (n : ℕ) :
    priorIncrementSigma (coordIncrement (T := T) E h s a V c) n ≤
      ⨆ j ∈ {j : SampleIndex State Action H T | j.1 = (h, s, a) ∧ j.2.val < n}, coordSigma j := by
  apply iSup₂_le
  intro k hk
  apply Measurable.comap_le
  by_cases hkT : k < T
  · have hY : Measurable[⨆ j ∈ {j : SampleIndex State Action H T | j.1 = (h, s, a) ∧ j.2.val < n},
        coordSigma j] (fun data : Samples State Action H T ↦ data ((h, s, a), ⟨k, hkT⟩)) :=
      (comap_measurable _).mono (le_iSup₂ (f := fun j (_ : j ∈ {j : SampleIndex State Action H T |
        j.1 = (h, s, a) ∧ j.2.val < n}) ↦ coordSigma j) ((h, s, a), ⟨k, hkT⟩) ⟨rfl, hk⟩) le_rfl
    have hF : Measurable (fun x : State ↦ c k * (V x - ((E h).transition s a).expectation V)) :=
      measurable_of_countable _
    have : coordIncrement (T := T) E h s a V c k =
        (fun x : State ↦ c k * (V x - ((E h).transition s a).expectation V)) ∘
          (fun data : Samples State Action H T ↦ data ((h, s, a), ⟨k, hkT⟩)) := by
      funext data
      simp [coordIncrement, hkT]
    rw [this]
    exact hF.comp hY
  · have : coordIncrement (T := T) E h s a V c k = fun _ ↦ 0 := by
      funext data
      simp [coordIncrement, hkT]
    rw [this]
    exact measurable_const

/-- Independence of the current increment's coordinate from the prior increments. -/
theorem coord_indep_prior {H T : ℕ} (E : Fin H → EnvironmentStage State Action)
    (h : Fin H) (s : State) (a : Action) (V : State → ℝ) (c : ℕ → ℝ) (n : ℕ) (hn : n < T) :
    Indep (⨆ j ∈ ({((h, s, a), ⟨n, hn⟩)} : Set (SampleIndex State Action H T)), coordSigma j)
      (priorIncrementSigma (coordIncrement (T := T) E h s a V c) n) (samplingLaw E T) := by
  have hind := (iIndepFun_iff_iIndep _ _ _).mp (samplingLaw_independent E T)
  have hdisj : Disjoint ({((h, s, a), ⟨n, hn⟩)} : Set (SampleIndex State Action H T))
      {j : SampleIndex State Action H T | j.1 = (h, s, a) ∧ j.2.val < n} := by
    rw [Set.disjoint_singleton_left]
    rintro ⟨-, hlt⟩
    exact lt_irrefl _ hlt
  have hle : ∀ j : SampleIndex State Action H T, coordSigma j ≤ MeasurableSpace.pi := fun j ↦
    (measurable_pi_apply j).comap_le
  exact indep_of_indep_of_le_right (indep_iSup_of_disjoint hle hind hdisj)
    (priorIncrementSigma_coord_le E h s a V c n)

theorem samplingLaw_integral_coord {H T : ℕ} (E : Fin H → EnvironmentStage State Action)
    (i : SampleIndex State Action H T) (F : State → ℝ) :
    ∫ data, F (data i) ∂samplingLaw E T = ((E i.1.1).transition i.1.2.1 i.1.2.2).expectation F := by
  rw [← FiniteDistribution.rowMeasure_integral, ← samplingLaw_marginal E T i]
  exact (integral_map (measurable_pi_apply i).aemeasurable
    (measurable_of_countable F).aestronglyMeasurable).symm

/-- Conditional expectation of a function of the current increment given the prior increments is
its (constant) mean. -/
theorem coord_condExp_eq {H T : ℕ} (E : Fin H → EnvironmentStage State Action)
    (h : Fin H) (s : State) (a : Action) (V : State → ℝ) (c : ℕ → ℝ) (n : ℕ) (hn : n < T)
    (F : ℝ → ℝ) :
    (samplingLaw E T)[fun data ↦ F (coordIncrement (T := T) E h s a V c n data) |
        priorIncrementSigma (coordIncrement (T := T) E h s a V c) n] =ᵐ[samplingLaw E T]
      fun _ ↦ ((E h).transition s a).expectation
        (fun x ↦ F (c n * (V x - ((E h).transition s a).expectation V))) := by
  have hle₁ : (⨆ j ∈ ({((h, s, a), ⟨n, hn⟩)} : Set (SampleIndex State Action H T)),
      coordSigma j) ≤ MeasurableSpace.pi :=
    iSup₂_le fun j _ ↦ (measurable_pi_apply j).comap_le
  have hle₂ : priorIncrementSigma (coordIncrement (T := T) E h s a V c) n ≤ MeasurableSpace.pi :=
    iSup₂_le fun k _ ↦ (coordIncrement_measurable E h s a V c k).comap_le
  have hci := condExp_indep_eq hle₁ hle₂
    (coordIncrement_measurable_own E h s a V c n hn F).stronglyMeasurable
    (coord_indep_prior E h s a V c n hn)
  refine hci.trans (Filter.Eventually.of_forall fun _ ↦ ?_)
  have heq : (fun data : Samples State Action H T ↦ F (coordIncrement (T := T) E h s a V c n data)) =
      fun data ↦ (fun x : State ↦ F (c n * (V x - ((E h).transition s a).expectation V)))
        (data ((h, s, a), ⟨n, hn⟩)) := by
    funext data
    simp [coordIncrement, hn]
  simp only
  rw [heq]
  exact samplingLaw_integral_coord E ((h, s, a), ⟨n, hn⟩)
    (fun x ↦ F (c n * (V x - ((E h).transition s a).expectation V)))

theorem coordIncrement_condExp_zero {H T : ℕ} (E : Fin H → EnvironmentStage State Action)
    (h : Fin H) (s : State) (a : Action) (V : State → ℝ) (c : ℕ → ℝ) (n : ℕ) :
    (samplingLaw E T)[coordIncrement (T := T) E h s a V c n |
        priorIncrementSigma (coordIncrement (T := T) E h s a V c) n] =ᵐ[samplingLaw E T]
      fun _ ↦ 0 := by
  by_cases hn : n < T
  · have hce := coord_condExp_eq E h s a V c n hn id
    simp only [id] at hce
    refine hce.trans (Filter.Eventually.of_forall fun _ ↦ ?_)
    simp only
    rw [FiniteDistribution.expectation_mul, FiniteDistribution.expectation_sub,
      FiniteDistribution.expectation_const, sub_self, mul_zero]
  · have : coordIncrement (T := T) E h s a V c n = fun _ ↦ 0 := by
      funext data; simp [coordIncrement, hn]
    rw [this, condExp_const]
    exact iSup₂_le fun k _ ↦ (coordIncrement_measurable E h s a V c k).comap_le

theorem coordIncrement_condExp_sq {H T : ℕ} (E : Fin H → EnvironmentStage State Action)
    (h : Fin H) (s : State) (a : Action) (V : State → ℝ) (c : ℕ → ℝ) (n : ℕ) :
    (samplingLaw E T)[fun data ↦ coordIncrement (T := T) E h s a V c n data ^ 2 |
        priorIncrementSigma (coordIncrement (T := T) E h s a V c) n] =ᵐ[samplingLaw E T]
      fun _ ↦ if n < T then c n ^ 2 * ((E h).transition s a).variance V else 0 := by
  by_cases hn : n < T
  · have hce := coord_condExp_eq E h s a V c n hn (fun y ↦ y ^ 2)
    refine hce.trans (Filter.Eventually.of_forall fun _ ↦ ?_)
    simp only [hn, if_true]
    rw [FiniteDistribution.variance_eq_expectation_centered_sq, ← FiniteDistribution.expectation_mul]
    congr 1
    funext x
    ring
  · have : (fun data ↦ coordIncrement (T := T) E h s a V c n data ^ 2) = fun _ ↦ 0 := by
      funext data; simp [coordIncrement, hn]
    rw [this, condExp_const]
    · simp [hn]
    exact iSup₂_le fun k _ ↦ (coordIncrement_measurable E h s a V c k).comap_le

/-- Freedman bound for the weighted row fluctuation with a deterministic radius:
if `|c n| ≤ cbar`, `|V x - P V| ≤ R` and `Σ_{n<T} c n² Var_P(V) ≤ σ`, then with probability at
least `1 - δ`,
`|Σ_{n<T} X_n| ≤ √(8 σ log(2/δ)) + (4/3) cbar R log(2/δ)`. -/
theorem coord_freedman {H T : ℕ} (E : Fin H → EnvironmentStage State Action)
    (h : Fin H) (s : State) (a : Action) (V : State → ℝ) (c : ℕ → ℝ) {cbar R σ : ℝ}
    (hcbar : ∀ n, |c n| ≤ cbar) (hR : ∀ x, |V x - ((E h).transition s a).expectation V| ≤ R)
    (hσ : (∑ n ∈ range T, c n ^ 2) * ((E h).transition s a).variance V ≤ σ)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ ≤ (samplingLaw E T).real {data |
      |∑ n ∈ range T, coordIncrement (T := T) E h s a V c n data| ≤
        Real.sqrt (8 * σ * Real.log (2 / δ)) + (4 / 3) * (cbar * R) * Real.log (2 / δ)} := by
  set μ := samplingLaw E T
  set X := coordIncrement (T := T) E h s a V c
  have hcbar0 : 0 ≤ cbar := (abs_nonneg _).trans (hcbar 0)
  have hR0 : 0 ≤ R := (abs_nonneg _).trans (hR (Classical.choice (E h).state_nonempty))
  have hvar0 := ((E h).transition s a).variance_nonneg V
  have hσ0 : 0 ≤ σ := le_trans (mul_nonneg (sum_nonneg fun n _ ↦ sq_nonneg _) hvar0) hσ
  have hb : ∀ n, ∀ᵐ ω ∂μ, |X n ω| ≤ cbar * R := fun n ↦ Filter.Eventually.of_forall fun ω ↦ by
    simp only [X, coordIncrement]
    split_ifs
    · rw [abs_mul]
      exact mul_le_mul (hcbar n) (hR _) (abs_nonneg _) hcbar0
    · simp [mul_nonneg hcbar0 hR0]
  have hW : ∀ᵐ ω ∂μ, historyPredictableVariance μ X T ω ≤ σ := by
    have hall := ae_all_iff.mpr fun n ↦ coordIncrement_condExp_sq E h s a V c n (T := T)
    filter_upwards [hall] with ω hω
    unfold historyPredictableVariance
    simp only [X] at hω ⊢
    rw [sum_congr rfl fun n _ ↦ hω n]
    calc ∑ n ∈ range T, (if n < T then c n ^ 2 * ((E h).transition s a).variance V else 0)
        = ∑ n ∈ range T, c n ^ 2 * ((E h).transition s a).variance V :=
          sum_congr rfl fun n hn ↦ by simp [mem_range.mp hn]
      _ = (∑ n ∈ range T, c n ^ 2) * ((E h).transition s a).variance V := by rw [sum_mul]
      _ ≤ σ := hσ
  have hfr := freedman_natural_history μ X (coordIncrement_measurable E h s a V c)
    (cbar * R) σ (mul_nonneg hcbar0 hR0) hσ0 hb
    (coordIncrement_condExp_zero E h s a V c) T 1 one_pos hW δ hδ hδ1
  have hL : 0 ≤ Real.log (2 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hsub : {ω | |incrementSum X T ω| ≤
      Real.sqrt (8 * max (historyPredictableVariance μ X T ω) (σ / (2 : ℝ) ^ 1) *
        Real.log (2 * ((1 : ℕ) : ℝ) / δ)) +
        (4 / 3) * (cbar * R) * Real.log (2 * ((1 : ℕ) : ℝ) / δ)} ≤ᵐ[μ]
      {data | |∑ n ∈ range T, coordIncrement (T := T) E h s a V c n data| ≤
        Real.sqrt (8 * σ * Real.log (2 / δ)) + (4 / 3) * (cbar * R) * Real.log (2 / δ)} := by
    filter_upwards [hW] with ω hω
    intro hmem
    change |incrementSum X T ω| ≤ Real.sqrt (8 * max (historyPredictableVariance μ X T ω)
      (σ / (2 : ℝ) ^ 1) * Real.log (2 * ((1 : ℕ) : ℝ) / δ)) +
        (4 / 3) * (cbar * R) * Real.log (2 * ((1 : ℕ) : ℝ) / δ) at hmem
    change |∑ n ∈ range T, coordIncrement (T := T) E h s a V c n ω| ≤ _
    simp only [Nat.cast_one, mul_one, pow_one] at hmem
    have hmax : max (historyPredictableVariance μ X T ω) (σ / 2) ≤ σ := max_le hω (by linarith)
    have hs : Real.sqrt (8 * max (historyPredictableVariance μ X T ω) (σ / 2) * Real.log (2 / δ)) ≤
        Real.sqrt (8 * σ * Real.log (2 / δ)) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right (by linarith) hL)
    have hi : incrementSum X T ω = ∑ n ∈ range T, coordIncrement (T := T) E h s a V c n ω := rfl
    rw [hi] at hmem
    linarith
  exact hfr.trans (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub))

end StatisticalRL.FiniteQLearning
