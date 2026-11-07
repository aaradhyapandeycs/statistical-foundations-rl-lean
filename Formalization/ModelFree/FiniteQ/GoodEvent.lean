import Formalization.ModelFree.FiniteQ.CoordFreedman
import Formalization.ModelFree.FiniteQ.Propagation

/-! # Probability of the good event

For the actual sampled stage list, every fluctuation entering `AllGood` is a weighted row sum
handled by `coord_freedman`. A union bound over the `2·H·S·A·T` tuples
`(sign, h, s, a, t)` (with `t = 0` trivial) gives probability at least `1 - 2HSAT δ'`. -/

open MeasureTheory ProbabilityTheory Finset

namespace StatisticalRL.FiniteQLearning

open FiniteHorizonGenerative

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance goodEventStateMeasurable : MeasurableSpace State := ⊤

/-- Stage `h` of the sampled stage list. -/
def sampledStage {H : ℕ} (E : Fin H → EnvironmentStage State Action) (T : ℕ)
    (Q₀ : Fin H → State → Action → ℝ) (data : Samples State Action H T) (h : Fin H) :
    LearningStage State Action where
  env := E h
  sample := fun t s a ↦ if ht : t < T then data ((h, s, a), ⟨t, ht⟩) else s
  init := Q₀ h

theorem sampledStages_getElem {H : ℕ} (E : Fin H → EnvironmentStage State Action) (T : ℕ)
    (Q₀ : Fin H → State → Action → ℝ) (data : Samples State Action H T) (k : ℕ)
    (hk : k < (sampledStages E T Q₀ data).length) :
    (sampledStages E T Q₀ data)[k] =
      sampledStage E T Q₀ data ⟨k, by simpa [sampledStages] using hk⟩ := by
  simp [sampledStages, sampledStage]

theorem sampledStages_drop_env {H : ℕ} (E : Fin H → EnvironmentStage State Action) (T : ℕ)
    (Q₀ : Fin H → State → Action → ℝ) (data : Samples State Action H T) (n : ℕ) :
    ((sampledStages E T Q₀ data).drop n).map LearningStage.env = (List.ofFn E).drop n := by
  rw [List.map_drop]
  congr 1
  simp [sampledStages, List.map_ofFn, Function.comp_def]

/-- Reindexing the late window `(t₀, t]` as zero-based sample indices `n < T`. -/
theorem sum_Ioc_eq_sum_range_ite (t₀ t T : ℕ) (ht : t ≤ T) (g : ℕ → ℝ) :
    ∑ i ∈ Ioc t₀ t, g i = ∑ n ∈ range T, if t₀ < n + 1 ∧ n + 1 ≤ t then g (n + 1) else 0 := by
  rw [← sum_filter]
  refine sum_nbij' (fun i ↦ i - 1) (fun n ↦ n + 1) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [mem_Ioc, mem_filter, mem_range] at hi ⊢
    omega
  · intro n hn
    simp only [mem_Ioc, mem_filter, mem_range] at hn ⊢
    omega
  · intro i hi
    simp only [mem_Ioc] at hi
    dsimp only
    omega
  · intro n _
    simp
  · intro i hi
    simp only [mem_Ioc] at hi
    dsimp only
    congr 1
    omega

/-- The coefficient of sample index `n` in the fluctuation at terminal iteration `t`. -/
noncomputable def fluctCoeff (η : ℕ → ℝ) (t₀ t : ℕ) (n : ℕ) : ℝ :=
  if t₀ < n + 1 ∧ n + 1 ≤ t then weight η (n + 1) t else 0

theorem fluct_sampledStage_eq {H : ℕ} (E : Fin H → EnvironmentStage State Action) (T : ℕ)
    (Q₀ : Fin H → State → Action → ℝ) (data : Samples State Action H T) (h : Fin H)
    (η : ℕ → ℝ) (t₀ t : ℕ) (ht : t ≤ T) (V : State → ℝ) (s : State) (a : Action) :
    fluct η t₀ (sampledStage E T Q₀ data h) V s a t =
      ∑ n ∈ range T, coordIncrement (T := T) E h s a V (fluctCoeff η t₀ t) n data := by
  unfold fluct
  rw [sum_Ioc_eq_sum_range_ite t₀ t T ht]
  refine sum_congr rfl fun n hn ↦ ?_
  have hnT := mem_range.mp hn
  simp only [coordIncrement, hnT, dif_pos, fluctCoeff, sampledStage, Nat.add_sub_cancel]
  split_ifs <;> simp

theorem sum_fluctCoeff_sq_le {η : ℕ → ℝ} {t₀ t T : ℕ} (ht : t ≤ T) (h : UnitRates η t₀ t)
    {ηbar : ℝ} (hbar0 : 0 ≤ ηbar) (hbar : ∀ i, t₀ < i → i ≤ t → η i ≤ ηbar) :
    ∑ n ∈ range T, fluctCoeff η t₀ t n ^ 2 ≤ ηbar := by
  by_cases ht₀ : t₀ ≤ t
  · have := sum_weight_sq_le ht₀ h hbar0 hbar
    rw [sum_Ioc_eq_sum_range_ite t₀ t T ht] at this
    refine le_of_eq_of_le (sum_congr rfl fun n _ ↦ ?_) this
    unfold fluctCoeff
    split_ifs <;> simp
  · have : ∀ n, fluctCoeff η t₀ t n = 0 := fun n ↦ by
      unfold fluctCoeff; rw [if_neg (by omega)]
    simp [this, hbar0]

theorem abs_fluctCoeff_le {η : ℕ → ℝ} {t₀ t : ℕ} (h : UnitRates η t₀ t) {ηbar : ℝ}
    (hbar0 : 0 ≤ ηbar) (hbar : ∀ i, t₀ < i → i ≤ t → η i ≤ ηbar) (n : ℕ) :
    |fluctCoeff η t₀ t n| ≤ ηbar := by
  unfold fluctCoeff
  split_ifs with hn
  · have hmem : n + 1 ∈ Ioc t₀ t := mem_Ioc.mpr hn
    rw [abs_of_nonneg (weight_nonneg h hmem)]
    exact (weight_le_rate h hmem).trans (hbar _ hn.1 hn.2)
  · simpa using hbar0

/-- One tuple: with probability at least `1 - δ'`, the fluctuation of a fixed value vector with
centred deviation at most `K` is at most `√(ρ Var) + ρK`, `ρ = 8 η̄ log(2/δ')`. -/
theorem fluct_good_prob {H T : ℕ} (E : Fin H → EnvironmentStage State Action)
    (Q₀ : Fin H → State → Action → ℝ) (η : ℕ → ℝ) (t₀ t : ℕ) (ht : t ≤ T)
    (hη : UnitRates η t₀ T) {ηbar K : ℝ} (hbar0 : 0 ≤ ηbar)
    (hbar : ∀ i, t₀ < i → i ≤ T → η i ≤ ηbar) (hK : 0 ≤ K)
    (h : Fin H) (s : State) (a : Action) (V : State → ℝ)
    (hV : ∀ x, |V x - ((E h).transition s a).expectation V| ≤ K)
    (δ' : ℝ) (hδ' : 0 < δ') (hδ'1 : δ' < 1) :
    1 - δ' ≤ (samplingLaw E T).real {data |
      |fluct η t₀ (sampledStage E T Q₀ data h) V s a t| ≤
        Real.sqrt (8 * ηbar * Real.log (2 / δ') * ((E h).transition s a).variance V) +
          8 * ηbar * Real.log (2 / δ') * K} := by
  have hunit : UnitRates η t₀ t := hη.mono ht
  have hbar' : ∀ i, t₀ < i → i ≤ t → η i ≤ ηbar := fun i hi hit ↦ hbar i hi (hit.trans ht)
  have hvar0 := ((E h).transition s a).variance_nonneg V
  have hσ : (∑ n ∈ range T, fluctCoeff η t₀ t n ^ 2) * ((E h).transition s a).variance V ≤
      ηbar * ((E h).transition s a).variance V :=
    mul_le_mul_of_nonneg_right (sum_fluctCoeff_sq_le ht hunit hbar0 hbar') hvar0
  have hfr := coord_freedman E h s a V (fluctCoeff η t₀ t)
    (abs_fluctCoeff_le hunit hbar0 hbar') hV hσ δ' hδ' hδ'1
  have hL : 0 ≤ Real.log (2 / δ') := Real.log_nonneg (by rw [le_div_iff₀ hδ']; linarith)
  refine hfr.trans (measureReal_mono (fun data hdata ↦ ?_))
  simp only [Set.mem_setOf_eq] at hdata ⊢
  rw [fluct_sampledStage_eq E T Q₀ data h η t₀ t ht V s a]
  have hsq : 8 * (ηbar * ((E h).transition s a).variance V) * Real.log (2 / δ') =
      8 * ηbar * Real.log (2 / δ') * ((E h).transition s a).variance V := by ring
  rw [hsq] at hdata
  have : (4 / 3) * (ηbar * K) * Real.log (2 / δ') ≤ 8 * ηbar * Real.log (2 / δ') * K := by
    have := mul_nonneg (mul_nonneg hbar0 hK) hL
    nlinarith
  linarith

/-- The good event of the actual algorithm has probability at least `1 - 2 H S A T δ'`. -/
theorem allGood_sampled_prob {H T : ℕ} (E : Fin H → EnvironmentStage State Action)
    (Q₀ : Fin H → State → Action → ℝ) (η : ℕ → ℝ) (t₀ : ℕ) (hη : UnitRates η t₀ T)
    {ηbar K : ℝ} (hbar0 : 0 ≤ ηbar) (hbar : ∀ i, t₀ < i → i ≤ T → η i ≤ ηbar) (hK : (H : ℝ) ≤ K)
    (δ' : ℝ) (hδ' : 0 < δ') (hδ'1 : δ' < 1) :
    1 - 2 * H * Fintype.card State * Fintype.card Action * T * δ' ≤
      (samplingLaw E T).real {data |
        AllGood η t₀ T (8 * ηbar * Real.log (2 / δ')) K (sampledStages E T Q₀ data)} := by
  classical
  set μ := samplingLaw E T
  set ρ := 8 * ηbar * Real.log (2 / δ') with hρ
  have hL : 0 ≤ Real.log (2 / δ') := Real.log_nonneg (by rw [le_div_iff₀ hδ']; linarith)
  have hρ0 : 0 ≤ ρ := by positivity
  have hK0 : 0 ≤ K := le_trans (Nat.cast_nonneg H) hK
  -- the value vector of each tuple
  let Vf : Bool → Fin H → State → ℝ := fun flag h ↦
    if flag then plusV ρ (2 * ρ * K) ((List.ofFn E).drop (h.val + 1))
    else minusV ρ (2 * ρ * K) ((List.ofFn E).drop (h.val + 1))
  have hVf : ∀ flag (h : Fin H) s a x,
      |Vf flag h x - ((E h).transition s a).expectation (Vf flag h)| ≤ K := by
    intro flag h s a x
    letI : Nonempty Action := (E h).action_nonempty
    have hlen : (((List.ofFn E).drop (h.val + 1)).length : ℝ) ≤ K := by
      simp only [List.length_drop, List.length_ofFn]
      exact le_trans (by exact_mod_cast Nat.sub_le H (h.val + 1)) hK
    cases flag
    · exact (minusV_centered_le hρ0 _ _ x).trans hlen
    · exact (plusV_centered_le hρ0 _ _ x).trans hlen
  let good : Bool × Fin H × State × Action × Fin T → Set (Samples State Action H T) := fun p ↦
    {data | |fluct η t₀ (sampledStage E T Q₀ data p.2.1) (Vf p.1 p.2.1) p.2.2.1 p.2.2.2.1
        (p.2.2.2.2.val + 1)| ≤
      Real.sqrt (ρ * ((E p.2.1).transition p.2.2.1 p.2.2.2.1).variance (Vf p.1 p.2.1)) + ρ * K}
  have hgood : ∀ p, 1 - δ' ≤ μ.real (good p) := fun p ↦
    fluct_good_prob E Q₀ η t₀ (p.2.2.2.2.val + 1) p.2.2.2.2.isLt hη hbar0 hbar hK0 p.2.1 p.2.2.1
      p.2.2.2.1 (Vf p.1 p.2.1) (hVf p.1 p.2.1 p.2.2.1 p.2.2.2.1) δ' hδ' hδ'1
  have hbad : ∀ p, μ.real (good p)ᶜ ≤ δ' := fun p ↦ by
    have hc := measureReal_compl (μ := μ) (Set.to_countable (good p)).measurableSet
    rw [probReal_univ] at hc
    linarith [hgood p]
  have hunion : μ.real (⋃ p, (good p)ᶜ) ≤ 2 * H * Fintype.card State * Fintype.card Action * T * δ' :=
    calc μ.real (⋃ p, (good p)ᶜ) ≤ ∑ p, μ.real (good p)ᶜ := measureReal_iUnion_fintype_le _
      _ ≤ ∑ _p : Bool × Fin H × State × Action × Fin T, δ' := sum_le_sum fun p _ ↦ hbad p
      _ = 2 * H * Fintype.card State * Fintype.card Action * T * δ' := by
        simp only [sum_const, card_univ, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin,
          nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
        ring
  have hsub : (⋃ p, (good p)ᶜ)ᶜ ⊆ {data | AllGood η t₀ T ρ K (sampledStages E T Q₀ data)} := by
    intro data hdata
    simp only [Set.compl_iUnion, compl_compl, Set.mem_iInter] at hdata
    simp only [Set.mem_setOf_eq]
    rw [allGood_iff]
    intro k hk s a t htT
    have hkH : k < H := by simpa [sampledStages] using hk
    rw [sampledStages_getElem, sampledStages_drop_env]
    cases t with
    | zero =>
      have hz : ∀ V, fluct η t₀ (sampledStage E T Q₀ data ⟨k, hkH⟩) V s a 0 = 0 := fun V ↦ by
        unfold fluct
        rw [Finset.Ioc_eq_empty (by omega), sum_empty]
      simp only [hz, abs_zero]
      exact ⟨by positivity, by positivity⟩
    | succ t' =>
      have hp := hdata (true, ⟨k, hkH⟩, s, a, ⟨t', by omega⟩)
      have hm := hdata (false, ⟨k, hkH⟩, s, a, ⟨t', by omega⟩)
      simp only [good, Set.mem_setOf_eq, Vf, if_true] at hp hm
      exact ⟨hp, hm⟩
  have hc := measureReal_compl (μ := μ) (Set.to_countable (⋃ p, (good p)ᶜ)).measurableSet
  rw [probReal_univ] at hc
  have hmono := measureReal_mono hsub (measure_ne_top μ _)
  linarith

end StatisticalRL.FiniteQLearning
