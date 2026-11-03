import Formalization.ModelFree.TDPropagatorRows

/-! Zero-tail extension of a finite-horizon TD schedule preserves all used-through-T objects and supplies global rate bounds. -/

open scoped BigOperators
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The finite-horizon schedule extension: preserve every source rate through
T, including the unused index zero, and set only the tail to zero. -/
def tdSourceRateExtend (T : ℕ) (η : ℕ → ℝ) : ℕ → ℝ :=
  fun i ↦ if i ≤ T then η i else 0

/-- Finite source schedule from Eq. `thm:eta-TD`, restricted to the indices
actually specified by the source. -/
def tdSourceRateSchedule (γ c₁ c₂ : ℝ) (T : ℕ) (η : ℕ → ℝ) : Prop :=
  ∀ i, 1 ≤ i → i ≤ T →
    1 / (1 + c₁ * (1 - γ) * T / Real.log (T : ℝ) ^ 2) ≤ η i ∧
      η i ≤ 1 / (1 + c₂ * (1 - γ) * i / Real.log (T : ℝ) ^ 2)

theorem tdSourceRateExtend_eq {T i : ℕ} (η : ℕ → ℝ) (hi : i ≤ T) :
    tdSourceRateExtend T η i = η i := by
  simp [tdSourceRateExtend, hi]

/-- A source schedule specified on positive indices through T yields a global
unit-interval premise after the zero-tail extension. -/
theorem tdSourceRateExtend_unit_interval (T : ℕ) (η : ℕ → ℝ)
    (hη : ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1) :
    ∀ i, 1 ≤ i → 0 ≤ tdSourceRateExtend T η i ∧
      tdSourceRateExtend T η i ≤ 1 := by
  intro i hi
  by_cases hit : i ≤ T
  · simpa [tdSourceRateExtend, hit] using hη i hi hit
  · simp [tdSourceRateExtend, hit]

/-- The source's finite schedule gives the unit interval on every used
positive rate, with the unused zero coordinate omitted. -/
theorem tdSourceRateSchedule_unit_interval (γ c₁ c₂ : ℝ) (T : ℕ)
    (hT : 2 ≤ T) (hγ1 : γ < 1)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (η : ℕ → ℝ)
    (hSched : tdSourceRateSchedule γ c₁ c₂ T η) :
    ∀ i, 1 ≤ i → i ≤ T → 0 ≤ η i ∧ η i ≤ 1 := by
  intro i hi hit
  have hgap : 0 < 1 - γ := by linarith
  have hlog : 0 < Real.log (T : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < T)
  have hlogSq : 0 < Real.log (T : ℝ) ^ 2 := sq_pos_of_pos hlog
  have hiR : 0 < (i : ℝ) := by exact_mod_cast (by omega : 0 < i)
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hloDen : 0 < 1 + c₁ * (1 - γ) * T / Real.log (T : ℝ) ^ 2 := by
    positivity
  have hhiDen : 0 < 1 + c₂ * (1 - γ) * i / Real.log (T : ℝ) ^ 2 := by
    positivity
  have hhiOne : 1 < 1 + c₂ * (1 - γ) * i / Real.log (T : ℝ) ^ 2 := by
    have hterm : 0 < c₂ * (1 - γ) * i / Real.log (T : ℝ) ^ 2 := by positivity
    linarith
  have hrecip : 1 / (1 + c₂ * (1 - γ) * i / Real.log (T : ℝ) ^ 2) ≤ 1 := by
    rw [div_le_iff₀ hhiDen]
    nlinarith
  have hs := hSched i hi hit
  constructor
  · have hpositive :
        0 < 1 + c₁ * (1 - γ) * T / Real.log (T : ℝ) ^ 2 := hloDen
    have hrecipPos :
        0 < 1 / (1 + c₁ * (1 - γ) * T / Real.log (T : ℝ) ^ 2) :=
      div_pos (by norm_num) hpositive
    exact le_trans hrecipPos.le hs.1
  · exact le_trans hs.2 hrecip

/-- Every source-eligible terminal has the explicit uniform late-rate
envelope `2 log^3(T)/((1−γ)T)`, directly from the schedule's upper bound. -/
theorem tdSourceRateSchedule_eligible_late_le
    (γ c₁ c₂ : ℝ) (T t k : ℕ) (hT : 2 ≤ T) (ht : t ≤ T)
    (hγ1 : γ < 1) (hc₂ : 0 < c₂)
    (η : ℕ → ℝ) (hSched : tdSourceRateSchedule γ c₁ c₂ T η)
    (hEligible : (T : ℝ) /
        (c₂ * Real.log (T : ℝ)) ≤ (t : ℝ))
    (hLate : t / 2 + 1 ≤ k) (hkt : k ≤ t) :
    η k ≤ 2 * Real.log (T : ℝ) ^ 3 /
      ((1 - γ) * T) := by
  have hgap : 0 < 1 - γ := by linarith
  have hlog : 0 < Real.log (T : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (by omega : 1 < T)
  have hlogSq : 0 < Real.log (T : ℝ) ^ 2 := sq_pos_of_pos hlog
  have hden : 0 < c₂ * Real.log (T : ℝ) := mul_pos hc₂ hlog
  have hkpos : 0 < (k : ℝ) := by
    have : 0 < k := by omega
    exact_mod_cast this
  have hkreal : (t : ℝ) < 2 * (k : ℝ) := by
    have hn : t < 2 * k := by omega
    exact_mod_cast hn
  have hTbyk : (T : ℝ) < 2 * c₂ * Real.log (T : ℝ) * k := by
    have he := (div_le_iff₀ hden).mp hEligible
    have hlt := mul_lt_mul_of_pos_right hkreal hden
    nlinarith [he, hlt]
  have hs := hSched k (by omega) (le_trans hkt ht)
  have hrateDen : 0 < c₂ * (1 - γ) * k / Real.log (T : ℝ) ^ 2 := by
    positivity
  have hrateDenOne : 0 < 1 + c₂ * (1 - γ) * k / Real.log (T : ℝ) ^ 2 := by
    linarith
  have hrecip :
      1 / (1 + c₂ * (1 - γ) * k / Real.log (T : ℝ) ^ 2) ≤
        Real.log (T : ℝ) ^ 2 / (c₂ * (1 - γ) * k) := by
    calc
      _ ≤ 1 / (c₂ * (1 - γ) * k / Real.log (T : ℝ) ^ 2) := by
        rw [div_le_div_iff₀ hrateDenOne hrateDen]
        nlinarith
      _ = _ := by
        field_simp [ne_of_gt hrateDen, ne_of_gt hlogSq]
  have hfrac : Real.log (T : ℝ) ^ 2 / (c₂ * (1 - γ) * k) ≤
      2 * Real.log (T : ℝ) ^ 3 / ((1 - γ) * T) := by
    apply (div_le_div_iff₀ (mul_pos (mul_pos hc₂ hgap) hkpos)
      (mul_pos hgap (by exact_mod_cast (by omega : 0 < T)))).2
    have hmult := mul_lt_mul_of_pos_left hTbyk
      (mul_pos hgap hlogSq)
    nlinarith [hmult]
  exact (hs.2.trans (hrecip.trans hfrac))

/-- The realized iterate at each time up to T is unchanged pointwise in the
sample array by the zero-tail extension. -/
theorem tdIterate_eq_sourceRateExtend (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ)
    (samples : ℕ → State → State) (V₀ : State → ℝ) (T t : ℕ) (ht : t ≤ T) :
    tdIterate M π (tdSourceRateExtend T η) samples V₀ t =
      tdIterate M π η samples V₀ t := by
  apply tdIterate_eq_of_rates_agree
  intro i hi hit
  rw [tdSourceRateExtend_eq η (le_trans hit ht)]

/-- The actual source scalar contraction factor is unchanged for every update
index through T. -/
theorem tdRateContraction_eq_sourceRateExtend (γ : ℝ) (η : ℕ → ℝ)
    (T i : ℕ) (hi : i ≤ T) :
    tdRateContraction γ (tdSourceRateExtend T η) i =
      tdRateContraction γ η i := by
  unfold tdRateContraction
  rw [tdSourceRateExtend_eq η hi]

/-- Exact source weights at every terminal t≤T are unchanged. This includes
the initial k=0 weight and every propagator factor in its finite product. -/
theorem tdRateWeight_eq_sourceRateExtend (γ : ℝ) (η : ℕ → ℝ)
    (T t k : ℕ) (ht : t ≤ T) :
    tdRateWeight γ (tdSourceRateExtend T η) t k = tdRateWeight γ η t k := by
  unfold tdRateWeight
  by_cases hkt : k ≤ t
  · simp only [if_pos hkt]
    congr 1
    · by_cases hk0 : k = 0
      · simp [hk0]
      · simp only [if_neg hk0]
        exact tdSourceRateExtend_eq η (le_trans hkt ht)
    · apply Finset.prod_congr rfl
      intro i hi
      have hii := Finset.mem_Icc.mp hi
      exact tdRateContraction_eq_sourceRateExtend γ η T i (le_trans hii.2 ht)
  · simp [hkt]

/-- A single actual transition agrees whenever its update-rate coordinates
agree; this is the local step for propagator preservation. -/
theorem tdErrorTransition_eq_of_rate_eq (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η ζ : ℕ → ℝ) (i : ℕ)
    (hi : η i = ζ i) (U : State → ℝ) :
    tdErrorTransition M π η i U = tdErrorTransition M π ζ i U := by
  funext s
  simp [tdErrorTransition, hi]

/-- Every chronological actual-error propagator ending by T is unchanged.
The proof follows its recursive update order and uses only rates at indices
`start+1,…,t`. -/
theorem tdErrorPropagate_eq_sourceRateExtend (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T start t : ℕ)
    (ht : t ≤ T) (U : State → ℝ) :
    tdErrorPropagate M π (tdSourceRateExtend T η) start t U =
      tdErrorPropagate M π η start t U := by
  induction t with
  | zero => rfl
  | succ t ih =>
    by_cases hs : start ≤ t
    · rw [tdErrorPropagate_succ M π (tdSourceRateExtend T η) start t hs U,
        tdErrorPropagate_succ M π η start t hs U, ih (by omega)]
      apply tdErrorTransition_eq_of_rate_eq
      exact tdSourceRateExtend_eq η (by omega)
    · simp [tdErrorPropagate, hs]

/-- The actual finite-horizon propagator rows, and hence their matrix action,
are unchanged through T. -/
theorem tdPropagatorRow_eq_sourceRateExtend (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T start t : ℕ)
    (ht : t ≤ T) (s r : State) :
    tdPropagatorRow M π (tdSourceRateExtend T η) start t s r =
      tdPropagatorRow M π η start t s r := by
  classical
  unfold tdPropagatorRow
  exact congrArg (fun f : State → ℝ ↦ f s)
    (tdErrorPropagate_eq_sourceRateExtend M π η T start t ht
      (fun x ↦ if x = r then 1 else 0))

/-- The weighted actual propagator row preserves its explicit γη_k factor as
well as the suffix row. -/
theorem tdWeightedPropagatorRow_eq_sourceRateExtend
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t k : ℕ) (hkt : k ≤ t) (ht : t ≤ T) (s r : State) :
    tdWeightedPropagatorRow M π (tdSourceRateExtend T η) t k s r =
      tdWeightedPropagatorRow M π η t k s r := by
  unfold tdWeightedPropagatorRow
  rw [tdSourceRateExtend_eq η (le_trans hkt ht),
    tdPropagatorRow_eq_sourceRateExtend M π η T k t ht s r]

end StatisticalRL.TemporalDifference
