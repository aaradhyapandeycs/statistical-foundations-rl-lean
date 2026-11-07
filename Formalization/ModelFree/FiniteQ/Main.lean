import Formalization.ModelFree.FiniteQ.GoodEvent
import Formalization.ModelFree.FiniteQ.Arithmetic

/-! # Theorem 4.13: finite-horizon synchronous Q-learning with a generative model

Source: `thm:finite-horizon-simple-Q-generative`,
`source/upstream/tex/chapters/generative_model_model_free.tex:2215–2236`, with the schedule
`eq:thm:finite-horizaon-eta` (:2203–2209), the sample-size condition `eq:thm:finite-horizon-T`
(:2220–2223) and the algorithm `eqn:q-learning-finite` (:2172–2200). The monograph cites
`li2021tightening-icml` and gives no proof; the proof here is self-contained (see the module
docstrings of the imported files).

Constants: every `c₁ ∈ (0, 1/64]` and `c₂ ∈ (0, c₁]` work with `c₃ = 8000 / c₂`. The theorem
assumes `2 ≤ T` (the printed schedule divides by `log² T`, which vanishes at `T = 1`; see
`docs/SOURCE-ISSUES.md` C35). The schedule is only used for `1 ≤ k ≤ T`. -/

open MeasureTheory ProbabilityTheory Finset

namespace StatisticalRL.FiniteQLearning

open FiniteHorizonGenerative

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance mainStateMeasurable : MeasurableSpace State := ⊤

/-- The late-window rate sum: `Σ_{j ∈ (T/2, T]} η_j ≥ 16 H log² T`. -/
theorem late_rate_sum_ge {c₁ : ℝ} {H T : ℕ} (hc₁0 : 0 < c₁) (hc₁ : c₁ ≤ 1 / 64)
    (hhl : 0 < (H : ℝ) * Real.log T ^ 2) (hT : 2 ≤ T)
    (hx : (H : ℝ) * Real.log T ^ 2 ≤ c₁ * T) (η : ℕ → ℝ)
    (hη : ∀ k, 1 ≤ k → k ≤ T → 1 / (1 + c₁ * T / (H * Real.log T ^ 2)) ≤ η k) :
    16 * (H : ℝ) * Real.log T ^ 2 ≤ ∑ j ∈ Ioc (T / 2) T, η j := by
  have hτ0 : (0 : ℝ) < T := by positivity
  have hlow : ∀ j ∈ Ioc (T / 2) T, (H : ℝ) * Real.log T ^ 2 / (2 * c₁ * T) ≤ η j := fun j hj ↦
    rate_ge hhl hτ0 hc₁0 hx (hη j (by have := (mem_Ioc.mp hj).1; omega) (mem_Ioc.mp hj).2)
  have hcard := card_nsmul_le_sum (Ioc (T / 2) T) η _ hlow
  rw [Nat.card_Ioc, nsmul_eq_mul] at hcard
  have hTt : (T : ℝ) / 2 ≤ ((T - T / 2 : ℕ) : ℝ) := by
    have : T ≤ 2 * (T - T / 2) := by omega
    have : (T : ℝ) ≤ 2 * ((T - T / 2 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  have hm0 : 0 ≤ (H : ℝ) * Real.log T ^ 2 / (2 * c₁ * T) := by positivity
  have h1 : (T : ℝ) / 2 * ((H : ℝ) * Real.log T ^ 2 / (2 * c₁ * T)) =
      (H : ℝ) * Real.log T ^ 2 / (4 * c₁) := by
    field_simp; ring
  have h2 : 16 * (H : ℝ) * Real.log T ^ 2 ≤ (H : ℝ) * Real.log T ^ 2 / (4 * c₁) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have h3 := mul_le_mul_of_nonneg_right hTt hm0
  linarith

/-- The late-window rates lie in `[0,1]` and below `η̄`. -/
theorem schedule_unit {c₁ c₂ : ℝ} {H T : ℕ} (hc₁0 : 0 < c₁) (hc₂ : 0 < c₂)
    (hhl : 0 < (H : ℝ) * Real.log T ^ 2) (η : ℕ → ℝ)
    (hη : ∀ k, 1 ≤ k → k ≤ T →
      1 / (1 + c₁ * T / (H * Real.log T ^ 2)) ≤ η k ∧
        η k ≤ 1 / (1 + c₂ * k / (H * Real.log T ^ 2))) :
    ∀ k, 1 ≤ k → k ≤ T → 0 ≤ η k ∧ η k ≤ 1 := by
  intro k hk hkT
  obtain ⟨hlo, hhi⟩ := hη k hk hkT
  have hx0 : 0 ≤ c₁ * T / (H * Real.log T ^ 2) := by positivity
  have hy0 : 0 ≤ c₂ * k / (H * Real.log T ^ 2) := by positivity
  constructor
  · exact le_trans (by positivity) hlo
  · refine hhi.trans ?_
    rw [div_le_one (by linarith)]
    linarith

/-- On the good event, every stage of the actual run is `ε`-accurate. -/
theorem sampled_accuracy_of_allGood [Nonempty Action] {H T : ℕ}
    (E : Fin H → EnvironmentStage State Action) (Q₀ : Fin H → State → Action → ℝ)
    (hQ₀ : ∀ h s a, 0 ≤ Q₀ h s a ∧ Q₀ h s a ≤ (H : ℝ) - h) (η : ℕ → ℝ) {t₀ : ℕ} (ht₀T : t₀ ≤ T)
    (hunitAll : ∀ k, 1 ≤ k → k ≤ T → 0 ≤ η k ∧ η k ≤ 1) {ρ lam D ε : ℝ} (hρ0 : 0 ≤ ρ)
    (hH : (0 : ℝ) < H) (hlam : 0 < lam) (hD0 : 0 ≤ D)
    (hD : (H : ℝ) * (2 * ρ * H + Real.sqrt (2 * ρ) * D + ρ / (2 * lam)) + lam * H ^ 2 ≤ D)
    (hfin : (H : ℝ) * 2 ^ H * halfProd η t₀ T + D ≤ ε)
    (data : Samples State Action H T) (hdata : AllGood η t₀ T ρ H (sampledStages E T Q₀ data))
    (h' : Fin H) (s : State) (a : Action) :
    |sampledIterate E η T Q₀ data h' s a -
      EnvironmentStage.optimalQ ((List.ofFn E).drop h'.val) s a| ≤ ε := by
  have hunit : UnitRates η t₀ T := fun j hj hjT ↦ hunitAll j (by omega) hjT
  have hinit := (initBounded_sampledStages E T Q₀ hQ₀ data).drop h'.val
  have hgood := hdata.drop h'.val
  have hlen : (((sampledStages E T Q₀ data).drop h'.val).length : ℝ) ≤ H := by
    simp only [List.length_drop, sampledStages_length]
    exact_mod_cast Nat.sub_le H h'.val
  have hacc := deterministic_accuracy hρ0 hH hlam hD0 hD hunitAll ht₀T _ hinit hgood hlen s a
  rw [sampledStages_drop_env] at hacc
  have hpow : (H : ℝ) * 2 ^ ((sampledStages E T Q₀ data).drop h'.val).length *
      halfProd η t₀ T ≤ H * 2 ^ H * halfProd η t₀ T := by
    apply mul_le_mul_of_nonneg_right _ (halfProd_nonneg hunit)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_right₀ (by norm_num)
    simp [sampledStages_length]
  change |iterate η ((sampledStages E T Q₀ data).drop h'.val) T s a - _| ≤ ε
  linarith

/-- **Theorem 4.13** (library form). For every `c₁ ∈ (0, 1/64]` and `c₂ ∈ (0, c₁]`, with
`c₃ = 8000 / c₂`: for every finite-horizon MDP, `δ ∈ (0,1)`, `ε ∈ (0,1]`, `T ≥ 2` satisfying the
sample-size condition, learning rates obeying the schedule for `1 ≤ k ≤ T`, and initialization
`0 ≤ Q_{0,h} ≤ H + 1 - h` (0-based: `H - h`), synchronous Q-learning satisfies
`|Q_{T,h}(s,a) - Q⋆_h(s,a)| ≤ ε` for all `(s,a,h)` with probability greater than `1 - δ`. -/
theorem finiteQLearning_sample_complexity
    (c₁ c₂ : ℝ) (hc₂ : 0 < c₂) (hc₂₁ : c₂ ≤ c₁) (hc₁ : c₁ ≤ 1 / 64)
    (H : ℕ) (E : Fin H → EnvironmentStage State Action) (η : ℕ → ℝ) (δ ε : ℝ) (T : ℕ)
    (hT : 2 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : ∀ k, 1 ≤ k → k ≤ T →
      1 / (1 + c₁ * T / (H * Real.log T ^ 2)) ≤ η k ∧
        η k ≤ 1 / (1 + c₂ * k / (H * Real.log T ^ 2)))
    (Q₀ : Fin H → State → Action → ℝ)
    (hQ₀ : ∀ h s a, 0 ≤ Q₀ h s a ∧ Q₀ h s a ≤ (H : ℝ) - h)
    (hbudget : 8000 / c₂ * (H : ℝ) ^ 4 * Real.log T ^ 3 *
      Real.log (Fintype.card State * Fintype.card Action * T / δ) / ε ^ 2 ≤ T) :
    1 - δ < (samplingLaw E T).real {data | ∀ (h : Fin H) (s : State) (a : Action),
      |sampledIterate E η T Q₀ data h s a -
        EnvironmentStage.optimalQ ((List.ofFn E).drop h.val) s a| ≤ ε} := by
  classical
  -- the vacuous case H = 0
  rcases Nat.eq_zero_or_pos H with hH0 | hH
  · subst hH0
    have : {data : Samples State Action 0 T | ∀ (h : Fin 0) (s : State) (a : Action),
        |sampledIterate E η T Q₀ data h s a -
          EnvironmentStage.optimalQ ((List.ofFn E).drop h.val) s a| ≤ ε} = Set.univ := by
      ext data; simp
    rw [this, probReal_univ]
    linarith
  haveI : Nonempty Action := (E ⟨0, hH⟩).action_nonempty
  haveI : Nonempty State := (E ⟨0, hH⟩).state_nonempty
  have hh1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have hτ2 : (2 : ℝ) ≤ T := by exact_mod_cast hT
  have hτ0 : (0 : ℝ) < T := by linarith
  have hS1 : (1 : ℝ) ≤ Fintype.card State := by exact_mod_cast Fintype.card_pos
  have hA1 : (1 : ℝ) ≤ Fintype.card Action := by exact_mod_cast Fintype.card_pos
  have hl : 0.6931 < Real.log T := by
    have : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) hτ2
    linarith [log_two_gt]
  have hX : (T : ℝ) ≤ Fintype.card State * Fintype.card Action * T / δ := by
    rw [le_div_iff₀ hδ]
    have : (1 : ℝ) ≤ Fintype.card State * Fintype.card Action := by nlinarith
    nlinarith
  have hℓ : Real.log T ≤ Real.log (Fintype.card State * Fintype.card Action * T / δ) :=
    Real.log_le_log hτ0 hX
  have hb := budget_clear hc₂ hε hbudget
  have hx := schedule_x_ge_one hc₂ hc₂₁ hh1 hl hℓ hε hε1 hτ0 hb
  have hc₁0 : 0 < c₁ := by linarith
  have hhl : 0 < (H : ℝ) * Real.log T ^ 2 := by
    have : 0 < Real.log (T : ℝ) := by linarith
    positivity
  obtain ⟨hHT, hHε⟩ := budget_consequences hc₂ hc₂₁ hc₁ hh1 hτ0 hl hℓ hε hε1 hb
  -- schedule consequences
  have ht₀T : T / 2 ≤ T := Nat.div_le_self T 2
  have hunitAll := schedule_unit hc₁0 hc₂ hhl η hη
  have hunit : UnitRates η (T / 2) T := fun j hj hjT ↦ hunitAll j (by omega) hjT
  have hbar0 : 0 ≤ 2 * (H : ℝ) * Real.log T ^ 2 / (c₂ * T) := by positivity
  have hbar : ∀ i, T / 2 < i → i ≤ T → η i ≤ 2 * (H : ℝ) * Real.log T ^ 2 / (c₂ * T) :=
    fun i hi hiT ↦ late_rate_le hc₂ hhl (by omega) hi (hη i (by omega) hiT).2
  have hsumη := late_rate_sum_ge hc₁0 hc₁ hhl hT hx η fun k hk hkT ↦ (hη k hk hkT).1
  -- confidence allocation and radius
  have hL5 := log_confidence_le hS1 hA1 (by linarith) hHT hτ2 hδ hδ1.le
  have hden : (0 : ℝ) < 4 * Fintype.card State * Fintype.card Action * H * T := by positivity
  have hδ'0 : (0 : ℝ) < δ / (4 * Fintype.card State * Fintype.card Action * H * T) := by positivity
  have hδ'1 : δ / (4 * Fintype.card State * Fintype.card Action * H * T) < 1 := by
    rw [div_lt_one hden]
    have : (1 : ℝ) ≤ Fintype.card State * Fintype.card Action * H := by
      have : (1 : ℝ) ≤ Fintype.card State * Fintype.card Action := by nlinarith
      nlinarith
    nlinarith
  have hL0 : 0 ≤ Real.log (2 / (δ / (4 * Fintype.card State * Fintype.card Action * H * T))) :=
    Real.log_nonneg (by rw [le_div_iff₀ hδ'0]; linarith)
  have hρH := rho_bound hc₂ (by linarith) hτ0 hl hL0 hL5 hb
  have hρ0 : 0 ≤ 8 * (2 * (H : ℝ) * Real.log T ^ 2 / (c₂ * T)) *
      Real.log (2 / (δ / (4 * Fintype.card State * Fintype.card Action * H * T))) := by positivity
  -- the propagation tail
  have htail : (H : ℝ) * 2 ^ H * halfProd η (T / 2) T ≤ ε / 6 := by
    have hp := halfProd_le_exp hunit
    have hexp : Real.exp (-(∑ j ∈ Ioc (T / 2) T, η j) / 2) ≤
        Real.exp (-(8 * H * Real.log T ^ 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    have h2pos : (0 : ℝ) ≤ H * 2 ^ H := by positivity
    calc (H : ℝ) * 2 ^ H * halfProd η (T / 2) T ≤
          H * 2 ^ H * Real.exp (-(8 * H * Real.log T ^ 2)) :=
          mul_le_mul_of_nonneg_left (hp.trans hexp) h2pos
      _ ≤ H / T := propagation_tail_le hH hT
      _ ≤ ε / 6 := hHε
  -- the good event
  have hprob := allGood_sampled_prob E Q₀ η (T / 2) hunit hbar0 hbar (le_refl (H : ℝ))
    (δ / (4 * Fintype.card State * Fintype.card Action * H * T)) hδ'0 hδ'1
  have hcount : 2 * (H : ℝ) * Fintype.card State * Fintype.card Action * T *
      (δ / (4 * Fintype.card State * Fintype.card Action * H * T)) = δ / 2 := by
    field_simp
    ring
  rw [hcount] at hprob
  generalize 8 * (2 * (H : ℝ) * Real.log T ^ 2 / (c₂ * T)) *
      Real.log (2 / (δ / (4 * Fintype.card State * Fintype.card Action * H * T))) = ρ
    at hprob hρH hρ0
  obtain ⟨lam, D, hlam, hD0, hD, hDle⟩ := stability_constants hρ0 hh1 hε hε1 hρH
  have hsub : {data | AllGood η (T / 2) T ρ H (sampledStages E T Q₀ data)} ⊆
      {data | ∀ (h' : Fin H) (s : State) (a : Action),
        |sampledIterate E η T Q₀ data h' s a -
          EnvironmentStage.optimalQ ((List.ofFn E).drop h'.val) s a| ≤ ε} := by
    have hHpos : (0 : ℝ) < H := by linarith only [hh1]
    have hfin : (H : ℝ) * 2 ^ H * halfProd η (T / 2) T + D ≤ ε := by
      linarith only [htail, hDle, hε]
    intro data hdata
    exact sampled_accuracy_of_allGood E Q₀ hQ₀ η ht₀T hunitAll hρ0 hHpos hlam hD0 hD hfin data
      hdata
  have hmono := measureReal_mono hsub (measure_ne_top (samplingLaw E T) _)
  exact lt_of_lt_of_le (by linarith only [hδ] : 1 - δ < 1 - δ / 2) (hprob.trans hmono)

end StatisticalRL.FiniteQLearning
