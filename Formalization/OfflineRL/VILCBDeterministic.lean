import Formalization.OfflineRL.VILCBPessimism
import Formalization.OfflineRL.VILCBBonusSumScalar
import Formalization.OfflineRL.OccupancyWeightedVarianceMDP
import Formalization.OfflineRL.LCBQSeriesBasic

/-!
# Theorem 6.3: the deterministic (good-dataset) guarantee

Source: `chapters/offlineRL.tex:1031–1623`. For a dataset `x` in the Lemma 6.6 good set
(`goodSet p P p.δ`, the event of `lem:Bernstein-infinite` with the penalty's own `δ`) and in the
Lemma 6.5 count event (`eq:assumption-Nsa-LB-infinite`, `:1120–1125`), with `γ ≥ 1/2`, the
stopping rule of Theorem 6.3, `c_b ≥ 96` and `N ≥ 10⁴ c_b S C⋆ log(NS/((1-γ)δ))/((1-γ)³ε²)`,
every greedy VI-LCB policy `π̂` satisfies `V⋆(ρ) − V^{π̂}(ρ) ≤ ε`.
-/

open scoped BigOperators ENNReal

namespace StatisticalRL.OfflineVILCB.Theorem63

open StatisticalRL StatisticalRL.OfflineVILCB StatisticalRL.OfflineRL.LCBQ

variable {S A : Type*} [Fintype S] [Fintype A]

omit [Fintype S] [Fintype A] in
theorem dataCount_le {N : ℕ} (x : Fin N → (S × A) × S) (s : S) (a : A) : dataCount x s a ≤ N := by
  classical
  unfold dataCount
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- **Steps 1–3 for one run** (`offlineRL.tex:1056–1327`): with `γ ≥ 1/2`, `c_b ≥ 96`, the
Theorem 6.3 stopping rule and the Lemma 6.6 conclusions for the true rows `P` (the predicate
defining `goodSet`), `V̂ = value Q̂` lies in `[0, 1/(1-γ)]`, satisfies the Lemma 6.6 bounds at
every positive-count pair, the pessimism upper bound `Q̂ ≤ r + γ P V̂` and the lower bound
`eq:infinite-v-lower`. -/
theorem run_facts [Nonempty A] (I : Input S A) (P : S → A → FiniteDistribution S)
    (hhalf : 1 / 2 ≤ I.γ) (hcb : 96 ≤ I.cb) (τ : ℕ)
    (hτ : (1 / (1 - I.γ)) * Real.log (I.N / (1 - I.γ)) ≤ τ)
    (hgood : ∀ Qstar : S → A → ℝ, I.pess Qstar = Qstar →
      ∀ (s : S) (a : A), 0 < I.count s a →
      ∀ Vt : S → ℝ, (∀ t, |Vt t - Input.value Qstar t| ≤ 1 / I.N) →
        (∀ t, |Vt t| ≤ 1 / (1 - I.γ)) →
        I.Lemma66Bound (P s a) s a (Real.log (4 * I.N / ((1 - I.γ) * I.δ))) Vt) :
    (∀ t, 0 ≤ Input.value (I.iter τ) t) ∧
    (∀ t, Input.value (I.iter τ) t ≤ 1 / (1 - I.γ)) ∧
    (∀ s a, 0 < I.count s a → I.Lemma66Bound (P s a) s a
      (Real.log (4 * I.N / ((1 - I.γ) * I.δ))) (Input.value (I.iter τ))) ∧
    (∀ s a, I.iter τ s a ≤ I.r s a + I.γ * (P s a).expectation (Input.value (I.iter τ))) ∧
    (∀ s a, I.r s a + I.γ * (P s a).expectation (Input.value (I.iter τ)) -
      2 * I.bonus s a (Input.value (I.iter τ)) ≤ Input.value (I.iter τ) s) := by
  obtain ⟨Qstar, hfix, huniq, hiter, hstop⟩ := I.lem_monotone_contraction_corrected hhalf
  obtain ⟨Q₂, hfix₂, -, hVnorm, hbclose⟩ := I.exists_fixed_point_preliminary_facts hhalf τ hτ
  have hQ₂ : Q₂ = Qstar := huniq Q₂ hfix₂
  subst hQ₂
  set V := Input.value (I.iter τ) with hVdef
  have hQnorm := hstop τ (I.source_stopping_threshold hhalf τ hτ)
  have hclose : ∀ s a, |I.iter τ s a - Q₂ s a| ≤ 1 / I.N := by
    intro s a
    have h1 := norm_le_pi_norm ((I.iter τ - Q₂) s) a
    have h2 := norm_le_pi_norm (I.iter τ - Q₂) s
    simp only [Pi.sub_apply, Real.norm_eq_abs] at h1
    exact h1.trans (h2.trans hQnorm)
  have hV : ∀ t, |Input.value Q₂ t - V t| ≤ 1 / I.N := by
    intro t
    have h := (norm_le_pi_norm (V - Input.value Q₂) t).trans hVnorm
    simpa [Real.norm_eq_abs, abs_sub_comm] using h
  have hbox := I.iter_mem_box τ
  have hV0 : ∀ t, 0 ≤ V t := fun t => I.value_nonneg _ hbox t
  have hV1 : ∀ t, V t ≤ 1 / (1 - I.γ) := fun t => I.value_le_bound _ hbox t
  have hgood' : ∀ s a, 0 < I.count s a →
      I.Lemma66Bound (P s a) s a (Real.log (4 * I.N / ((1 - I.γ) * I.δ))) V := by
    intro s a hpos
    exact hgood Q₂ hfix₂ s a hpos V (fun t => by rw [abs_sub_comm]; exact hV t)
      (fun t => by rw [abs_of_nonneg (hV0 t)]; exact hV1 t)
  have hdom : ∀ s a, |(I.Phat s a).expectation V - (P s a).expectation V| + 5 / I.N ≤
      I.bonus s a V := fun s a =>
    bonus_dominates I hhalf hcb (P s a) s a V hV0 hV1 (hgood' s a)
  exact ⟨hV0, hV1, hgood', iter_le_reward_add I P τ Q₂ hfix₂ (hiter τ).1 hV hbclose hdom,
    reward_add_sub_le_value I P τ Q₂ hfix₂ hclose hV hbclose hdom⟩

/-- **Step 3 for `π⋆`** (`offlineRL.tex:1340–1402`): from `eq:infinite-v-lower` at `π⋆(s)` and the
Bellman equation of `V⋆` along a `Q⋆`-greedy `π⋆`,
`(1-γ) ⟨ρ, V⋆ − V⟩ ≤ 2 ⟨d⋆_ρ, b⋆⟩`. -/
theorem optimal_gap_reduction [Nonempty A] (M : DiscountedMDP S A) (ρ : FiniteDistribution S)
    (πstar : S → A)
    (hopt : ∀ s, M.optimalityFixedPoint s (πstar s) = actionMaximum (M.optimalityFixedPoint s))
    (V bst : S → ℝ)
    (hlow : ∀ s, M.reward s (πstar s) + M.discount * (M.transition s (πstar s)).expectation V -
      2 * bst s ≤ V s) :
    (1 - M.discount) *
        ρ.expectation (fun s => M.trajectoryExpectedValue M.optimalGreedyPolicy s - V s) ≤
      2 * ∑ s, M.discountedStateOccupancy (detPolicy πstar) ρ s * bst s := by
  set Vs := M.trajectoryExpectedValue M.optimalGreedyPolicy with hVs
  apply occupancy_reduction M πstar ρ _ bst
  intro s
  have h1 : Vs s = M.reward s (πstar s) +
      M.discount * (M.transition s (πstar s)).expectation Vs := by
    rw [hVs, optValue_eq M s, ← hopt s, optQ_eq_reward_add M s (πstar s)]
  have h2 := hlow s
  have h3 : (M.transition s (πstar s)).expectation (fun t => Vs t - V t) =
      (M.transition s (πstar s)).expectation Vs - (M.transition s (πstar s)).expectation V :=
    (M.transition s (πstar s)).expectation_sub Vs V
  rw [h3]
  linarith

/-- **Lemma 6.7 for `V̂`, `b⋆`, `π⋆`** (`lem:sum-d-Var-UB`, `offlineRL.tex:1529–1556`), with its
premises discharged from `eq:infinite-v-lower` and `γ ≥ 1/2`:
`Σ_s d⋆(s) Var_{P_{s,π⋆(s)}}(V) ≤ (8 + 16 ⟨d⋆, b⋆⟩)/(1-γ)`. -/
theorem lemma67_instance (M : DiscountedMDP S A) (ρ : FiniteDistribution S) (πstar : S → A)
    (hhalf : 1 / 2 ≤ M.discount) (V bst : S → ℝ) (hV0 : ∀ s, 0 ≤ V s)
    (hV1 : ∀ s, V s ≤ 1 / (1 - M.discount)) (hb0 : ∀ s, 0 ≤ bst s)
    (hlow : ∀ s, M.reward s (πstar s) + M.discount * (M.transition s (πstar s)).expectation V -
      2 * bst s ≤ V s) :
    ∑ s, M.discountedStateOccupancy (detPolicy πstar) ρ s * (M.transition s (πstar s)).variance V ≤
      (8 + 16 * ∑ s, M.discountedStateOccupancy (detPolicy πstar) ρ s * bst s) /
        (1 - M.discount) := by
  have hγpos : 0 < M.discount := by linarith
  have hk' : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hres : ∀ s, 0 ≤ V s - M.discount *
      (M.policyTransition (detPolicy πstar) s).expectation V + 2 * bst s := by
    intro s
    rw [policyTransition_detPolicy]
    have := hlow s
    have := M.reward_nonneg s (πstar s)
    linarith
  have h67 := OfflineRL.BonusSummation.occupancyWeightedVariance_mdp M (detPolicy πstar) ρ V bst
    hγpos hV0 hV1 hb0 hres
  simp only [policyTransition_detPolicy] at h67
  set xs := ∑ s, M.discountedStateOccupancy (detPolicy πstar) ρ s * bst s with hxs
  have hxs0 : 0 ≤ xs := Finset.sum_nonneg fun s _ =>
    mul_nonneg (M.discountedStateOccupancy_nonneg _ ρ s) (hb0 s)
  have hg2 : 1 / 4 ≤ M.discount ^ 2 := by nlinarith
  have e1 : 2 / (M.discount ^ 2 * (1 - M.discount)) ≤ 8 / (1 - M.discount) := by
    rw [div_le_div_iff₀ (by positivity) hk']
    nlinarith
  have e2 : 4 / (M.discount ^ 2 * (1 - M.discount)) * xs ≤ 16 * xs / (1 - M.discount) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hk']
    nlinarith [mul_nonneg hxs0 hk'.le]
  have e3 : (8 + 16 * xs) / (1 - M.discount) = 8 / (1 - M.discount) + 16 * xs / (1 - M.discount) :=
    add_div _ _ _
  linarith

/-- The three logarithms of the proof: `L = log(N/((1-γ)δ)) ≤ L₂ = log(NS/((1-γ)δ))`,
`L₂ ≥ 1/2` (for `γ ≥ 1/2`) and `log(SN/δ) ≤ L₂`. -/
theorem log_facts {γ δ N Sc : ℝ} (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hN : 1 ≤ N) (hS : 1 ≤ Sc) :
    Real.log (N / ((1 - γ) * δ)) ≤ Real.log (N * Sc / ((1 - γ) * δ)) ∧
    1 / 2 ≤ Real.log (N * Sc / ((1 - γ) * δ)) ∧
    Real.log (Sc * N / δ) ≤ Real.log (N * Sc / ((1 - γ) * δ)) := by
  have hk : 0 < 1 - γ := by linarith
  have hkδ : 0 < (1 - γ) * δ := mul_pos hk hδ
  have hN0 : 0 < N := by linarith
  have h1 : Real.log (N / ((1 - γ) * δ)) ≤ Real.log (N * Sc / ((1 - γ) * δ)) :=
    Real.log_le_log (div_pos hN0 hkδ)
      (div_le_div_of_nonneg_right (le_mul_of_one_le_right hN0.le hS) hkδ.le)
  refine ⟨h1, ?_, ?_⟩
  · have h2 : 2 ≤ N / ((1 - γ) * δ) := by
      rw [le_div_iff₀ hkδ]; nlinarith
    have h3 := Real.log_le_log (by norm_num) h2
    have := Real.log_two_gt_d9
    linarith
  · apply Real.log_le_log (by positivity)
    rw [mul_comm Sc N, div_le_div_iff₀ hδ hkδ]
    have h0 : 0 ≤ N * Sc := by positivity
    have h4 : (1 - γ) * δ ≤ δ := by nlinarith
    exact mul_le_mul_of_nonneg_left h4 h0

/-- The sample-size condition with `c₁ = 10⁴ c_b` gives `Y ≤ t²/10⁴`, where
`Y = c_b S C L₂/((1-γ)N)` and `t = (1-γ)ε`. -/
theorem Y_le_of_sample_size {cb Sc C L₂ k ε N : ℝ} (hk : 0 < k) (hε : 0 < ε) (hN : 0 < N)
    (hNcond : 10000 * cb * Sc * C * L₂ / (k ^ 3 * ε ^ 2) ≤ N) :
    cb * Sc * C * L₂ / (k * N) ≤ (k * ε) ^ 2 / 10000 := by
  have hden : 0 < k ^ 3 * ε ^ 2 := by positivity
  rw [div_le_iff₀ hden] at hNcond
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  have e : (k * ε) ^ 2 * (k * N) = N * (k ^ 3 * ε ^ 2) := by ring
  rw [e]
  linarith

/-- **Theorem 6.3 on a good dataset** (`thm:infinite-offline`, `offlineRL.tex:899–920`, proof
`:1031–1623`), deterministic form. -/
theorem gap_le_of_good [Nonempty S] [Nonempty A] (M : DiscountedMDP S A)
    (db : FiniteDistribution (S × A)) (p : Params S A)
    (hγ : p.γ = M.discount) (hr : p.r = M.reward) (hcb : 96 ≤ p.cb) (hhalf : 1 / 2 ≤ M.discount)
    (τ : ℕ) (hτ : (1 / (1 - M.discount)) * Real.log (p.N / (1 - M.discount)) ≤ τ)
    (ρ : FiniteDistribution S) (πstar : S → A)
    (hopt : ∀ s, M.optimalityFixedPoint s (πstar s) = actionMaximum (M.optimalityFixedPoint s))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / (1 - M.discount))
    (hC : concentrability M ρ πstar db ≠ ⊤)
    (hNcond : 10000 * p.cb * Fintype.card S * (concentrability M ρ πstar db).toReal *
        Real.log (p.N * Fintype.card S / ((1 - M.discount) * p.δ)) /
        ((1 - M.discount) ^ 3 * ε ^ 2) ≤ p.N)
    (x : Fin p.N → (S × A) × S) (hgood : x ∈ LeaveOneOut.goodSet p M.transition p.δ)
    (hcount : ∀ s a, max ((dataCount x s a : ℕ) : ℝ)
        ((2 / 3 : ℝ) * Real.log ((Fintype.card S : ℝ) * p.N / p.δ)) ≥
      (p.N : ℝ) * db.prob (s, a) / 12)
    (πhat : S → A)
    (hgreedy : ∀ s a, (p.input x).iter τ s a ≤ (p.input x).iter τ s (πhat s)) :
    ρ.expectation (M.trajectoryExpectedValue M.optimalGreedyPolicy) -
      ρ.expectation (M.trajectoryExpectedValue (fun x => EnvironmentStage.pointMass (πhat x))) ≤
      ε := by
  set I := p.input x with hI
  have hIγ : I.γ = M.discount := hγ
  have hIr : I.r = M.reward := hr
  have hhalfI : 1 / 2 ≤ I.γ := hIγ ▸ hhalf
  have hcbI : 96 ≤ I.cb := hcb
  have hN : (0 : ℝ) < p.N := by exact_mod_cast p.N_pos
  have hk' : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hτI : (1 / (1 - I.γ)) * Real.log (I.N / (1 - I.γ)) ≤ τ := by rw [hIγ]; exact hτ
  obtain ⟨hV0, hV1, hgood', hup, hlow⟩ := run_facts I M.transition hhalfI hcbI τ hτI hgood
  set V := Input.value (I.iter τ) with hVdef
  have hpess := value_le_trajectoryValue I M hIγ hIr τ hup πhat hgreedy
  set bst : S → ℝ := fun s => I.bonus s (πstar s) V with hbst
  have hlow' : ∀ s, M.reward s (πstar s) + M.discount * (M.transition s (πstar s)).expectation V -
      2 * bst s ≤ V s := by
    intro s
    have h := hlow s (πstar s)
    rw [hIr, hIγ] at h
    exact h
  have hred := optimal_gap_reduction M ρ πstar hopt V bst hlow'
  have hV1' : ∀ s, V s ≤ 1 / (1 - M.discount) := fun s => hIγ ▸ hV1 s
  have hbst0 : ∀ s, 0 ≤ bst s := fun s => I.bonus_nonneg s (πstar s) V
  have h67 := lemma67_instance M ρ πstar hhalf V bst hV0 hV1' hbst0 hlow'
  set d := M.discountedStateOccupancy (detPolicy πstar) ρ with hd
  set xs := ∑ s, d s * bst s with hxs
  -- Step 4
  have hS1 : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  set C := (concentrability M ρ πstar db).toReal with hCdef
  have hC1 : 1 ≤ C := one_le_concentrability M ρ πstar db hC
  have hN1 : (1 : ℝ) ≤ p.N := by exact_mod_cast p.N_pos
  obtain ⟨hLleL₂, hL₂half, hLsL₂⟩ := log_facts hhalf M.discount_lt_one p.δ_pos p.δ_lt_one hN1 hS1
  have hLL₂ : I.logTerm = Real.log (p.N / ((1 - M.discount) * p.δ)) := by
    unfold Input.logTerm; rw [hIγ]; rfl
  have hk1 : 1 - M.discount ≤ 1 := by linarith [M.discount_nonneg]
  have hstep4 := step4_abstract (ι := S) d bst (fun s => (M.transition s (πstar s)).variance V)
    (fun s => db.prob (s, πstar s)) (fun s => (I.count s (πstar s) : ℝ))
    (N := p.N) (C := C) (cb := p.cb) (L := I.logTerm)
    (k := 1 - M.discount) hN hk' hk1 hC1 hcb I.logTerm_pos.le (hLL₂ ▸ hLleL₂) hL₂half hLsL₂
    (fun s => M.discountedStateOccupancy_nonneg _ ρ s) (M.discountedStateOccupancy_sum _ ρ)
    (fun s => dstarState_le M ρ πstar db hC s)
    (fun s => (M.transition s (πstar s)).variance_nonneg V) hbst0
    (fun s => by
      have h := bonus_le_bound I s (πstar s) V
      rw [hIγ] at h
      exact h)
    (fun s => hcount s (πstar s))
    (fun s hpos => by
      have hpos' : 0 < I.count s (πstar s) := by
        have h' : (0 : ℝ) < I.count s (πstar s) := hpos
        exact_mod_cast h'
      have h := bonus_le_of_lemma66 I hhalfI hcbI (M.transition s (πstar s)) s (πstar s) V hpos'
        (dataCount_le x s (πstar s)) (hgood' s (πstar s) hpos')
      rw [hIγ] at h
      exact h)
    h67
  -- Step 4.3
  have hYt := Y_le_of_sample_size hk' hε hN (by simpa only [mul_assoc] using hNcond)
  have ht0 : 0 ≤ (1 - M.discount) * ε := by positivity
  have ht1 : (1 - M.discount) * ε ≤ 1 := by
    rw [le_div_iff₀ hk'] at hε1; linarith
  have hY0 : 0 ≤ p.cb * Fintype.card S * C *
      Real.log (p.N * Fintype.card S / ((1 - M.discount) * p.δ)) / ((1 - M.discount) * p.N) := by
    have := p.cb_pos; positivity
  have hxs0 : 0 ≤ xs := Finset.sum_nonneg fun s _ =>
    mul_nonneg (M.discountedStateOccupancy_nonneg _ ρ s) (hbst0 s)
  have h2x := self_bound hxs0 hY0 ht0 ht1 hYt hstep4
  -- conclusion
  have h1 : ρ.expectation V ≤
      ρ.expectation (M.trajectoryExpectedValue (fun x => EnvironmentStage.pointMass (πhat x))) :=
    ρ.expectation_mono hpess
  have h2 := ρ.expectation_sub (M.trajectoryExpectedValue M.optimalGreedyPolicy) V
  have hfin : (1 - M.discount) *
      ρ.expectation (fun s => M.trajectoryExpectedValue M.optimalGreedyPolicy s - V s) ≤
      (1 - M.discount) * ε := by linarith
  have := le_of_mul_le_mul_left hfin hk'
  linarith

end StatisticalRL.OfflineVILCB.Theorem63
