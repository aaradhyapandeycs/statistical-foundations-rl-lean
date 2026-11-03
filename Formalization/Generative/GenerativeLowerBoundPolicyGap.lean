import Formalization.Generative.GenerativeLowerBoundFamilyMDP

/-! Correct policy Q-loss at a misidentified active state. -/
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.DiscountedMDP

/-- A deterministic policy induces a point-mass action at every state. -/
noncomputable def deterministicFamilyPolicy {m n : ℕ}
    (f : Option (Fin m) → Fin (n + 1)) : StationaryPolicy (Option (Fin m)) (Fin (n + 1)) :=
  fun s ↦ EnvironmentStage.pointMass (f s)

/-- The actual value of every deterministic policy is zero at the absorber. -/
theorem familyMDP_deterministic_value_absorber {m n : ℕ}
    (i : HardFamilyIndex m n) (γ p q : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q < 1)
    (f : Option (Fin m) → Fin (n + 1)) :
    let M := familyMDP i γ p q hγ hγ1 hp hpq hq
    M.trajectoryExpectedValue (deterministicFamilyPolicy f) none = 0 := by
  let M := familyMDP i γ p q hγ hγ1 hp hpq hq
  let π := deterministicFamilyPolicy f
  have hb := congrFun (M.valueFixedPoint_spec π) none
  rw [← M.trajectoryExpectedValue_eq_valueFixedPoint π] at hb
  change (EnvironmentStage.pointMass (f none)).expectation (M.reward none) + γ *
    ((EnvironmentStage.pointMass (f none)).bind (M.transition none)).expectation
      (M.trajectoryExpectedValue π) = M.trajectoryExpectedValue π none at hb
  rw [FiniteDistribution.expectation_bind, EnvironmentStage.expectation_pointMass,
    EnvironmentStage.expectation_pointMass] at hb
  change 0 + γ * (EnvironmentStage.pointMass none).expectation
    (M.trajectoryExpectedValue π) = M.trajectoryExpectedValue π none at hb
  rw [EnvironmentStage.expectation_pointMass] at hb
  change M.trajectoryExpectedValue π none = 0
  nlinarith

/-- A deterministic policy choosing a bad action has actual active-state
value V₀, even if its actions at all other states are arbitrary. -/
theorem familyMDP_badPolicy_active_value {m n : ℕ}
    (i : HardFamilyIndex m n) (γ p q : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q < 1)
    (f : Option (Fin m) → Fin (n + 1)) (j : Fin m)
    (hbad : f (some j) ≠ hardPolicySignature i j) :
    let M := familyMDP i γ p q hγ hγ1 hp hpq hq
    M.trajectoryExpectedValue (deterministicFamilyPolicy f) (some j) = 1 / (1 - γ * p) := by
  let M := familyMDP i γ p q hγ hγ1 hp hpq hq
  let π := deterministicFamilyPolicy f
  have hden : 0 < 1 - γ * p := by
    have hp1 : p < 1 := lt_of_le_of_lt hpq hq
    have h := mul_le_mul_of_nonneg_left hp1.le hγ
    nlinarith
  have hn : M.trajectoryExpectedValue π none = 0 :=
    familyMDP_deterministic_value_absorber i γ p q hγ hγ1 hp hpq hq f
  have hb := congrFun (M.valueFixedPoint_spec π) (some j)
  rw [← M.trajectoryExpectedValue_eq_valueFixedPoint π] at hb
  change (EnvironmentStage.pointMass (f (some j))).expectation (M.reward (some j)) + γ *
    ((EnvironmentStage.pointMass (f (some j))).bind (M.transition (some j))).expectation
      (M.trajectoryExpectedValue π) = M.trajectoryExpectedValue π (some j) at hb
  rw [FiniteDistribution.expectation_bind, EnvironmentStage.expectation_pointMass,
    EnvironmentStage.expectation_pointMass] at hb
  change 1 + γ * (familyActiveRow j (familyStay i p q j (f (some j))) _ _).expectation
    (M.trajectoryExpectedValue π) = M.trajectoryExpectedValue π (some j) at hb
  rw [familyActiveRow_expectation, hn] at hb
  simp [familyStay, hbad] at hb
  change M.trajectoryExpectedValue π (some j) = _
  apply (eq_div_iff (ne_of_gt hden)).2
  nlinarith

/-- Exact actual policy Q loss when the forced first action is good but the
continuation policy chooses a bad action at that state. -/
theorem familyMDP_badPolicy_goodAction_Q_loss {m n : ℕ}
    (i : HardFamilyIndex m n) (γ p q : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1)
    (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q < 1)
    (f : Option (Fin m) → Fin (n + 1)) (j : Fin m)
    (hbad : f (some j) ≠ hardPolicySignature i j) :
    let M := familyMDP i γ p q hγ hγ1 hp hpq hq
    M.trajectoryExpectedQ M.optimalGreedyPolicy (some j) (hardPolicySignature i j) -
      M.trajectoryExpectedQ (deterministicFamilyPolicy f) (some j) (hardPolicySignature i j) =
    γ * q * (1 / (1 - γ * q) - 1 / (1 - γ * p)) := by
  let M := familyMDP i γ p q hγ hγ1 hp hpq hq
  let π := deterministicFamilyPolicy f
  let a := hardPolicySignature i j
  have hv₀ : M.trajectoryExpectedValue π none = 0 :=
    familyMDP_deterministic_value_absorber i γ p q hγ hγ1 hp hpq hq f
  have hv : M.trajectoryExpectedValue π (some j) = 1 / (1 - γ * p) :=
    familyMDP_badPolicy_active_value i γ p q hγ hγ1 hp hpq hq f j hbad
  have hvopt : M.trajectoryExpectedValue M.optimalGreedyPolicy (some j) = 1 / (1 - γ * q) :=
    familyMDP_optimal_trajectoryValue i γ p q hγ hγ1 hp hpq hq (some j)
  have hvopt0 : M.trajectoryExpectedValue M.optimalGreedyPolicy none = 0 :=
    familyMDP_optimal_trajectoryValue i γ p q hγ hγ1 hp hpq hq none
  change M.trajectoryExpectedQ M.optimalGreedyPolicy (some j) a -
    M.trajectoryExpectedQ π (some j) a = _
  rw [M.trajectoryQ_sub_eq_discount_expectation_value_sub]
  change γ * (familyActiveRow j (familyStay i p q j a) _ _).expectation
    (M.trajectoryExpectedValue M.optimalGreedyPolicy - M.trajectoryExpectedValue π) = _
  rw [familyActiveRow_expectation]
  simp [familyStay, a, hv, hv₀, hvopt, hvopt0]
  ring

/-- Under the source parameters, a bad active-state policy action creates
strictly more than ε actual Q loss at the forced good first action. -/
theorem sourceFamilyMDP_badPolicy_Q_loss_gt {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (i : HardFamilyIndex m n) (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ)))
    (f : Option (Fin m) → Fin (n + 1)) (j : Fin m)
    (hbad : f (some j) ≠ hardPolicySignature i j) :
    let M := sourceFamilyMDP i γ ε hγ hγ1 hε hεmax
    ε < M.trajectoryExpectedQ M.optimalGreedyPolicy (some j) (hardPolicySignature i j) -
      M.trajectoryExpectedQ (deterministicFamilyPolicy f) (some j) (hardPolicySignature i j) := by
  have ha := source_parameters_admissible γ ε hγ hγ1 hε hεmax
  have hd := source_parameters_scalar_separation γ ε hγ hγ1 hε hεmax
  have hg : 0 < γ := by linarith
  have hprod : 1 / 2 < γ * (baseProbability γ + probabilityIncrement γ ε) := by
    have hγp : γ * baseProbability γ = (4 * γ - 1) / 3 := by
      unfold baseProbability
      field_simp
    have hincr : 0 ≤ γ * probabilityIncrement γ ε :=
      mul_nonneg hg.le (by linarith [ha.2.1])
    nlinarith [hγp]
  have hfac := mul_lt_mul_of_pos_left hd (by positivity : 0 < γ * (baseProbability γ + probabilityIncrement γ ε))
  have hfac' := mul_pos (show 0 < γ * (baseProbability γ + probabilityIncrement γ ε) - 1 / 2 by linarith)
    (show 0 < 2 * ε by positivity)
  dsimp only [sourceFamilyMDP]
  rw [familyMDP_badPolicy_goodAction_Q_loss _ _ _ _ _ _ _ _ _ f j hbad]
  nlinarith

/-- If the total decoder reports the wrong model index, the true actual
trajectory Q loss of the returned deterministic policy exceeds ε. -/
theorem sourceFamilyMDP_decoder_error_Q_norm_gt {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (i : HardFamilyIndex m n) (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ)))
    (f : Option (Fin m) → Fin (n + 1))
    (hdecode : decodeHardPolicy (fun j ↦ f (some j)) ≠ i) :
    let M := sourceFamilyMDP i γ ε hγ hγ1 hε hεmax
    ε < ‖M.trajectoryExpectedQ M.optimalGreedyPolicy -
      M.trajectoryExpectedQ (deterministicFamilyPolicy f)‖ := by
  have hne := decodeHardPolicy_error_ne_signature m n (fun j ↦ f (some j)) i hdecode
  have hex : ∃ j, f (some j) ≠ hardPolicySignature i j := by
    by_contra h
    apply hne
    funext j
    by_contra hj
    exact h ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hex
  let M := sourceFamilyMDP i γ ε hγ hγ1 hε hεmax
  have hgap := sourceFamilyMDP_badPolicy_Q_loss_gt hm hn i γ ε hγ hγ1 hε hεmax f j hj
  have h₁ := norm_le_pi_norm (M.trajectoryExpectedQ M.optimalGreedyPolicy -
    M.trajectoryExpectedQ (deterministicFamilyPolicy f)) (some j)
  have h₂ := norm_le_pi_norm ((M.trajectoryExpectedQ M.optimalGreedyPolicy -
    M.trajectoryExpectedQ (deterministicFamilyPolicy f)) (some j)) (hardPolicySignature i j)
  simp only [Pi.sub_apply, Real.norm_eq_abs] at h₂
  have hpos : 0 ≤ M.trajectoryExpectedQ M.optimalGreedyPolicy (some j) (hardPolicySignature i j) -
      M.trajectoryExpectedQ (deterministicFamilyPolicy f) (some j) (hardPolicySignature i j) := by linarith
  rw [abs_of_nonneg hpos] at h₂
  exact hgap.trans_le (h₂.trans h₁)

/-- Under any actual sample law, the total decoder's error event is contained
in the strict actual-Q loss event for the same data-dependent estimator. -/
theorem sourceFamilyMDP_decoder_error_probability_le_Q_risk {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (i : HardFamilyIndex m n)
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ)))
    (estimate : Ω → Option (Fin m) → Fin (n + 1)) :
    let M := sourceFamilyMDP i γ ε hγ hγ1 hε hεmax
    μ.real {ω | decodeHardPolicy (fun j ↦ estimate ω (some j)) ≠ i} ≤
    μ.real {ω | ε < ‖M.trajectoryExpectedQ M.optimalGreedyPolicy -
      M.trajectoryExpectedQ (deterministicFamilyPolicy (estimate ω))‖} := by
  apply MeasureTheory.measureReal_mono _ (MeasureTheory.measure_ne_top μ _)
  intro ω hω
  exact sourceFamilyMDP_decoder_error_Q_norm_gt hm hn i γ ε hγ hγ1 hε hεmax (estimate ω) hω

/-- The same decoder-error bound in the source norm orientation Q^π−Q*. -/
theorem sourceFamilyMDP_decoder_error_probability_le_source_Q_risk {Ω : Type*} [Fintype Ω]
    [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (i : HardFamilyIndex m n)
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ)))
    (estimate : Ω → Option (Fin m) → Fin (n + 1)) :
    let M := sourceFamilyMDP i γ ε hγ hγ1 hε hεmax
    μ.real {ω | decodeHardPolicy (fun j ↦ estimate ω (some j)) ≠ i} ≤
    μ.real {ω | ε < ‖M.trajectoryExpectedQ (deterministicFamilyPolicy (estimate ω)) -
      M.trajectoryExpectedQ M.optimalGreedyPolicy‖} := by
  have h := sourceFamilyMDP_decoder_error_probability_le_Q_risk μ hm hn i γ ε hγ hγ1 hε hεmax estimate
  simpa only [norm_sub_rev] using h

end StatisticalRL.GenerativeLowerBound
