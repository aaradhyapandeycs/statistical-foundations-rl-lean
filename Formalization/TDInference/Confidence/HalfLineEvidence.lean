import Formalization.TDInference.Confidence.Intervals
import Formalization.MDP.PointMassDefinitions
import Formalization.OfflineRL.VILCBDatasetDefinitions

/-!
# C47(1) evidence: data-selected half-lines are not confidence regions (oracle covariance)

Source: `chapters/inference.tex:187–196` (rule `eq:convex.Cdelta` :189–195, display :191–193, "such
sets serve as approximate confidence regions" :196); SOURCE-ISSUES C47(1). Plan item E2.

**Instance O (one state).** `State = Unit`, two actions with rewards `r(·,0) = 0`, `r(·,1) = 1`,
`γ = 1/2`, `π` and `μ` uniform. Then `V^π = 1`, `Γ_true = 1/4 > 0`, `A = 1/2` and the oracle
covariance is `Λ = A⁻¹Γ_trueA⁻ᵀ = 1` (`oneState_valueFixedPoint`, `oneState_trueGamma`,
`oneState_oracleLambda`).

**Rule.** Given the data, select the half-line `signSel z T V̄_T`:
`[V̄_T − z√(Λ/T), ∞)` if `V̄_T ≥ 1`, and `(−∞, V̄_T + z√(Λ/T)]` otherwise, for a level `z ≥ 0`
(`α = 1 − Φ(z) ∈ (0, 1/2]`). Each selected set is convex (`convex_signSel`). The rule reads only
the data, but its threshold `1` is chosen equal to `V^π` of instance O; this is essential (for a
threshold `c ≠ V^π` the coverage tends to `Φ(z)`) and legitimate, since the printed claim is
universal over convex sets with conditional mass `1 − α`: one instance and one data-measurable
rule refute it. Same structure as the Gaussian witness of C47(1) (threshold `0 = θ`). Each
selected set has mass exactly `Φ(z) = 1 − α` under `N(V̄_T, Λ/T)` (`gaussianReal_signSel`), i.e.
it is a `(1−α)`-region of the oracle Gaussian `N(V̄_T, Λ/T)` (not of the printed rule's
`N(V̄_T, Λ̂_T/T)`). But its coverage is `P(|√TΔ̄_T| ≤ z)`, which is within `2K T^{-1/3}` of
`2Φ(z) − 1 = 1 − 2α` (`oneState_signSel_coverage`), and so eventually at most
`Φ(z) − (1 − Φ(z))/2 < 1 − α` (`oneState_signSel_coverage_eventually_lt`).

Scope: this refutes the rule with the **oracle** covariance `Λ`; the printed `Λ̂_T` version
additionally needs consistency of `Λ̂_T` (plan item C3), which is not used here.
-/

open MeasureTheory ProbabilityTheory Finset Matrix Filter
open scoped BigOperators NNReal Topology

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Probability.Stein
open StatisticalRL.EnvironmentStage (pointMass)
open StatisticalRL.OfflineVILCB (uniformRow)

/-- `Φ(z) < 1` for every `z`: the standard Gaussian tail is positive. -/
theorem stdTail_pos (z : ℝ) : 0 < stdTail z := by
  rw [stdTail, setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun x ↦ (stdPDF_pos x).le) integrable_stdPDF.integrableOn]
  have hs : Function.support stdPDF = Set.univ :=
    Set.eq_univ_of_forall fun x ↦ (stdPDF_pos x).ne'
  rw [hs, Set.univ_inter, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

theorem gaussianReal_real_Iic_lt_one (z : ℝ) : (gaussianReal 0 1).real (Set.Iic z) < 1 := by
  rw [gaussianReal_real_Iic]
  linarith [stdCDF_add_stdTail z, stdTail_pos z]

/-! ## Gaussian mass of the selected half-line -/

/-- `N(v, σ²) = law of c·X + v`, `X ∼ N(0,1)`, whenever `c² = σ²`. -/
theorem gaussianReal_eq_map_mul_add (v c : ℝ) (σ2 : ℝ≥0) (hc : c ^ 2 = (σ2 : ℝ)) :
    gaussianReal v σ2 = (gaussianReal 0 1).map (fun x ↦ c * x + v) := by
  have h : (fun x : ℝ ↦ c * x + v) = (· + v) ∘ (c * ·) := rfl
  rw [h, ← Measure.map_map (measurable_add_const v) (measurable_const_mul c),
    gaussianReal_map_const_mul, gaussianReal_map_add_const]
  congr 1
  · ring
  · ext; simp [hc]

/-- The sign-selected half-line of radius `ρ` around the estimate `v`
(threshold the fixed number `1`). -/
def signSel (ρ v : ℝ) : Set ℝ :=
  if 1 ≤ v then Set.Ici (v - ρ) else Set.Iic (v + ρ)

/-- Each sign-selected half-line is convex. -/
theorem convex_signSel (ρ v : ℝ) : Convex ℝ (signSel ρ v) := by
  unfold signSel
  split_ifs
  · exact convex_Ici _
  · exact convex_Iic _

/-- Each selected half-line has mass `Φ(z)` under `N(v, 1/T)`, for every `v`. -/
theorem gaussianReal_signSel (v z : ℝ) {T : ℕ} (hT : 1 ≤ T) :
    (gaussianReal v (T : ℝ≥0)⁻¹).real (signSel (z * Real.sqrt (1 / T)) v) =
      (gaussianReal 0 1).real (Set.Iic z) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  set σ := Real.sqrt (1 / T) with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 (by positivity)
  have hσ2 : σ ^ 2 = ((T : ℝ≥0)⁻¹ : ℝ≥0) := by
    rw [hσdef, Real.sq_sqrt (by positivity)]; simp
  unfold signSel
  split_ifs with hv
  · rw [gaussianReal_eq_map_mul_add v (-σ) _ (by rw [neg_sq]; exact hσ2),
      map_measureReal_apply (by fun_prop) measurableSet_Ici]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_Ici, Set.mem_Iic]
    constructor <;> intro h <;> nlinarith
  · rw [gaussianReal_eq_map_mul_add v σ _ hσ2,
      map_measureReal_apply (by fun_prop) measurableSet_Iic]
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic]
    constructor <;> intro h <;> nlinarith

/-- `1 ∈ signSel ρ v ⇔ |v − 1| ≤ ρ`. -/
theorem one_mem_signSel_iff (ρ v : ℝ) : (1 : ℝ) ∈ signSel ρ v ↔ |v - 1| ≤ ρ := by
  unfold signSel
  split_ifs with hv
  · rw [Set.mem_Ici, abs_of_nonneg (by linarith)]
    constructor <;> intro h <;> linarith
  · rw [Set.mem_Iic, abs_of_neg (by linarith)]
    constructor <;> intro h <;> linarith

/-! ## Instance O -/

namespace OneState

/-- Instance O: one state, actions `0, 1` with rewards `0, 1`, `γ = 1/2`. -/
noncomputable def oMDP : DiscountedMDP Unit (Fin 2) where
  state_nonempty := ⟨()⟩
  action_nonempty := ⟨0⟩
  transition _ _ := pointMass ()
  reward _ a := ![0, 1] a
  reward_nonneg _ a := by fin_cases a <;> norm_num
  reward_le_one _ a := by fin_cases a <;> norm_num
  discount := 1 / 2
  discount_nonneg := by norm_num
  discount_lt_one := by norm_num

/-- The uniform policy. -/
noncomputable def oPolicy : StationaryPolicy Unit (Fin 2) := fun _ ↦ uniformRow (Fin 2)

/-- The sampling distribution (the point mass on the only state). -/
noncomputable def oMu : FiniteDistribution Unit := uniformRow Unit

theorem oPolicy_prob (s : Unit) (a : Fin 2) : (oPolicy s).prob a = 1 / 2 := by
  norm_num [oPolicy, uniformRow]

theorem oMu_prob (s : Unit) : oMu.prob s = 1 := by
  norm_num [oMu, uniformRow]

theorem oTransition_prob (s : Unit) (a : Fin 2) (t : Unit) : (oMDP.transition s a).prob t = 1 := by
  simp [oMDP, pointMass]

theorem oneState_valueFixedPoint : oMDP.valueFixedPoint oPolicy = fun _ ↦ 1 := by
  refine ((oMDP.valueFixedPoint_characterization oPolicy _).1 ?_).symm
  funext s
  simp only [DiscountedMDP.valueBellman, FiniteDistribution.expectation, Fin.sum_univ_two,
    DiscountedMDP.policyTransition_prob, oPolicy_prob, oTransition_prob, Fintype.univ_unit,
    Finset.sum_singleton]
  norm_num [oMDP]

theorem oneState_trueGamma (s : Unit) : trueGamma oMDP oPolicy oMu s = 1 / 4 := by
  simp only [trueGamma, FiniteDistribution.expectation, Fin.sum_univ_two, oPolicy_prob,
    oTransition_prob, oMu_prob, oneState_valueFixedPoint, Fintype.univ_unit,
    Finset.sum_singleton]
  norm_num [oMDP]

theorem oneState_tdA : tdA oMDP oPolicy oMu = diagonal fun _ ↦ 1 / 2 := by
  ext i j
  simp only [tdA, Matrix.diagonal_mul, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    policyMatrix, Matrix.of_apply, DiscountedMDP.policyTransition_prob,
    FiniteDistribution.expectation, Fin.sum_univ_two, oPolicy_prob, oTransition_prob, oMu_prob,
    smul_eq_mul, Matrix.diagonal_apply, Subsingleton.elim i j, if_true]
  norm_num [oMDP]

/-- The oracle covariance is `Λ = A⁻¹Γ_trueA⁻ᵀ = 1`. -/
theorem oneState_oracleLambda (s s' : Unit) :
    ((tdA oMDP oPolicy oMu)⁻¹ * diagonal (trueGamma oMDP oPolicy oMu) *
      (tdA oMDP oPolicy oMu)⁻¹ᵀ) s s' = 1 := by
  have hinv : (diagonal fun _ : Unit ↦ (1 / 2 : ℝ))⁻¹ = diagonal fun _ ↦ 2 := by
    refine Matrix.inv_eq_left_inv ?_
    rw [diagonal_mul_diagonal]
    ext i j
    rw [Subsingleton.elim j i, diagonal_apply_eq, one_apply_eq]
    norm_num
  rw [oneState_tdA, hinv, diagonal_transpose, diagonal_mul_diagonal,
    diagonal_mul_diagonal, Subsingleton.elim s' s, diagonal_apply_eq, oneState_trueGamma]
  norm_num

/-- **E2, coverage of the sign-selected half-lines (oracle covariance).** For `0 < η₀ ≤ 1` and
every `V₀` there is `K > 0` such that for all `T ≥ 1` and `z ≥ 0`,
`|P(V^π ∈ signSel(z√(Λ/T), V̄_T)) − (2Φ(z) − 1)| ≤ 2K T^{-1/3}` (here `Λ = 1`). -/
theorem oneState_signSel_coverage {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : Unit → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ T : ℕ, 1 ≤ T → ∀ z : ℝ, 0 ≤ z →
      |(∑ ω : Fin T → Tuple Unit (Fin 2), pathWeight oMDP oPolicy oMu ω *
          {ω' : Fin T → Tuple Unit (Fin 2) | oMDP.valueFixedPoint oPolicy () ∈
            signSel (z * Real.sqrt (1 / T)) (prAverage oMDP η₀ V₀ ω' ())}.indicator 1 ω) -
        (2 * (gaussianReal 0 1).real (Set.Iic z) - 1)| ≤ 2 * K * (T : ℝ) ^ (-(1 / 3 : ℝ)) := by
  have hμ : ∀ s, 0 < oMu.prob s := fun s ↦ by rw [oMu_prob]; norm_num
  have hΓ : ∀ s, 0 < trueGamma oMDP oPolicy oMu s := fun s ↦ by
    rw [oneState_trueGamma]; norm_num
  obtain ⟨K, hK, hb⟩ := abs_coverage_twoSided_sub_le oMDP oPolicy oMu h0 h1 V₀ hμ hΓ
  refine ⟨K, hK, fun T hT z hz ↦ ?_⟩
  have h := hb T hT (fun _ ↦ 1) (fun h ↦ by simpa using congrFun h ()) z hz
  simp only [oneState_valueFixedPoint, one_mem_signSel_iff, oneState_oracleLambda,
    Fintype.univ_unit, Finset.sum_singleton, one_mul, mul_one] at h ⊢
  exact h

/-- **E2, the rule under-covers.** For every `z ≥ 0`, eventually in `T` the coverage of the
selected half-lines is at most `Φ(z) − (1 − Φ(z))/2`, hence strictly below the nominal level
`1 − α = Φ(z)` that each selected set carries under the oracle Gaussian `N(V̄_T, Λ/T)`. -/
theorem oneState_signSel_coverage_eventually_lt {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1)
    (V₀ : Unit → ℝ) {z : ℝ} (hz : 0 ≤ z) :
    ∀ᶠ T : ℕ in atTop,
      (∑ ω : Fin T → Tuple Unit (Fin 2), pathWeight oMDP oPolicy oMu ω *
          {ω' : Fin T → Tuple Unit (Fin 2) | oMDP.valueFixedPoint oPolicy () ∈
            signSel (z * Real.sqrt (1 / T)) (prAverage oMDP η₀ V₀ ω' ())}.indicator 1 ω) ≤
        (gaussianReal 0 1).real (Set.Iic z) -
          (1 - (gaussianReal 0 1).real (Set.Iic z)) / 2 := by
  obtain ⟨K, hK, hb⟩ := oneState_signSel_coverage h0 h1 V₀
  set Φz := (gaussianReal 0 1).real (Set.Iic z)
  have hgap : 0 < 1 - Φz := sub_pos.2 (gaussianReal_real_Iic_lt_one z)
  have hlim : Tendsto (fun T : ℕ ↦ (T : ℝ) ^ (-(1 / 3 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  have hε : 0 < (1 - Φz) / (4 * K) := by positivity
  filter_upwards [hlim.eventually (gt_mem_nhds hε), eventually_ge_atTop 1] with T hTr hT
  have h := (abs_le.1 (hb T hT z hz)).2
  have hr : 2 * K * (T : ℝ) ^ (-(1 / 3 : ℝ)) ≤ (1 - Φz) / 2 := by
    have := mul_le_mul_of_nonneg_left hTr.le (by positivity : (0 : ℝ) ≤ 2 * K)
    calc 2 * K * (T : ℝ) ^ (-(1 / 3 : ℝ)) ≤ 2 * K * ((1 - Φz) / (4 * K)) := this
      _ = (1 - Φz) / 2 := by field_simp; ring
  linarith

end OneState

end StatisticalRL.Ch7Rest.TDInference
