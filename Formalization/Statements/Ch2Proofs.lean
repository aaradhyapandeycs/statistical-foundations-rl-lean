import Formalization.PrelimKL.KLArbitraryFinitePi
import Formalization.Probability.EmpiricalBernsteinSharp.EmpiricalBernsteinRandomFamily
import Formalization.Probability.Fano.ReverseFanoInfimum
import Formalization.Probability.Fano.FanoLemma
import Formalization.Probability.BernoulliKLComparison
import Formalization.Generative.GenerativeLowerBoundBernoulli
import Formalization.Probability.BernoulliTailProofs
import Formalization.MDP.PolicyIteration
import Formalization.MDP.PolicyMatrixResolvent
import Formalization.Probability.AzumaNaturalHistory
import Formalization.Statements.Ch2
import Formalization.Probability.Variance
import Formalization.Probability.FreedmanNaturalHistory
import Formalization.MDP.RewardPerturbation
import Formalization.MDP.IterationCount
import Formalization.MDP.MatrixBellman
import Formalization.MDP.PrelimDisplays
import Formalization.MDP.ForcedPrefixBridge
import Formalization.MDP.PrefixValueBridge
import Formalization.MDP.DiscountedOccupancy
import Formalization.MDP.FiniteOccupancy
import Formalization.MDP.FiniteQTrajectory

namespace StatisticalRL.Statements.Ch2
open MeasureTheory

/-- Identification of the policy Bellman solution with the trajectory Q-value, assembled from
`trajectoryExpectedQ_eq_policyFixedPoint`. -/
private theorem trajQ_ident {State Action : Type*} [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action) :
    M.trajectoryExpectedQ π = M.policyFixedPoint π :=
  funext fun s ↦ funext fun a ↦ M.trajectoryExpectedQ_eq_policyFixedPoint π s a

/-- Identification of the trajectory value with the policy average of the Bellman solution. -/
private theorem trajV_ident {State Action : Type*} [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action) :
    M.trajectoryExpectedValue π = fun s ↦ (π s).expectation (M.policyFixedPoint π s) := by
  funext s
  rw [M.trajectoryExpectedValue_eq_policyAverageQ π s, trajQ_ident]

theorem Lemma2_2_holds : Lemma2_2 := by
  intro State Action _ _ M V Vhat hV hVhat
  exact M.transitionVariance_perturbation hV hVhat

theorem Lemma2_9_holds : Lemma2_9 := by
  intro Ω _ μ _ X hX B σ hb hc n K hK hcap δ hδ hδ1
  have hbounded : ∀ᵐ ω ∂μ, |X 0 ω| ≤ B := Filter.Eventually.of_forall (hb 0)
  obtain ⟨ω, hω⟩ := hbounded.exists
  have hB : 0 ≤ B := (abs_nonneg (X 0 ω)).trans hω
  exact freedman_natural_history μ X hX B (σ ^ 2) hB (sq_nonneg σ)
    (fun k ↦ Filter.Eventually.of_forall (hb k)) hc n K hK
    hcap δ hδ hδ1

theorem Lemma2_8_holds : Lemma2_8 := by
  intro Ω _ μ _ X B hX hb hc n δ hδ hδ1
  exact azuma_natural_history_source μ X B hX hb hc n δ hδ hδ1

theorem Lemma2_3_holds : Lemma2_3 := by
  intro State Action _ _ M π
  classical
  rcases M.policyMatrices_resolvent_properties π with
    ⟨⟨_, hP⟩, ⟨_, hQ⟩⟩
  simpa only [DiscountedMDP.policyStateTransitionMatrix,
    DiscountedMDP.policyStateActionTransitionMatrix] using And.intro hP hQ

theorem Lemma2_1_holds : Lemma2_1 := by
  intro State Action _ _ M
  refine ⟨trajQ_ident M, ?_, ?_, ?_⟩
  · simp only [trajQ_ident M]
    exact M.iSup_policyFixedPoint_eq_optimalityFixedPoint
  · intro Q₀ k _
    exact M.value_iteration_error Q₀ k
  · intro π f hupdate hmax k _
    exact M.arbitraryGreedyPolicyIteration_error π f hupdate hmax k

theorem Lemma2_7_holds.{w} : Lemma2_7.{w} :=
  StatisticalRL.Probability.bernoulliTailBound_source.{w}

theorem Lemma2_13_holds : Lemma2_13 := by
  refine ⟨fun p q hp hp1 hq hq1 => ?_, fun p q hq hqp hp1 => ⟨?_, ?_⟩⟩
  · exact StatisticalRL.GenerativeLowerBound.bernoulliKLExpression_le_quadratic p q hq hq1 hp hp1
  · exact StatisticalRL.Probability.bernoulliKL_le_reverse p q hq hqp hp1
  · have h := StatisticalRL.GenerativeLowerBound.bernoulliKLExpression_le_quadratic q p
      (by linarith) hp1 (by linarith) (by linarith)
    have hsq : (q - p) ^ 2 = (p - q) ^ 2 := by ring
    rw [hsq] at h
    exact h

theorem Lemma2_11_holds : Lemma2_11.{u} := by
  intro Ω _ M P _
  exact StatisticalRL.PrelimFano.reverseFano_infimum_lower M P

section Lemma2_6
-- Scope of the V2 wrapper (its original `open` line), kept local to this entry.
open StatisticalRL.FiniteDistribution MeasureTheory ProbabilityTheory

theorem Lemma2_6_holds : Lemma2_6 := by
  intro State _ Ω _ μ _ d N hN2 δ hδ hδ1
  letI : MeasurableSpace State := ⊤
  intro hN draw hdraw hlaw family hfamily hindep hV
  have h := d.randomBorelFamily_empiricalBernstein_success_gt μ N hN hN2 δ hδ hδ1
    draw hdraw hlaw family hfamily hindep (Filter.Eventually.of_forall hV)
  have hsubset : {ω | ∀ V ∈ family ω,
      |(empiricalRow N hN (draw ω)).expectation V-d.expectation V| ≤
        empiricalBernsteinFamilyRadius (empiricalRow N hN (draw ω)) N (family ω).card δ V} ⊆
      {ω | ∀ V ∈ family ω,
        |(empiricalRow N hN (draw ω)).expectation V-d.expectation V| ≤
          Real.sqrt (2*Real.log (4*(family ω).card/δ)/((N : ℝ)-1)) *
            Real.sqrt ((empiricalRow N hN (draw ω)).expectation (fun s ↦ V s^2) -
              ((empiricalRow N hN (draw ω)).expectation V)^2) +
          7*‖V‖*Real.log (4*(family ω).card/δ)/(3*((N : ℝ)-1))} := by
    intro ω hω V hmem
    have hk : 0 < (family ω).card := Finset.card_pos.mpr ⟨V, hmem⟩
    have hk1 : (1 : ℝ) ≤ (family ω).card := by exact_mod_cast hk
    have harg : 1 < 4*((family ω).card : ℝ)/δ := by
      apply (lt_div_iff₀ hδ).2
      nlinarith
    have hlog : 0 ≤ Real.log (4*((family ω).card : ℝ)/δ) := (Real.log_pos harg).le
    have hn : (0 : ℝ) < (N : ℝ)-1 := by
      have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
      linarith
    let row := empiricalRow N hN (draw ω)
    have hroot : Real.sqrt (2*row.variance V*Real.log (4*((family ω).card : ℝ)/δ)/((N : ℝ)-1)) =
        Real.sqrt (2*Real.log (4*((family ω).card : ℝ)/δ)/((N : ℝ)-1))*Real.sqrt (row.variance V) := by
      rw [← Real.sqrt_mul (by positivity : 0 ≤ 2*Real.log (4*((family ω).card : ℝ)/δ)/((N : ℝ)-1))]
      congr 1
      ring
    have hv := hω V hmem
    unfold empiricalBernsteinFamilyRadius at hv
    rw [hroot] at hv
    simpa only [FiniteDistribution.variance] using hv
  exact h.trans_le (measureReal_mono hsubset (measure_ne_top μ _))

end Lemma2_6

section Lemma2_4_5
open StatisticalRL.FiniteDistribution MeasureTheory ProbabilityTheory

theorem Lemma2_4_holds : Lemma2_4 := by
  intro State _ Ω _ μ _ d N hN δ hδ hδ1
  letI : MeasurableSpace State := ⊤
  intro draw hdraw hlaw family hfamily hindep hV
  exact d.randomBorelFamily_empiricalRow_success_gt μ N hN δ hδ hδ1 draw hdraw hlaw family
    hfamily hindep (Filter.Eventually.of_forall hV)

theorem Lemma2_5_holds : Lemma2_5 := by
  refine ⟨?_, ?_⟩
  · intro State _ Ω _ μ _ d N hN δ hδ hδ1
    letI : MeasurableSpace State := ⊤
    intro draw hdraw hlaw family hfamily hindep hV
    exact d.randomBorelFamily_bernstein_source μ N hN δ hδ hδ1 draw hdraw hlaw family
      hfamily hindep (Filter.Eventually.of_forall hV)
  · intro State Action _ _ _ _ Ω _ μ _ d N hN δ hδ hδ1
    letI : MeasurableSpace State := ⊤
    intro draw hdraw hrowlaw family hfamily hindep hV
    exact randomBorelFamily_matrixBernstein_of_rowMarginals μ d N hN δ hδ hδ1 draw hdraw
      hrowlaw family hfamily hindep (Filter.Eventually.of_forall hV)

end Lemma2_4_5

theorem Lemma2_12_holds : Lemma2_12.{u, v} := by
  intro ι hι α hα P Q hP hQ
  exact StatisticalRL.PrelimKL.klDiv_pi_eq_sum α P Q

theorem Lemma2_10_holds : Lemma2_10.{u} := by
  refine ⟨?_, ?_⟩
  · intro Ω _ P _ β hfin hβ
    exact StatisticalRL.PrelimFano.fano_binary_infimum_lower P β hfin hβ
  · intro Ω _ M P _ β hM hβ0 hβ1 hKL
    exact StatisticalRL.PrelimFano.fano_multi_infimum_lower M P β hM hβ0 hβ1 hKL

theorem Eq_QV_pi_perturbation_r_inf_holds : Eq_QV_pi_perturbation_r_inf := by
  intro State Action _ _ M M' hP hγ π
  exact ⟨⟨trajQ_ident M π, trajQ_ident M' π,
      trajV_ident M π, trajV_ident M' π⟩,
    M.policyFixedPoint_sub_norm_le_of_reward M' hP hγ π,
    M.policyValue_sub_norm_le_of_reward M' hP hγ π⟩

theorem Eq_QV_star_perturbation_r_inf_holds : Eq_QV_star_perturbation_r_inf := by
  intro State Action _ _ M M' hP hγ
  exact ⟨fun π ↦ ⟨trajQ_ident M π, trajQ_ident M' π,
      trajV_ident M π, trajV_ident M' π⟩,
    M.optimal_reward_perturbation M' hP hγ⟩

theorem Lemma2_1_iterationCount_holds : Lemma2_1_iterationCount := by
  intro State Action _ _ M ε hε
  refine ⟨trajQ_ident M, ?_, fun Q₀ k hk ↦ M.value_iteration_count ε hε Q₀ k hk,
    fun π f hupdate hmax k hk ↦
      M.arbitraryGreedyPolicyIteration_count ε hε π f hupdate hmax k hk⟩
  simp only [trajQ_ident M]
  exact M.iSup_policyFixedPoint_eq_optimalityFixedPoint

theorem Eq_Qpi_Vpi_matrix_notation_inf_holds : Eq_Qpi_Vpi_matrix_notation_inf := by
  intro State Action _ _ M π
  have h := M.policyFixedPoint_matrix_forms π
  refine ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, ?_, ?_⟩
  · funext sa
    exact (congrFun (congrFun (trajQ_ident M π) sa.1) sa.2).symm
  · funext s
    rw [congrFun (trajV_ident M π) s]
    rfl

theorem Eq_defn_Vpi_inf_holds : Eq_defn_Vpi_inf := by
  intro State Action _ _ M π s
  exact ⟨M.integrable_infiniteDiscountedReturn π s, M.trajectoryExpectedValue_bounds π s⟩

theorem Eq_defn_Qpi_inf_horizon_holds : Eq_defn_Qpi_inf_horizon := by
  intro State Action _ _ M π s a
  exact ⟨M.integrable_infiniteDiscountedReturn_forced π s a, (M.trajectoryExpectedQ_bounds π s a).1,
    (M.trajectoryExpectedQ_bounds π s a).2, M.trajectoryExpectedValue_eq_policyAverageQ π s⟩

theorem Eq_optimal_Vstar_Qstar_defn_holds : Eq_optimal_Vstar_Qstar_defn := by
  intro State Action _ _ M
  refine ⟨M.exists_stationary_trajectory_optimal, fun f g hf hg ↦ ⟨?_, ?_⟩⟩
  · funext s a
    exact le_antisymm (hg _ s a).1 (hf _ s a).1
  · funext s
    obtain ⟨a⟩ := M.action_nonempty
    exact le_antisymm (hg _ s a).2 (hf _ s a).2

theorem Eq_defn_dpi_occupancy_discounted_dist_holds : Eq_defn_dpi_occupancy_discounted_dist := by
  intro State Action _ _ _ M ρ d dj
  have hd : ∀ π s, d π s = M.discountedStateOccupancy π ρ s := fun π s ↦
    (M.discountedStateOccupancy_eq_source π ρ s).symm
  have hdj : ∀ π s a, dj π s a = M.discountedJointOccupancy π ρ s a := fun π s a ↦
    (M.discountedJointOccupancy_eq_source π ρ s a).symm
  refine ⟨fun π ↦ ⟨?_, ?_⟩, fun f s a ↦ ?_⟩
  · simp only [hd]
    exact M.discountedStateOccupancy_sum π ρ
  · simp only [hdj]
    exact M.discountedJointOccupancy_sum π ρ
  · rw [hdj, hd, M.discountedJointOccupancy_deterministic]
    by_cases h : a = f s <;> simp [h]

theorem Eq_bellman_consistency_V_holds : Eq_bellman_consistency_V := by
  intro State Action _ _ M π Tπ TV
  refine ⟨M.trajectoryExpectedQ_bellman π, fun Q hQ ↦ ?_, ?_⟩
  · exact (M.policy_fixedPoint_exists_unique π).unique hQ (M.trajectoryExpectedQ_bellman π)
  · rw [M.trajectoryExpectedValue_eq_valueFixedPoint π]
    exact M.valueFixedPoint_spec π

theorem Eq_bellman_fix_point_holds : Eq_bellman_fix_point := by
  intro State Action _ _ M f hf T
  have hQ := M.trajectoryExpectedQ_eq_optimalityFixedPoint_of_optimal f (fun π s a ↦ (hf π s a).1)
  have hT : T = M.qOptimality := funext fun Q ↦ (M.qOptimality_eq_ciSup Q).symm
  rw [hT, hQ]
  exact ⟨M.optimalityFixedPoint_spec, fun Q h ↦
    M.optimality_fixedPoint_exists_unique.unique h M.optimalityFixedPoint_spec⟩

theorem Eq_gamma_contraction_preliminary_inf_holds : Eq_gamma_contraction_preliminary_inf := by
  intro State Action _ _ M π Q₁ Q₂ Tπ T
  have hT : T = M.qOptimality := funext fun Q ↦ (M.qOptimality_eq_ciSup Q).symm
  rw [hT]
  exact ⟨M.norm_qBellman_sub_le π Q₁ Q₂, M.norm_qOptimality_sub_le Q₁ Q₂⟩

theorem Eq_dh_pi_defn_holds : Eq_dh_pi_defn := by
  intro State Action _ _ _ _ stages ρ d dj
  have hd : ∀ i s, d i s = DecisionStage.stateOccupancy stages ρ i s := by
    intro i s
    convert (DecisionStage.stateOccupancy_eq_trajectory_event stages ρ i s).symm
  have hdj : ∀ i s a, dj i s a = DecisionStage.stateActionOccupancy stages ρ i s a := by
    intro i s a
    convert (DecisionStage.stateActionOccupancy_eq_trajectory_event stages ρ i s a).symm
  refine ⟨fun i s a ↦ ?_, fun i hi s ↦ ?_, fun f hf i s a ↦ ?_⟩
  · rw [hdj, hd]
    exact DecisionStage.stateActionOccupancy_eq stages ρ i s a
  · rw [hd]
    simp only [DecisionStage.stateOccupancy, hi, List.take_zero]
    rfl
  · rw [hdj, hd, DecisionStage.stateActionOccupancy_eq, hf i s]
    by_cases h : a = f i.val s <;> simp [EnvironmentStage.pointMass, h]

theorem Eq_Bellman_finite_pi_holds : Eq_Bellman_finite_pi := by
  intro State Action _ _ stages
  refine ⟨fun s ↦ ?_, fun s a ↦ ?_, fun i s a ↦ DecisionStage.trajectory_bellman_at stages i s a⟩
  · simp [DecisionStage.trajectoryValue_nil]
  · simp

theorem Eq_Bellman_finite_opt_holds : Eq_Bellman_finite_opt := by
  intro State Action _ _ _ es V Q det IsOptimal
  refine ⟨⟨EnvironmentStage.greedyDetSeq es, fun π n s a _ ↦
    EnvironmentStage.greedyDetSeq_dominates es π n s a⟩, fun f hf ↦ ?_⟩
  have hopt := EnvironmentStage.finite_det_optimal_eq es f hf
  have hlen := EnvironmentStage.controlled_length es (det f)
  refine ⟨fun s ↦ ?_, fun s a ↦ ?_, fun i s a ↦ ⟨?_, ?_⟩⟩
  · show DecisionStage.trajectoryValue ((EnvironmentStage.controlled es (det f)).drop es.length) s = 0
    rw [← hlen, List.drop_length]
    exact DecisionStage.trajectoryValue_nil s
  · show DecisionStage.trajectoryQ ((EnvironmentStage.controlled es (det f)).drop es.length) s a = 0
    rw [← hlen, List.drop_length]
    rfl
  · let i' : Fin (EnvironmentStage.controlled es (det f)).length := ⟨i.val, by rw [hlen]; exact i.isLt⟩
    have hb := (DecisionStage.trajectory_bellman_at (EnvironmentStage.controlled es (det f)) i' s a).1
    have hg : (EnvironmentStage.controlled es (det f)).get i' = (es.get i).withPolicy (det f i.val) := by
      rw [List.get_eq_getElem, EnvironmentStage.controlled_getElem]
      rfl
    rw [hg] at hb
    exact hb
  · show DecisionStage.trajectoryValue ((EnvironmentStage.controlled es
        (fun k x ↦ EnvironmentStage.pointMass (f k x))).drop i.val) s =
      ⨆ a', DecisionStage.trajectoryQ ((EnvironmentStage.controlled es
        (fun k x ↦ EnvironmentStage.pointMass (f k x))).drop i.val) s a'
    rw [(hopt i.val i.isLt).1 s]
    simp only [(hopt i.val i.isLt).2 s]
    rw [List.drop_eq_getElem_cons i.isLt]
    exact actionMaximum_eq_ciSup _

end StatisticalRL.Statements.Ch2
