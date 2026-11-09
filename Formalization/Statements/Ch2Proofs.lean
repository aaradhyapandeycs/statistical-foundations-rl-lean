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

namespace StatisticalRL.Statements
open MeasureTheory

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
    (Filter.Eventually.of_forall hcap) δ hδ hδ1

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
  constructor
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
  exact ⟨M.policyFixedPoint_sub_norm_le_of_reward M' hP hγ π,
    M.policyValue_sub_norm_le_of_reward M' hP hγ π⟩

theorem Eq_QV_star_perturbation_r_inf_holds : Eq_QV_star_perturbation_r_inf := by
  intro State Action _ _ M M' hP hγ
  exact M.optimal_reward_perturbation M' hP hγ

theorem Lemma2_1_iterationCount_holds : Lemma2_1_iterationCount := by
  intro State Action _ _ M ε hε
  exact ⟨fun Q₀ k hk ↦ M.value_iteration_count ε hε Q₀ k hk,
    fun π f hupdate hmax k hk ↦
      M.arbitraryGreedyPolicyIteration_count ε hε π f hupdate hmax k hk⟩

theorem Eq_Qpi_Vpi_matrix_notation_inf_holds : Eq_Qpi_Vpi_matrix_notation_inf := by
  intro State Action _ _ M π
  exact M.policyFixedPoint_matrix_forms π

end StatisticalRL.Statements
