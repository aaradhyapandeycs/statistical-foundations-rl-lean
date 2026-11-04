import Formalization.Statements.Ch7
import Formalization.RobustRL.TVSourceMaximum

open scoped BigOperators
namespace StatisticalRL.Statements.Ch7
universe u

theorem Lemma7_1_tv_holds : Lemma7_1_tv.{u} := by
  intro State instF instN p V σ hσ hV
  classical
  have hfeasible : StatisticalRL.RobustRL.tvFeasibleRow p σ =
      (fun q : StatisticalRL.FiniteDistribution State ↦
        (1 / 2 : ℝ) * ∑ s, |p.prob s - q.prob s| ≤ σ) := by
    funext q
    apply propext
    unfold StatisticalRL.RobustRL.tvFeasibleRow
    rw [StatisticalRL.RobustRL.eventTV_eq_finiteTotalVariation
      p.prob q.prob p.prob_nonneg q.prob_nonneg p.sum_prob q.sum_prob]
    rfl
  have hInf : StatisticalRL.RobustRL.tvPrimalInf p V σ =
      (⨅ q : {q : StatisticalRL.FiniteDistribution State //
        (1 / 2 : ℝ) * ∑ s, |p.prob s - q.prob s| ≤ σ},
        ∑ s, q.1.prob s * V s) := by
    unfold StatisticalRL.RobustRL.tvPrimalInf StatisticalRL.RobustRL.tvFeasibleRows
    rw [hfeasible]
    rfl
  obtain ⟨α, hα, heq, hmax⟩ :=
    StatisticalRL.RobustRL.TVProof.SourceMaximum.tvPrimalInf_eq_source_max p V σ hσ hV
  refine ⟨α, hα, ?_, ?_⟩
  · rw [← hInf]
    simpa [StatisticalRL.RobustRL.tvDualObjective,
      StatisticalRL.RobustRL.tvClipAbove, StatisticalRL.FiniteDistribution.expectation] using heq
  · intro β hβ
    simpa [StatisticalRL.RobustRL.tvDualObjective,
      StatisticalRL.RobustRL.tvClipAbove, StatisticalRL.FiniteDistribution.expectation] using hmax β hβ
end StatisticalRL.Statements.Ch7
