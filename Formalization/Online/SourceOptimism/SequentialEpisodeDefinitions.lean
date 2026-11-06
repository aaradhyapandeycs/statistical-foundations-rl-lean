import Formalization.Online.SourceOptimism.EpisodicSelectorDefinitions
import Formalization.Online.SourceOptimism.FinitePathHistoryDefinitions
import Formalization.MDP.PointMassDefinitions
import Formalization.Probability.FiniteSampleDefinitions
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Definitions of the causal sequential online law and realized history. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {Row Outcome : Type*} [Fintype Row] [Fintype Outcome]

/-- The direct chronological successor law. At each step choose from the
revealed history, draw from the true selected row, and recurse from the actual
appended observation. No stack experiment appears in this definition. -/
noncomputable def onlineSequentialOutcomeLaw
    (d : Row → FiniteDistribution Outcome)
    (choose : List (Row × Outcome) → Row) :
    (n : ℕ) → List (Row × Outcome) → FiniteDistribution (OnlineOutcomePath Outcome n)
  | 0, _ => EnvironmentStage.pointMass PUnit.unit
  | n+1, history =>
    { prob := fun path => (d (choose history)).prob path.2.1 *
        (onlineSequentialOutcomeLaw d choose n
          (history++[(choose history,path.2.1)])).prob path.2.2
      prob_nonneg := fun path => mul_nonneg ((d (choose history)).prob_nonneg _)
        ((onlineSequentialOutcomeLaw d choose n _).prob_nonneg _)
      sum_prob := by
        classical
        change (∑ path : PUnit × Outcome × OnlineOutcomePath Outcome n,
          (d (choose history)).prob path.2.1 *
            (onlineSequentialOutcomeLaw d choose n
              (history++[(choose history,path.2.1)])).prob path.2.2)=1
        rw [Fintype.sum_prod_type]
        simp only [Fintype.sum_unique]
        rw [Fintype.sum_prod_type]
        simp_rw [← Finset.mul_sum,FiniteDistribution.sum_prob,mul_one]
        exact (d (choose history)).sum_prob }

/-- The independent source reset-vector law, defined without stacks. -/
noncomputable def onlineInitialVectorLaw {State : Type*} [Fintype State]
    (ρ : FiniteDistribution State) (K : ℕ) : FiniteDistribution (Fin K → State) where
  prob initial := ∏ k,ρ.prob (initial k)
  prob_nonneg initial := Finset.prod_nonneg (fun k _ => ρ.prob_nonneg _)
  sum_prob := by
    classical
    rw [← Fintype.prod_sum]
    simp [FiniteDistribution.sum_prob]

/-- Actual source sequential joint reset/path law for a deterministic causal
episode planner. Its normalization follows from the reset and conditional path
laws, not a coupling assumption. -/
noncomputable def onlineSequentialEpisodeLaw
    {State Action : Type*} [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0<H) (E : Fin H → EnvironmentStage State Action)
    (ρ : FiniteDistribution State) (fallback : State)
    (planner : OnlineEpisodePlanner State Action H) (n : ℕ) :
    FiniteDistribution ((Fin K → State) × OnlineOutcomePath State n) where
  prob sample := (onlineInitialVectorLaw ρ K).prob sample.1 *
    (onlineSequentialOutcomeLaw (onlineMDPSuccessorRowLaw E)
      (onlineEpisodicChoose H K hH sample.1 fallback planner) n []).prob sample.2
  prob_nonneg sample := mul_nonneg ((onlineInitialVectorLaw ρ K).prob_nonneg _)
    ((onlineSequentialOutcomeLaw (onlineMDPSuccessorRowLaw E)
      (onlineEpisodicChoose H K hH sample.1 fallback planner) n []).prob_nonneg _)
  sum_prob := by
    classical
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum,FiniteDistribution.sum_prob,mul_one]
    exact (onlineInitialVectorLaw ρ K).sum_prob

end StatisticalRL.OnlineRL
