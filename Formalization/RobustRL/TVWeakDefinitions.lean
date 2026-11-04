import Formalization.RobustRL.TVCore
import Formalization.MDP.Basic

/-! Definitions for the source finite TV duality statement. -/
open scoped BigOperators
namespace StatisticalRL.RobustRL
variable {State : Type*} [Fintype State] [Nonempty State] [DecidableEq State]

/-- Actual finite probability rows allowed by the source TV uncertainty ball.
The radius is the source `σ` (the command `\ror` expands to `\sigma`). -/
def tvFeasibleRow (p : StatisticalRL.FiniteDistribution State) (σ : ℝ)
    (q : StatisticalRL.FiniteDistribution State) : Prop :=
  StatisticalRL.RobustRL.eventTV p.prob q.prob ≤ σ

/-- The actual feasible-row type for a fixed nominal row and radius. -/
abbrev tvFeasibleRows (p : StatisticalRL.FiniteDistribution State) (σ : ℝ) :=
  {q : StatisticalRL.FiniteDistribution State // tvFeasibleRow p σ q}

/-- The exact source clipped-vector dual objective. The final term uses the
actual finite minimum of the clipped vector, as in `robust_RL.tex`; it is not
silently replaced by a candidate parameter. -/
noncomputable def tvDualObjective (p : StatisticalRL.FiniteDistribution State)
    (V : State → ℝ) (σ α : ℝ) : ℝ :=
  p.expectation (StatisticalRL.RobustRL.tvClipAbove V α) -
    σ * (α -
      Finset.univ.inf' Finset.univ_nonempty
        (StatisticalRL.RobustRL.tvClipAbove V α))

/-- The source primal infimum over actual finite distributions in the TV ball. -/
noncomputable def tvPrimalInf (p : StatisticalRL.FiniteDistribution State)
    (V : State → ℝ) (σ : ℝ) : ℝ :=
  ⨅ q : tvFeasibleRows p σ, q.1.expectation V

/-- The source dual supremum over the closed interval `[Vmin,Vmax]`. Once
continuity is established this supremum is a maximum; this file only proves
the weak-duality inequality and does not use attainment. -/
noncomputable def tvDualSup (p : StatisticalRL.FiniteDistribution State)
    (V : State → ℝ) (σ : ℝ) : ℝ :=
  ⨆ α : Set.Icc
      (Finset.univ.inf' Finset.univ_nonempty V)
      (Finset.univ.sup' Finset.univ_nonempty V),
    tvDualObjective p V σ α.1


end StatisticalRL.RobustRL
