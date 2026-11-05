import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.Complex.ExponentialBounds

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.Probability

universe u

/-- The real-valued observation represented by a Boolean Bernoulli draw. -/
def bernoulliBoolReal (b : Bool) : ℝ := if b then 1 else 0

/-- The real-valued Bernoulli law, obtained by mapping the Bool Bernoulli PMF
through its `0`/`1` embedding. -/
noncomputable def bernoulliRealLaw (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : Measure ℝ :=
  (PMF.bernoulli p.toNNReal (by
    apply NNReal.coe_le_coe.mp
    simpa only [Real.coe_toNNReal p hp] using hp1)).toMeasure |>.map bernoulliBoolReal

end StatisticalRL.Probability
