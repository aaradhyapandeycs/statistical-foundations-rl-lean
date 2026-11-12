import Formalization.Probability.EmpiricalRow
import Formalization.Probability.Variance
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Probability.Moments.Variance

/-!
# Bridges from `FiniteDistribution` to Mathlib

`StatisticalRL.FiniteDistribution Ω` is the real probability simplex on a finite carrier.  This
module records, once, how it sits inside Mathlib's notions:

* `FiniteDistribution.equivStdSimplex`: the equivalence with `stdSimplex ℝ Ω`;
* `FiniteDistribution.equivPMF`: the equivalence with `PMF Ω` (via the existing `toPMF`);
* `FiniteDistribution.rowMeasure_singleton`, `FiniteDistribution.rowMeasure_real_singleton`,
  `FiniteDistribution.isProbabilityMeasure_rowMeasure_top`: atom masses and normalisation of the
  row measure, for the discrete sigma-algebra `⊤` used by `rowMeasure`;
* `FiniteDistribution.variance_rowMeasure`: `ProbabilityTheory.variance f d.rowMeasure` is
  `d.variance f`.

The expectation bridge is `FiniteDistribution.rowMeasure_integral`
(`Formalization/Probability/EmpiricalRow.lean`).
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace StatisticalRL

namespace FiniteDistribution

variable {Ω : Type*} [Fintype Ω]

/-- The masses of a finite distribution lie in Mathlib's standard simplex. -/
theorem prob_mem_stdSimplex (d : FiniteDistribution Ω) : d.prob ∈ stdSimplex ℝ Ω :=
  ⟨d.prob_nonneg, d.sum_prob⟩

/-- The finite distribution with the masses of a point of the standard simplex. -/
def ofStdSimplex (p : stdSimplex ℝ Ω) : FiniteDistribution Ω where
  prob := p.1
  prob_nonneg := p.2.1
  sum_prob := p.2.2

/-- A finite distribution as a point of the standard simplex. -/
def toStdSimplex (d : FiniteDistribution Ω) : stdSimplex ℝ Ω :=
  ⟨d.prob, d.prob_mem_stdSimplex⟩

@[simp]
theorem prob_ofStdSimplex (p : stdSimplex ℝ Ω) : (ofStdSimplex p).prob = p.1 := rfl

@[simp]
theorem toStdSimplex_val (d : FiniteDistribution Ω) : (d.toStdSimplex : Ω → ℝ) = d.prob := rfl

/-- Finite distributions on `Ω` are the points of the standard simplex `stdSimplex ℝ Ω`. -/
def equivStdSimplex : FiniteDistribution Ω ≃ stdSimplex ℝ Ω where
  toFun := toStdSimplex
  invFun := ofStdSimplex
  left_inv _ := rfl
  right_inv _ := rfl

/-- The finite distribution with the real masses of a Mathlib probability mass function. -/
noncomputable def ofPMF (p : PMF Ω) : FiniteDistribution Ω where
  prob x := (p x).toReal
  prob_nonneg _ := ENNReal.toReal_nonneg
  sum_prob := by
    rw [← ENNReal.toReal_sum (fun x _ ↦ p.apply_ne_top x), ← tsum_fintype (L := .unconditional _),
      p.tsum_coe]
    rfl

@[simp]
theorem prob_ofPMF (p : PMF Ω) (x : Ω) : (ofPMF p).prob x = (p x).toReal := rfl

@[simp]
theorem toPMF_ofPMF (p : PMF Ω) : (ofPMF p).toPMF = p :=
  PMF.ext fun x ↦ by rw [toPMF_apply, prob_ofPMF, ENNReal.ofReal_toReal (p.apply_ne_top x)]

@[simp]
theorem ofPMF_toPMF (d : FiniteDistribution Ω) : ofPMF d.toPMF = d :=
  ext (funext fun x ↦ by rw [prob_ofPMF, toPMF_apply, ENNReal.toReal_ofReal (d.prob_nonneg x)])

/-- `toPMF` is injective: a finite distribution is determined by its probability mass function. -/
theorem toPMF_injective : Function.Injective (toPMF : FiniteDistribution Ω → PMF Ω) :=
  fun d e h ↦ by rw [← ofPMF_toPMF d, ← ofPMF_toPMF e, h]

/-- Finite distributions on `Ω` are the probability mass functions on `Ω`. -/
noncomputable def equivPMF : FiniteDistribution Ω ≃ PMF Ω where
  toFun := toPMF
  invFun := ofPMF
  left_inv := ofPMF_toPMF
  right_inv := toPMF_ofPMF

/-- The expectation of a finite distribution is the integral against its Mathlib probability mass
function, viewed as a measure (for the discrete sigma-algebra). -/
theorem expectation_eq_integral_toPMF (d : FiniteDistribution Ω) (f : Ω → ℝ) :
    letI : MeasurableSpace Ω := ⊤
    d.expectation f = ∫ x, f x ∂d.toPMF.toMeasure :=
  (rowMeasure_integral d f).symm

section RowMeasure

local instance rowMeasureDiscrete : MeasurableSpace Ω := ⊤

/-- The row measure assigns to each atom the mass of the distribution. -/
theorem rowMeasure_singleton (d : FiniteDistribution Ω) (x : Ω) :
    d.rowMeasure {x} = ENNReal.ofReal (d.prob x) := by
  rw [rowMeasure, PMF.toMeasure_apply_singleton _ _ (MeasurableSpace.measurableSet_top),
    toPMF_apply]

/-- The row measure assigns to each atom its (real) mass. -/
theorem rowMeasure_real_singleton (d : FiniteDistribution Ω) (x : Ω) :
    d.rowMeasure.real {x} = d.prob x := by
  rw [measureReal_def, rowMeasure_singleton, ENNReal.toReal_ofReal (d.prob_nonneg x)]

/-- The row measure of a finite distribution is a probability measure (for the sigma-algebra
`⊤` with which `rowMeasure` is built). -/
theorem isProbabilityMeasure_rowMeasure_top (d : FiniteDistribution Ω) :
    IsProbabilityMeasure d.rowMeasure :=
  inferInstanceAs (IsProbabilityMeasure d.toPMF.toMeasure)

/-- The measure-theoretic variance of `f` under the row measure is the finite-row variance
`E[f²] - (E f)²`. -/
theorem variance_rowMeasure (d : FiniteDistribution Ω) (f : Ω → ℝ) :
    ProbabilityTheory.variance f d.rowMeasure = d.variance f := by
  have hf : AEMeasurable f d.rowMeasure := (measurable_from_top (f := f)).aemeasurable
  rw [ProbabilityTheory.variance_eq_integral hf, rowMeasure_integral d f,
    d.variance_eq_expectation_centered_sq]
  exact rowMeasure_integral d (fun x ↦ (f x - d.expectation f) ^ 2)

end RowMeasure

end FiniteDistribution

end StatisticalRL
