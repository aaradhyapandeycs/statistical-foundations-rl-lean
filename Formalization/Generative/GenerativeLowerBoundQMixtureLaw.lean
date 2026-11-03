import Formalization.Generative.GenerativeLowerBoundQMixtureLikelihood
import Formalization.Generative.GenerativeLowerBoundJointLaw

/-! Actual uniform alternative mixture on common active-coordinate samples. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound

variable {m A N : ℕ} [NeZero m] [NeZero A]
local notation "Θ" => Fin m × Fin A
local notation "Ω" => QMixtureActiveCoordinates m A N → Bool

/-- Each index uses its actual heterogeneous product probability law. -/
noncomputable def qMixtureActiveAlternative (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1)
    (θ : Θ) : Measure Ω :=
  indexedBernoulliLaw (qMixtureBernoulliParameter (some θ) p q)
    (qMixtureBernoulliParameter_le_one (some θ) p q hp hq)

instance qMixtureActiveAlternative_probability (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1)
    (θ : Θ) : IsProbabilityMeasure (qMixtureActiveAlternative (N := N) p q hp hq θ) := by
  unfold qMixtureActiveAlternative
  infer_instance

/-- The actual baseline product probability law. -/
noncomputable def qMixtureActiveBaseline (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1) : Measure Ω :=
  indexedBernoulliLaw (qMixtureBernoulliParameter none p q)
    (qMixtureBernoulliParameter_le_one none p q hp hq)

instance qMixtureActiveBaseline_probability (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1) :
    IsProbabilityMeasure (qMixtureActiveBaseline (m := m) (A := A) (N := N) p q hp hq) := by
  unfold qMixtureActiveBaseline
  infer_instance

/-- Actual equally weighted alternative mixture, normalized by the uniform
prior on the nonempty set of exactly m*A changed rows. -/
noncomputable def qMixtureActiveLaw (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1) : Measure Ω :=
  (finiteJointLaw (qMixtureActiveAlternative (m := m) (A := A) (N := N) p q hp hq)).map Prod.snd

instance qMixtureActiveLaw_probability (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1) :
    IsProbabilityMeasure (qMixtureActiveLaw (m := m) (A := A) (N := N) p q hp hq) := by
  unfold qMixtureActiveLaw
  exact Measure.isProbabilityMeasure_map (measurable_snd.aemeasurable)

/-- Baseline atom positivity makes its Radon–Nikodym denominator legitimate,
including when N=0 and the product is empty. -/
theorem qMixtureActiveBaseline_atom_ne_zero (p q : ℝ≥0) (hp : 0 < p)
    (hp1 : p < 1) (hq1 : q ≤ 1) (x : Ω) :
    qMixtureActiveBaseline p q hp1.le hq1 {x} ≠ 0 := by
  unfold qMixtureActiveBaseline
  apply indexedBernoulliLaw_atom_ne_zero
  · intro z; simpa [qMixtureBernoulliParameter] using hp
  · intro z; simpa [qMixtureBernoulliParameter] using hp1

/-- Pointwise actual mixture Radon–Nikodym density as an atom ratio. The
further identification with the uniform sum of row likelihood products is
separate and is not assumed here. -/
theorem qMixtureActiveLaw_rnDeriv_atom (p q : ℝ≥0) (hp : 0 < p)
    (hp1 : p < 1) (hq1 : q ≤ 1) (x : Ω) :
    (qMixtureActiveLaw p q hp1.le hq1).rnDeriv
        (qMixtureActiveBaseline p q hp1.le hq1) x =
      qMixtureActiveLaw p q hp1.le hq1 {x} /
        qMixtureActiveBaseline p q hp1.le hq1 {x} := by
  exact finite_rnDeriv_apply _ _ (qMixtureActiveBaseline_atom_ne_zero p q hp hp1 hq1) x

end StatisticalRL.GenerativeLowerBound
