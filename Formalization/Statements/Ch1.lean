import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.Real

/-! Source-facing statement index for Chapter 1. -/

open MeasureTheory
open scoped ENNReal

namespace StatisticalRL.Statements
universe u

/-- `eq:KL-ub-chi2`, `chapters/intro.tex:216–247` (`eq:TV` `:222–227`, `eq:defn-KL` and
`eq:defn-chi2` `:229–235`, display `:241–247`). For probability measures `P ≪ Q` on a common
measurable space: `2 TV(P,Q)² ≤ KL(P‖Q) ≤ χ²(P‖Q)`, with
`TV(P,Q) = sup_{A ∈ 𝓕} |P(A) − Q(A)|` (supremum over measurable events) and
`χ²(P‖Q) = ∫ (dP/dQ − 1)² dQ` as an extended-real (`ℝ≥0∞`) integral, which is `∞` when
`dP/dQ ∉ L²(Q)` (the printed integral of a nonnegative function). `KL` is Mathlib's
`InformationTheory.klDiv`: for probability measures with `P ≪ Q` it equals
`∫ log(dP/dQ) dP` when the log-likelihood ratio is `P`-integrable and `∞` otherwise, which is
the printed `∫ log(dP/dQ) dP` (its negative part is integrable, so the integral is `+∞` exactly
when it is not integrable). `P ≪ Q` is the printed condition under which KL and `χ²` are
defined (`:229`). `P ≪ Q` is also needed for the `∫⁻` form of χ²: without it KL = ∞ while
the integral of the absolutely-continuous part can be finite (e.g. P = δ₁, Q = δ₀). The
inequalities are cited ("well known", `tsybakov2009introduction`) and are proved from
scratch. -/
def Eq_KL_ub_chi2 : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P Q : Measure Ω) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q], P ≪ Q →
    ENNReal.ofReal
        (2 * (⨆ A : {A : Set Ω // MeasurableSet A}, |P.real A.1 - Q.real A.1|) ^ 2) ≤
      InformationTheory.klDiv P Q ∧
    InformationTheory.klDiv P Q ≤
      ∫⁻ x, ENNReal.ofReal (((P.rnDeriv Q x).toReal - 1) ^ 2) ∂Q

end StatisticalRL.Statements
