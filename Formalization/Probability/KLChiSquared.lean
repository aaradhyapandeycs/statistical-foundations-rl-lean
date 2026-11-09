import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Formalization.Probability.Fano.ReverseTest

/-!
# Total variation, KL and chi-squared divergences

Source: arXiv:2610.41903v1, `eq:KL-ub-chi2`, `chapters/intro.tex:216–247`
(definitions `eq:TV` `:222–227`, `eq:defn-KL` and `eq:defn-chi2` `:229–235`,
display `:241–247`).

* `klDiv_le_chiSquared`: `KL(P‖Q) ≤ χ²(P‖Q)` whenever `P ≪ Q`, with the
  chi-squared divergence written as the extended-real integral
  `∫⁻ x, ofReal ((dP/dQ x − 1)²) ∂Q` (it is `∞` when `dP/dQ ∉ L²(Q)`).
* `two_mul_sq_tv_le_klDiv`: `2 TV(P,Q)² ≤ KL(P‖Q)` with `TV` the supremum of
  `|P(A) − Q(A)|` over measurable events (Pinsker), from the event-level bound
  `StatisticalRL.PrelimFano.event_sq_gap_le_klDiv`.
-/

open MeasureTheory Real
open scoped ENNReal

namespace StatisticalRL.Probability

/-- Pointwise comparison of the KL generator with the chi-squared generator:
`x log x + 1 − x ≤ (x − 1)²` for `x ≥ 0` (from `log x ≤ x − 1`). -/
theorem klFun_le_sq_sub_one {x : ℝ} (hx : 0 ≤ x) :
    InformationTheory.klFun x ≤ (x - 1) ^ 2 := by
  rw [InformationTheory.klFun_apply]
  rcases hx.eq_or_lt with rfl | hpos
  · norm_num
  · have hlog := Real.log_le_sub_one_of_pos hpos
    have h := mul_le_mul_of_nonneg_left hlog hx
    nlinarith [h]

/-- `KL(P‖Q) ≤ χ²(P‖Q)` for finite measures with `P ≪ Q`, where the right side
is the extended-real integral `∫⁻ (dP/dQ − 1)² dQ`. -/
theorem klDiv_le_chiSquared {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsFiniteMeasure P] [IsFiniteMeasure Q] (hPQ : P ≪ Q) :
    InformationTheory.klDiv P Q ≤
      ∫⁻ x, ENNReal.ofReal (((P.rnDeriv Q x).toReal - 1) ^ 2) ∂Q := by
  rw [InformationTheory.klDiv_eq_lintegral_klFun, if_pos hPQ]
  exact lintegral_mono fun x ↦
    ENNReal.ofReal_le_ofReal (klFun_le_sq_sub_one ENNReal.toReal_nonneg)

/-- Pinsker's inequality with the total variation distance written as the
supremum over measurable events: `2 TV(P,Q)² ≤ KL(P‖Q)`. -/
theorem two_mul_sq_tv_le_klDiv {Ω : Type*} [MeasurableSpace Ω] (P Q : Measure Ω)
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    ENNReal.ofReal
        (2 * (⨆ A : {A : Set Ω // MeasurableSet A}, |P.real A.1 - Q.real A.1|) ^ 2) ≤
      InformationTheory.klDiv P Q := by
  by_cases htop : InformationTheory.klDiv P Q = ∞
  · rw [htop]; exact le_top
  set k := (InformationTheory.klDiv P Q).toReal with hk
  haveI : Nonempty {A : Set Ω // MeasurableSet A} := ⟨⟨∅, MeasurableSet.empty⟩⟩
  have hev : ∀ A : {A : Set Ω // MeasurableSet A}, |P.real A.1 - Q.real A.1| ≤ √(k / 2) := by
    intro A
    have h := StatisticalRL.PrelimFano.event_sq_gap_le_klDiv P Q A.2
    rw [ENNReal.ofReal_le_iff_le_toReal htop] at h
    apply Real.abs_le_sqrt
    rw [← hk] at h
    linarith
  have hsup : (⨆ A : {A : Set Ω // MeasurableSet A}, |P.real A.1 - Q.real A.1|) ≤ √(k / 2) :=
    ciSup_le hev
  have hbdd : BddAbove (Set.range fun A : {A : Set Ω // MeasurableSet A} ↦
      |P.real A.1 - Q.real A.1|) := ⟨√(k / 2), by rintro _ ⟨A, rfl⟩; exact hev A⟩
  have hnonneg : 0 ≤ ⨆ A : {A : Set Ω // MeasurableSet A}, |P.real A.1 - Q.real A.1| :=
    (abs_nonneg _).trans (le_ciSup hbdd ⟨∅, MeasurableSet.empty⟩)
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hsq : (⨆ A : {A : Set Ω // MeasurableSet A}, |P.real A.1 - Q.real A.1|) ^ 2 ≤ k / 2 := by
    calc _ ≤ (√(k / 2)) ^ 2 := pow_le_pow_left₀ hnonneg hsup 2
      _ = k / 2 := Real.sq_sqrt (by linarith)
  calc ENNReal.ofReal (2 * (⨆ A : {A : Set Ω // MeasurableSet A}, |P.real A.1 - Q.real A.1|) ^ 2)
      ≤ ENNReal.ofReal k := ENNReal.ofReal_le_ofReal (by linarith)
    _ = InformationTheory.klDiv P Q := ENNReal.ofReal_toReal htop

/-- The two printed inequalities of `eq:KL-ub-chi2` together. -/
theorem two_mul_sq_tv_le_klDiv_le_chiSquared {Ω : Type*} [MeasurableSpace Ω]
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hPQ : P ≪ Q) :
    ENNReal.ofReal
        (2 * (⨆ A : {A : Set Ω // MeasurableSet A}, |P.real A.1 - Q.real A.1|) ^ 2) ≤
      InformationTheory.klDiv P Q ∧
    InformationTheory.klDiv P Q ≤
      ∫⁻ x, ENNReal.ofReal (((P.rnDeriv Q x).toReal - 1) ^ 2) ∂Q :=
  ⟨two_mul_sq_tv_le_klDiv P Q, klDiv_le_chiSquared P Q hPQ⟩

end StatisticalRL.Probability
