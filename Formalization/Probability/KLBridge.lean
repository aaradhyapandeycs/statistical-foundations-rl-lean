import Formalization.OfflineRL.LowerBoundDataKL
import Formalization.Generative.GenerativeLowerBoundBernoulliMeasure
import Formalization.ModelFree.QLearningFiniteLogSumPinsker
import Formalization.ModelFree.QLearningStoppedPrefixKLAtomBase
import Formalization.Probability.InformationTheory.CountableTailLogSum
import Formalization.Probability.InformationTheory.PinskerBinary
import Formalization.RLHF.VPO.Definitions

/-!
# One Kullback-Leibler vocabulary

The library carries several real-valued Kullback-Leibler (KL) forms, each written as a sum of
atoms `a * log (a / b)`.  This module records, once, how they are related to each other and to
Mathlib's `InformationTheory.klDiv`.

## Mathlib status (pin `32d24245`)

Mathlib has `InformationTheory.klDiv μ ν : ℝ≥0∞` (`Mathlib/InformationTheory/KullbackLeibler/Basic.lean`),
equal to `⊤` when `μ` is not absolutely continuous with respect to `ν`
(`InformationTheory.klDiv_of_not_ac`), and `InformationTheory.toReal_klDiv_of_measure_eq` for the
real value in the absolutely continuous case.  There is no Pinsker inequality, chain rule or
data-processing inequality at the pin.

## The totalisation caveat

All local forms are **totalised**: in Lean `Real.log 0 = 0` and `x / 0 = 0`, so an atom
`a * log (a / b)` with `a > 0` and `b = 0` contributes `0`, whereas the true KL divergence is `⊤`.
The real-valued forms (`StatisticalRL.GenerativeLowerBound.finiteKLExpression`,
`StatisticalRL.QLearning.qFiniteKLOn`,
`StatisticalRL.QLearning.CountablePinsker.klAtom`, `StatisticalRL.QLearning.qBinaryKL`,
`StatisticalRL.Ch7Rest.Rlhf.klDiv`) are therefore meaningful as KL divergences only under a support
hypothesis (absolute continuity, i.e. `b = 0 → a = 0` atomwise).  The bridges below carry exactly
that hypothesis, and the `*_off_support` lemmas record that without it Mathlib's value is `⊤`
while the real-valued forms stay finite.

## Contents

* `StatisticalRL.klTerm`: the single shared atom `a * log (a / b)`.  The three scalar atoms
  `qFiniteKLTerm`, `klAtom`, `qStoppedPrefixKLAtom` (each written with an `if a = 0 then 0` guard)
  equal it for all reals, and `finiteKLExpression`, `qFiniteKLOn` and the `RLHF` `klDiv` are
  its sums.
* Bridges to Mathlib for finite distributions via `FiniteDistribution.rowMeasure`.
* The binary form `qBinaryKL` against `bernoulliKLExpression` and Mathlib's `klDiv` of Bernoulli
  laws.
* Off-support behaviour.

`StatisticalRL.Ch7Rest.Rlhf.klDiv` is deliberately not renamed here: it is cited from the
statement index and the ledgers.  Renaming it (for example to `klExpr`, to avoid the clash in
spirit with `InformationTheory.klDiv`) is deferred.
-/

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace StatisticalRL

/-- The shared KL atom `a * log (a / b)` (numerator first, reference second), with Lean's
totalised `log` and division.  For `a = 0` it is `0`; for `a > 0` and `b = 0` it is `0` as well,
which is *not* the KL value (`⊤`), so the sums of these atoms are KL divergences only under the
support hypothesis `b = 0 → a = 0`. -/
noncomputable def klTerm (a b : ℝ) : ℝ := a * Real.log (a / b)

section Atoms

/-- A zero numerator contributes zero. -/
@[simp] theorem klTerm_zero_left (b : ℝ) : klTerm 0 b = 0 := by simp [klTerm]

/-- A zero reference mass contributes zero (the totalised value, whatever the numerator). -/
@[simp] theorem klTerm_zero_right (a : ℝ) : klTerm a 0 = 0 := by simp [klTerm]

/-- `QLearning.qFiniteKLTerm` is the shared atom `klTerm`, for all reals. -/
theorem qFiniteKLTerm_eq_klTerm (a b : ℝ) : QLearning.qFiniteKLTerm a b = klTerm a b := by
  unfold QLearning.qFiniteKLTerm klTerm
  split_ifs with h <;> simp [h]

/-- `QLearning.CountablePinsker.klAtom` is the shared atom `klTerm`, for all reals. -/
theorem klAtom_eq_klTerm (a b : ℝ) : QLearning.CountablePinsker.klAtom a b = klTerm a b := by
  unfold QLearning.CountablePinsker.klAtom klTerm
  split_ifs with h <;> simp [h]

/-- `QLearning.CountablePinsker.qStoppedPrefixKLAtom` is the shared atom `klTerm`, for all
reals. -/
theorem qStoppedPrefixKLAtom_eq_klTerm (a b : ℝ) :
    QLearning.CountablePinsker.qStoppedPrefixKLAtom a b = klTerm a b := by
  unfold QLearning.CountablePinsker.qStoppedPrefixKLAtom klTerm
  split_ifs with h <;> simp [h]

/-- The three guarded scalar atoms agree: `klAtom = qFiniteKLTerm`. -/
theorem klAtom_eq_qFiniteKLTerm (a b : ℝ) :
    QLearning.CountablePinsker.klAtom a b = QLearning.qFiniteKLTerm a b := by
  rw [klAtom_eq_klTerm, qFiniteKLTerm_eq_klTerm]

/-- The three guarded scalar atoms agree: `qStoppedPrefixKLAtom = klAtom`. -/
theorem qStoppedPrefixKLAtom_eq_klAtom (a b : ℝ) :
    QLearning.CountablePinsker.qStoppedPrefixKLAtom a b =
      QLearning.CountablePinsker.klAtom a b := by
  rw [qStoppedPrefixKLAtom_eq_klTerm, klAtom_eq_klTerm]

end Atoms

section Sums

variable {Ω : Type*} [Fintype Ω]

/-- `finiteKLExpression` is the sum of `klTerm` atoms (definitional). -/
theorem finiteKLExpression_eq_sum_klTerm (u v : Ω → ℝ) :
    GenerativeLowerBound.finiteKLExpression u v = ∑ i, klTerm (u i) (v i) := rfl

omit [Fintype Ω] in
/-- `qFiniteKLOn s` is the sum of `klTerm` atoms over `s`, with no hypothesis. -/
theorem qFiniteKLOn_eq_sum_klTerm (s : Finset Ω) (a b : Ω → ℝ) :
    QLearning.qFiniteKLOn s a b = ∑ i ∈ s, klTerm (a i) (b i) := by
  unfold QLearning.qFiniteKLOn
  exact Finset.sum_congr rfl fun i _ => qFiniteKLTerm_eq_klTerm _ _

/-- `qFiniteKLOn` over the whole carrier is `finiteKLExpression`, with no hypothesis. -/
theorem qFiniteKLOn_univ_eq_finiteKLExpression (a b : Ω → ℝ) :
    QLearning.qFiniteKLOn Finset.univ a b = GenerativeLowerBound.finiteKLExpression a b :=
  qFiniteKLOn_eq_sum_klTerm _ _ _

/-- On a finite carrier the countable KL series of `klAtom` atoms is `finiteKLExpression`. -/
theorem tsum_klAtom_eq_finiteKLExpression (a b : Ω → ℝ) :
    (∑' i, QLearning.CountablePinsker.klAtom (a i) (b i)) =
      GenerativeLowerBound.finiteKLExpression a b := by
  rw [tsum_fintype]
  exact Finset.sum_congr rfl fun i _ => klAtom_eq_klTerm _ _

/-- The `RLHF` `klDiv` (a real-valued sum, not Mathlib's `InformationTheory.klDiv`) is
`finiteKLExpression` (definitional).  It is a KL divergence only under the support hypothesis
`q y = 0 → p y = 0`; see `rlhfKlDiv_eq_toReal_klDiv_rowMeasure`. -/
theorem rlhfKlDiv_eq_finiteKLExpression {Y : Type} [Fintype Y] (p q : Y → ℝ) :
    Ch7Rest.Rlhf.klDiv p q = GenerativeLowerBound.finiteKLExpression p q := rfl

end Sums

section Mathlib

variable {X : Type} [Fintype X]

local instance klBridgeMeasurableSpace : MeasurableSpace X := ⊤

local instance klBridgeSingletonClass : MeasurableSingletonClass X :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

/-- **Bridge to Mathlib.**  For finite distributions with `d ≪ d'` (atomwise,
`d'.prob x = 0 → d.prob x = 0`), Mathlib's `klDiv` of the row laws is finite and its real value is
`finiteKLExpression d.prob d'.prob`.  This is the support hypothesis under which the real-valued
form is the KL divergence. -/
theorem finiteKLExpression_eq_toReal_klDiv_rowMeasure (d d' : FiniteDistribution X)
    (h : ∀ x, d'.prob x = 0 → d.prob x = 0) :
    GenerativeLowerBound.finiteKLExpression d.prob d'.prob =
      (InformationTheory.klDiv d.rowMeasure d'.rowMeasure).toReal :=
  (OfflineRL.JointRow.rowMeasure_klDiv d d' h).2.symm

/-- Under the support hypothesis, `qFiniteKLOn` over the whole carrier is the real value of
Mathlib's `klDiv` of the row laws. -/
theorem qFiniteKLOn_univ_eq_toReal_klDiv_rowMeasure (d d' : FiniteDistribution X)
    (h : ∀ x, d'.prob x = 0 → d.prob x = 0) :
    QLearning.qFiniteKLOn Finset.univ d.prob d'.prob =
      (InformationTheory.klDiv d.rowMeasure d'.rowMeasure).toReal := by
  rw [qFiniteKLOn_univ_eq_finiteKLExpression]
  exact finiteKLExpression_eq_toReal_klDiv_rowMeasure d d' h

/-- Under the support hypothesis, the countable `klAtom` series over a finite carrier is the real
value of Mathlib's `klDiv` of the row laws. -/
theorem tsum_klAtom_eq_toReal_klDiv_rowMeasure (d d' : FiniteDistribution X)
    (h : ∀ x, d'.prob x = 0 → d.prob x = 0) :
    (∑' x, QLearning.CountablePinsker.klAtom (d.prob x) (d'.prob x)) =
      (InformationTheory.klDiv d.rowMeasure d'.rowMeasure).toReal := by
  rw [tsum_klAtom_eq_finiteKLExpression]
  exact finiteKLExpression_eq_toReal_klDiv_rowMeasure d d' h

/-- The `RLHF` `klDiv` of two probability vectors (rows of `FiniteDistribution`s) is the real
value of Mathlib's `klDiv` of the row laws, under the support hypothesis
`d'.prob y = 0 → d.prob y = 0` (for example `π_ref` positive). -/
theorem rlhfKlDiv_eq_toReal_klDiv_rowMeasure (d d' : FiniteDistribution X)
    (h : ∀ x, d'.prob x = 0 → d.prob x = 0) :
    Ch7Rest.Rlhf.klDiv d.prob d'.prob =
      (InformationTheory.klDiv d.rowMeasure d'.rowMeasure).toReal := by
  rw [rlhfKlDiv_eq_finiteKLExpression]
  exact finiteKLExpression_eq_toReal_klDiv_rowMeasure d d' h

/-- **Off support (general measures).**  If `ν` gives mass zero to an atom to which `μ` gives
positive mass, then `μ` is not absolutely continuous with respect to `ν` and Mathlib's
`klDiv μ ν` is `⊤`.  The real-valued forms assign such an atom the totalised contribution `0`
(`klTerm_zero_right`), so they are not KL divergences there. -/
theorem klDiv_eq_top_of_singleton_null {Ω : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ ν : Measure Ω) {x : Ω} (hν : ν {x} = 0) (hμ : μ {x} ≠ 0) :
    InformationTheory.klDiv μ ν = ∞ :=
  InformationTheory.klDiv_of_not_ac fun hac => hμ (hac hν)

/-- **Off support (finite distributions).**  If `d'.prob x = 0 < d.prob x` for some `x`, Mathlib's
`klDiv` of the row laws is `⊤` (so its `toReal` is the junk value `0`), whereas the real-valued
forms are finite reals which, in general, are not even nonnegative; see
`finiteKLExpression_off_support_example`. -/
theorem klDiv_rowMeasure_eq_top_of_off_support (d d' : FiniteDistribution X) {x : X}
    (hx : d'.prob x = 0) (hd : d.prob x ≠ 0) :
    InformationTheory.klDiv d.rowMeasure d'.rowMeasure = ∞ := by
  refine klDiv_eq_top_of_singleton_null _ _ (x := x) ?_ ?_
  · rw [FiniteDistribution.rowMeasure_singleton, hx, ENNReal.ofReal_zero]
  · rw [FiniteDistribution.rowMeasure_singleton]
    exact (ENNReal.ofReal_pos.2 (lt_of_le_of_ne (d.prob_nonneg x) (Ne.symm hd))).ne'

end Mathlib

section OffSupportExample

/-- The uniform law on `Bool`. -/
noncomputable def boolUniform : FiniteDistribution Bool where
  prob := fun _ => 1 / 2
  prob_nonneg := fun _ => by norm_num
  sum_prob := by simp

/-- The point mass at `false` on `Bool`. -/
noncomputable def boolDiracFalse : FiniteDistribution Bool where
  prob := fun b => if b then 0 else 1
  prob_nonneg := fun b => by cases b <;> norm_num
  sum_prob := by simp

/-- **Off-support example.**  For the uniform law `d` and the point mass `d'` at `false` on `Bool`
(so `d ≪ d'` fails at `true`), Mathlib's `klDiv d d'` is `⊤`, while the real-valued form
`finiteKLExpression` is the finite *negative* number `-(1/2) log 2`.  This is why the real-valued
forms are only meaningful as KL under the support hypothesis. -/
theorem finiteKLExpression_off_support_example :
    InformationTheory.klDiv
        boolUniform.rowMeasure boolDiracFalse.rowMeasure = ∞ ∧
      GenerativeLowerBound.finiteKLExpression boolUniform.prob boolDiracFalse.prob =
        -(1 / 2 * Real.log 2) := by
  refine ⟨klDiv_rowMeasure_eq_top_of_off_support _ _ (x := true) (by simp [boolDiracFalse])
    (by simp [boolUniform]), ?_⟩
  simp [GenerativeLowerBound.finiteKLExpression, boolUniform, boolDiracFalse]

end OffSupportExample

section Binary

/-- **Binary form against the Bernoulli expression.**  For an interior reference `0 < q < 1`
(and every numerator `p`), the Bregman-form `QLearning.qBinaryKL p q` equals
`GenerativeLowerBound.bernoulliKLExpression p q`, the explicit `p log (p / q) + (1 - p) log
((1 - p) / (1 - q))`.  The interior hypothesis is the support hypothesis: `qBinaryKL` is `0` at
`q ∈ {0, 1}` regardless of `p` (see `qBinaryKL_zero_right`). -/
theorem qBinaryKL_eq_bernoulliKLExpression (p q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    QLearning.qBinaryKL p q = GenerativeLowerBound.bernoulliKLExpression p q := by
  have h1 : (1 - q) ≠ 0 := (sub_pos.2 hq1).ne'
  have key : ∀ x y : ℝ, y ≠ 0 → x * Real.log (x / y) = x * (Real.log x - Real.log y) := by
    intro x y hy
    by_cases hx : x = 0
    · simp [hx]
    · rw [Real.log_div hx hy]
  have e1 := key p q hq0.ne'
  have e2 := key (1 - p) (1 - q) h1
  unfold QLearning.qBinaryKL GenerativeLowerBound.bernoulliKLExpression
  rw [if_neg hq0.ne', if_neg hq1.ne, e1, e2]
  unfold QLearning.qBinaryPotential
  ring

/-- `qBinaryKL` is the totalised value `0` at reference `0`, whatever the numerator. -/
theorem qBinaryKL_zero_right (p : ℝ) : QLearning.qBinaryKL p 0 = 0 := by
  simp [QLearning.qBinaryKL]

/-- `qBinaryKL` is the totalised value `0` at reference `1`, whatever the numerator. -/
theorem qBinaryKL_one_right (p : ℝ) : QLearning.qBinaryKL p 1 = 0 := by
  simp [QLearning.qBinaryKL]

/-- **Bridge to Mathlib (Bernoulli laws).**  For `p q : ℝ≥0` with `0 < q < 1` and `p < 1`, the
Bregman-form `qBinaryKL p q` is the real value of Mathlib's `klDiv` of the Bernoulli laws
`PMF.bernoulli p` and `PMF.bernoulli q`.  The hypotheses `0 < q < 1` (the support hypothesis) and
`p < 1` are those of `GenerativeLowerBound.bernoulli_toReal_klDiv_eq_expression`. -/
theorem qBinaryKL_eq_toReal_klDiv_bernoulli (p q : ℝ≥0) (hq : 0 < q) (hq1 : q < 1) (hp1 : p < 1) :
    QLearning.qBinaryKL (p : ℝ) (q : ℝ) =
      (InformationTheory.klDiv (PMF.bernoulli p hp1.le).toMeasure
        (PMF.bernoulli q hq1.le).toMeasure).toReal := by
  rw [GenerativeLowerBound.bernoulli_toReal_klDiv_eq_expression p q hq hq1 hp1,
    qBinaryKL_eq_bernoulliKLExpression _ _ (by exact_mod_cast hq) (by exact_mod_cast hq1)]

/-- **Off support (Bernoulli, reference `0`).**  If `p ≠ 0` then Mathlib's `klDiv` of
`Bernoulli p` against `Bernoulli 0` is `⊤`, whereas `qBinaryKL p 0 = 0`. -/
theorem klDiv_bernoulli_eq_top_of_reference_zero (p : ℝ≥0) (hp1 : p ≤ 1) (hp : p ≠ 0) :
    InformationTheory.klDiv (PMF.bernoulli p hp1).toMeasure
      (PMF.bernoulli 0 zero_le_one).toMeasure = ∞ := by
  refine klDiv_eq_top_of_singleton_null _ _ (x := true) ?_ ?_
  · rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp [PMF.bernoulli_apply]
  · rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simpa [PMF.bernoulli_apply] using hp

/-- **Off support (Bernoulli, reference `1`).**  If `p ≠ 1` then Mathlib's `klDiv` of
`Bernoulli p` against `Bernoulli 1` is `⊤`, whereas `qBinaryKL p 1 = 0`. -/
theorem klDiv_bernoulli_eq_top_of_reference_one (p : ℝ≥0) (hp1 : p ≤ 1) (hp : p ≠ 1) :
    InformationTheory.klDiv (PMF.bernoulli p hp1).toMeasure
      (PMF.bernoulli 1 le_rfl).toMeasure = ∞ := by
  refine klDiv_eq_top_of_singleton_null _ _ (x := false) ?_ ?_
  · rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    simp [PMF.bernoulli_apply]
  · rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    have : (1 : ℝ≥0∞) - p ≠ 0 := by
      intro h
      exact hp (le_antisymm hp1 (by simpa using tsub_eq_zero_iff_le.1 h))
    simpa [PMF.bernoulli_apply] using this

end Binary

end StatisticalRL
