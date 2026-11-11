import Formalization.Probability.InformationTheory.CountableTailLogSum
import Formalization.Probability.InformationTheory.CountableL1Difference
import Formalization.ModelFree.QLearningStoppedPrefixPinskerInputs
import Formalization.ModelFree.QLearningFinitePinskerCoarsening

/-! Countable half-L1 Pinsker and its actual stopped-prefix specialization. -/

namespace StatisticalRL.QLearning.CountablePinsker

/-- Countable half-L1 total variation in the `p` versus `q` orientation. -/
noncomputable def qCountableTotalVariation {Ω : Type*} [Countable Ω]
    (p q : Ω → ℝ) : ℝ :=
  (1 / 2) * ∑' ω, |p ω - q ω|

/-- Countable Pinsker with exact factor 2. The laws are actual nonnegative
atomic probability masses, support inclusion is `p>0 → q>0`, and absolute
summability of the oriented KL atoms licenses restriction to the positive
difference set and its complement. The proof uses countable log-sum on those
two cells followed by the exact binary inequality, including binary boundary
cases. -/
theorem qCountablePinsker
    {Ω : Type*} [Countable Ω]
    (p q : Ω → ℝ)
    (hp : ∀ ω, 0 ≤ p ω) (hq : ∀ ω, 0 ≤ q ω)
    (hpSum : HasSum p 1) (hqSum : HasSum q 1)
    (hsupport : ∀ ω, p ω ≠ 0 → q ω ≠ 0)
    (hklAbs : Summable (fun ω ↦ |klAtom (p ω) (q ω)|)) :
    2 * qCountableTotalVariation p q ^ 2 ≤ ∑' ω, klAtom (p ω) (q ω) := by
  classical
  let E : Set Ω := {ω | q ω ≤ p ω}
  let Ec : Set Ω := Eᶜ
  let A : ℝ := ∑' ω : {ω // ω ∈ E}, p ω.1
  let B : ℝ := ∑' ω : {ω // ω ∈ E}, q ω.1
  let Ac : ℝ := ∑' ω : {ω // ω ∈ Ec}, p ω.1
  let Bc : ℝ := ∑' ω : {ω // ω ∈ Ec}, q ω.1
  have hpE : Summable (fun ω : {ω // ω ∈ E} ↦ p ω.1) := hpSum.summable.subtype E
  have hqE : Summable (fun ω : {ω // ω ∈ E} ↦ q ω.1) := hqSum.summable.subtype E
  have hpEc : Summable (fun ω : {ω // ω ∈ Ec} ↦ p ω.1) := hpSum.summable.subtype Ec
  have hqEc : Summable (fun ω : {ω // ω ∈ Ec} ↦ q ω.1) := hqSum.summable.subtype Ec
  have hpEHas : HasSum (fun ω : {ω // ω ∈ E} ↦ p ω.1) A := by
    simpa [A] using hpE.hasSum
  have hqEHas : HasSum (fun ω : {ω // ω ∈ E} ↦ q ω.1) B := by
    simpa [B] using hqE.hasSum
  have hpEcHas : HasSum (fun ω : {ω // ω ∈ Ec} ↦ p ω.1) Ac := by
    simpa [Ac] using hpEc.hasSum
  have hqEcHas : HasSum (fun ω : {ω // ω ∈ Ec} ↦ q ω.1) Bc := by
    simpa [Bc] using hqEc.hasSum
  have hpSplit := hpSum.summable.tsum_subtype_add_tsum_subtype_compl E
  have hqSplit := hqSum.summable.tsum_subtype_add_tsum_subtype_compl E
  have hpMass : A + Ac = 1 := by
    simpa [A, Ac] using hpSplit.trans hpSum.tsum_eq
  have hqMass : B + Bc = 1 := by
    simpa [B, Bc] using hqSplit.trans hqSum.tsum_eq
  have hA0 : 0 ≤ A := by
    rw [← hpEHas.tsum_eq]
    exact tsum_nonneg fun ω ↦ hp ω.1
  have hB0 : 0 ≤ B := by
    rw [← hqEHas.tsum_eq]
    exact tsum_nonneg fun ω ↦ hq ω.1
  have hAc0 : 0 ≤ Ac := by
    rw [← hpEcHas.tsum_eq]
    exact tsum_nonneg fun ω ↦ hp ω.1
  have hBc0 : 0 ≤ Bc := by
    rw [← hqEcHas.tsum_eq]
    exact tsum_nonneg fun ω ↦ hq ω.1
  have hA1 : A ≤ 1 := by linarith
  have hB1 : B ≤ 1 := by linarith
  have hAcEq : Ac = 1 - A := by linarith
  have hBcEq : Bc = 1 - B := by linarith

  have hsupportE : ∀ ω : {ω // ω ∈ E}, p ω.1 ≠ 0 → q ω.1 ≠ 0 :=
    fun ω h ↦ hsupport ω.1 h
  have hsupportEc : ∀ ω : {ω // ω ∈ Ec}, p ω.1 ≠ 0 → q ω.1 ≠ 0 :=
    fun ω h ↦ hsupport ω.1 h
  have hklE : Summable (fun ω : {ω // ω ∈ E} ↦
      |klAtom (p ω.1) (q ω.1)|) := hklAbs.subtype E
  have hklEc : Summable (fun ω : {ω // ω ∈ Ec} ↦
      |klAtom (p ω.1) (q ω.1)|) := hklAbs.subtype Ec
  have hlogE := klSeries_logSum (p := fun ω : {ω // ω ∈ E} ↦ p ω.1)
    (q := fun ω : {ω // ω ∈ E} ↦ q ω.1) A B
    (fun ω ↦ hp ω.1) (fun ω ↦ hq ω.1) hpEHas hqEHas hA0 hB0
    hsupportE hklE
  have hlogEc := klSeries_logSum (p := fun ω : {ω // ω ∈ Ec} ↦ p ω.1)
    (q := fun ω : {ω // ω ∈ Ec} ↦ q ω.1) Ac Bc
    (fun ω ↦ hp ω.1) (fun ω ↦ hq ω.1) hpEcHas hqEcHas hAc0 hBc0
    hsupportEc hklEc
  have hklSummable : Summable (fun ω ↦ klAtom (p ω) (q ω)) := hklAbs.of_abs
  have hklSplit := hklSummable.tsum_subtype_add_tsum_subtype_compl E
  have hcoarse : klAtom A B + klAtom Ac Bc ≤ ∑' ω, klAtom (p ω) (q ω) := by
    have hE : klAtom A B ≤
        ∑' ω : {ω // ω ∈ E}, klAtom (p ω.1) (q ω.1) := hlogE
    have hEc : klAtom Ac Bc ≤
        ∑' ω : {ω // ω ∈ Ec}, klAtom (p ω.1) (q ω.1) := hlogEc
    have hsplit :
        (∑' ω : {ω // ω ∈ E}, klAtom (p ω.1) (q ω.1)) +
          (∑' ω : {ω // ω ∈ Ec}, klAtom (p ω.1) (q ω.1)) =
            ∑' ω, klAtom (p ω) (q ω) := by
      simpa [E, Ec] using hklSplit
    rw [← hsplit]
    exact add_le_add hE hEc

  have hsupportA0 : B = 0 → A = 0 := by
    intro hB
    exact countable_support_zero_reference_mass
      (fun ω : {ω // ω ∈ E} ↦ p ω.1) (fun ω ↦ q ω.1) A B
      (fun ω ↦ hp ω.1) (fun ω ↦ hq ω.1) hpEHas hqEHas hsupportE hB
  have hsupportA1 : B = 1 → A = 1 := by
    intro hB
    have hBc : Bc = 0 := by linarith [hqMass]
    have hAc : Ac = 0 := countable_support_zero_reference_mass
      (fun ω : {ω // ω ∈ Ec} ↦ p ω.1) (fun ω ↦ q ω.1) Ac Bc
      (fun ω ↦ hp ω.1) (fun ω ↦ hq ω.1) hpEcHas hqEcHas hsupportEc hBc
    linarith [hpMass]
  have hbinary := StatisticalRL.QLearning.qBinaryPinsker_source_complete
    A B hA0 hA1 hB0 hB1 hsupportA0 hsupportA1
  have hbinaryAtoms :
      StatisticalRL.QLearning.qBinaryKL A B = klAtom A B + klAtom Ac Bc := by
    have htermA : StatisticalRL.QLearning.qFiniteKLTerm A B = klAtom A B := by
      by_cases hA : A = 0 <;> simp [StatisticalRL.QLearning.qFiniteKLTerm, klAtom, hA]
    have htermC : StatisticalRL.QLearning.qFiniteKLTerm Ac Bc = klAtom Ac Bc := by
      by_cases hAc : Ac = 0 <;> simp [StatisticalRL.QLearning.qFiniteKLTerm, klAtom, hAc]
    rw [StatisticalRL.QLearning.qBinaryKL_eq_twoFiniteKLTerms
      A B hA0 hA1 hB0 hB1 hsupportA0 hsupportA1, htermA,
      ← hAcEq, ← hBcEq, htermC]
  have hTV : qCountableTotalVariation p q = A - B := by
    let d : Ω → ℝ := fun ω ↦ p ω - q ω
    have hAbsD : Summable (fun ω ↦ |d ω|) := by
      simpa only [d] using qCountable_abs_sub_summable p q hp hq hpSum hqSum
    have hsumE : (∑' ω : {ω // ω ∈ E}, d ω.1) = A - B := by
      calc
        _ = (∑' ω : {ω // ω ∈ E}, p ω.1) -
            (∑' ω : {ω // ω ∈ E}, q ω.1) := by
          dsimp [d]
          rw [hpE.tsum_sub hqE]
        _ = A - B := by rw [hpEHas.tsum_eq, hqEHas.tsum_eq]
    have hsumEc : (∑' ω : {ω // ω ∈ Ec}, d ω.1) = Ac - Bc := by
      calc
        _ = (∑' ω : {ω // ω ∈ Ec}, p ω.1) -
            (∑' ω : {ω // ω ∈ Ec}, q ω.1) := by
          dsimp [d]
          rw [hpEc.tsum_sub hqEc]
        _ = Ac - Bc := by rw [hpEcHas.tsum_eq, hqEcHas.tsum_eq]
    have hAbsE : (∑' ω : {ω // ω ∈ E}, |d ω.1|) = A - B := by
      calc
        _ = ∑' ω : {ω // ω ∈ E}, d ω.1 := by
          apply tsum_congr
          intro ω
          have hle : q ω.1 ≤ p ω.1 := by
            change ω.1 ∈ E
            exact ω.2
          have hd : 0 ≤ d ω.1 := by dsimp [d]; linarith
          exact abs_of_nonneg hd
        _ = A - B := hsumE
    have hAbsEc : (∑' ω : {ω // ω ∈ Ec}, |d ω.1|) = A - B := by
      calc
        _ = ∑' ω : {ω // ω ∈ Ec}, -d ω.1 := by
          apply tsum_congr
          intro ω
          have hnot : ¬ q ω.1 ≤ p ω.1 := by
            change ω.1 ∈ Ec
            change ¬ ω.1 ∈ E
            change ¬ q ω.1 ≤ p ω.1
            exact ω.2
          have hd : d ω.1 ≤ 0 := by dsimp [d]; linarith
          rw [abs_of_nonpos hd]
        _ = -∑' ω : {ω // ω ∈ Ec}, d ω.1 := tsum_neg
        _ = A - B := by rw [hsumEc, hAcEq, hBcEq]; ring
    have hAbsSplit := hAbsD.tsum_subtype_add_tsum_subtype_compl E
    have hAbsAll : (∑' ω, |d ω|) = 2 * (A - B) := by
      calc
        _ = (∑' ω : {ω // ω ∈ E}, |d ω.1|) +
            (∑' ω : {ω // ω ∈ Ec}, |d ω.1|) := hAbsSplit.symm
        _ = 2 * (A - B) := by rw [hAbsE, hAbsEc]; ring
    unfold qCountableTotalVariation
    rw [hAbsAll]
    ring
  rw [hTV]
  rw [← hbinaryAtoms] at hcoarse
  exact hbinary.trans hcoarse

/-- Actual stopped-prefix specialization. Normalization, support inclusion,
and absolute KL summability are derived from the actual geometric prefix law
and row hypotheses; they are not supplied as target-shaped inputs. -/
theorem qActualStoppedPrefixPinsker
    {State Action : Type*} [Fintype State] [Fintype Action]
    (M M' : StatisticalRL.DiscountedMDP State Action)
    (π : StatisticalRL.StationaryPolicy State Action)
    (γ ρ : ℝ) (s : State) (a : Action)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hρ : 0 ≤ ρ)
    (hrowSupport : ∀ x b y, (M'.transition x b).prob y ≠ 0 →
      (M.transition x b).prob y ≠ 0)
    (hrowKL : ∀ x b,
      StatisticalRL.GenerativeLowerBound.finiteKLExpression
        (fun y ↦ (M'.transition x b).prob y)
        (fun y ↦ (M.transition x b).prob y) ≤ ρ) :
    2 * qCountableTotalVariation
        (qActualStoppedPrefixMass M' π γ s a)
        (qActualStoppedPrefixMass M π γ s a) ^ 2 ≤
      ∑' z, klAtom (qActualStoppedPrefixMass M' π γ s a z)
        (qActualStoppedPrefixMass M π γ s a z) := by
  obtain ⟨hM'Norm, hMNorm, hstopSupport, hklAbs'⟩ :=
    qActualStoppedPrefixPinskerInputs M M' π γ ρ s a hγ hγ1 hρ hrowSupport hrowKL
  have hklAbs : Summable (fun z : qStoppedPrefixAbsCarrier
      (State := State) (Action := Action) ↦
      |klAtom (qActualStoppedPrefixMass M' π γ s a z)
        (qActualStoppedPrefixMass M π γ s a z)|) := by
    simpa [klAtom, qStoppedPrefixKLAtom] using hklAbs'
  exact qCountablePinsker
    (qActualStoppedPrefixMass M' π γ s a)
    (qActualStoppedPrefixMass M π γ s a)
    (fun z ↦ mul_nonneg (qGeometricStopWeight_nonneg γ z.1 hγ hγ1)
          ((qForcedPrefixLaw M' π s a z.1).prob_nonneg z.2))
    (fun z ↦ mul_nonneg (qGeometricStopWeight_nonneg γ z.1 hγ hγ1)
          ((qForcedPrefixLaw M π s a z.1).prob_nonneg z.2))
    hM'Norm hMNorm hstopSupport hklAbs

end StatisticalRL.QLearning.CountablePinsker
