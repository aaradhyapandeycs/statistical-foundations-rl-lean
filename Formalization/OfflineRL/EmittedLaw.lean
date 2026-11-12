import Formalization.OfflineRL.JointRowLaw
import Formalization.OfflineRL.StackProjection
import Formalization.Probability.FiniteDistributionBridge

/-! The law of the source's emitted sample sequence.

The emitted records are proved to have the source iid joint law; the conditional
fixed-label law and the stack projection are explicit dependencies. -/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.OfflineRL.EmittedLaw

open StatisticalRL StatisticalRL.OfflineRL

variable {State Action : Type*} [Fintype State] [Fintype Action]
  [DecidableEq State] [DecidableEq Action]

/-- The independent transition stack: coordinate `(r, k)` is a draw from the
actual transition row `P(·|r)`. `State` carries `⊤` (as in
`FiniteSampleDefinitions`); the stack space carries the product σ-algebra. -/
noncomputable def transitionStack (P : State → Action → FiniteDistribution State) (n : ℕ) :
    letI : MeasurableSpace State := ⊤
    Measure ((State × Action) × Fin n → State) :=
  letI : MeasurableSpace State := ⊤
  StackProjection.stackLaw (fun r : State × Action => (P r.1 r.2).rowMeasure) n

/-- Emitted observation sequence: row label and the stack entry at its rank. -/
def emitObservation {n : ℕ}
    (ω : (Fin n → State × Action) × ((State × Action) × Fin n → State)) :
    Fin n → (State × Action) × State :=
  fun i => (ω.1 i, StackProjection.selectByRank ω.1 ω.2 i)

/-- **Emitted-law identity.** iid behaviour labels, independent transition
stack, rank selection: the emitted sequence is `n` iid joint-row draws. -/
theorem emitObservation_law (ρ : FiniteDistribution (State × Action))
    (P : State → Action → FiniteDistribution State) (n : ℕ) :
    letI : MeasurableSpace State := ⊤
    letI : MeasurableSpace (State × Action) := ⊤
    letI : MeasurableSpace ((State × Action) × State) := ⊤
    ((ρ.sampleMeasure n).prod (transitionStack P n)).map emitObservation =
      (JointRow.jointRow ρ P).sampleMeasure n := by
  classical
  letI : MeasurableSpace State := ⊤
  letI : MeasurableSpace (State × Action) := ⊤
  letI : MeasurableSpace ((State × Action) × State) := ⊤
  haveI hPr : ∀ r : State × Action, IsProbabilityMeasure (P r.1 r.2).rowMeasure :=
    fun r => FiniteDistribution.isProbabilityMeasure_rowMeasure_top _
  haveI hρr : IsProbabilityMeasure ρ.rowMeasure := FiniteDistribution.isProbabilityMeasure_rowMeasure_top _
  haveI hJr : IsProbabilityMeasure (JointRow.jointRow ρ P).rowMeasure := FiniteDistribution.isProbabilityMeasure_rowMeasure_top _
  haveI : IsProbabilityMeasure (transitionStack P n) := by
    show IsProbabilityMeasure (Measure.pi _); infer_instance
  haveI : IsProbabilityMeasure (ρ.sampleMeasure n) := by
    unfold FiniteDistribution.sampleMeasure; infer_instance
  refine Measure.ext_iff_singleton.2 fun x => ?_
  set l0 : Fin n → State × Action := fun i => (x i).1 with hl0
  set y0 : Fin n → State := fun i => (x i).2 with hy0
  have hpre : (emitObservation (State := State) (Action := Action)) ⁻¹' {x} =
      ({l0} : Set (Fin n → State × Action)) ×ˢ
        (StackProjection.selectByRank l0 ⁻¹' {y0}) := by
    ext ⟨l, Y⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod]
    constructor
    · intro h
      have hl : l = l0 := funext fun i => by rw [hl0]; rw [← h]; rfl
      refine ⟨hl, ?_⟩
      subst hl
      funext i
      rw [hy0]; rw [← h]; rfl
    · rintro ⟨hl, hY⟩
      subst hl
      funext i
      show ((x i).1, StackProjection.selectByRank l0 Y i) = x i
      rw [hY]
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton x), hpre,
    Measure.prod_prod]
  have hstack : transitionStack P n (StackProjection.selectByRank l0 ⁻¹' {y0}) =
      ∏ i, (P (l0 i).1 (l0 i).2).rowMeasure {y0 i} := by
    rw [← Measure.map_apply (measurable_of_countable _) (measurableSet_singleton y0)]
    unfold transitionStack
    rw [StackProjection.stackLaw_map_selectByRank, Measure.pi_singleton]
  have hlab : ρ.sampleMeasure n {l0} = ∏ i, ρ.rowMeasure {l0 i} := by
    unfold FiniteDistribution.sampleMeasure
    rw [Measure.pi_singleton]
  have hjoint : (JointRow.jointRow ρ P).sampleMeasure n {x} =
      ∏ i, (JointRow.jointRow ρ P).rowMeasure {x i} := by
    unfold FiniteDistribution.sampleMeasure
    rw [Measure.pi_singleton]
  rw [hstack, hlab, hjoint, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [FiniteDistribution.rowMeasure_singleton, FiniteDistribution.rowMeasure_singleton,
    FiniteDistribution.rowMeasure_singleton,
    ← ENNReal.ofReal_mul (ρ.prob_nonneg _)]
  rfl

end StatisticalRL.OfflineRL.EmittedLaw
