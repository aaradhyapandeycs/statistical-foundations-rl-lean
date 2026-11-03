import Formalization.Generative.GenerativeLowerBoundFamilyMDP
import Formalization.Generative.GenerativeLowerBoundIndexedProductKL
import Formalization.Generative.PolicyLearningHoeffding

/-! Encode and reconstruct actual indexed-family sample arrays. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.ModelBasedPolicyLearning
local instance familyObservationStateMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
local instance familyObservationFinMeasurable (n : ℕ) : MeasurableSpace (Fin n) := ⊤

/-- Active row and sample indices, excluding the deterministic absorber. -/
abbrev FamilyActiveCoordinates (m n N : ℕ) := (Fin m × Fin (n + 1)) × Fin N

/-- Coordinate encoder: did the active row self-loop? -/
def familyEncode {m n N : ℕ}
    (data : Samples (Option (Fin m)) (Fin (n + 1)) N) : FamilyActiveCoordinates m n N → Bool :=
  fun z ↦ decide (data ((some z.1.1, z.1.2), z.2) = some z.1.1)

/-- Model-independent full-array reconstruction; absorber rows are filled
with none, and each active row can reach only itself or the absorber. -/
def familyReconstruct {m n N : ℕ} (x : FamilyActiveCoordinates m n N → Bool) :
    Samples (Option (Fin m)) (Fin (n + 1)) N :=
  fun z ↦ match z.1.1 with
    | none => none
    | some j => if x ((j, z.1.2), z.2) then some j else none

/-- Reconstruction retains every encoded indicator, including the empty-array case. -/
theorem familyEncode_reconstruct {m n N : ℕ} (x : FamilyActiveCoordinates m n N → Bool) :
    familyEncode (familyReconstruct x) = x := by
  funext z
  rcases z with ⟨⟨j, a⟩, t⟩
  cases hx : x ((j, a), t) <;> simp [familyEncode, familyReconstruct, hx]

/-- Consequently reconstruction is injective, so no information in the
heterogeneous Bernoulli coordinates is lost. -/
theorem familyReconstruct_injective {m n N : ℕ} :
    Function.Injective (@familyReconstruct m n N) := by
  intro x y h
  have := congrArg (@familyEncode m n N) h
  simpa only [familyEncode_reconstruct] using this

/-- Each active transition row is the pushforward of the corresponding
Bernoulli row by the self-loop/absorber embedding. -/
theorem familyActiveRow_measure_eq_map {m : ℕ} (j : Fin m) (r : ℝ≥0) (hr : r ≤ 1) :
    (familyActiveRow j (r : ℝ) (by positivity) (by exact_mod_cast hr)).rowMeasure =
      ((PMF.bernoulli r hr).toMeasure.map (fun b ↦ if b then some j else none)) := by
  classical
  apply Measure.ext_of_singleton
  intro t
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    FiniteDistribution.rowMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rw [PMF.toMeasure_apply _ (Set.to_countable _).measurableSet, tsum_fintype]
  cases t with
  | none =>
    simp [FiniteDistribution.toPMF_apply, familyActiveRow, FiniteDistribution.bind,
      FiniteDistribution.expectation, hardRow, EnvironmentStage.pointMass, PMF.bernoulli_apply,
      ENNReal.ofReal_sub, ENNReal.ofReal_coe_nnreal]
  | some k =>
    by_cases h : k = j
    · subst k
      simp [FiniteDistribution.toPMF_apply, familyActiveRow, FiniteDistribution.bind,
        FiniteDistribution.expectation, hardRow, EnvironmentStage.pointMass, PMF.bernoulli_apply,
        ENNReal.ofReal_sub, ENNReal.ofReal_coe_nnreal]
    · simp [FiniteDistribution.toPMF_apply, familyActiveRow, FiniteDistribution.bind,
        FiniteDistribution.expectation, hardRow, EnvironmentStage.pointMass, PMF.bernoulli_apply,
        ENNReal.ofReal_sub, ENNReal.ofReal_coe_nnreal, h, Ne.symm h]

/-- Encoding a source active row recovers its actual Bernoulli law. -/
theorem familyActiveRow_encode_measure {m : ℕ} (j : Fin m) (r : ℝ≥0) (hr : r ≤ 1) :
    ((familyActiveRow j (r : ℝ) (by positivity) (by exact_mod_cast hr)).rowMeasure).map
      (fun s ↦ decide (s = some j)) = (PMF.bernoulli r hr).toMeasure := by
  rw [familyActiveRow_measure_eq_map, Measure.map_map (measurable_of_countable _)
    (measurable_of_countable _)]
  have heq : (fun b : Bool ↦ decide ((if b then some j else none) = some j)) = id := by
    funext b
    cases b <;> simp
  change Measure.map (fun b : Bool ↦ decide ((if b then some j else none) = some j)) _ = _
  rw [heq, Measure.map_id]

/-- Bernoulli parameter of each active state/action/sample coordinate. -/
def familyBernoulliParameter {m n N : ℕ} (i : HardFamilyIndex m n) (p q : ℝ≥0)
    (z : FamilyActiveCoordinates m n N) : ℝ≥0 :=
  if z.1.2 = hardPolicySignature i z.1.1 then q else p

/-- The family parameter is always valid under the two row bounds. -/
theorem familyBernoulliParameter_le_one {m n N : ℕ} (i : HardFamilyIndex m n)
    (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1) :
    ∀ z : FamilyActiveCoordinates m n N, familyBernoulliParameter i p q z ≤ 1 := by
  intro z
  unfold familyBernoulliParameter
  split <;> assumption

/-- The self-loop indicators extracted from the actual complete generative
array have the exact heterogeneous Bernoulli product law. -/
theorem familyEncode_samplingLaw {m n : ℕ} (i : HardFamilyIndex m n) (γ : ℝ)
    (p q : ℝ≥0) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hpq : p ≤ q) (hq : q < 1) (N : ℕ) :
    let M := familyMDP i γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq) (by exact_mod_cast hq)
    (samplingLaw M N).map familyEncode =
      indexedBernoulliLaw (familyBernoulliParameter i p q)
        (familyBernoulliParameter_le_one i p q (le_trans hpq hq.le) hq.le) := by
  classical
  let M := familyMDP i γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
    (by exact_mod_cast hpq) (by exact_mod_cast hq)
  let μ := samplingLaw M N
  let j : FamilyActiveCoordinates m n N → ((Option (Fin m) × Fin (n + 1)) × Fin N) :=
    fun z ↦ ((some z.1.1, z.1.2), z.2)
  have hj : Function.Injective j := by
    intro x y h
    rcases x with ⟨⟨xj, xa⟩, xt⟩
    rcases y with ⟨⟨yj, ya⟩, yt⟩
    simp only [j, Prod.mk.injEq, Option.some.injEq] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
    rfl
  let raw : FamilyActiveCoordinates m n N → Samples (Option (Fin m)) (Fin (n + 1)) N → Option (Fin m) :=
    fun z data ↦ data (j z)
  let enc : FamilyActiveCoordinates m n N → Option (Fin m) → Bool :=
    fun z s ↦ decide (s = some z.1.1)
  have hi : iIndepFun raw μ := (samplingLaw_independent M N).precomp hj
  have he : iIndepFun (fun z ↦ enc z ∘ raw z) μ := hi.comp enc (fun z ↦ measurable_of_countable _)
  have hm : ∀ z, AEMeasurable (fun data ↦ enc z (raw z data)) μ :=
    fun z ↦ (measurable_of_countable _).aemeasurable
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map hm).mp he
  change μ.map familyEncode = _
  change μ.map (fun data z ↦ enc z (raw z data)) = _
  rw [hmap]
  unfold indexedBernoulliLaw
  congr 1
  funext z
  have hcoord : μ.map (raw z) = (M.transition (some z.1.1) z.1.2).rowMeasure :=
    samplingLaw_marginal M N (j z)
  change μ.map (enc z ∘ raw z) = _
  rw [← Measure.map_map (measurable_of_countable _) (measurable_of_countable _), hcoord]
  by_cases hz : z.1.2 = hardPolicySignature i z.1.1
  · simpa [M, familyMDP, familyStay, familyBernoulliParameter, enc, hz] using
      familyActiveRow_encode_measure z.1.1 q hq.le
  · simpa [M, familyMDP, familyStay, familyBernoulliParameter, enc, hz] using
      familyActiveRow_encode_measure z.1.1 p (le_trans hpq hq.le)

/-- Every coordinate of the actual full sample array lies in its model's
row support, including every padded absorber action. -/
theorem familySamplingLaw_rows_supported {m n : ℕ} (i : HardFamilyIndex m n) (γ : ℝ)
    (p q : ℝ≥0) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hpq : p ≤ q) (hq : q < 1) (N : ℕ) :
    let M := familyMDP i γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq) (by exact_mod_cast hq)
    ∀ᵐ data ∂(samplingLaw M N), ∀ z : (Option (Fin m) × Fin (n + 1)) × Fin N,
      match z.1.1 with
      | none => data z = none
      | some j => data z = none ∨ data z = some j := by
  classical
  let M := familyMDP i γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
    (by exact_mod_cast hpq) (by exact_mod_cast hq)
  let μ := samplingLaw M N
  apply ae_all_iff.mpr
  intro z
  rw [ae_iff]
  change μ ((fun data : Samples (Option (Fin m)) (Fin (n + 1)) N ↦ data z) ⁻¹'
    {s | ¬ (match z.1.1 with | none => s = none | some j => s = none ∨ s = some j)}) = 0
  rw [← Measure.map_apply (measurable_pi_apply z) (Set.to_countable _).measurableSet,
    samplingLaw_marginal]
  rcases z with ⟨⟨s, a⟩, t⟩
  cases s with
  | none =>
    simp [M, familyMDP, FiniteDistribution.rowMeasure, FiniteDistribution.toPMF_apply,
      EnvironmentStage.pointMass, PMF.toMeasure_apply, tsum_fintype]
  | some j =>
    by_cases ha : a = hardPolicySignature i j
    · simp only [M, familyMDP, familyStay, ha, ↓reduceIte]
      change ((familyActiveRow j (q : ℝ) _ _).rowMeasure)
        {s | ¬ (s = none ∨ s = some j)} = 0
      rw [familyActiveRow_measure_eq_map j q hq.le,
        Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
      simp
    · simp only [M, familyMDP, familyStay, ha, ↓reduceIte]
      change ((familyActiveRow j (p : ℝ) _ _).rowMeasure)
        {s | ¬ (s = none ∨ s = some j)} = 0
      rw [familyActiveRow_measure_eq_map j p (le_trans hpq hq.le),
        Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
      simp

/-- The entire actual array law is the heterogeneous Bernoulli product law
pushed through the same model-independent reconstruction map. -/
theorem familySamplingLaw_eq_reconstructed_product {m n : ℕ}
    (i : HardFamilyIndex m n) (γ : ℝ) (p q : ℝ≥0)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hpq : p ≤ q) (hq : q < 1) (N : ℕ) :
    let M := familyMDP i γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq) (by exact_mod_cast hq)
    samplingLaw M N =
      (indexedBernoulliLaw (familyBernoulliParameter i p q)
        (familyBernoulliParameter_le_one i p q (le_trans hpq hq.le) hq.le)).map familyReconstruct := by
  classical
  let M := familyMDP i γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
    (by exact_mod_cast hpq) (by exact_mod_cast hq)
  let μ := samplingLaw M N
  have hencode : μ.map familyEncode =
      indexedBernoulliLaw (familyBernoulliParameter i p q)
        (familyBernoulliParameter_le_one i p q (le_trans hpq hq.le) hq.le) :=
    familyEncode_samplingLaw i γ p q hγ hγ1 hpq hq N
  have hae : (fun data ↦ familyReconstruct (familyEncode data)) =ᵐ[μ] id := by
    filter_upwards [familySamplingLaw_rows_supported i γ p q hγ hγ1 hpq hq N] with data hd
    funext z
    rcases z with ⟨⟨s, a⟩, t⟩
    cases s with
    | none => simpa [familyReconstruct, familyEncode] using (hd ((none, a), t)).symm
    | some j =>
      rcases hd ((some j, a), t) with h | h
      · simp [familyReconstruct, familyEncode, h]
      · simp [familyReconstruct, familyEncode, h]
  change μ = _
  calc
    μ = μ.map id := (Measure.map_id).symm
    _ = μ.map (fun data ↦ familyReconstruct (familyEncode data)) := (Measure.map_congr hae).symm
    _ = (μ.map familyEncode).map familyReconstruct := by
      rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
      rfl
    _ = _ := by rw [hencode]

/-- Any fixed estimator/event on the complete original data has the same
probability after model-independent reconstruction from the indicator array. -/
theorem familySamplingLaw_estimator_event {m n : ℕ}
    (i : HardFamilyIndex m n) (γ : ℝ) (p q : ℝ≥0)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hpq : p ≤ q) (hq : q < 1) (N : ℕ)
    {Result : Type*} (estimate : Samples (Option (Fin m)) (Fin (n + 1)) N → Result)
    (event : Set Result) :
    let M := familyMDP i γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq) (by exact_mod_cast hq)
    (samplingLaw M N).real {data | estimate data ∈ event} =
      (indexedBernoulliLaw (familyBernoulliParameter i p q)
        (familyBernoulliParameter_le_one i p q (le_trans hpq hq.le) hq.le)).real
        {x | estimate (familyReconstruct x) ∈ event} := by
  dsimp only
  rw [familySamplingLaw_eq_reconstructed_product i γ p q hγ hγ1 hpq hq N]
  rw [measureReal_def, measureReal_def,
    Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  rfl

end StatisticalRL.GenerativeLowerBound
