import Formalization.Generative.GenerativeLowerBoundQMixtureFamily
import Formalization.Generative.GenerativeLowerBoundFamilyObservation
import Formalization.Generative.GenerativeLowerBoundIndexedProductKL
import Formalization.Generative.PolicyLearningHoeffding

/-! Encode and reconstruct actual indexed-family sample arrays. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.ModelBasedPolicyLearning
local instance qMixtureObservationStateMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
local instance qMixtureObservationFinMeasurable (n : ℕ) : MeasurableSpace (Fin n) := ⊤

/-- Active row and sample indices, excluding the deterministic absorber. -/
abbrev QMixtureActiveCoordinates (m n N : ℕ) := (Fin m × Fin n) × Fin N

/-- Coordinate encoder: did the active row self-loop? -/
def qMixtureEncode {m n N : ℕ}
    (data : Samples (Option (Fin m)) (Fin n) N) : QMixtureActiveCoordinates m n N → Bool :=
  fun z ↦ decide (data ((some z.1.1, z.1.2), z.2) = some z.1.1)

/-- Model-independent full-array reconstruction; absorber rows are filled
with none, and each active row can reach only itself or the absorber. -/
def qMixtureReconstruct {m n N : ℕ} (x : QMixtureActiveCoordinates m n N → Bool) :
    Samples (Option (Fin m)) (Fin n) N :=
  fun z ↦ match z.1.1 with
    | none => none
    | some j => if x ((j, z.1.2), z.2) then some j else none

/-- Bernoulli parameter of each active state/action/sample coordinate. -/
def qMixtureBernoulliParameter {m n N : ℕ} (i : QMixtureIndex m n) (p q : ℝ≥0)
    (z : QMixtureActiveCoordinates m n N) : ℝ≥0 :=
  if i = some (z.1.1, z.1.2) then q else p

/-- The family parameter is always valid under the two row bounds. -/
theorem qMixtureBernoulliParameter_le_one {m n N : ℕ} (i : QMixtureIndex m n)
    (p q : ℝ≥0) (hp : p ≤ 1) (hq : q ≤ 1) :
    ∀ z : QMixtureActiveCoordinates m n N, qMixtureBernoulliParameter i p q z ≤ 1 := by
  intro z
  unfold qMixtureBernoulliParameter
  split <;> assumption

/-- The self-loop indicators extracted from the actual complete generative
array have the exact heterogeneous Bernoulli product law. -/
theorem qMixtureEncode_samplingLaw {m n : ℕ} [NeZero n] (i : QMixtureIndex m n) (γ : ℝ)
    (p q : ℝ≥0) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hpq : p ≤ q) (hq : q < 1) (N : ℕ) :
    let M := qMixtureMDP i γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq) (by exact_mod_cast hq)
    (samplingLaw M N).map qMixtureEncode =
      indexedBernoulliLaw (qMixtureBernoulliParameter i p q)
        (qMixtureBernoulliParameter_le_one i p q (le_trans hpq hq.le) hq.le) := by
  classical
  let M := qMixtureMDP i γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
    (by exact_mod_cast hpq) (by exact_mod_cast hq)
  let μ := samplingLaw M N
  let j : QMixtureActiveCoordinates m n N → ((Option (Fin m) × Fin n) × Fin N) :=
    fun z ↦ ((some z.1.1, z.1.2), z.2)
  have hj : Function.Injective j := by
    intro x y h
    rcases x with ⟨⟨xj, xa⟩, xt⟩
    rcases y with ⟨⟨yj, ya⟩, yt⟩
    simp only [j, Prod.mk.injEq, Option.some.injEq] at h
    rcases h with ⟨⟨rfl, rfl⟩, rfl⟩
    rfl
  let raw : QMixtureActiveCoordinates m n N → Samples (Option (Fin m)) (Fin n) N → Option (Fin m) :=
    fun z data ↦ data (j z)
  let enc : QMixtureActiveCoordinates m n N → Option (Fin m) → Bool :=
    fun z s ↦ decide (s = some z.1.1)
  have hi : iIndepFun raw μ := (samplingLaw_independent M N).precomp hj
  have he : iIndepFun (fun z ↦ enc z ∘ raw z) μ := hi.comp enc (fun z ↦ measurable_of_countable _)
  have hm : ∀ z, AEMeasurable (fun data ↦ enc z (raw z data)) μ :=
    fun z ↦ (measurable_of_countable _).aemeasurable
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map hm).mp he
  change μ.map qMixtureEncode = _
  change μ.map (fun data z ↦ enc z (raw z data)) = _
  rw [hmap]
  unfold indexedBernoulliLaw
  congr 1
  funext z
  have hcoord : μ.map (raw z) = (M.transition (some z.1.1) z.1.2).rowMeasure :=
    samplingLaw_marginal M N (j z)
  change μ.map (enc z ∘ raw z) = _
  rw [← Measure.map_map (measurable_of_countable _) (measurable_of_countable _), hcoord]
  by_cases hz : i = some (z.1.1, z.1.2)
  · simpa [M, qMixtureMDP, qMixtureStay, qMixtureBernoulliParameter, enc, hz] using
      familyActiveRow_encode_measure z.1.1 q hq.le
  · simpa [M, qMixtureMDP, qMixtureStay, qMixtureBernoulliParameter, enc, hz] using
      familyActiveRow_encode_measure z.1.1 p (le_trans hpq hq.le)

/-- Every coordinate of the actual full sample array lies in its model's
row support, including every padded absorber action. -/
theorem qMixtureSamplingLaw_rows_supported {m n : ℕ} [NeZero n] (i : QMixtureIndex m n) (γ : ℝ)
    (p q : ℝ≥0) (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hpq : p ≤ q) (hq : q < 1) (N : ℕ) :
    let M := qMixtureMDP i γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq) (by exact_mod_cast hq)
    ∀ᵐ data ∂(samplingLaw M N), ∀ z : (Option (Fin m) × Fin n) × Fin N,
      match z.1.1 with
      | none => data z = none
      | some j => data z = none ∨ data z = some j := by
  classical
  let M := qMixtureMDP i γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
    (by exact_mod_cast hpq) (by exact_mod_cast hq)
  let μ := samplingLaw M N
  apply ae_all_iff.mpr
  intro z
  rw [ae_iff]
  change μ ((fun data : Samples (Option (Fin m)) (Fin n) N ↦ data z) ⁻¹'
    {s | ¬ (match z.1.1 with | none => s = none | some j => s = none ∨ s = some j)}) = 0
  rw [← Measure.map_apply (measurable_pi_apply z) (Set.to_countable _).measurableSet,
    samplingLaw_marginal]
  rcases z with ⟨⟨s, a⟩, t⟩
  cases s with
  | none =>
    simp [M, qMixtureMDP, FiniteDistribution.rowMeasure, FiniteDistribution.toPMF_apply,
      EnvironmentStage.pointMass, PMF.toMeasure_apply, tsum_fintype]
  | some j =>
    by_cases ha : i = some (j,a)
    · simp only [M, qMixtureMDP, qMixtureStay, ha, ↓reduceIte]
      change ((familyActiveRow j (q : ℝ) _ _).rowMeasure)
        {s | ¬ (s = none ∨ s = some j)} = 0
      rw [familyActiveRow_measure_eq_map j q hq.le,
        Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
      simp
    · simp only [M, qMixtureMDP, qMixtureStay, ha, ↓reduceIte]
      change ((familyActiveRow j (p : ℝ) _ _).rowMeasure)
        {s | ¬ (s = none ∨ s = some j)} = 0
      rw [familyActiveRow_measure_eq_map j p (le_trans hpq hq.le),
        Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
      simp

/-- The entire actual array law is the heterogeneous Bernoulli product law
pushed through the same model-independent reconstruction map. -/
theorem qMixtureSamplingLaw_eq_reconstructed_product {m n : ℕ} [NeZero n]
    (i : QMixtureIndex m n) (γ : ℝ) (p q : ℝ≥0)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hpq : p ≤ q) (hq : q < 1) (N : ℕ) :
    let M := qMixtureMDP i γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
      (by exact_mod_cast hpq) (by exact_mod_cast hq)
    samplingLaw M N =
      (indexedBernoulliLaw (qMixtureBernoulliParameter i p q)
        (qMixtureBernoulliParameter_le_one i p q (le_trans hpq hq.le) hq.le)).map qMixtureReconstruct := by
  classical
  let M := qMixtureMDP i γ (p : ℝ) (q : ℝ) hγ hγ1 (by positivity)
    (by exact_mod_cast hpq) (by exact_mod_cast hq)
  let μ := samplingLaw M N
  have hencode : μ.map qMixtureEncode =
      indexedBernoulliLaw (qMixtureBernoulliParameter i p q)
        (qMixtureBernoulliParameter_le_one i p q (le_trans hpq hq.le) hq.le) :=
    qMixtureEncode_samplingLaw i γ p q hγ hγ1 hpq hq N
  have hae : (fun data ↦ qMixtureReconstruct (qMixtureEncode data)) =ᵐ[μ] id := by
    filter_upwards [qMixtureSamplingLaw_rows_supported i γ p q hγ hγ1 hpq hq N] with data hd
    funext z
    rcases z with ⟨⟨s, a⟩, t⟩
    cases s with
    | none => simpa [qMixtureReconstruct, qMixtureEncode] using (hd ((none, a), t)).symm
    | some j =>
      rcases hd ((some j, a), t) with h | h
      · simp [qMixtureReconstruct, qMixtureEncode, h]
      · simp [qMixtureReconstruct, qMixtureEncode, h]
  change μ = _
  calc
    μ = μ.map id := (Measure.map_id).symm
    _ = μ.map (fun data ↦ qMixtureReconstruct (qMixtureEncode data)) := (Measure.map_congr hae).symm
    _ = (μ.map qMixtureEncode).map qMixtureReconstruct := by
      rw [Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
      rfl
    _ = _ := by rw [hencode]

end StatisticalRL.GenerativeLowerBound
