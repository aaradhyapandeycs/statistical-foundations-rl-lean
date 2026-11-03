import Formalization.Generative.GenerativeLowerBoundJointDecision
import Formalization.Generative.GenerativeLowerBoundFamilySparseKL
import Formalization.Generative.GenerativeLowerBoundIndexGeometry

/-! Finite Fano on the indexed generative-model family. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.ModelBasedPolicyLearning
local instance familyFanoStateMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
local instance familyFanoFinMeasurable (n : ℕ) : MeasurableSpace (Fin n) := ⊤

/-- The genuine full-array indexed-family average error is bounded below by
finite Fano, for one common decoder and exact family cardinality. -/
theorem sourceFamily_average_error_fano {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) (N : ℕ)
    (d : Samples (Option (Fin m)) (Fin (n + 1)) N → HardFamilyIndex m n) :
    let K := Fintype.card (HardFamilyIndex m n)
    let B := (1024 : ℝ) * N * (1 - γ) ^ 3 * ε ^ 2
    1 - (B + Real.log 2) / Real.log K ≤
      (∑ i : HardFamilyIndex m n,
        (samplingLaw (sourceFamilyMDP i γ ε hγ hγ1 hε hεmax) N).real
          {data | d data ≠ i}) / K := by
  classical
  let I := HardFamilyIndex m n
  let Ω := FamilyActiveCoordinates m n N → Bool
  haveI : Nonempty I := ⟨none⟩
  letI : MeasurableSpace I := ⊤
  haveI : MeasurableSingletonClass I := ⟨fun _ ↦ trivial⟩
  have ha := source_parameters_admissible γ ε hγ hγ1 hε hεmax
  let p : ℝ≥0 := ⟨baseProbability γ, by linarith [ha.1]⟩
  let q : ℝ≥0 := ⟨baseProbability γ + probabilityIncrement γ ε, by linarith [ha.1, ha.2.1]⟩
  have hp : 0 < p := by change 0 < baseProbability γ; linarith [ha.1]
  have hpq : p ≤ q := by change baseProbability γ ≤ baseProbability γ + probabilityIncrement γ ε; linarith [ha.2.1]
  have hq : q < 1 := by exact_mod_cast ha.2.2.1
  have hp1 : p < 1 := lt_of_le_of_lt hpq hq
  have hq0 : 0 < q := lt_of_lt_of_le hp hpq
  let u (i : I) : FamilyActiveCoordinates m n N → ℝ≥0 := familyBernoulliParameter i p q
  have hu0 (i : I) : ∀ z, 0 < u i z := familyBernoulliParameter_pos i p q hp hq0
  have hu1 (i : I) : ∀ z, u i z < 1 := familyBernoulliParameter_lt_one i p q hp1 hq
  let P (i : I) : Measure Ω := indexedBernoulliLaw (u i) (fun z ↦ (hu1 i z).le)
  haveI (i : I) : IsProbabilityMeasure (P i) := by dsimp [P]; infer_instance
  have hP : ∀ i x, P i {x} ≠ 0 := fun i ↦ indexedBernoulliLaw_atom_ne_zero (u i) (hu0 i) (hu1 i)
  have hK : 2 ≤ Fintype.card I := by
    have h := hardFamilyIndex_card m n
    dsimp [I] at ⊢
    rw [h]
    nlinarith
  let dec : Ω → I := fun x ↦ d (familyReconstruct x)
  have hf := finite_joint_decoding_error_bound P (P none) hP (hP none) hK dec
  let B : ℝ := 1024 * N * (1 - γ) ^ 3 * ε ^ 2
  have hB : 0 ≤ B := by
    have hh : 0 ≤ 1 - γ := by linarith
    dsimp [B]
    positivity
  have heq (i : I) : (InformationTheory.klDiv (P i) (P none)).toReal =
      (InformationTheory.klDiv (samplingLaw (sourceFamilyMDP i γ ε hγ hγ1 hε hεmax) N)
        (samplingLaw (sourceFamilyMDP none γ ε hγ hγ1 hε hεmax) N)).toReal := by
    have h := familySamplingLaw_klDiv_eq_indexedProduct i none γ p q (by linarith) hγ1 hp hpq hq N
    dsimp only at h
    dsimp only [sourceFamilyMDP]
    exact h.symm
  have hkl (i : I) : (InformationTheory.klDiv (P i) (P none)).toReal ≤ B := by
    cases i with
    | none => simp [InformationTheory.klDiv_self, hB]
    | some v =>
      rcases v with ⟨j, k⟩
      rw [heq]
      exact sourceFamilyAlternative_fullKL_le j k γ ε hγ hγ1 hε hεmax N
  have herr (i : I) : (P i).real {x | dec x ≠ i} =
      (samplingLaw (sourceFamilyMDP i γ ε hγ hγ1 hε hεmax) N).real {data | d data ≠ i} := by
    have h := familySamplingLaw_eq_reconstructed_product i γ p q (by linarith) hγ1 hpq hq N
    dsimp only [sourceFamilyMDP]
    change (P i).real {x | dec x ≠ i} =
      (samplingLaw (familyMDP i γ (p : ℝ) (q : ℝ) _ _ _ _ _) N).real {data | d data ≠ i}
    rw [h]
    simp only [measureReal_def]
    rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
    rfl
  have hmean : (∑ i, (InformationTheory.klDiv (P i) (P none)).toReal) / Fintype.card I ≤ B := by
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hkl i)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    have hcard : (0 : ℝ) < Fintype.card I := by exact_mod_cast Fintype.card_pos
    apply (div_le_iff₀ hcard).2
    nlinarith
  have hlog : 0 < Real.log (Fintype.card I) := Real.log_pos (by exact_mod_cast hK)
  have hdiv : ((∑ i, (InformationTheory.klDiv (P i) (P none)).toReal) / Fintype.card I + Real.log 2) /
      Real.log (Fintype.card I) ≤ (B + Real.log 2) / Real.log (Fintype.card I) :=
    div_le_div_of_nonneg_right (by linarith) hlog.le
  simp_rw [herr] at hf
  dsimp only
  linarith

end StatisticalRL.GenerativeLowerBound
