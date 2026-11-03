import Formalization.Generative.GenerativeLowerBoundFamilyFano
import Formalization.Generative.GenerativeLowerBoundFamilyDecision
import Formalization.Generative.GenerativeLowerBoundKLAffinity

/-! Actual two-point family testing to trajectory-Q policy risk. -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.ModelBasedPolicyLearning
local instance twoPointRiskStateMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
local instance twoPointRiskFinMeasurable (n : ℕ) : MeasurableSpace (Fin n) := ⊤

/-- A common policy estimator has strict >0.1 risk for one of two actual
family models when the source KL upper bound is at most 0.9. -/
theorem sourceFamily_twoPoint_policy_risk {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) (N : ℕ)
    (hbudget : 1024 * (N : ℝ) * (1 - γ) ^ 3 * ε ^ 2 ≤ 9 / 10)
    (estimate : Samples (Option (Fin m)) (Fin (n + 1)) N → Option (Fin m) → Fin (n + 1)) :
    ∃ i : HardFamilyIndex m n,
      let M := sourceFamilyMDP i γ ε hγ hγ1 hε hεmax
      (1 : ℝ) / 10 < (samplingLaw M N).real {data | ε < ‖M.trajectoryExpectedQ
        (deterministicFamilyPolicy (estimate data)) - M.trajectoryExpectedQ M.optimalGreedyPolicy‖} := by
  classical
  let I := HardFamilyIndex m n
  let Ω := FamilyActiveCoordinates m n N → Bool
  haveI : Nonempty Ω := ⟨fun _ ↦ false⟩
  let j : Fin m := ⟨0, by omega⟩
  let k : Fin n := ⟨0, by omega⟩
  let a : I := some (j, k)
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
  have heq : (InformationTheory.klDiv (P a) (P none)).toReal =
      (InformationTheory.klDiv (samplingLaw (sourceFamilyMDP a γ ε hγ hγ1 hε hεmax) N)
        (samplingLaw (sourceFamilyMDP none γ ε hγ hγ1 hε hεmax) N)).toReal := by
    have h := familySamplingLaw_klDiv_eq_indexedProduct a none γ p q (by linarith) hγ1 hp hpq hq N
    dsimp only at h
    dsimp only [sourceFamilyMDP]
    exact h.symm
  have hKL : (InformationTheory.klDiv (P a) (P none)).toReal ≤ 9 / 10 := by
    rw [heq]
    exact (sourceFamilyAlternative_fullKL_le j k γ ε hγ hγ1 hε hεmax N).trans hbudget
  let est : Ω → Option (Fin m) → Fin (n + 1) := fun x ↦ estimate (familyReconstruct x)
  let test : Ω → Bool := fun x ↦ decide (decodeHardPolicy (fun z ↦ est x (some z)) = a)
  have ht := finite_test_error_gt_one_tenth (P a) (P none) (hP a) (hP none) hKL test
  have hbase : (P none).real {x | test x = true} ≤
      (P none).real {x | decodeHardPolicy (fun z ↦ est x (some z)) ≠ none} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro x hx
    have hx' : decodeHardPolicy (fun z ↦ est x (some z)) = a := of_decide_eq_true hx
    simp [hx', a]
  have halt : (P a).real {x | test x = false} ≤
      (P a).real {x | decodeHardPolicy (fun z ↦ est x (some z)) ≠ a} := by
    apply measureReal_mono _ (measure_ne_top _ _)
    intro x hx
    exact of_decide_eq_false hx
  have hrisk (i : I) : (P i).real {x | decodeHardPolicy (fun z ↦ est x (some z)) ≠ i} ≤
      (samplingLaw (sourceFamilyMDP i γ ε hγ hγ1 hε hεmax) N).real
        {data | ε < ‖(sourceFamilyMDP i γ ε hγ hγ1 hε hεmax).trajectoryExpectedQ
          (deterministicFamilyPolicy (estimate data)) -
          (sourceFamilyMDP i γ ε hγ hγ1 hε hεmax).trajectoryExpectedQ
            (sourceFamilyMDP i γ ε hγ hγ1 hε hεmax).optimalGreedyPolicy‖} := by
    have hh := sourceFamilyMDP_decoder_error_probability_le_source_Q_risk
      (P i) hm hn i γ ε hγ hγ1 hε hεmax est
    apply hh.trans
    have h := familySamplingLaw_eq_reconstructed_product i γ p q (by linarith) hγ1 hpq hq N
    dsimp only [sourceFamilyMDP] at ⊢
    change _ ≤ (samplingLaw (familyMDP i γ (p : ℝ) (q : ℝ) _ _ _ _ _) N).real _
    rw [h]
    simp only [measureReal_def]
    rw [Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
    rfl
  rcases lt_max_iff.mp ht with h | h
  · exact ⟨none, h.trans_le (hbase.trans (hrisk none))⟩
  · exact ⟨a, h.trans_le (halt.trans (hrisk a))⟩

end StatisticalRL.GenerativeLowerBound
