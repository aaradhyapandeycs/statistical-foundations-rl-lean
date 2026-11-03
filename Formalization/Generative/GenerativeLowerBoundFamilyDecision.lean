import Formalization.Generative.GenerativeLowerBoundPolicyGap
import Formalization.Generative.ModelBasedPolicyLearning

/-! Conditional finite testing-to-policy-risk reduction on actual family laws. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.ModelBasedPolicyLearning
local instance familyDecisionStateMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
local instance familyDecisionFinMeasurable (n : ℕ) : MeasurableSpace (Fin n) := ⊤

/-- Conditional decision-theoretic reduction: an explicit average testing
lower bound for every common test implies one actual family-model policy risk
is at least c. The information-theoretic premise is not proved here. -/
theorem sourceFamily_averageTesting_to_policyRisk {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) (N : ℕ) (c : ℝ)
    (estimate : Samples (Option (Fin m)) (Fin (n + 1)) N → Option (Fin m) → Fin (n + 1))
    (htest : ∀ test : Samples (Option (Fin m)) (Fin (n + 1)) N → HardFamilyIndex m n,
      c ≤ (∑ i : HardFamilyIndex m n,
        (samplingLaw (sourceFamilyMDP i γ ε hγ hγ1 hε hεmax) N).real {data | test data ≠ i}) /
          Fintype.card (HardFamilyIndex m n)) :
    ∃ i : HardFamilyIndex m n,
      let M := sourceFamilyMDP i γ ε hγ hγ1 hε hεmax
      c ≤ (samplingLaw M N).real {data | ε < ‖M.trajectoryExpectedQ
        (deterministicFamilyPolicy (estimate data)) - M.trajectoryExpectedQ M.optimalGreedyPolicy‖} := by
  classical
  let I := HardFamilyIndex m n
  let test : Samples (Option (Fin m)) (Fin (n + 1)) N → I :=
    fun data ↦ decodeHardPolicy (fun j ↦ estimate data (some j))
  let E (i : I) : ℝ := (samplingLaw (sourceFamilyMDP i γ ε hγ hγ1 hε hεmax) N).real
    {data | test data ≠ i}
  let R (i : I) : ℝ :=
    let M := sourceFamilyMDP i γ ε hγ hγ1 hε hεmax
    (samplingLaw M N).real {data | ε < ‖M.trajectoryExpectedQ
      (deterministicFamilyPolicy (estimate data)) - M.trajectoryExpectedQ M.optimalGreedyPolicy‖}
  have hle (i : I) : E i ≤ R i :=
    sourceFamilyMDP_decoder_error_probability_le_source_Q_risk
      (samplingLaw (sourceFamilyMDP i γ ε hγ hγ1 hε hεmax) N)
      hm hn i γ ε hγ hγ1 hε hεmax estimate
  have hk : (0 : ℝ) < Fintype.card I := by
    haveI : Nonempty I := ⟨none⟩
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have ha : c ≤ (∑ i : I, E i) / Fintype.card I := htest test
  have hsum : (∑ i : I, E i) ≤ ∑ i : I, R i := Finset.sum_le_sum (fun i _ ↦ hle i)
  by_contra hno
  push_neg at hno
  haveI : Nonempty I := ⟨none⟩
  have hno' (i : I) : R i < c := by
    apply lt_of_not_ge
    exact hno i
  have hlt : (∑ i : I, R i) < ∑ _i : I, c :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ ↦ hno' i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
  have hm' := (le_div_iff₀ hk).1 ha
  nlinarith

end StatisticalRL.GenerativeLowerBound
