import Formalization.Generative.GenerativeLowerBoundSeededAveraging
import Formalization.Generative.GenerativeLowerBoundFanoThreshold
import Formalization.Generative.GenerativeLowerBoundFamilyFano

/-! One hard model for a shared finite seed, large family branch. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.GenerativeLowerBound
open StatisticalRL.ModelBasedPolicyLearning
local instance seededLargeState (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤
local instance seededLargeFin (n : ℕ) : MeasurableSpace (Fin n) := ⊤

/-- Strict actual trajectory-Q risk after averaging one common seed. -/
theorem sourceFamily_seeded_large_policy_risk {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hsize : 16 ≤ (m + 1) * (n + 1))
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) (N : ℕ)
    (hbudget : 4096 * (N : ℝ) * (1 - γ) ^ 3 * ε ^ 2 ≤
      Real.log (Fintype.card (HardFamilyIndex m n)))
    {Ξ : Type*} [Fintype Ξ] [MeasurableSpace Ξ] [MeasurableSingletonClass Ξ]
    (σ : Measure Ξ) [IsProbabilityMeasure σ]
    (estimate : Samples (Option (Fin m)) (Fin (n + 1)) N × Ξ → Option (Fin m) → Fin (n + 1)) :
    ∃ i : HardFamilyIndex m n,
      let M := sourceFamilyMDP i γ ε hγ hγ1 hε hεmax
      (1 : ℝ) / 10 < (independentSeedLaw (samplingLaw M N) σ).real
        {z | ε < ‖M.trajectoryExpectedQ (deterministicFamilyPolicy (estimate z)) -
          M.trajectoryExpectedQ M.optimalGreedyPolicy‖} := by
  classical
  let I := HardFamilyIndex m n
  haveI : Nonempty I := ⟨none⟩
  let M (i : I) := sourceFamilyMDP i γ ε hγ hγ1 hε hεmax
  let P (i : I) := samplingLaw (M i) N
  haveI (i : I) : IsProbabilityMeasure (P i) := by dsimp [P]; infer_instance
  let D (i : I) := {z | decodeHardPolicy (fun j ↦ estimate z (some j)) ≠ i}
  let R (i : I) := {z | ε < ‖(M i).trajectoryExpectedQ (deterministicFamilyPolicy (estimate z)) -
      (M i).trajectoryExpectedQ (M i).optimalGreedyPolicy‖}
  have hsub : ∀ i, D i ⊆ R i := by
    intro i z hz
    have h := sourceFamilyMDP_decoder_error_Q_norm_gt hm hn i γ ε hγ hγ1 hε hεmax (estimate z) hz
    simpa only [R, M, norm_sub_rev] using h
  have hk : (4 : ℝ) ≤ Fintype.card I := by
    exact_mod_cast hardFamilyIndex_card_ge_four m n hm hn hsize
  have hb : 1024 * (N : ℝ) * (1 - γ) ^ 3 * ε ^ 2 ≤ Real.log (Fintype.card I) / 4 := by linarith
  have htest (r : Ξ) : (1 : ℝ) / 4 ≤
      (∑ i : I, (P i).real {x | (x,r) ∈ D i}) / Fintype.card I := by
    have h := sourceFamily_average_error_fano hm hn γ ε hγ hγ1 hε hεmax N
      (fun x ↦ decodeHardPolicy (fun j ↦ estimate (x,r) (some j)))
    exact (fano_large_cardinality_quarter _ _ hk hb).trans h
  obtain ⟨i, hi⟩ := finiteSeed_averageTesting_to_oneRisk P σ D R (1 / 4) hsub htest
  exact ⟨i, lt_of_lt_of_le (by norm_num) hi⟩

end StatisticalRL.GenerativeLowerBound
