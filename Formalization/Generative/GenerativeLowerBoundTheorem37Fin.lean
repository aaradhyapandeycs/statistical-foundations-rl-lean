import Formalization.Generative.StateRelabelSampling
import Formalization.Generative.GenerativeLowerBoundQMixtureAnyAction
import Formalization.Generative.GenerativeLowerBoundFamilyFano
import Formalization.Generative.GenerativeLowerBoundUnifiedThreshold
import Formalization.Generative.GenerativeLowerBoundFamilyDecision

/-!
# Corrected Theorem 3.7 on `Fin S × Fin A` carriers

Source: `theorem:azar`, `source/upstream/tex/chapters/generative_model_model_based.tex:1443–1464`.
The printed statement is false at `S = 1` (SOURCE-ISSUES C2) and, for part (i), at `A = 1`
(C1). This module proves the corrected statement with `S ≥ 2` in both parts and `A ≥ 2` in
part (i) only, with `c_N = 1/32768`, for deterministic estimators that receive the known
reward table, the known discount and the full `N`-per-row sample array. The hard models are
the reviewed `Option (Fin m)` families, relabeled to `Fin (m+1)` states by
`(finSuccEquiv m).symm`; the risk events are transported by `relabelStates_*` and
`samplingLaw_relabelStates_real`.
-/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.GenerativeLowerBound

open StatisticalRL.ModelBasedPolicyLearning StatisticalRL.DiscountedMDP

local instance theorem37FinOptionMeasurable (m : ℕ) : MeasurableSpace (Option (Fin m)) := ⊤

/-- Deterministic policy estimators on the source hard family: risk at least `1/4` under
the common `32768` budget. -/
theorem sourceFamily_deterministic_policy_risk_quarter {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hsize : 16 ≤ (m + 1) * (n + 1))
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ))) (N : ℕ)
    (hbudget : 32768 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) ≤
      Real.log ((m + 1 : ℕ) * (n + 1)))
    (estimate : Samples (Option (Fin m)) (Fin (n + 1)) N → Option (Fin m) → Fin (n + 1)) :
    ∃ i : HardFamilyIndex m n,
      let M := sourceFamilyMDP i γ ε hγ hγ1 hε hεmax
      (1 : ℝ) / 4 ≤ (samplingLaw M N).real {data | ε < ‖M.trajectoryExpectedQ
        (deterministicFamilyPolicy (estimate data)) -
          M.trajectoryExpectedQ M.optimalGreedyPolicy‖} := by
  classical
  have ht : 0 ≤ (N : ℝ) * (1 - γ) ^ 3 * ε ^ 2 := by
    have hg : 0 ≤ 1 - γ := by linarith
    positivity
  have hb := correctedFamily_common_budget m n hm hn _ ht hbudget
  have hlarge : 4096 * (N : ℝ) * (1 - γ) ^ 3 * ε ^ 2 ≤
      Real.log (Fintype.card (HardFamilyIndex m n)) := by
    rcases hb with ⟨_, h⟩ | ⟨hs, _⟩
    · nlinarith
    · omega
  have hk : (4 : ℝ) ≤ Fintype.card (HardFamilyIndex m n) := by
    exact_mod_cast hardFamilyIndex_card_ge_four m n hm hn hsize
  have hb4 : 1024 * (N : ℝ) * (1 - γ) ^ 3 * ε ^ 2 ≤
      Real.log (Fintype.card (HardFamilyIndex m n)) / 4 := by linarith
  have htest (d : Samples (Option (Fin m)) (Fin (n + 1)) N → HardFamilyIndex m n) :
      (1 : ℝ) / 4 ≤ (∑ i : HardFamilyIndex m n,
        (samplingLaw (sourceFamilyMDP i γ ε hγ hγ1 hε hεmax) N).real
          {data | d data ≠ i}) / Fintype.card (HardFamilyIndex m n) :=
    (fano_large_cardinality_quarter _ _ hk hb4).trans
      (sourceFamily_average_error_fano hm hn γ ε hγ hγ1 hε hεmax N d)
  exact sourceFamily_averageTesting_to_policyRisk hm hn γ ε hγ hγ1 hε hεmax
    N (1 / 4) estimate htest

/-- The printed sample bound with `c_N = 1/32768`, in budget form. `N = 0` is allowed. -/
theorem theorem37_budget_of_sampleBound (S A N : ℕ) (γ ε : ℝ) (hγ1 : γ < 1) (hε : 0 < ε)
    (hN : (N : ℝ) ≤ (1 / 32768) * Real.log ((S : ℝ) * (A : ℝ)) / ((1 - γ) ^ 3 * ε ^ 2)) :
    32768 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) ≤ Real.log ((S : ℝ) * (A : ℝ)) := by
  have hg : 0 < 1 - γ := by linarith
  have hD : 0 < (1 - γ) ^ 3 * ε ^ 2 := by positivity
  have h := (le_div_iff₀ hD).mp hN
  nlinarith

/-- Corrected Theorem 3.7(i) on `Fin S × Fin A`: every deterministic policy estimator that
receives the known reward, the known discount and the samples fails on some MDP with `S`
states, `A` actions and discount `γ`. -/
theorem theorem37_policy_fin {S A N : ℕ} (hS : 2 ≤ S) (hA : 2 ≤ A) (hSA : 16 ≤ S * A)
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ)))
    (hbudget : 32768 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) ≤ Real.log ((S : ℝ) * (A : ℝ)))
    (piHat : (Fin S → Fin A → ℝ) → ℝ → Samples (Fin S) (Fin A) N → Fin S → Fin A) :
    ∃ M : DiscountedMDP (Fin S) (Fin A), M.discount = γ ∧
      (1 : ℝ) / 4 ≤ (samplingLaw M N).real
        {data | ε < ‖M.trajectoryExpectedQ
            (fun s ↦ EnvironmentStage.pointMass (piHat M.reward M.discount data s)) -
          M.trajectoryExpectedQ M.optimalGreedyPolicy‖} := by
  obtain ⟨m, rfl⟩ : ∃ m, S = m + 1 := ⟨S - 1, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, A = n + 1 := ⟨A - 1, by omega⟩
  let e : Option (Fin m) ≃ Fin (m + 1) := (finSuccEquiv m).symm
  let r₀ : Fin (m + 1) → Fin (n + 1) → ℝ :=
    ((sourceFamilyMDP (none : HardFamilyIndex m n) γ ε hγ hγ1 hε hεmax).relabelStates e).reward
  let est : Samples (Option (Fin m)) (Fin (n + 1)) N → Option (Fin m) → Fin (n + 1) :=
    fun d s ↦ piHat r₀ γ (relabelSamples e N d) (e s)
  have hb' : 32768 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) ≤
      Real.log ((m + 1 : ℕ) * (n + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hbudget
  obtain ⟨i, hi⟩ := sourceFamily_deterministic_policy_risk_quarter (by omega) (by omega) hSA
    γ ε hγ hγ1 hε hεmax N hb' est
  refine ⟨(sourceFamilyMDP i γ ε hγ hγ1 hε hεmax).relabelStates e, rfl, ?_⟩
  rw [samplingLaw_relabelStates_real]
  refine le_of_le_of_eq hi ?_
  congr 1
  ext d
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [relabelStates_policy_Q_loss_norm]
  rfl

/-- Corrected Theorem 3.7(ii) on `Fin S × Fin A`, for every `A` with `SA ≥ 16`: every
deterministic Q-function estimator that receives the known reward, the known discount and
the samples fails on some MDP with `S` states, `A` actions and discount `γ`. -/
theorem theorem37_Q_fin {S A N : ℕ} (hS : 2 ≤ S) (hSA : 16 ≤ S * A)
    (γ ε : ℝ) (hγ : (2 : ℝ) / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hεmax : ε < 1 / (32 * (1 - γ)))
    (hbudget : 32768 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) ≤ Real.log ((S : ℝ) * (A : ℝ)))
    (QHat : (Fin S → Fin A → ℝ) → ℝ → Samples (Fin S) (Fin A) N → Fin S → Fin A → ℝ) :
    ∃ M : DiscountedMDP (Fin S) (Fin A), M.discount = γ ∧
      (1 : ℝ) / 4 ≤ (samplingLaw M N).real
        {data | ε < ‖QHat M.reward M.discount data -
          M.trajectoryExpectedQ M.optimalGreedyPolicy‖} := by
  obtain ⟨m, rfl⟩ : ∃ m, S = m + 1 := ⟨S - 1, by omega⟩
  have hA : 1 ≤ A := by
    rcases Nat.eq_zero_or_pos A with h | h
    · subst h; omega
    · exact h
  letI : NeZero A := ⟨by omega⟩
  let e : Option (Fin m) ≃ Fin (m + 1) := (finSuccEquiv m).symm
  let r₀ : Fin (m + 1) → Fin A → ℝ :=
    ((qMixtureSourceMDP (none : QMixtureIndex m A) γ ε hγ hγ1 hε hεmax).relabelStates e).reward
  let est : Samples (Option (Fin m)) (Fin A) N → Option (Fin m) → Fin A → ℝ :=
    fun d s ↦ QHat r₀ γ (relabelSamples e N d) (e s)
  have hgap : 0 ≤ 1 - γ := by linarith
  have hterm : 0 ≤ (N : ℝ) * (1 - γ) ^ 3 * ε ^ 2 := by positivity
  have hb' : 512 * ((N : ℝ) * (1 - γ) ^ 3 * ε ^ 2) ≤ Real.log ((m + 1) * A) := by
    have h := hbudget
    push_cast at h
    linarith
  obtain ⟨i, hi⟩ := qMixtureSource_deterministic_Q_risk_of_pos (by omega) hA hSA
    γ ε hγ hγ1 hε hεmax N hb' est
  refine ⟨(qMixtureSourceMDP i γ ε hγ hγ1 hε hεmax).relabelStates e, rfl, ?_⟩
  rw [samplingLaw_relabelStates_real]
  refine le_of_le_of_eq hi ?_
  congr 1
  ext d
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  rw [relabelStates_estimate_Q_loss_norm]
  rfl

/-- The body of the proposed `Thm3_7_corrected` index entry at `c_N = 1/32768`. -/
theorem theorem37_corrected_fin_carriers :
    ∀ (S A N : ℕ) (γ ε : ℝ),
      2 ≤ S → 16 ≤ S * A →
      (2 : ℝ) / 3 ≤ γ → γ < 1 → 0 < ε → ε < 1 / (32 * (1 - γ)) →
      (N : ℝ) ≤ (1 / 32768) * Real.log ((S : ℝ) * (A : ℝ)) / ((1 - γ) ^ 3 * ε ^ 2) →
      (2 ≤ A →
        ∀ piHat : (Fin S → Fin A → ℝ) → ℝ →
            StatisticalRL.ModelBasedPolicyLearning.Samples (Fin S) (Fin A) N → Fin S → Fin A,
          ∃ M : DiscountedMDP (Fin S) (Fin A), M.discount = γ ∧
            (1 : ℝ) / 4 ≤ (StatisticalRL.ModelBasedPolicyLearning.samplingLaw M N).real
              {data | ε < ‖M.trajectoryExpectedQ
                  (fun s ↦ EnvironmentStage.pointMass (piHat M.reward M.discount data s)) -
                M.trajectoryExpectedQ M.optimalGreedyPolicy‖}) ∧
      (∀ QHat : (Fin S → Fin A → ℝ) → ℝ →
            StatisticalRL.ModelBasedPolicyLearning.Samples (Fin S) (Fin A) N → Fin S → Fin A → ℝ,
          ∃ M : DiscountedMDP (Fin S) (Fin A), M.discount = γ ∧
            (1 : ℝ) / 4 ≤ (StatisticalRL.ModelBasedPolicyLearning.samplingLaw M N).real
              {data | ε < ‖QHat M.reward M.discount data -
                M.trajectoryExpectedQ M.optimalGreedyPolicy‖}) := by
  intro S A N γ ε hS hSA hγ hγ1 hε hεmax hN
  have hbudget := theorem37_budget_of_sampleBound S A N γ ε hγ1 hε hN
  exact ⟨fun hA piHat ↦ theorem37_policy_fin hS hA hSA γ ε hγ hγ1 hε hεmax hbudget piHat,
    fun QHat ↦ theorem37_Q_fin hS hSA γ ε hγ hγ1 hε hεmax hbudget QHat⟩

end StatisticalRL.GenerativeLowerBound
