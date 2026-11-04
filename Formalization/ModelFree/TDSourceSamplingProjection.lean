import Formalization.ModelFree.TDSourceSamplingDefinitions
import Formalization.ModelFree.TDSynchronousSampling
import Mathlib.Probability.Independence.Basic

/-! Joint-law and pathwise correspondence of the padded and exact-T experiments. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdSourceProjectionStateMeasurable : MeasurableSpace State := ⊤

/-- Projecting the padded product law gives the entire exact-T product law. -/
theorem tdUsedSampleProjection_map_law (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (T : ℕ) :
    (tdSamplingLaw M π T).map (tdUsedSampleProjection T) = tdSourceSamplingLaw M π T := by
  classical
  let shift : State × Fin T → State × Fin (T + 1) := fun i ↦ (i.1, i.2.succ)
  have hinj : Function.Injective shift := by
    intro ⟨s, i⟩ ⟨s', j⟩ h
    have hs : s = s' := congrArg Prod.fst h
    have hi : i = j := Fin.succ_injective T (congrArg Prod.snd h)
    cases hs
    cases hi
    rfl
  have hind := (tdSamplingLaw_independent M π T).precomp hinj
  have hm : ∀ i : State × Fin T,
      AEMeasurable (fun data : TDSamples State T ↦ data (shift i)) (tdSamplingLaw M π T) :=
    fun i ↦ (measurable_pi_apply (shift i)).aemeasurable
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map hm).mp hind
  have hmarginal (i : State × Fin T) :
      (tdSamplingLaw M π T).map (fun data ↦ data (shift i)) =
        (M.policyTransition π i.1).rowMeasure := by
    exact tdSamplingLaw_marginal M π T i.1 i.2.succ
  simpa only [tdUsedSampleProjection, tdSourceSamplingLaw,
    StatisticalRL.ModelBasedPolicyEvaluation.samplingLaw, shift, hmarginal] using hmap

/-- Each finite-prefix iterate agrees pathwise after dropping time zero. -/
theorem tdIterate_usedSampleProjection (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T : ℕ)
    (V₀ : State → ℝ) (data : TDSamples State T) (t : ℕ) (ht : t ≤ T) :
    tdIterate M π η (tdSamplesExtend M T data) V₀ t =
      tdIterate M π η (tdSourceSamplesExtend M T (tdUsedSampleProjection T data)) V₀ t := by
  induction t with
  | zero => rfl
  | succ n ih =>
    have hn : n ≤ T := by omega
    have hn1 : n + 1 ≤ T := by omega
    have hsample : ∀ s, tdSamplesExtend M T data (n + 1) s =
        tdSourceSamplesExtend M T (tdUsedSampleProjection T data) (n + 1) s := by
      intro s
      simp [tdSamplesExtend, tdSourceSamplesExtend, tdUsedSampleProjection,
        show n + 1 < T + 1 by omega, show 1 ≤ n + 1 ∧ n + 1 ≤ T by omega]
    funext s
    simp only [tdIterate]
    rw [ih hn, hsample]

/-- The actual output agrees on every padded sample array. -/
theorem tdSampledIterate_eq_sourceSampledIterate (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T : ℕ)
    (V₀ : State → ℝ) (data : TDSamples State T) :
    tdSampledIterate M π η T V₀ data =
      tdSourceSampledIterate M π η T V₀ (tdUsedSampleProjection T data) := by
  exact tdIterate_usedSampleProjection M π η T V₀ data T le_rfl
end StatisticalRL.TemporalDifference
