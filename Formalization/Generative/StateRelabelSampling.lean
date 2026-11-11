import Formalization.MDP.StateRelabel
import Formalization.Generative.ModelBasedDefinitions

/-!
# State relabeling of the generative-model sampling law

For a bijection `e : σ ≃ τ` of state carriers, the full `N`-per-row generative sample
array of the relabeled MDP has exactly the law of the original array with every row
index and every observed next state renamed by `e`.
-/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.ModelBasedPolicyLearning

open StatisticalRL.DiscountedMDP

variable {σ τ Action : Type*} [Fintype σ] [Fintype τ] [Fintype Action]

local instance stateRelabelSamplingMeasurable {X : Type*} [Fintype X] : MeasurableSpace X := ⊤

/-- One draw from a relabeled row is the image under `e` of one draw from the row. -/
theorem rowMeasure_relabel (d : FiniteDistribution σ) (e : σ ≃ τ) :
    (d.relabel e).rowMeasure = d.rowMeasure.map e := by
  unfold FiniteDistribution.rowMeasure
  rw [PMF.toMeasure_map (hf := measurable_from_top)]
  congr 1
  ext t
  rw [PMF.map_apply, tsum_fintype]
  unfold FiniteDistribution.toPMF
  simp only [PMF.ofFintype_apply, FiniteDistribution.relabel_prob]
  rw [Finset.sum_eq_single (e.symm t)]
  · rw [if_pos (by simp)]
  · intro s _ hs
    rw [if_neg]
    intro h
    apply hs
    rw [h, Equiv.symm_apply_apply]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Rename every row index and every observed next state of a sample array. -/
def relabelSamples (e : σ ≃ τ) (N : ℕ) (data : Samples σ Action N) : Samples τ Action N :=
  fun i ↦ e (data ((e.symm i.1.1, i.1.2), i.2))

/-- The sampling law of the relabeled MDP is the image of the original sampling law. -/
theorem samplingLaw_relabelStates (M : DiscountedMDP σ Action) (e : σ ≃ τ) (N : ℕ) :
    samplingLaw (M.relabelStates e) N = (samplingLaw M N).map (relabelSamples e N) := by
  let eα : (σ × Action) × Fin N ≃ (τ × Action) × Fin N :=
    (e.prodCongr (Equiv.refl Action)).prodCongr (Equiv.refl (Fin N))
  let eβ : σ ≃ᵐ τ :=
    { toEquiv := e, measurable_toFun := measurable_from_top,
      measurable_invFun := measurable_from_top }
  have hm : ∀ i : (σ × Action) × Fin N, MeasurePreserving eβ
      ((M.transition i.1.1 i.1.2).rowMeasure)
      (((M.relabelStates e).transition (eα i).1.1 (eα i).1.2).rowMeasure) := by
    intro i
    refine ⟨eβ.measurable, ?_⟩
    change _ = ((M.transition (e.symm (e i.1.1)) i.1.2).relabel e).rowMeasure
    rw [Equiv.symm_apply_apply, rowMeasure_relabel]
    rfl
  have h := (measurePreserving_arrowCongr'
    (fun i : (σ × Action) × Fin N ↦ (M.transition i.1.1 i.1.2).rowMeasure)
    (fun i : (τ × Action) × Fin N ↦ ((M.relabelStates e).transition i.1.1 i.1.2).rowMeasure)
    eα eβ hm).map_eq
  unfold samplingLaw
  rw [← h]
  rfl

/-- Event probabilities under the relabeled MDP are preimage probabilities under the
original MDP. -/
theorem samplingLaw_relabelStates_real (M : DiscountedMDP σ Action) (e : σ ≃ τ) (N : ℕ)
    (E : Set (Samples τ Action N)) :
    (samplingLaw (M.relabelStates e) N).real E =
      (samplingLaw M N).real (relabelSamples e N ⁻¹' E) := by
  have hmeas : Measurable (relabelSamples (Action := Action) e N) :=
    measurable_pi_iff.mpr fun i ↦ measurable_from_top.comp (measurable_pi_apply _)
  rw [samplingLaw_relabelStates, measureReal_def, measureReal_def,
    Measure.map_apply hmeas (Set.to_countable E).measurableSet]

end StatisticalRL.ModelBasedPolicyLearning
