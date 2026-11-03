import Formalization.ModelFree.TDSynchronousSampling

/-! Actual TD prefix dependence and fresh policy-row sampling.
Stored time zero is unused; the next source update is t+1 with t<T. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.TemporalDifference
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance tdCausalityStateMeasurable : MeasurableSpace State := ⊤

/-- Exactly the used sample coordinates at source times 1,…,t.
The experiment also stores time zero, but that coordinate is never observed. -/
noncomputable def tdPastIndices (T t : ℕ) : Finset (State × Fin (T + 1)) :=
  Finset.univ.filter fun i ↦ 1 ≤ i.2.val ∧ i.2.val ≤ t

noncomputable def tdPastData (T t : ℕ) (data : TDSamples State T) :
    (i : tdPastIndices (State := State) T t) → State := fun i ↦ data i.1

noncomputable def tdCompletePast (M : DiscountedMDP State Action) (T t : ℕ)
    (code : (i : tdPastIndices (State := State) T t) → State) : TDSamples State T := by
  classical
  exact fun i ↦ if h : i ∈ tdPastIndices (State := State) T t then code ⟨i,h⟩
    else Classical.choice M.state_nonempty

noncomputable def tdPastSigma (T t : ℕ) : MeasurableSpace (TDSamples State T) :=
  MeasurableSpace.comap (tdPastData (State := State) T t) inferInstance

/-- No sample at time zero or after t can affect the actual TD iterate V_t. -/
theorem tdIterate_eq_of_samples_agree (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (samples samples' : ℕ → State → State)
    (V₀ : State → ℝ) (t : ℕ)
    (h : ∀ k, 1 ≤ k → k ≤ t → ∀ s, samples k s = samples' k s) :
    tdIterate M π η samples V₀ t = tdIterate M π η samples' V₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hi := ih (fun k hk hkt ↦ h k hk (by omega))
    funext s
    simp only [tdIterate, hi, h (t + 1) (by omega) (by omega) s]

theorem tdIterate_factors_past (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T)
    (V₀ : State → ℝ) (data : TDSamples State T) :
    tdIterate M π η (tdSamplesExtend M T data) V₀ t =
      tdIterate M π η (tdSamplesExtend M T (tdCompletePast M T t (tdPastData T t data))) V₀ t := by
  apply tdIterate_eq_of_samples_agree
  intro k hk hkt s
  have hkT : k < T + 1 := by omega
  have hmem : (s, (⟨k,hkT⟩ : Fin (T + 1))) ∈ tdPastIndices (State := State) T t := by
    simp only [tdPastIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hk,hkt⟩
  simp only [tdSamplesExtend, dif_pos hkT, tdCompletePast, dif_pos hmem, tdPastData]

/-- The actual old iterate is measurable in precisely the used prefix. -/
theorem tdIterate_measurable_past (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ) :
    Measurable[tdPastSigma T t] (fun data : TDSamples State T ↦
      tdIterate M π η (tdSamplesExtend M T data) V₀ t) := by
  let F := fun code ↦ tdIterate M π η (tdSamplesExtend M T (tdCompletePast M T t code)) V₀ t
  have hF : Measurable F := measurable_of_countable _
  have hP : Measurable[tdPastSigma T t] (tdPastData (State := State) T t) := comap_measurable _
  have he : F ∘ tdPastData T t = fun data : TDSamples State T ↦
      tdIterate M π η (tdSamplesExtend M T data) V₀ t := by
    funext data
    exact (tdIterate_factors_past M π η T t ht V₀ data).symm
  rw [← he]
  exact hF.comp hP

/-- The entire next source-time layer, not only one selected row. -/
noncomputable def tdLayerIndices (T t : ℕ) : Finset (State × Fin (T + 1)) :=
  Finset.univ.filter fun i ↦ i.2.val = t + 1

noncomputable def tdLayerData (T t : ℕ) (data : TDSamples State T) :
    (i : tdLayerIndices (State := State) T t) → State := fun i ↦ data i.1

theorem tdPast_disjoint_layer (T t : ℕ) :
    Disjoint (tdPastIndices (State := State) T t) (tdLayerIndices (State := State) T t) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hi' := (Finset.mem_filter.mp hi).2
  have hj' := (Finset.mem_filter.mp hj).2
  omega

theorem tdPast_indep_layer (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (T t : ℕ) :
    IndepFun (tdPastData (State := State) T t) (tdLayerData (State := State) T t) (tdSamplingLaw M π T) := by
  exact iIndepFun.indepFun_finset _ _ (tdPast_disjoint_layer T t)
    (tdSamplingLaw_independent M π T) (fun i ↦ measurable_pi_apply i)

/-- The next policy-row draw has the actual true policy transition law. -/
theorem tdFresh_marginal (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (T t : ℕ) (ht : t < T) (s : State) :
    (tdSamplingLaw M π T).map (fun data ↦ data (s, (⟨t + 1, by omega⟩ : Fin (T + 1)))) =
      (M.policyTransition π s).rowMeasure := tdSamplingLaw_marginal M π T s _

/-- Freshness follows from the actual independent product law and disjoint
source-time blocks; it is not an assumption on a data-selected iterate. -/
theorem tdPast_indep_fresh (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (T t : ℕ) (ht : t < T) (s : State) :
    IndepFun (tdPastData (State := State) T t)
      (fun data : TDSamples State T ↦ data (s, (⟨t + 1, by omega⟩ : Fin (T + 1)))) (tdSamplingLaw M π T) := by
  let getFresh : ((i : tdLayerIndices (State := State) T t) → State) → State :=
    fun code ↦ code ⟨(s, (⟨t + 1, by omega⟩ : Fin (T + 1))), by simp [tdLayerIndices]⟩
  have hm : Measurable getFresh := measurable_of_countable _
  exact (tdPast_indep_layer M π T t).comp measurable_id hm

theorem tdIterate_indep_fresh (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T t : ℕ) (ht : t < T)
    (V₀ : State → ℝ) (s : State) :
    IndepFun (fun data : TDSamples State T ↦ tdIterate M π η (tdSamplesExtend M T data) V₀ t)
      (fun data : TDSamples State T ↦ data (s, (⟨t + 1, by omega⟩ : Fin (T + 1)))) (tdSamplingLaw M π T) := by
  let F := fun code ↦ tdIterate M π η (tdSamplesExtend M T (tdCompletePast M T t code)) V₀ t
  have hm : Measurable F := measurable_of_countable _
  have hp := (tdPast_indep_fresh M π T t ht s).comp hm measurable_id
  have he : F ∘ tdPastData T t = fun data : TDSamples State T ↦
      tdIterate M π η (tdSamplesExtend M T data) V₀ t := by
    funext data
    exact (tdIterate_factors_past M π η T t ht.le V₀ data).symm
  rw [he] at hp
  exact hp

end StatisticalRL.TemporalDifference
