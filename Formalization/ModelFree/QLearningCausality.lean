import Formalization.ModelFree.QLearningSynchronousSampling

/-! Uncompiled draft: finite-prefix causality and fresh-row independence. -/
open MeasureTheory ProbabilityTheory
namespace StatisticalRL.QLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤
local instance : MeasurableSpace Action := ⊤

/-- The first t time layers, within the experiment containing exactly T layers. -/
noncomputable def qPastIndices (T t : ℕ) : Finset ((State × Action) × Fin T) :=
  Finset.univ.filter fun i ↦ i.2.val < t

noncomputable def qPastData (T t : ℕ) (data : QSamples State Action T) :
    (i : qPastIndices (State := State) (Action := Action) T t) → State :=
  fun i ↦ data i.1

noncomputable def qCompletePast (M : DiscountedMDP State Action) (T t : ℕ)
    (code : (i : qPastIndices (State := State) (Action := Action) T t) → State) :
    QSamples State Action T := by
  classical
  exact fun i ↦
    if h : i ∈ qPastIndices (State := State) (Action := Action) T t then code ⟨i,h⟩
    else Classical.choice M.state_nonempty

/-- Pathwise dependence only on draws at source update times 1,…,t. -/
theorem qIterate_eq_of_samples_agree (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (samples samples' : ℕ → State → Action → State) (Q₀ : State → Action → ℝ)
    (t : ℕ) (h : ∀ k, 1 ≤ k → k ≤ t → ∀ s a, samples k s a = samples' k s a) :
    qLearningIterate M η samples Q₀ t = qLearningIterate M η samples' Q₀ t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hi := ih (fun k hk ht ↦ h k hk (by omega))
    funext s a
    simp only [qLearningIterate, hi, h (t + 1) (by omega) (by omega) s a]

/-- Replacing all samples outside the prefix leaves Q_t unchanged. -/
theorem qIterate_factors_past (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T t : ℕ) (ht : t ≤ T) (Q₀ : State → Action → ℝ)
    (data : QSamples State Action T) :
    qLearningIterate M η (qSamplesExtend M T data) Q₀ t =
      qLearningIterate M η
        (qSamplesExtend M T (qCompletePast M T t (qPastData T t data))) Q₀ t := by
  apply qIterate_eq_of_samples_agree
  intro k hk hkt s a
  have hkT : k - 1 < T := by omega
  have he := qSamplesExtend_succ M T data (k - 1) hkT s a
  have he' := qSamplesExtend_succ M T (qCompletePast M T t (qPastData T t data))
    (k - 1) hkT s a
  have hmem : ((s,a), (⟨k-1,hkT⟩ : Fin T)) ∈
      qPastIndices (State := State) (Action := Action) T t := by
    simp [qPastIndices]
    omega
  have hc : qCompletePast M T t (qPastData T t data) ((s,a), ⟨k-1,hkT⟩) =
      data ((s,a), ⟨k-1,hkT⟩) := by
    simp [qCompletePast, qPastData, hmem]
  have heq := he.trans (hc.symm.trans he'.symm)
  simpa only [show k - 1 + 1 = k by omega] using heq

/-- Current row's single fresh coordinate. -/
noncomputable def qFreshIndices (T t : ℕ) (ht : t < T) (s : State) (a : Action) :
    Finset ((State × Action) × Fin T) := {((s,a), ⟨t,ht⟩)}

theorem qPast_disjoint_fresh (T t : ℕ) (ht : t < T) (s : State) (a : Action) :
    Disjoint (qPastIndices (State := State) (Action := Action) T t)
      (qFreshIndices T t ht s a) := by
  apply Finset.disjoint_left.mpr
  intro i hi hj
  have hv : i.2.val < t := (Finset.mem_filter.mp hi).2
  have eqi : i = ((s,a), ⟨t,ht⟩) := by simpa [qFreshIndices] using hj
  subst i
  exact (Nat.lt_irrefl t) hv

/-- The past block is independent of the actual current-row transition draw. -/
theorem qPast_indep_fresh (M : DiscountedMDP State Action) (T t : ℕ) (ht : t < T)
    (s : State) (a : Action) :
    IndepFun (qPastData (State := State) (Action := Action) T t)
      (fun data : QSamples State Action T ↦ data ((s,a), ⟨t,ht⟩)) (qSamplingLaw M T) := by
  let S := qPastIndices (State := State) (Action := Action) T t
  let U := qFreshIndices T t ht s a
  have hind := iIndepFun.indepFun_finset S U (qPast_disjoint_fresh T t ht s a)
    (qSamplingLaw_independent M T) (fun i ↦ measurable_pi_apply i)
  let getFresh : ((i : U) → State) → State := fun code ↦
    code ⟨((s,a), ⟨t,ht⟩), by simp [U, qFreshIndices]⟩
  have hm : Measurable getFresh := measurable_of_countable _
  have h := hind.comp measurable_id hm
  change IndepFun (qPastData (State := State) (Action := Action) T t)
    (fun data : QSamples State Action T ↦ data ((s,a), ⟨t,ht⟩)) (qSamplingLaw M T) at h
  exact h

/-- The iterate is independent of the fresh draw, with no data-independence premise. -/
theorem qIterate_indep_fresh (M : DiscountedMDP State Action) (η : ℕ → ℝ)
    (T t : ℕ) (ht : t < T) (Q₀ : State → Action → ℝ) (s : State) (a : Action) :
    IndepFun (fun data : QSamples State Action T ↦
      qLearningIterate M η (qSamplesExtend M T data) Q₀ t)
      (fun data : QSamples State Action T ↦ data ((s,a), ⟨t,ht⟩)) (qSamplingLaw M T) := by
  let F := fun code ↦ qLearningIterate M η
    (qSamplesExtend M T (qCompletePast M T t code)) Q₀ t
  have hm : Measurable F := measurable_of_countable _
  have h := (qPast_indep_fresh M T t ht s a).comp hm measurable_id
  have heq : F ∘ qPastData T t = fun data : QSamples State Action T ↦
      qLearningIterate M η (qSamplesExtend M T data) Q₀ t := by
    funext data
    exact (qIterate_factors_past M η T t (Nat.le_of_lt ht) Q₀ data).symm
  rw [heq] at h
  exact h

end StatisticalRL.QLearning
