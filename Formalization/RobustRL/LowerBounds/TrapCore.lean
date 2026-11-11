import Formalization.RobustRL.LowerBounds.TrapInstance
import Formalization.RobustRL.LowerBounds.Ch7PrintedStatements
import Formalization.Probability.EmpiricalRow

/-!
# Horizon trap: robust values, sampling, and the DRVI failure event

For the trap `trapMDP L γ` and any trap ball family (TV or χ²) at radius
`σ ∈ [0,1]`, any `N > 0`, any `1 ≤ T ≤ L+1`, any greedy selector of the
empirical DRVI iterate `Q̂_T`, and any `ε < q^{L+1}/(1-q) - 1/2` with
`q = γ(1-σ)`: the event `∀ s, V^{⋆,σ}(s) - V^{π̂,σ}(s) ≤ ε` is a null set of the
actual product sampling law (it is contained in the event that some
generative sample differs from its deterministic nominal successor).
-/

open MeasureTheory
open scoped BigOperators

namespace StatisticalRL.RobustRL.Ch7.HorizonTrap

open StatisticalRL.EnvironmentStage

local instance trapCoreStateMeasurable (State : Type*) : MeasurableSpace State := ⊤

variable {L : ℕ} {γ : ℝ} {hγ0 : 0 ≤ γ} {hγ1 : γ < 1}

section RobustValues

variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem robustPolicyValue_le_nominal (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) (hb : ∀ p, p ∈ ball p σ) (π : StationaryPolicy State Action) (s : State) :
    robustPolicyValue ball M σ π s ≤ (withKernel M M.transition).trajectoryExpectedValue π s := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro v ⟨K, -, rfl⟩
    exact ((withKernel M K).trajectoryExpectedValue_bounds π s).1
  · exact ⟨M.transition, fun s a ↦ hb _, rfl⟩

theorem robustPolicyValue_le_horizon (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) (hb : ∀ p, p ∈ ball p σ) (π : StationaryPolicy State Action) (s : State) :
    robustPolicyValue ball M σ π s ≤ 1 / (1 - M.discount) :=
  (robustPolicyValue_le_nominal ball M σ hb π s).trans
    ((withKernel M M.transition).trajectoryExpectedValue_bounds π s).2

theorem robustPolicyValue_le_optimal (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) (hb : ∀ p, p ∈ ball p σ) (π : StationaryPolicy State Action) (s : State) :
    robustPolicyValue ball M σ π s ≤ robustOptimalValue ball M σ s := by
  apply le_csSup
  · refine ⟨1 / (1 - M.discount), ?_⟩
    rintro v ⟨π', rfl⟩
    exact robustPolicyValue_le_horizon ball M σ hb π' s
  · exact ⟨π, rfl⟩

end RobustValues

/-- Robust gap of any policy bailing at `s₀` in the trap. -/
theorem trap_robustGap (ball : RowBall (Fin (L + 3))) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hball : TrapBall ball σ) (f : Fin (L + 3) → Fin 2) (hf : f 0 = 1) :
    (γ * (1 - σ)) ^ (L + 1) / (1 - γ * (1 - σ)) - 1 / 2 ≤
      robustOptimalValue ball (trapMDP L γ hγ0 hγ1) σ 0 -
        robustPolicyValue ball (trapMDP L γ hγ0 hγ1) σ (detPolicy f) 0 := by
  set M := trapMDP L γ hγ0 hγ1
  have hupper : robustPolicyValue ball M σ (detPolicy f) 0 ≤ 1 / 2 := by
    refine (robustPolicyValue_le_nominal ball M σ hball.self_mem _ 0).trans (le_of_eq ?_)
    exact bailValue_eq (withKernel M M.transition) (fun s a ↦ rfl) (fun s a ↦ rfl) f hf
  have hlower : (γ * (1 - σ)) ^ (L + 1) / (1 - γ * (1 - σ)) ≤
      robustPolicyValue ball M σ (detPolicy fun _ ↦ 0) 0 := by
    apply le_csInf
    · exact ⟨_, M.transition, fun s a ↦ hball.self_mem _, rfl⟩
    · rintro v ⟨K, hK, rfl⟩
      exact enterValue_lower (withKernel M K) (fun s a ↦ rfl) hσ0 hσ1
        (fun s ↦ hball.pointMass_mass _ _ (hK s 0))
  have hopt := robustPolicyValue_le_optimal ball M σ hball.self_mem (detPolicy fun _ ↦ 0) 0
  linarith

/-- The empirical row of a constant sample is the point mass. -/
theorem empiricalRow_const {State : Type*} [Fintype State] (N : ℕ) (hN : 0 < N) (j : State) :
    FiniteDistribution.empiricalRow N hN (fun _ ↦ j) = pointMass j := by
  classical
  apply fd_ext
  intro x
  rw [pointMass_prob]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  by_cases h : x = j
  · subst h; simp [FiniteDistribution.empiricalRow, hN']
  · have h' : ¬ j = x := fun e ↦ h e.symm
    simp [FiniteDistribution.empiricalRow, h, h']

/-- Samples that all equal their deterministic nominal successor. -/
def goodSamples (N : ℕ) : Set (ModelBasedPolicyLearning.Samples (Fin (L + 3)) (Fin 2) N) :=
  {data | ∀ i, data i = next L i.1.1 i.1.2}

theorem rowMeasure_pointMass_compl {State : Type*} [Fintype State] (j : State) :
    (pointMass j).rowMeasure ({j}ᶜ : Set State) = 0 := by
  classical
  unfold FiniteDistribution.rowMeasure
  rw [PMF.toMeasure_apply_fintype]
  apply Finset.sum_eq_zero
  intro x _
  by_cases h : x = j
  · subst h; simp
  · rw [Set.indicator_of_mem (by simpa using h)]
    simp [FiniteDistribution.toPMF, PMF.ofFintype_apply, pointMass_prob, h]

theorem goodSamples_compl_null (N : ℕ) :
    ModelBasedPolicyLearning.samplingLaw (trapMDP L γ hγ0 hγ1) N (goodSamples N)ᶜ = 0 := by
  have hsub : (goodSamples (L := L) N)ᶜ ⊆
      ⋃ i, (fun data : ModelBasedPolicyLearning.Samples (Fin (L + 3)) (Fin 2) N ↦ data i) ⁻¹'
        ({next L i.1.1 i.1.2}ᶜ) := by
    intro data hdata
    simp only [goodSamples, Set.mem_compl_iff, Set.mem_setOf_eq, not_forall] at hdata
    obtain ⟨i, hi⟩ := hdata
    exact Set.mem_iUnion.2 ⟨i, by simpa using hi⟩
  apply measure_mono_null hsub
  apply measure_iUnion_null
  intro i
  unfold ModelBasedPolicyLearning.samplingLaw
  rw [(measurePreserving_eval
      (fun i : (Fin (L + 3) × Fin 2) × Fin N ↦
        ((trapMDP L γ hγ0 hγ1).transition i.1.1 i.1.2).rowMeasure) i).measure_preimage
      (MeasurableSet.nullMeasurableSet trivial)]
  exact rowMeasure_pointMass_compl _

/-- **Core failure.** Under the actual sampling law, the success event of the
printed DRVI clause is null, for every greedy selector, every `1 ≤ T ≤ L+1`, and
every `ε` below the trap gap. -/
theorem trap_success_null (ball : RowBall (Fin (L + 3))) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1)
    (hball : TrapBall ball σ) (N : ℕ) (hN : 0 < N) (T : ℕ) (hT1 : 1 ≤ T) (hTL : T ≤ L + 1)
    (ε : ℝ) (hε : ε < (γ * (1 - σ)) ^ (L + 1) / (1 - γ * (1 - σ)) - 1 / 2)
    (pick : ModelBasedPolicyLearning.Samples (Fin (L + 3)) (Fin 2) N → Fin (L + 3) → Fin 2)
    (hpick : ∀ data, IsGreedy
      (empiricalDRVI ball (trapMDP L γ hγ0 hγ1) σ N hN data T) (pick data)) :
    ModelBasedPolicyLearning.samplingLaw (trapMDP L γ hγ0 hγ1) N
      {data | ∀ s, robustOptimalValue ball (trapMDP L γ hγ0 hγ1) σ s -
        robustPolicyValue ball (trapMDP L γ hγ0 hγ1) σ (detPolicy (pick data)) s ≤ ε} = 0 := by
  apply measure_mono_null _ (goodSamples_compl_null (hγ0 := hγ0) (hγ1 := hγ1) N)
  intro data hdata hgood
  have hT : ∀ s a, (ModelBasedPolicyLearning.empiricalModel (trapMDP L γ hγ0 hγ1) N hN data).transition s a =
      pointMass (next L s a) := by
    intro s a
    change FiniteDistribution.empiricalRow N hN (fun i ↦ data ((s, a), i)) = _
    have : (fun i ↦ data ((s, a), i)) = fun _ ↦ next L s a := funext fun i ↦ hgood ((s, a), i)
    rw [this, empiricalRow_const]
  have hbail := drvi_greedy_bails _ hball.self_mem hT (fun s a ↦ rfl) T hT1 hTL (pick data)
    (hpick data)
  have hgap := trap_robustGap (hγ0 := hγ0) (hγ1 := hγ1) ball hσ0 hσ1 hball (pick data) hbail
  have := hdata 0
  linarith

end StatisticalRL.RobustRL.Ch7.HorizonTrap
