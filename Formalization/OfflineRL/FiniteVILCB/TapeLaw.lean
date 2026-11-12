import Formalization.OfflineRL.FiniteVILCB.TapeDefinitions
import Formalization.OfflineRL.StackProjection
import Formalization.Probability.FiniteDistributionBridge
import Formalization.Probability.EmpiricalRow
import Formalization.Generative.FiniteHorizonGenerativeSampling

/-!
# Tape representation of iid trajectories (Lemma T)

`n` main trajectories built from independent initial states, action tapes (cell `(h,s,j)` drawn
from `π_h(·|s)`) and next-state tapes (cell `((h,s,a),i)` drawn from `P_h(·|s,a)`) have exactly the
law of `n` iid trajectories of `eq:finite-batch-size-def` (`offlineRL.tex:2955–2961`).

Proof: the preimage of a dataset `x` under the build map is a product of cylinders whose cells are
distinct (visit ranks are injective), so its mass is the product of the cell masses, which
regroups into the trajectory product.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A]
set_option linter.unusedSectionVars false

noncomputable local instance tapeDecS : DecidableEq S := Classical.decEq S
noncomputable local instance tapeDecA : DecidableEq A := Classical.decEq A
local instance tapeMS : MeasurableSpace S := ⊤
local instance tapeMA : MeasurableSpace A := ⊤
local instance tapeMT (H : ℕ) : MeasurableSpace (Traj S A H) := ⊤

theorem rowMeasure_singleton {X : Type*} [Fintype X] (d : FiniteDistribution X) (x : X) :
    d.rowMeasure {x} = ENNReal.ofReal (d.prob x) :=
  FiniteDistribution.rowMeasure_singleton d x

/-- Mass of a cylinder fixing the coordinates along an injective index map. -/
theorem pi_cylinder {ι J β : Type*} [Fintype ι] [Fintype J] [MeasurableSpace β]
    [MeasurableSingletonClass β] (ν : ι → Measure β) [∀ i, IsProbabilityMeasure (ν i)]
    (g : J → ι) (hg : Function.Injective g) (w : J → β) :
    Measure.pi ν {ω | ∀ j, ω (g j) = w j} = ∏ j, ν (g j) {w j} := by
  have hmeas : Measurable (fun ω : ι → β ↦ fun j ↦ ω (g j)) :=
    measurable_pi_lambda _ fun j ↦ measurable_pi_apply (g j)
  have hset : {ω : ι → β | ∀ j, ω (g j) = w j} = (fun ω : ι → β ↦ fun j ↦ ω (g j)) ⁻¹' {w} := by
    ext ω
    simp [funext_iff]
  rw [hset, ← Measure.map_apply hmeas (measurableSet_singleton w),
    OfflineRL.StackProjection.pi_map_comp_injective ν g hg, ← Set.univ_pi_singleton w, Measure.pi_pi]

/-- Two indices with equal labels and equal visit ranks coincide. -/
theorem rankFin_injective {n : ℕ} {γ : Type*} (f : Fin n → γ) {k k' : Fin n} (hf : f k = f k')
    (hr : rankFin (fun j ↦ f j = f k) k = rankFin (fun j ↦ f j = f k') k') : k = k' := by
  classical
  have key : ∀ k k' : Fin n, f k = f k' → k < k' →
      (rankFin (fun j ↦ f j = f k) k).val < (rankFin (fun j ↦ f j = f k') k').val := by
    intro k k' hf hlt
    simp only [rankFin]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨k, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hlt, hf⟩
      · simp
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact ⟨hj.1.trans hlt, hj.2.trans hf⟩
  rcases lt_trichotomy k k' with h | h | h
  · exact absurd (congrArg Fin.val hr) (ne_of_lt (key k k' hf h))
  · exact h
  · exact absurd (congrArg Fin.val hr) (ne_of_gt (key k' k hf.symm h))

section Build

variable {H n : ℕ}

/-- Action-tape cell read by main trajectory `k` at stage `h` when the dataset is `x`. -/
noncomputable def actCell (x : Fin n → Traj S A H) (hk : Fin H × Fin n) : Fin H × S × Fin n :=
  (hk.1, (x hk.2).1 hk.1.castSucc,
    rankFin (fun k' ↦ (x k').1 hk.1.castSucc = (x hk.2).1 hk.1.castSucc) hk.2)

/-- Next-state-tape cell read by main trajectory `k` at stage `h` when the dataset is `x`. -/
noncomputable def nxtCell (x : Fin n → Traj S A H) (hk : Fin H × Fin n) :
    FiniteHorizonGenerative.SampleIndex S A H n :=
  ((hk.1, (x hk.2).1 hk.1.castSucc, (x hk.2).2 hk.1),
    rankFin (fun k' ↦ ((x k').1 hk.1.castSucc, (x k').2 hk.1) =
      ((x hk.2).1 hk.1.castSucc, (x hk.2).2 hk.1)) hk.2)

theorem actCell_injective (x : Fin n → Traj S A H) : Function.Injective (actCell x) := by
  rintro ⟨h, k⟩ ⟨h', k'⟩ he
  simp only [actCell, Prod.mk.injEq] at he
  obtain ⟨rfl, hs, hr⟩ := he
  have := rankFin_injective (fun k ↦ (x k).1 h.castSucc) hs hr
  rw [this]

theorem nxtCell_injective (x : Fin n → Traj S A H) : Function.Injective (nxtCell x) := by
  rintro ⟨h, k⟩ ⟨h', k'⟩ he
  have he1 := congrArg Prod.fst he
  have hr := congrArg Prod.snd he
  simp only [nxtCell] at he1 hr
  simp only [Prod.mk.injEq] at he1
  obtain ⟨rfl, hs, ha⟩ := he1
  have := rankFin_injective (fun k ↦ ((x k).1 h.castSucc, (x k).2 h))
    (by simp only [hs, ha]) hr
  rw [this]

theorem stateVec_succ (ι₀ : Fin n → S) (α : ActTape S A H n) (β : NxtTape S A H n) (h : Fin H) :
    stateVec ι₀ α β (h.val + 1) = nxtVec α β h (stateVec ι₀ α β h.val) := by
  rw [stateVec, dif_pos h.isLt]

/-- The build map hits a dataset exactly on the product of the cell cylinders. -/
theorem buildMain_eq_iff (ι₀ : Fin n → S) (α : ActTape S A H n) (β : NxtTape S A H n)
    (x : Fin n → Traj S A H) :
    buildMain ι₀ α β = x ↔ (∀ k, ι₀ k = (x k).1 0) ∧
      (∀ hk, α (actCell x hk) = (x hk.2).2 hk.1) ∧
      (∀ hk, β (nxtCell x hk) = (x hk.2).1 hk.1.succ) := by
  constructor
  · intro hb
    have hs : ∀ i : Fin (H + 1), stateVec ι₀ α β i.val = fun k ↦ (x k).1 i := by
      intro i
      funext k
      have := congrArg (fun y ↦ (y k).1 i) hb
      simpa [buildMain] using this
    have ha : ∀ h : Fin H, actVec α h (stateVec ι₀ α β h.val) = fun k ↦ (x k).2 h := by
      intro h
      funext k
      have := congrArg (fun y ↦ (y k).2 h) hb
      simpa [buildMain] using this
    refine ⟨fun k ↦ ?_, fun ⟨h, k⟩ ↦ ?_, fun ⟨h, k⟩ ↦ ?_⟩
    · have := congrFun (hs 0) k
      simpa [stateVec] using this
    · have := congrFun (ha h) k
      have hsc : stateVec ι₀ α β h.val = fun k ↦ (x k).1 h.castSucc := by simpa using hs h.castSucc
      rw [hsc] at this
      simpa [actVec, actCell] using this
    · have h1 := congrFun (hs h.succ) k
      simp only [Fin.val_succ] at h1
      have hsc : stateVec ι₀ α β h.val = fun k ↦ (x k).1 h.castSucc := by simpa using hs h.castSucc
      rw [stateVec_succ, hsc] at h1
      have h2 := ha h
      rw [hsc] at h2
      simp only [nxtVec] at h1
      rw [h2] at h1
      simpa [nxtCell] using h1
  · rintro ⟨hι, hα, hβ⟩
    have hs : ∀ i : ℕ, (hi : i < H + 1) → stateVec ι₀ α β i = fun k ↦ (x k).1 ⟨i, hi⟩ := by
      intro i
      induction i with
      | zero =>
        intro _
        funext k
        simpa [stateVec] using hι k
      | succ i ih =>
        intro hi
        have hiH : i < H := by omega
        have := stateVec_succ ι₀ α β ⟨i, hiH⟩
        simp only at this
        rw [this, ih (by omega)]
        have ha : actVec α ⟨i, hiH⟩ (fun k ↦ (x k).1 ⟨i, by omega⟩) = fun k ↦ (x k).2 ⟨i, hiH⟩ := by
          funext k
          have := hα (⟨i, hiH⟩, k)
          simpa [actVec, actCell] using this
        funext k
        have := hβ (⟨i, hiH⟩, k)
        simp only [nxtVec]
        rw [ha]
        simpa [nxtCell] using this
    funext k
    refine Prod.ext ?_ ?_
    · funext i
      simp [buildMain, hs i.val i.isLt]
    · funext h
      simp only [buildMain]
      rw [hs h.val (by omega)]
      have := hα (h, k)
      simpa [actVec, actCell] using this

end Build

section Law

variable {H n : ℕ}

/-- Law of the initial states of the main trajectories. -/
noncomputable def initMeasure (ρ : FiniteDistribution S) (n : ℕ) : Measure (Fin n → S) :=
  Measure.pi fun _ : Fin n ↦ ρ.rowMeasure

/-- Law of the action tapes. -/
noncomputable def actMeasure (π : Fin H → StationaryPolicy S A) (n : ℕ) :
    Measure (ActTape S A H n) :=
  Measure.pi fun c : Fin H × S × Fin n ↦ (π c.1 c.2.1).rowMeasure

instance initMeasure_prob (ρ : FiniteDistribution S) (n : ℕ) :
    IsProbabilityMeasure (initMeasure ρ n) := by unfold initMeasure; infer_instance

instance actMeasure_prob (π : Fin H → StationaryPolicy S A) (n : ℕ) :
    IsProbabilityMeasure (actMeasure π n) := by unfold actMeasure; infer_instance

/-- The tape law for the main half. -/
noncomputable def tapeMeasure (E : Fin H → EnvironmentStage S A) (π : Fin H → StationaryPolicy S A)
    (ρ : FiniteDistribution S) (n : ℕ) :
    Measure ((Fin n → S) × ActTape S A H n × NxtTape S A H n) :=
  (initMeasure ρ n).prod ((actMeasure π n).prod (FiniteHorizonGenerative.samplingLaw E n))

instance tapeMeasure_prob (E : Fin H → EnvironmentStage S A) (π : Fin H → StationaryPolicy S A)
    (ρ : FiniteDistribution S) (n : ℕ) : IsProbabilityMeasure (tapeMeasure E π ρ n) := by
  unfold tapeMeasure; infer_instance

theorem trajMeasure_singleton (E : Fin H → EnvironmentStage S A) (π : Fin H → StationaryPolicy S A)
    (ρ : FiniteDistribution S) (τ : Traj S A H) :
    trajMeasure E π ρ {τ} = ENNReal.ofReal (trajProb E π ρ τ) := by
  unfold trajMeasure
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single τ]
  · rw [Measure.dirac_apply' _ (MeasurableSpace.measurableSet_top)]
    simp
  · intro τ' _ hne
    rw [Measure.dirac_apply' _ (MeasurableSpace.measurableSet_top)]
    simp [Set.mem_singleton_iff, hne]
  · simp

instance trajMeasure_finite (E : Fin H → EnvironmentStage S A)
    (π : Fin H → StationaryPolicy S A) (ρ : FiniteDistribution S) :
    IsFiniteMeasure (trajMeasure E π ρ) := by
  constructor
  unfold trajMeasure
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  exact ENNReal.sum_lt_top.mpr fun τ _ ↦ by simp

theorem trajProb_nonneg (E : Fin H → EnvironmentStage S A) (π : Fin H → StationaryPolicy S A)
    (ρ : FiniteDistribution S) (τ : Traj S A H) : 0 ≤ trajProb E π ρ τ :=
  mul_nonneg (ρ.prob_nonneg _) (Finset.prod_nonneg fun h _ ↦
    mul_nonneg ((π h _).prob_nonneg _) (((E h).transition _ _).prob_nonneg _))

/-- **Lemma T.** The main trajectories built from tapes are iid with the trajectory law. -/
theorem tapeMeasure_map_buildMain (E : Fin H → EnvironmentStage S A)
    (π : Fin H → StationaryPolicy S A) (ρ : FiniteDistribution S) (n : ℕ) :
    (tapeMeasure E π ρ n).map (fun t ↦ buildMain t.1 t.2.1 t.2.2) =
      Measure.pi (fun _ : Fin n ↦ trajMeasure E π ρ) := by
  apply Measure.ext_of_singleton
  intro x
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton x)]
  have hpre : (fun t : (Fin n → S) × ActTape S A H n × NxtTape S A H n ↦
      buildMain t.1 t.2.1 t.2.2) ⁻¹' {x} =
      {ι₀ : Fin n → S | ∀ k, ι₀ (id k) = (x k).1 0} ×ˢ
        ({α : ActTape S A H n | ∀ hk, α (actCell x hk) = (x hk.2).2 hk.1} ×ˢ
          {β : NxtTape S A H n | ∀ hk, β (nxtCell x hk) = (x hk.2).1 hk.1.succ}) := by
    ext t
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_prod, Set.mem_setOf_eq, id]
    exact buildMain_eq_iff t.1 t.2.1 t.2.2 x
  rw [hpre, tapeMeasure, Measure.prod_prod, Measure.prod_prod, initMeasure, actMeasure,
    FiniteHorizonGenerative.samplingLaw,
    pi_cylinder _ id Function.injective_id, pi_cylinder _ _ (actCell_injective x),
    pi_cylinder _ _ (nxtCell_injective x), ← Set.univ_pi_singleton x, Measure.pi_pi]
  simp only [rowMeasure_singleton, trajMeasure_singleton, actCell, nxtCell]
  -- regroup into trajectory products
  have hρ : ∀ k, 0 ≤ ρ.prob ((x k).1 0) := fun k ↦ ρ.prob_nonneg _
  simp only [trajProb]
  rw [Fintype.prod_prod_type, Fintype.prod_prod_type, Finset.prod_comm (s := Finset.univ (α := Fin H)),
    Finset.prod_comm (s := Finset.univ (α := Fin H)), ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ ↦ ?_
  rw [ENNReal.ofReal_mul (ρ.prob_nonneg _), ENNReal.ofReal_prod_of_nonneg
    (fun h _ ↦ mul_nonneg ((π h _).prob_nonneg _) (((E h).transition _ _).prob_nonneg _)),
    ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun h _ ↦ ?_
  rw [ENNReal.ofReal_mul ((π h _).prob_nonneg _)]

end Law

end StatisticalRL.FiniteVILCB
