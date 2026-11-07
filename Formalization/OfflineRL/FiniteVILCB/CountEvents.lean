import Formalization.OfflineRL.FiniteVILCB.CountTails
import Formalization.OfflineRL.FiniteVILCB.TapeLaw
import Formalization.OfflineRL.FiniteVILCB.Occupancy
import Formalization.OfflineRL.FiniteVILCB.RowEvents

/-!
# Count events E1–E4

* E1 (aux upper): `X_a(h,s) ≤ max(2 n_a d^b_h(s), 16ι)`;
* E3 (aux lower): `n_a d^b_h(s) ≥ 8ι ⇒ X_a(h,s) ≥ n_a d^b_h(s)/2`;
* E2 (main lower, on the iid main trajectories): same with `n = K - ⌊K/2⌋`;
* E4 (action tapes, `a = π⋆_h(s)` only, for fixed trimmed counts `m ≤ n`):
  `m q ≥ 8ι ⇒ N^id_h(s,π⋆) ≥ m q/2`, `q = π^b_h(π⋆_h(s)|s)`.

Each fails with probability at most `H·S·e^{-ι}` (E1 needs `ι ≥ 1/2`).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace StatisticalRL.FiniteVILCB

open StatisticalRL.OfflineRL

variable {S A : Type*} [Fintype S] [Fintype A]
set_option linter.unusedSectionVars false

noncomputable local instance evDecS : DecidableEq S := Classical.decEq S
noncomputable local instance evDecA : DecidableEq A := Classical.decEq A
local instance evMS : MeasurableSpace S := ⊤
local instance evMA : MeasurableSpace A := ⊤
local instance evMT (H : ℕ) : MeasurableSpace (Traj S A H) := ⊤

section Traj

variable {H : ℕ} (E : Fin H → EnvironmentStage S A) (π : Fin H → StationaryPolicy S A)
  (ρ : FiniteDistribution S)

theorem trajMeasure_apply_toReal (P : Traj S A H → Prop) [DecidablePred P] :
    (trajMeasure E π ρ {τ | P τ}).toReal =
      ∑ τ, trajProb E π ρ τ * (if P τ then 1 else 0) := by
  classical
  unfold trajMeasure
  rw [Measure.coe_finset_sum, Finset.sum_apply, ENNReal.toReal_sum]
  · refine Finset.sum_congr rfl fun τ _ ↦ ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    rw [Measure.dirac_apply' _ MeasurableSpace.measurableSet_top]
    by_cases h : P τ
    · simp [h, Set.indicator, ENNReal.toReal_ofReal (trajProb_nonneg E π ρ τ)]
    · simp [h, Set.indicator]
  · intro τ _
    simp only [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

instance trajMeasure_prob : IsProbabilityMeasure (trajMeasure E π ρ) := by
  constructor
  have h := trajMeasure_apply_toReal E π ρ (fun _ ↦ True)
  simp only [Set.setOf_true, ↓reduceIte, mul_one] at h
  rw [sum_trajProb] at h
  have hfin : trajMeasure E π ρ Set.univ ≠ ⊤ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hfin, h, ENNReal.ofReal_one]

/-- The stage-`i` state law has mass `d_i(s)` at `s`. -/
theorem stageLaw_real (i : Fin (H + 1)) (s : S) :
    ((trajMeasure E π ρ).map (fun τ : Traj S A H ↦ τ.1 i)).real {s} = stateMarg E π ρ i s := by
  rw [measureReal_def, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton s)]
  have : (fun τ : Traj S A H ↦ τ.1 i) ⁻¹' {s} = {τ | τ.1 i = s} := rfl
  rw [this, trajMeasure_apply_toReal]
  unfold stateMarg
  rfl

end Traj

/-- Union bound over the `H·S` stage-state pairs. -/
theorem union_HS {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ] {H : ℕ}
    (bad : Fin H → S → Set Ω) (b : ℝ) (hb : ∀ h s, μ.real (bad h s) ≤ b) :
    μ.real (⋃ h, ⋃ s, bad h s) ≤ H * Fintype.card S * b := by
  have h1 : (⋃ h, ⋃ s, bad h s) = ⋃ c : Fin H × S, bad c.1 c.2 := by
    ext ω; simp
  rw [h1]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  refine (Finset.sum_le_sum fun c _ ↦ hb c.1 c.2).trans ?_
  simp [Finset.card_univ, Fintype.card_prod]

theorem visitCount_eq_card {Ω : Type*} {N : ℕ} (Y : Fin N → Ω → S) (x : S) (ω : Ω) :
    visitCount Y x ω = (Finset.univ.filter (fun j ↦ Y j ω = x)).card := by
  unfold visitCount
  rw [Finset.card_filter]

section Events

variable {H : ℕ} (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
  (ρb : FiniteDistribution S) (ι : ℝ)

/-- Visits of a block of trajectories to `(h,s)`. -/
noncomputable def visits {N : ℕ} (y : Fin N → Traj S A H) (h : Fin H) (s : S) : ℕ :=
  (Finset.univ.filter (fun i ↦ (y i).1 h.castSucc = s)).card

/-- Lower count event for a block of `N` trajectories (E2 for the main half, E3 for aux). -/
def LowerEv {N : ℕ} (y : Fin N → Traj S A H) : Prop :=
  ∀ h s, 8 * ι ≤ N * stateMarg E πb ρb h.castSucc s →
    N * stateMarg E πb ρb h.castSucc s / 2 ≤ visits y h s

/-- Upper count event E1. -/
def UpperEv {N : ℕ} (y : Fin N → Traj S A H) : Prop :=
  ∀ h s, (visits y h s : ℝ) ≤ max (2 * N * stateMarg E πb ρb h.castSucc s) (16 * ι)

theorem lowerEv_bad (N : ℕ) (hι : 0 ≤ ι) :
    (Measure.pi fun _ : Fin N ↦ trajMeasure E πb ρb).real {y | ¬ LowerEv E πb ρb ι y} ≤
      H * Fintype.card S * Real.exp (-ι) := by
  have hsub : {y : Fin N → Traj S A H | ¬ LowerEv E πb ρb ι y} ⊆
      ⋃ h, ⋃ s, {y | 8 * ι ≤ N * stateMarg E πb ρb h.castSucc s ∧
        (visits y h s : ℝ) < N * stateMarg E πb ρb h.castSucc s / 2} := by
    intro y hy
    simp only [LowerEv, Set.mem_setOf_eq, not_forall, not_le] at hy
    obtain ⟨h, s, h1, h2⟩ := hy
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨h, s, h1, h2⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans (union_HS _ _ _ fun h s ↦ ?_)
  haveI : IsProbabilityMeasure ((trajMeasure E πb ρb).map (fun τ : Traj S A H ↦ τ.1 h.castSucc)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  by_cases hc : 8 * ι ≤ N * stateMarg E πb ρb h.castSucc s
  · have hl := pi_count_lower (fun _ : Fin N ↦ trajMeasure E πb ρb) id Function.injective_id
      (fun τ : Traj S A H ↦ τ.1 h.castSucc) (measurable_of_countable _)
      ((trajMeasure E πb ρb).map (fun τ : Traj S A H ↦ τ.1 h.castSucc)) (fun _ ↦ rfl) s
    rw [stageLaw_real] at hl
    refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (hl.trans ?_)
    · intro y hy
      simp only [Set.mem_setOf_eq] at hy ⊢
      rw [visitCount_eq_card]
      exact hy.2
    · exact Real.exp_le_exp.mpr (by linarith)
  · have : {y : Fin N → Traj S A H | 8 * ι ≤ N * stateMarg E πb ρb h.castSucc s ∧
        (visits y h s : ℝ) < N * stateMarg E πb ρb h.castSucc s / 2} = ∅ := by
      ext y; simp [hc]
    rw [this, measureReal_empty]
    positivity

theorem upperEv_bad (N : ℕ) (hι : 1 / 2 ≤ ι) :
    (Measure.pi fun _ : Fin N ↦ trajMeasure E πb ρb).real {y | ¬ UpperEv E πb ρb ι y} ≤
      H * Fintype.card S * Real.exp (-ι) := by
  have hsub : {y : Fin N → Traj S A H | ¬ UpperEv E πb ρb ι y} ⊆
      ⋃ h, ⋃ s, {y | max (2 * N * stateMarg E πb ρb h.castSucc s) (16 * ι) <
        (visits y h s : ℝ)} := by
    intro y hy
    simp only [UpperEv, Set.mem_setOf_eq, not_forall, not_le] at hy
    obtain ⟨h, s, h1⟩ := hy
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨h, s, h1⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans (union_HS _ _ _ fun h s ↦ ?_)
  set τ := max (2 * N * stateMarg E πb ρb h.castSucc s) (16 * ι)
  haveI : IsProbabilityMeasure ((trajMeasure E πb ρb).map (fun τ : Traj S A H ↦ τ.1 h.castSucc)) :=
    Measure.isProbabilityMeasure_map (measurable_of_countable _).aemeasurable
  have hu := pi_count_upper (fun _ : Fin N ↦ trajMeasure E πb ρb) id Function.injective_id
    (fun τ : Traj S A H ↦ τ.1 h.castSucc) (measurable_of_countable _)
    ((trajMeasure E πb ρb).map (fun τ : Traj S A H ↦ τ.1 h.castSucc)) (fun _ ↦ rfl) s τ
    (le_trans (by linarith) (le_max_right _ _))
    (by rw [stageLaw_real]; nlinarith [le_max_left (2 * N * stateMarg E πb ρb h.castSucc s) (16 * ι)])
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (hu.trans ?_)
  · intro y hy
    simp only [Set.mem_setOf_eq] at hy ⊢
    rw [visitCount_eq_card]
    exact hy
  · have hτ : 16 * ι ≤ τ := le_max_right _ _
    have h1 : Real.exp (-(0.19 : ℝ) * τ) ≤ Real.exp (-(0.19 : ℝ) * (16 * ι)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have h2 : 2 * Real.exp (-(0.19 : ℝ) * (16 * ι)) ≤ Real.exp (-ι) := by
      have e : -(0.19 : ℝ) * (16 * ι) = -ι + -(2.04 * ι) := by ring
      rw [e, Real.exp_add]
      have : Real.exp (-(2.04 * ι)) ≤ 1 / 2 := by
        have hle : Real.exp (-(2.04 * ι)) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
        have he : Real.exp (-1) ≤ 1 / 2 := by
          rw [Real.exp_neg]
          rw [inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
          have := Real.add_one_le_exp (1 : ℝ)
          norm_num
          linarith
        linarith
      have hpos := Real.exp_pos (-ι)
      nlinarith
    linarith

/-- Action-tape event E4 for fixed trimmed counts. -/
def ActEv {n : ℕ} (πs : Fin H → S → A) (m : Fin H → S → ℕ) (α : ActTape S A H n) : Prop :=
  ∀ h s, 8 * ι ≤ m h s * (πb h s).prob (πs h s) →
    m h s * (πb h s).prob (πs h s) / 2 ≤ idealCount m α h s (πs h s)

theorem actEv_bad {n : ℕ} (πs : Fin H → S → A) (m : Fin H → S → ℕ) (hm : ∀ h s, m h s ≤ n)
    (hι : 0 ≤ ι) :
    (actMeasure πb n).real {α | ¬ ActEv πb ι πs m α} ≤ H * Fintype.card S * Real.exp (-ι) := by
  have hsub : {α : ActTape S A H n | ¬ ActEv πb ι πs m α} ⊆
      ⋃ h, ⋃ s, {α | 8 * ι ≤ m h s * (πb h s).prob (πs h s) ∧
        (idealCount m α h s (πs h s) : ℝ) < m h s * (πb h s).prob (πs h s) / 2} := by
    intro α hα
    simp only [ActEv, Set.mem_setOf_eq, not_forall, not_le] at hα
    obtain ⟨h, s, h1, h2⟩ := hα
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨h, s, h1, h2⟩
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans (union_HS _ _ _ fun h s ↦ ?_)
  by_cases hc : 8 * ι ≤ m h s * (πb h s).prob (πs h s)
  · have hinj : Function.Injective (fun j : Fin (m h s) ↦ (h, s, Fin.castLE (hm h s) j)) := by
      intro j j' he
      exact Fin.castLE_injective (hm h s) (congrArg (fun c ↦ c.2.2) he)
    have hl := pi_count_lower (fun c : Fin H × S × Fin n ↦ (πb c.1 c.2.1).rowMeasure)
      (fun j : Fin (m h s) ↦ (h, s, Fin.castLE (hm h s) j)) hinj id measurable_id
      (πb h s).rowMeasure (fun _ ↦ Measure.map_id) (πs h s)
    have hreal : (πb h s).rowMeasure.real {πs h s} = (πb h s).prob (πs h s) := by
      rw [measureReal_def, rowMeasure_singleton, ENNReal.toReal_ofReal ((πb h s).prob_nonneg _)]
    rw [hreal] at hl
    unfold actMeasure
    refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (hl.trans ?_)
    · intro α hα
      simp only [Set.mem_setOf_eq] at hα ⊢
      rw [visitCount_eq_card]
      have hc : idealCount m α h s (πs h s) =
          (Finset.univ.filter (fun j : Fin (m h s) ↦ id (α (h, s, Fin.castLE (hm h s) j)) =
            πs h s)).card := by
        unfold idealCount
        rw [card_fin_lt (hm h s) (fun j ↦ α (h, s, j) = πs h s)]
        rfl
      rw [← hc]
      exact hα.2
    · exact Real.exp_le_exp.mpr (by linarith)
  · have : {α : ActTape S A H n | 8 * ι ≤ m h s * (πb h s).prob (πs h s) ∧
        (idealCount m α h s (πs h s) : ℝ) < m h s * (πb h s).prob (πs h s) / 2} = ∅ := by
      ext α; simp [hc]
    rw [this, measureReal_empty]
    positivity

end Events

end StatisticalRL.FiniteVILCB
