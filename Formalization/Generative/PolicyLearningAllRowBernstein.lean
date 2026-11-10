import Formalization.Generative.PolicyLearningLeaveOneOutBernstein
import Formalization.Generative.PolicyLearningAbsorbingGrid

import Formalization.Generative.ModelBasedDefinitions
/-! The source simultaneous all-row Bernstein event for a fixed parameter grid.
No independence of the families from the full empirical matrix is assumed. -/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.ModelBasedPolicyLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance allRowStateMeasurable : MeasurableSpace State := ⊤
noncomputable local instance allRowStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance allRowActionDecidable : DecidableEq Action := Classical.decEq Action

/-- The actual fixed-grid vector written in the one-row Bernstein API. -/
noncomputable def leaveOneOutGridValue (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (x : State) (i : Fin (N+1))
    (data : Samples State Action N) : State → ℝ :=
  fixedAbsorbingValue M N hN x (absorbingGridPoint M N hN i)
    (absorbingGridPoint_bounds M N hN i).1 (absorbingGridPoint_bounds M N hN i).2 data

/-- The two independently developed representations are the same actual value. -/
theorem leaveOneOutGridValue_eq_gridValue (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (x : State) (i : Fin (N+1))
    (data : Samples State Action N) :
    leaveOneOutGridValue M N hN x i data =
      absorbingGridValue (empiricalModel M N hN data) N hN x i := by
  rfl

/-- Every actual grid value is bounded by the source horizon. -/
theorem leaveOneOutGridValue_norm_le (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (x : State) (i : Fin (N+1))
    (data : Samples State Action N) :
    ‖leaveOneOutGridValue M N hN x i data‖ ≤ 1 / (1 - M.discount) := by
  let H := stateAbsorbingModel (empiricalModel M N hN data) x
    (absorbingGridPoint M N hN i) (absorbingGridPoint_bounds M N hN i).1
    (absorbingGridPoint_bounds M N hN i).2
  have hd : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  apply (pi_norm_le_iff_of_nonneg (by positivity)).2
  intro s
  have hv := H.trajectoryExpectedValue_bounds H.optimalGreedyPolicy s
  change ‖H.trajectoryExpectedValue H.optimalGreedyPolicy s‖ ≤ 1 / (1 - M.discount)
  rw [Real.norm_eq_abs, abs_of_nonneg hv.1]
  exact hv.2

/-- The actual family cardinal is nonzero and at most the index count. -/
theorem leaveOneOutGridFamily_card_bounds (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (x : State) (data : Samples State Action N) :
    let u := absorbingGridPoint M N hN
    let hu0 := fun i ↦ (absorbingGridPoint_bounds M N hN i).1
    let hu1 := fun i ↦ (absorbingGridPoint_bounds M N hN i).2
    let family := fixedAbsorbingFamily M N hN x u hu0 hu1 (offStateData x N data)
    0 < family.card ∧ family.card ≤ N + 1 := by
  classical
  dsimp only
  constructor
  · apply Finset.card_pos.mpr
    let j : Fin (N+1) := ⟨0, Nat.zero_lt_succ N⟩
    unfold fixedAbsorbingFamily
    exact ⟨_, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
  · simpa using fixedAbsorbingFamily_card_le M N hN x (absorbingGridPoint M N hN)
      (fun i ↦ (absorbingGridPoint_bounds M N hN i).1)
      (fun i ↦ (absorbingGridPoint_bounds M N hN i).2) (offStateData x N data)

/-- The exact random-family radius is dominated by the source β radius. -/
theorem leaveOneOutGrid_radius_le (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (x : State) (a : Action) (i : Fin (N+1))
    (data : Samples State Action N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    let u := absorbingGridPoint M N hN
    let hu0 := fun j ↦ (absorbingGridPoint_bounds M N hN j).1
    let hu1 := fun j ↦ (absorbingGridPoint_bounds M N hN j).2
    let k := (fixedAbsorbingFamily M N hN x u hu0 hu1 (offStateData x N data)).card
    let η := δ / (2 * Fintype.card State * Fintype.card Action)
    let V := leaveOneOutGridValue M N hN x i data
    FiniteDistribution.bernsteinRadius (M.transition x a) N k η V ≤
      Real.sqrt (leaveOneOutBeta M N δ / N) * Real.sqrt ((M.transition x a).variance V) +
        leaveOneOutBeta M N δ / (3 * N * (1 - M.discount)) := by
  classical
  letI : Nonempty State := M.state_nonempty
  letI : Nonempty Action := M.action_nonempty
  let u := absorbingGridPoint M N hN
  let hu0 := fun j ↦ (absorbingGridPoint_bounds M N hN j).1
  let hu1 := fun j ↦ (absorbingGridPoint_bounds M N hN j).2
  let k := (fixedAbsorbingFamily M N hN x u hu0 hu1 (offStateData x N data)).card
  let η : ℝ := δ / (2 * Fintype.card State * Fintype.card Action)
  let L := Real.log (4 * k / η)
  let β := leaveOneOutBeta M N δ
  let V := leaveOneOutGridValue M N hN x i data
  have hk := leaveOneOutGridFamily_card_bounds M N hN x data
  have hS : (1 : ℝ) ≤ Fintype.card State := by exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hA : (1 : ℝ) ≤ Fintype.card Action := by exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hSA : 1 ≤ (Fintype.card State : ℝ) * Fintype.card Action := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hS) (sub_nonneg.mpr hA)]
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η < 1 := by
    dsimp [η]
    apply (div_lt_iff₀ (by positivity)).2
    nlinarith
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
  have hL : 0 ≤ L := by
    apply (Real.log_pos _).le
    apply (lt_div_iff₀ hη).2
    nlinarith
  have hlog : 2 * L ≤ β :=
    absorbingGrid_bernstein_log_bound M N hN k hk.1 hk.2 δ hδ
  have hβ : 0 ≤ β := (mul_nonneg (by norm_num) hL).trans hlog
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : 0 < 1 - M.discount := sub_pos.mpr M.discount_lt_one
  have hnorm : ‖V‖ ≤ 1 / (1 - M.discount) := leaveOneOutGridValue_norm_le M N hN x i data
  change FiniteDistribution.bernsteinRadius (M.transition x a) N k η V ≤
    Real.sqrt (β / N) * Real.sqrt ((M.transition x a).variance V) +
      β / (3 * N * (1 - M.discount))
  rw [FiniteDistribution.bernsteinRadius_eq_source]
  have hroot : Real.sqrt (2 * L / N) ≤ Real.sqrt (β / N) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hlog hn.le)
  have hterm : Real.sqrt (2 * L / N) * Real.sqrt ((M.transition x a).variance V) ≤
      Real.sqrt (β / N) * Real.sqrt ((M.transition x a).variance V) :=
    mul_le_mul_of_nonneg_right hroot (Real.sqrt_nonneg _)
  have hprod : ‖V‖ * (2 * L) ≤ (1 / (1 - M.discount)) * β :=
    mul_le_mul hnorm hlog (by positivity) (by positivity)
  have hlin : 2 * ‖V‖ * L / (3 * N) ≤ β / (3 * N * (1 - M.discount)) := by
    have h := div_le_div_of_nonneg_right hprod (by positivity : (0:ℝ) ≤ 3 * N)
    convert h using 1 <;> field_simp
  exact add_le_add hterm hlin

/-- Source `eqn:bernstein-union`: under the actual product sampling law, a
single event controls all state-action rows and all fixed grid indices. -/
theorem leaveOneOutGrid_allRows_bernstein (M : DiscountedMDP State Action)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ / 2 < (samplingLaw M N).real {data |
      ∀ (x : State) (a : Action) (i : Fin (N+1)),
      |(empiricalRow N hN data x a).expectation (leaveOneOutGridValue M N hN x i data) -
        (M.transition x a).expectation (leaveOneOutGridValue M N hN x i data)| ≤
      Real.sqrt (leaveOneOutBeta M N δ / N) *
        Real.sqrt ((M.transition x a).variance (leaveOneOutGridValue M N hN x i data)) +
      leaveOneOutBeta M N δ / (3 * N * (1 - M.discount))} := by
  classical
  letI : Nonempty State := M.state_nonempty
  letI : Nonempty Action := M.action_nonempty
  let μ := samplingLaw M N
  let S : ℝ := Fintype.card State
  let A : ℝ := Fintype.card Action
  let η := δ / (2 * S * A)
  let u := absorbingGridPoint M N hN
  let hu0 := fun i ↦ (absorbingGridPoint_bounds M N hN i).1
  let hu1 := fun i ↦ (absorbingGridPoint_bounds M N hN i).2
  have hS : 0 < S := by dsimp [S]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hA : 0 < A := by dsimp [A]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hS1 : 1 ≤ S := by dsimp [S]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hA1 : 1 ≤ A := by dsimp [A]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hSA : 1 ≤ S * A := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hS1) (sub_nonneg.mpr hA1)]
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η < 1 := by
    dsimp [η]
    rw [div_lt_iff₀ (by positivity : 0 < 2 * S * A)]
    nlinarith
  let rowgood (x : State) (a : Action) : Set (Samples State Action N) := {data |
    ∀ i : Fin (N+1),
      |(empiricalRow N hN data x a).expectation (leaveOneOutGridValue M N hN x i data) -
        (M.transition x a).expectation (leaveOneOutGridValue M N hN x i data)| ≤
      FiniteDistribution.bernsteinRadius (M.transition x a) N
        (fixedAbsorbingFamily M N hN x u hu0 hu1 (offStateData x N data)).card η
        (leaveOneOutGridValue M N hN x i data)}
  let rowsource (x : State) (a : Action) : Set (Samples State Action N) := {data |
    ∀ i : Fin (N+1),
      |(empiricalRow N hN data x a).expectation (leaveOneOutGridValue M N hN x i data) -
        (M.transition x a).expectation (leaveOneOutGridValue M N hN x i data)| ≤
      Real.sqrt (leaveOneOutBeta M N δ / N) *
        Real.sqrt ((M.transition x a).variance (leaveOneOutGridValue M N hN x i data)) +
      leaveOneOutBeta M N δ / (3 * N * (1 - M.discount))}
  have hrow (x : State) (a : Action) : 1 - η < μ.real (rowsource x a) := by
    have hs : 1 - η < μ.real (rowgood x a) :=
      fixedAbsorbingValues_row_bernstein M N hN x a u hu0 hu1 η hη hη1
    have hsub : rowgood x a ⊆ rowsource x a := by
      intro data hd i
      exact (hd i).trans (leaveOneOutGrid_radius_le M N hN x a i data δ hδ hδ1)
    exact hs.trans_le (measureReal_mono hsub (measure_ne_top μ (rowsource x a)))
  let bad (p : State × Action) : Set (Samples State Action N) := (rowsource p.1 p.2)ᶜ
  have hbad (p : State × Action) : μ.real (bad p) < η := by
    have hc := measureReal_compl (μ := μ) ((Set.to_countable (rowsource p.1 p.2)).measurableSet)
    rw [probReal_univ] at hc
    have hs := hrow p.1 p.2
    change μ.real (rowsource p.1 p.2)ᶜ < η
    linarith
  have hbadall : μ.real (⋃ p : State × Action, bad p) < δ / 2 := by
    calc
      _ ≤ ∑ p : State × Action, μ.real (bad p) := measureReal_iUnion_fintype_le _
      _ < ∑ _p : State × Action, η :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun p _ ↦ hbad p)
      _ = δ / 2 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod, Nat.cast_mul]
        change (S * A) * η = δ / 2
        dsimp [η]
        field_simp
  let target : Set (Samples State Action N) := {data |
      ∀ (x : State) (a : Action) (i : Fin (N+1)),
      |(empiricalRow N hN data x a).expectation (leaveOneOutGridValue M N hN x i data) -
        (M.transition x a).expectation (leaveOneOutGridValue M N hN x i data)| ≤
      Real.sqrt (leaveOneOutBeta M N δ / N) *
        Real.sqrt ((M.transition x a).variance (leaveOneOutGridValue M N hN x i data)) +
      leaveOneOutBeta M N δ / (3 * N * (1 - M.discount))}
  have hsub : (⋃ p : State × Action, bad p)ᶜ ⊆ target := by
    intro data hd x a i
    have hrowgood : data ∈ rowsource x a := by
      by_contra h
      exact hd (Set.mem_iUnion.mpr ⟨(x,a), h⟩)
    exact hrowgood i
  have hmono := measureReal_mono hsub (measure_ne_top μ target)
  have hc := measureReal_compl (μ := μ) ((Set.to_countable (⋃ p : State × Action, bad p)).measurableSet)
  rw [probReal_univ] at hc
  change 1 - δ / 2 < μ.real target
  linarith

end StatisticalRL.ModelBasedPolicyLearning
