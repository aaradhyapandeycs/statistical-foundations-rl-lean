import Formalization.OfflineRL.FiniteVILCB.Definitions
import Formalization.MDP.Basic

/-!
# Basic facts about the generic backward VI-LCB recursion

Unfolding, the range bound `0 ≤ V̂_h ≤ H - h` (fact F0 of the plan), and locality: `V̂_h` depends
only on the statistics at stages `≥ h`.
-/

open scoped BigOperators

namespace StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
set_option linter.unusedSectionVars false

/-- Backward induction on stage indices. -/
theorem backward_induction {H : ℕ} {P : ℕ → Prop} (hbase : ∀ h, H ≤ h → P h)
    (hstep : ∀ h, h < H → P (h + 1) → P h) : ∀ h, P h := by
  intro h
  induction hk : H - h generalizing h with
  | zero => exact hbase h (by omega)
  | succ k ih =>
    have hh : h < H := by omega
    exact hstep h hh (ih (h + 1) (by omega))

section Gen

variable {H : ℕ} (cb ι : ℝ) (r : Fin H → S → A → ℝ) (cnt : Fin H → S → A → ℕ)
  (row : Fin H → S → A → FiniteDistribution S)

theorem vhatGen_of_lt (h : Fin H) (s : S) :
    vhatGen cb ι r cnt row h.val s = actionMaximum (qhatGen cb ι r cnt row h s) := by
  rw [vhatGen, dif_pos h.isLt]
  rfl

theorem vhatGen_of_ge {h : ℕ} (hh : H ≤ h) (s : S) : vhatGen cb ι r cnt row h s = 0 := by
  rw [vhatGen, dif_neg (by omega)]

theorem vmax_nonneg {V : S → ℝ} (hV : ∀ s, 0 ≤ V s) : 0 ≤ vmax V := by
  obtain ⟨s⟩ := (inferInstance : Nonempty S)
  exact (hV s).trans (Finset.le_sup' V (Finset.mem_univ s))

theorem le_vmax (V : S → ℝ) (s : S) : V s ≤ vmax V := Finset.le_sup' V (Finset.mem_univ s)

theorem vmax_le {V : S → ℝ} {c : ℝ} (hV : ∀ s, V s ≤ c) : vmax V ≤ c :=
  Finset.sup'_le _ _ fun s _ ↦ hV s

theorem bonus_nonneg (hcb : 0 ≤ cb) (hι : 0 ≤ ι) (n : ℕ) (q : FiniteDistribution S) {V : S → ℝ}
    (hV : ∀ s, 0 ≤ V s) : 0 ≤ bonus cb ι H n q V := by
  unfold bonus
  split_ifs
  · exact vmax_nonneg hV
  · exact le_min (le_max_of_le_left (Real.sqrt_nonneg _)) (vmax_nonneg hV)

theorem bonus_le_vmax (n : ℕ) (q : FiniteDistribution S) (V : S → ℝ) :
    bonus cb ι H n q V ≤ vmax V := by
  unfold bonus
  split_ifs
  · exact le_rfl
  · exact min_le_right _ _

theorem actionMaximum_le {f : A → ℝ} {c : ℝ} (hf : ∀ a, f a ≤ c) : actionMaximum f ≤ c :=
  Finset.sup'_le _ _ fun a _ ↦ hf a

/-- **F0.** `0 ≤ V̂_h ≤ H - h`. -/
theorem vhatGen_bounds (hcb : 0 ≤ cb) (hι : 0 ≤ ι) (hr0 : ∀ h s a, 0 ≤ r h s a)
    (hr1 : ∀ h s a, r h s a ≤ 1) :
    ∀ h s, 0 ≤ vhatGen cb ι r cnt row h s ∧ vhatGen cb ι r cnt row h s ≤ ((H - h : ℕ) : ℝ) := by
  refine backward_induction (H := H) (P := fun h ↦ ∀ s, 0 ≤ vhatGen cb ι r cnt row h s ∧
    vhatGen cb ι r cnt row h s ≤ ((H - h : ℕ) : ℝ)) ?_ ?_
  · intro h hh s
    rw [vhatGen_of_ge cb ι r cnt row hh]
    exact ⟨le_rfl, Nat.cast_nonneg _⟩
  · intro h hh ih s
    have := vhatGen_of_lt cb ι r cnt row ⟨h, hh⟩ s
    simp only at this
    rw [this]
    obtain ⟨a⟩ := (inferInstance : Nonempty A)
    constructor
    · exact le_trans (by unfold qhatGen; exact le_max_right _ _) (le_actionMaximum _ a)
    · apply actionMaximum_le
      intro a
      unfold qhatGen
      apply max_le _ (Nat.cast_nonneg _)
      have hV0 : ∀ t, 0 ≤ vhatGen cb ι r cnt row (h + 1) t := fun t ↦ (ih t).1
      have hb := bonus_nonneg (H := H) cb ι hcb hι (cnt ⟨h, hh⟩ s a) (row ⟨h, hh⟩ s a) hV0
      have hE : (row ⟨h, hh⟩ s a).expectation (vhatGen cb ι r cnt row (h + 1)) ≤
          ((H - (h + 1) : ℕ) : ℝ) := (row ⟨h, hh⟩ s a).expectation_le_const fun t ↦ (ih t).2
      have hcast : ((H - h : ℕ) : ℝ) = 1 + ((H - (h + 1) : ℕ) : ℝ) := by
        rw [show H - h = (H - (h + 1)) + 1 by omega]
        push_cast
        ring
      rw [hcast]
      linarith [hr1 ⟨h, hh⟩ s a]

/-- **Locality.** `V̂_{h₀}` depends only on the statistics at stages `≥ h₀`. -/
theorem vhatGen_congr (cnt' : Fin H → S → A → ℕ) (row' : Fin H → S → A → FiniteDistribution S)
    (h₀ : ℕ) (hagree : ∀ h : Fin H, h₀ ≤ h.val → cnt h = cnt' h ∧ row h = row' h) :
    ∀ h, h₀ ≤ h → vhatGen cb ι r cnt row h = vhatGen cb ι r cnt' row' h := by
  refine backward_induction (H := H) (P := fun h ↦ h₀ ≤ h →
    vhatGen cb ι r cnt row h = vhatGen cb ι r cnt' row' h) ?_ ?_
  · intro h hh _
    funext s
    rw [vhatGen_of_ge cb ι r cnt row hh, vhatGen_of_ge cb ι r cnt' row' hh]
  · intro h hh ih hle
    funext s
    have e1 := vhatGen_of_lt cb ι r cnt row ⟨h, hh⟩ s
    have e2 := vhatGen_of_lt cb ι r cnt' row' ⟨h, hh⟩ s
    simp only at e1 e2
    rw [e1, e2]
    obtain ⟨hc, hrw⟩ := hagree ⟨h, hh⟩ hle
    unfold qhatGen
    simp only
    rw [ih (by omega), hc, hrw]

end Gen

end StatisticalRL.FiniteVILCB
