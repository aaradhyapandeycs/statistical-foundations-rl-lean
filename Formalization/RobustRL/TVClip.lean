import Mathlib

/-! TV proof source helper for the robust-RL dual-form lemma.

This file formalizes only the source's clipped-vector operation and elementary
finite-range facts. It does not assert the TV or chi-squared strong-duality
identities, which depend on the substantive cited optimization theorem. -/

namespace StatisticalRL.RobustRL.TVProof.Clip

variable {State : Type*}

/-- The source clipping operation `[V]_α`: cap coordinates strictly above α. -/
noncomputable def clipAbove (V : State → ℝ) (α : ℝ) : State → ℝ :=
  fun s ↦ if V s > α then α else V s

theorem clipAbove_eq_min (V : State → ℝ) (α : ℝ) (s : State) :
    clipAbove V α s = min (V s) α := by
  by_cases h : V s > α
  · simp [clipAbove, h, min_eq_right (le_of_lt h)]
  · have h' : V s ≤ α := le_of_not_gt h
    simp [clipAbove, h, min_eq_left h']

theorem clipAbove_le_value (V : State → ℝ) (α : ℝ) (s : State) :
    clipAbove V α s ≤ V s := by
  rw [clipAbove_eq_min]
  exact min_le_left _ _

theorem clipAbove_le_cap (V : State → ℝ) (α : ℝ) (s : State) :
    clipAbove V α s ≤ α := by
  rw [clipAbove_eq_min]
  exact min_le_right _ _

theorem clipAbove_eq_value_of_le (V : State → ℝ) (α : ℝ) (s : State)
    (h : V s ≤ α) : clipAbove V α s = V s := by
  rw [clipAbove_eq_min]
  exact min_eq_left h

theorem clipAbove_eq_cap_of_le (V : State → ℝ) (α : ℝ) (s : State)
    (h : α ≤ V s) : clipAbove V α s = α := by
  rw [clipAbove_eq_min]
  exact min_eq_right h

/-- If `vmin` is the attained minimum of `V` and α lies above it, then
clipping preserves that minimum. These hypotheses are the source finite-min
facts, separated so no optimizer or duality premise is smuggled in. -/
theorem clipAbove_minimum
    (V : State → ℝ) (α vmin : ℝ)
    (hlower : ∀ s, vmin ≤ V s)
    (hattained : ∃ s, V s = vmin)
    (hα : vmin ≤ α) :
    (∀ s, vmin ≤ clipAbove V α s) ∧
      ∃ s, clipAbove V α s = vmin := by
  constructor
  · intro s
    rw [clipAbove_eq_min]
    exact le_min (hlower s) hα
  · obtain ⟨s, hs⟩ := hattained
    refine ⟨s, ?_⟩
    rw [clipAbove_eq_min, hs]
    exact min_eq_left hα

end StatisticalRL.RobustRL.TVProof.Clip
