import Mathlib

/-! TV proof list-prefix helper for the finite knapsack
threshold argument. The theorem finds the first item at which cumulative
nonnegative weight crosses a positive capacity. It does not yet connect a
sorted list of cost levels to the original `Finset` filters. -/

namespace StatisticalRL.RobustRL.TVProof.PrefixCrossing

/-- A positive capacity bounded by a finite list's total nonnegative weight
is crossed at some item. The returned prefix mass is strictly below the
capacity, and adding the crossing item's weight reaches it. -/
theorem exists_weighted_prefix_crossing {α : Type*} (w : α → ℝ) :
    ∀ (l : List α) (σ : ℝ),
      (∀ a ∈ l, 0 ≤ w a) →
      0 < σ →
      σ ≤ (l.map w).sum →
      ∃ pre a post, l = pre ++ (a :: post) ∧
        (pre.map w).sum < σ ∧ σ ≤ (pre.map w).sum + w a := by
  intro l
  induction l with
  | nil =>
      intro σ hw hσ htotal
      simp only [List.map_nil, List.sum_nil] at htotal
      linarith
  | cons a l ih =>
      intro σ hw hσ htotal
      have hwa : 0 ≤ w a := hw a (by simp)
      have htotal' : σ ≤ w a + (l.map w).sum := by
        simpa only [List.map_cons, List.sum_cons] using htotal
      by_cases hfirst : σ ≤ w a
      · refine ⟨[], a, l, by simp, ?_, ?_⟩
        · simpa using hσ
        · simpa using hfirst
      · have hwa_lt : w a < σ := lt_of_not_ge hfirst
        have hσ' : 0 < σ - w a := sub_pos.mpr hwa_lt
        have htail : σ - w a ≤ (l.map w).sum := by linarith
        obtain ⟨pre, b, post, hdecomp, hpre, hcross⟩ :=
          ih (σ - w a) (fun x hx ↦ hw x (List.mem_cons_of_mem _ hx)) hσ' htail
        refine ⟨a :: pre, b, post, ?_, ?_, ?_⟩
        · simp [hdecomp]
        · have h : w a + (pre.map w).sum < σ := by linarith
          simpa only [List.map_cons, List.sum_cons] using h
        · have h : σ ≤ w a + ((pre.map w).sum + w b) := by linarith
          simpa only [List.map_cons, List.sum_cons, add_assoc] using h

end StatisticalRL.RobustRL.TVProof.PrefixCrossing
