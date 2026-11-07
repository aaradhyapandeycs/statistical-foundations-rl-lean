import Formalization.OfflineRL.FiniteVILCB.Links

/-!
# Count chain and number of visited triples

Plan §3.2 (count chain `N ≥ K d^b/54` on large states, from E3 and E4) and §3.3 (at most
`Σ_{h,s} m_h(s) ≤ H ⌊K/2⌋/4 ≤ HK/8` visited triples).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
set_option linter.unusedSectionVars false

noncomputable local instance lk2DecS : DecidableEq S := Classical.decEq S
noncomputable local instance lk2DecA : DecidableEq A := Classical.decEq A

variable {H K : ℕ}

theorem auxTrim_eq (ι : ℝ) (aux : Fin (K / 2) → Traj S A H) (h : Fin H) (s : S) :
    auxTrim ι aux h s = trim ι (visits aux h s) := rfl

/-- **Count chain.** On E3 and E4, large states have `K d^b_h(s,π⋆) ≤ 54 N_h(s,π⋆)`. -/
theorem count_chain (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
    (ρb : FiniteDistribution S) (πs : Fin H → S → A) (ι : ℝ) (hι : 1 ≤ ι)
    (aux : Fin (K / 2) → Traj S A H) (α : ActTape S A H (K - K / 2))
    (hE3 : LowerEv E πb ρb ι aux) (hE4 : ActEv πb ι πs (auxTrim ι aux) α) (h : Fin H) (s : S)
    (hx : 288 * ι ≤ K * occupancy E πb ρb h s (πs h s)) :
    K * occupancy E πb ρb h s (πs h s) ≤ 54 * idealCount (auxTrim ι aux) α h s (πs h s) := by
  rw [occupancy_eq] at hx ⊢
  set p := stateMarg E πb ρb h.castSucc s with hp
  set q := (πb h s).prob (πs h s) with hq
  have hp0 : 0 ≤ p := stateMarg_nonneg _ _ _ _ _
  have hp1 : p ≤ 1 := stateMarg_le_one _ _ _ _ _
  have hq0 : 0 ≤ q := (πb h s).prob_nonneg _
  have hq1 : q ≤ 1 := prob_le_one _ _
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hpq : p * q ≤ 1 := by nlinarith
  have hK2 : 2 ≤ K := by
    by_contra hlt
    push_neg at hlt
    have : (K : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.mp hlt
    have : (K : ℝ) * (p * q) ≤ 1 := by nlinarith
    nlinarith
  have hna : (K : ℝ) / 3 ≤ (K / 2 : ℕ) := by
    have : K ≤ 3 * (K / 2) := by omega
    have : (K : ℝ) ≤ 3 * ((K / 2 : ℕ) : ℝ) := by exact_mod_cast this
    linarith
  set na : ℝ := ((K / 2 : ℕ) : ℝ) with hnadef
  set x := (K : ℝ) * (p * q) with hxdef
  -- μ_a = na p ≥ x/3
  have hμ : x / 3 ≤ na * p := by
    have h1 : (K : ℝ) / 3 * p ≤ na * p := mul_le_mul_of_nonneg_right hna hp0
    have h2 : x ≤ K * p := by
      rw [hxdef]
      have := mul_le_mul_of_nonneg_left hq1 (mul_nonneg hK0 hp0)
      linarith
    linarith
  have hμq : x / 3 ≤ na * p * q := by
    have h1 : (K : ℝ) / 3 * (p * q) ≤ na * (p * q) :=
      mul_le_mul_of_nonneg_right hna (mul_nonneg hp0 hq0)
    rw [hxdef]
    nlinarith
  -- E3
  have h3 := hE3 h s (by linarith)
  set X := visits aux h s with hX
  have hX16 : 16 * ι < X := by
    have : na * p / 2 ≤ X := h3
    linarith
  have hm : auxTrim ι aux h s = X / 4 := by
    rw [auxTrim_eq, trim, if_pos hX16]
  have hmX : (X : ℝ) / 4 - 1 ≤ ((X / 4 : ℕ) : ℝ) := by
    have : X ≤ 4 * (X / 4) + 3 := by omega
    have : (X : ℝ) ≤ 4 * ((X / 4 : ℕ) : ℝ) + 3 := by exact_mod_cast this
    linarith
  -- m q ≥ x/24 - 1 ≥ 8ι
  have hmq : x / 24 - 1 ≤ ((auxTrim ι aux h s : ℕ) : ℝ) * q := by
    rw [hm]
    have h1 : ((X : ℝ) / 4 - 1) * q ≤ ((X / 4 : ℕ) : ℝ) * q := mul_le_mul_of_nonneg_right hmX hq0
    have h2 : (na * p / 8 - 1) * q ≤ ((X : ℝ) / 4 - 1) * q := by
      apply mul_le_mul_of_nonneg_right _ hq0
      linarith [show na * p / 2 ≤ X from h3]
    have h3' : x / 24 - 1 ≤ (na * p / 8 - 1) * q := by nlinarith
    linarith
  have h4 := hE4 h s (by linarith)
  linarith

theorem trim_le (ι : ℝ) (X : ℕ) : (trim ι X : ℝ) ≤ X / 4 := by
  unfold trim
  split_ifs
  · exact Nat.cast_div_le
  · simp only [Nat.cast_zero]; positivity

theorem sum_visits (aux : Fin (K / 2) → Traj S A H) (h : Fin H) :
    ∑ s, visits aux h s = K / 2 := by
  unfold visits
  rw [← Finset.card_eq_sum_card_fiberwise (f := fun i ↦ (aux i).1 h.castSucc)
    (fun _ _ ↦ Finset.mem_univ _)]
  simp

theorem sum_idealCount_le (m : Fin H → S → ℕ) (α : ActTape S A H (K - K / 2)) (h : Fin H) (s : S) :
    ∑ a, idealCount m α h s a ≤ m h s := by
  unfold idealCount
  have : ∑ a, (Finset.univ.filter (fun j : Fin (K - K / 2) ↦ j.val < m h s ∧ α (h, s, j) = a)).card
      = (Finset.univ.filter (fun j : Fin (K - K / 2) ↦ j.val < m h s)).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun j ↦ α (h, s, j)) (t := Finset.univ)
      (fun _ _ ↦ Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.filter_filter]
  rw [this]
  calc (Finset.univ.filter (fun j : Fin (K - K / 2) ↦ j.val < m h s)).card
      ≤ (Finset.range (m h s)).card := by
        rw [← Finset.card_map Fin.valEmbedding]
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Fin.valEmbedding_apply] at hi
        obtain ⟨j, hj, rfl⟩ := hi
        exact Finset.mem_range.mpr hj
    _ = m h s := Finset.card_range _

/-- At most `H K / 8` visited triples. -/
theorem visited_card_le (ι : ℝ) (aux : Fin (K / 2) → Traj S A H) (α : ActTape S A H (K - K / 2)) :
    ((visited (auxTrim ι aux) α).card : ℝ) ≤ H * K / 8 := by
  set m := auxTrim ι aux
  have h1 : (visited m α).card ≤ ∑ c : Fin H × S × A, idealCount m α c.1 c.2.1 c.2.2 := by
    unfold visited
    rw [Finset.card_filter]
    exact Finset.sum_le_sum fun c _ ↦ by split_ifs with hc <;> omega
  have h2 : ∑ c : Fin H × S × A, idealCount m α c.1 c.2.1 c.2.2 ≤ ∑ h : Fin H, ∑ s, m h s := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun h _ ↦ ?_
    rw [Fintype.sum_prod_type]
    exact Finset.sum_le_sum fun s _ ↦ sum_idealCount_le m α h s
  have h3 : ∀ h : Fin H, (∑ s, (m h s : ℝ)) ≤ ((K / 2 : ℕ) : ℝ) / 4 := by
    intro h
    calc ∑ s, (m h s : ℝ) ≤ ∑ s, (visits aux h s : ℝ) / 4 :=
          Finset.sum_le_sum fun s _ ↦ by rw [show m h s = trim ι (visits aux h s) from rfl]; exact trim_le ι _
      _ = ((∑ s, visits aux h s : ℕ) : ℝ) / 4 := by push_cast; rw [Finset.sum_div]
      _ = ((K / 2 : ℕ) : ℝ) / 4 := by rw [sum_visits]
  have h4 : ((K / 2 : ℕ) : ℝ) ≤ K / 2 := Nat.cast_div_le
  calc ((visited m α).card : ℝ) ≤ ((∑ h : Fin H, ∑ s, m h s : ℕ) : ℝ) := by
        exact_mod_cast h1.trans h2
    _ = ∑ h : Fin H, ∑ s, (m h s : ℝ) := by push_cast; rfl
    _ ≤ ∑ _h : Fin H, ((K / 2 : ℕ) : ℝ) / 4 := Finset.sum_le_sum fun h _ ↦ h3 h
    _ = H * (((K / 2 : ℕ) : ℝ) / 4) := by simp
    _ ≤ H * K / 8 := by
        have : (0 : ℝ) ≤ H := Nat.cast_nonneg _
        nlinarith

end StatisticalRL.FiniteVILCB
