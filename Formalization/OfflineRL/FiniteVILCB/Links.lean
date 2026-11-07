import Formalization.OfflineRL.FiniteVILCB.Step4
import Formalization.OfflineRL.FiniteVILCB.MeasureGlue
import Formalization.OfflineRL.FiniteVILCB.RowBernstein
import Formalization.MDP.FiniteOptimal

/-!
# Links between the probabilistic events and the deterministic analysis

* on the trimming event the algorithm's Q-estimates are the ideal ones;
* the optimal state marginals form a `Flow` and are dominated by `C⋆ d^b`;
* `C⋆ ≥ 1`;
* the count chain `E3 ∧ E4 ⇒ N_h(s,π⋆) ≥ K d^b_h(s,π⋆)/54` on large states;
* the number of visited triples is at most `H K / 8`.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
set_option linter.unusedSectionVars false

noncomputable local instance lkDecS : DecidableEq S := Classical.decEq S
noncomputable local instance lkDecA : DecidableEq A := Classical.decEq A

section

variable {H K : ℕ}

/-- On the trimming event the algorithm equals the ideal recursion. -/
theorem qhat_eq_ideal (cb δ : ℝ) (r : Fin H → S → A → ℝ) (aux : Fin (K / 2) → Traj S A H)
    (ι₀ : Fin (K - K / 2) → S) (α : ActTape S A H (K - K / 2)) (β : NxtTape S A H (K - K / 2))
    (hE : TrimEvent (auxTrim (iota H K δ) aux) ι₀ α β) :
    qhat cb δ r (joinData aux (buildMain ι₀ α β)) =
      qhatGen cb (iota H K δ) r (idealCount (auxTrim (iota H K δ) aux) α)
        (idealRow (auxTrim (iota H K δ) aux) α β) := by
  have hk := kept_eq_ideal (iota H K δ) aux ι₀ α β hE
  have hc : keptCount (trimCount (iota H K δ) (joinData aux (buildMain ι₀ α β)))
      (joinData aux (buildMain ι₀ α β)) = idealCount (auxTrim (iota H K δ) aux) α := by
    funext h s a; exact (hk h s a).1
  have hr : (fun h s a ↦ normRow (keptNext (trimCount (iota H K δ) (joinData aux (buildMain ι₀ α β)))
      (joinData aux (buildMain ι₀ α β)) h s a)) = idealRow (auxTrim (iota H K δ) aux) α β := by
    funext h s a
    unfold idealRow
    congr 1
    funext s'
    exact (hk h s a).2 s'
  funext h s a
  unfold qhat
  simp only
  rw [hc, hr]

theorem pointMass_prob_self (a : A) : (EnvironmentStage.pointMass a).prob a = 1 := by
  simp [EnvironmentStage.pointMass]

/-- Optimal state marginals extended by zero. -/
noncomputable def dstar (E : Fin H → EnvironmentStage S A) (πs : Fin H → S → A)
    (ρ : FiniteDistribution S) (h : ℕ) (s : S) : ℝ :=
  if hh : h ≤ H then stateMarg E (detPolicy πs) ρ ⟨h, Nat.lt_succ_of_le hh⟩ s else 0

theorem dstar_flow (E : Fin H → EnvironmentStage S A) (πs : Fin H → S → A)
    (ρ : FiniteDistribution S) : Flow E πs ρ (dstar E πs ρ) where
  init s := by
    simp only [dstar, Nat.zero_le, dif_pos]
    exact stateMarg_zero E _ ρ s
  nonneg h s := by
    unfold dstar
    split_ifs
    · exact stateMarg_nonneg _ _ _ _ _
    · exact le_rfl
  step h f := by
    have h1 : ∀ s, dstar E πs ρ (h.val + 1) s = stateMarg E (detPolicy πs) ρ h.succ s := by
      intro s
      simp only [dstar, dif_pos (show h.val + 1 ≤ H from h.isLt)]
      rfl
    have h2 : ∀ s, dstar E πs ρ h.val s = stateMarg E (detPolicy πs) ρ h.castSucc s := by
      intro s
      simp only [dstar, dif_pos h.isLt.le]
      rfl
    simp_rw [h1, h2]
    rw [stateMarg_succ]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    congr 1
    have := EnvironmentStage.expectation_pointMass (πs h s)
      (fun a ↦ ((E h).transition s a).expectation f)
    simpa [detPolicy, FiniteDistribution.expectation] using this

theorem ennreal_ratio_le {a b : ℝ} {C : ℝ≥0∞} (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : C ≠ ⊤)
    (h : ENNReal.ofReal a / ENNReal.ofReal b ≤ C) : a ≤ C.toReal * b := by
  rcases eq_or_lt_of_le hb with hb0 | hb0
  · subst hb0
    rcases eq_or_lt_of_le ha with ha0 | ha0
    · rw [← ha0]; simp
    · exfalso
      rw [ENNReal.ofReal_zero, ENNReal.div_zero (by simpa using ha0)] at h
      exact hC (top_le_iff.mp h)
  · rw [← ENNReal.ofReal_div_of_pos hb0, ENNReal.ofReal_le_iff_le_toReal hC,
      div_le_iff₀ hb0] at h
    exact h

theorem occ_le_conc (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
    (ρb ρ : FiniteDistribution S) (πs : Fin H → S → A) (h : Fin H) (s : S) (a : A) :
    ENNReal.ofReal (occupancy E (detPolicy πs) ρ h s a) /
      ENNReal.ofReal (occupancy E πb ρb h s a) ≤ concentrability E πb ρb ρ πs :=
  le_iSup_of_le h (le_iSup_of_le s (le_iSup_of_le a le_rfl))

theorem occupancy_nonneg (E : Fin H → EnvironmentStage S A) (π : Fin H → StationaryPolicy S A)
    (ρ : FiniteDistribution S) (h : Fin H) (s : S) (a : A) : 0 ≤ occupancy E π ρ h s a := by
  rw [occupancy_eq]
  exact mul_nonneg (stateMarg_nonneg _ _ _ _ _) ((π h s).prob_nonneg _)

/-- `d⋆_h(s) ≤ C⋆ d^b_h(s, π⋆_h(s))`. -/
theorem dstar_le (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
    (ρb ρ : FiniteDistribution S) (πs : Fin H → S → A)
    (hC : concentrability E πb ρb ρ πs ≠ ⊤) (h : Fin H) (s : S) :
    dstar E πs ρ h.val s ≤ (concentrability E πb ρb ρ πs).toReal *
      occupancy E πb ρb h s (πs h s) := by
  have hd : dstar E πs ρ h.val s = occupancy E (detPolicy πs) ρ h s (πs h s) := by
    simp only [dstar, dif_pos h.isLt.le]
    rw [occupancy_eq]
    simp [detPolicy, pointMass_prob_self]
    rfl
  rw [hd]
  exact ennreal_ratio_le (occupancy_nonneg _ _ _ _ _ _) (occupancy_nonneg _ _ _ _ _ _) hC
    (occ_le_conc E πb ρb ρ πs h s (πs h s))

theorem stateMarg_le_one (E : Fin H → EnvironmentStage S A) (π : Fin H → StationaryPolicy S A)
    (ρ : FiniteDistribution S) (i : Fin (H + 1)) (s : S) : stateMarg E π ρ i s ≤ 1 := by
  rw [← sum_trajProb E π ρ]
  unfold stateMarg
  refine Finset.sum_le_sum fun τ _ ↦ ?_
  have := trajProb_nonneg E π ρ τ
  split_ifs <;> nlinarith

theorem prob_le_one {X : Type*} [Fintype X] (d : FiniteDistribution X) (x : X) : d.prob x ≤ 1 := by
  rw [← d.sum_prob]
  exact Finset.single_le_sum (fun y _ ↦ d.prob_nonneg y) (Finset.mem_univ x)

/-- `C⋆ ≥ 1`. -/
theorem one_le_conc (hH : 0 < H) (E : Fin H → EnvironmentStage S A)
    (πb : Fin H → StationaryPolicy S A) (ρb ρ : FiniteDistribution S) (πs : Fin H → S → A)
    (hC : concentrability E πb ρb ρ πs ≠ ⊤) : 1 ≤ (concentrability E πb ρb ρ πs).toReal := by
  set h0 : Fin H := ⟨0, hH⟩
  let a : S → ℝ := fun s ↦ occupancy E (detPolicy πs) ρ h0 s (πs h0 s)
  let b : S → ℝ := fun s ↦ occupancy E πb ρb h0 s (πs h0 s)
  have ha : ∀ s, a s = ρ.prob s := by
    intro s
    simp only [a]
    rw [occupancy_eq]
    have : h0.castSucc = 0 := rfl
    rw [this, stateMarg_zero]
    simp [detPolicy, pointMass_prob_self]
  have hb : ∀ s, b s ≤ ρb.prob s := by
    intro s
    simp only [b]
    rw [occupancy_eq]
    have : h0.castSucc = 0 := rfl
    rw [this, stateMarg_zero]
    exact mul_le_of_le_one_right (ρb.prob_nonneg _) (prob_le_one _ _)
  have hb0 : ∀ s, 0 ≤ b s := fun s ↦ occupancy_nonneg _ _ _ _ _ _
  obtain ⟨s, hs0, hsb⟩ : ∃ s, 0 < a s ∧ b s ≤ a s := by
    by_contra hno
    push_neg at hno
    have hlt : ∑ s, a s < ∑ s, b s := by
      have hex : ∃ s, 0 < a s := by
        by_contra hne
        push_neg at hne
        have : ∑ s, a s ≤ 0 := Finset.sum_nonpos fun s _ ↦ hne s
        simp only [ha, ρ.sum_prob] at this
        linarith
      obtain ⟨s0, hs0⟩ := hex
      apply Finset.sum_lt_sum
      · intro s _
        rcases eq_or_lt_of_le (show 0 ≤ a s by rw [ha]; exact ρ.prob_nonneg s) with h | h
        · rw [← h]; exact hb0 s
        · exact (hno s h).le
      · exact ⟨s0, Finset.mem_univ _, hno s0 hs0⟩
    have h1 : ∑ s, a s = 1 := by simp only [ha, ρ.sum_prob]
    have h2 : ∑ s, b s ≤ 1 := (Finset.sum_le_sum fun s _ ↦ hb s).trans ρb.sum_prob.le
    linarith
  have hratio : 1 ≤ ENNReal.ofReal (a s) / ENNReal.ofReal (b s) := by
    rcases eq_or_lt_of_le (hb0 s) with h | h
    · rw [← h, ENNReal.ofReal_zero, ENNReal.div_zero (by simpa using hs0)]
      exact le_top
    · rw [← ENNReal.ofReal_div_of_pos h, ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal ((one_le_div h).mpr hsb)
  have := hratio.trans (occ_le_conc E πb ρb ρ πs h0 s (πs h0 s))
  have h1 : (1 : ℝ≥0∞).toReal ≤ (concentrability E πb ρb ρ πs).toReal :=
    ENNReal.toReal_mono hC this
  simpa using h1

end

end StatisticalRL.FiniteVILCB
