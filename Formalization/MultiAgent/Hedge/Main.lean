import Formalization.MultiAgent.Hedge.ZeroSum
import Formalization.MultiAgent.Hedge.Statement

/-!
# Theorem 7.7 restricted: main theorem

* `gap_margProd_le_two_mul`: in a two-player game whose rewards sum to `0` on steps `1..H`, the
  product of the marginals of a joint policy `π` has `gap ≤ 2·gapJ(π)`.
* `thm7_7_restricted : Thm7_7_restricted`, with the constant `C = 20000`.
-/

open scoped BigOperators
open Finset

namespace StatisticalRL.Ch7Rest.Marl77

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.Ch7Rest.Marl76 StatisticalRL.AdaptiveKL

section TwoPlayer

variable {S H : ℕ} {A : Fin 2 → ℕ}

theorem valueJ_zero_sum (G : MarkovGame 2 S H A)
    (hzs : ∀ h, 1 ≤ h → h ≤ H → ∀ s a, G.reward 1 h s a = -G.reward 0 h s a)
    (ρ : JointPolicy 2 S A) :
    ∀ k h, 1 ≤ h → h + k ≤ H + 1 → ∀ s, valueJ G ρ 1 h k s = -valueJ G ρ 0 h k s := by
  intro k
  induction k with
  | zero => intro h _ _ s; simp [valueJ]
  | succ k ih =>
    intro h h1 hk s
    have hnext : valueJ G ρ 1 (h + 1) k = fun s' => -valueJ G ρ 0 (h + 1) k s' :=
      funext fun s' => ih (h + 1) (by omega) (by omega) s'
    simp only [valueJ]
    rw [hnext, ← sum_neg_distrib]
    refine sum_congr rfl fun a _ => ?_
    rw [hzs h h1 (by omega) s a]
    have := FiniteDistribution.expectation_mul (G.transition h s a) (-1) (valueJ G ρ 0 (h + 1) k)
    simp only [neg_one_mul] at this
    rw [this]; ring

theorem other_ne (i : Fin 2) : (if i = 0 then (1 : Fin 2) else 0) ≠ i := by
  fin_cases i <;> simp

theorem bestResponseValueJ_margProd (hA : ∀ k, 0 < A k) (G : MarkovGame 2 S H A)
    (π : JointPolicy 2 S A) (i : Fin 2) (s : Fin S) :
    bestResponseValueJ G (toJoint (margProd π)) i s = bestResponseValueJ G π i s := by
  unfold bestResponseValueJ
  refine iSup_congr fun π' => ?_
  refine valueJ_congr G _ _ i (fun h s g => deviate_sum_two hA _ _ i π' h s (fun c => ?_) g) H 1 s
  rw [margDist_toJoint]
  rfl

theorem valueJ_le_bestResponseValueJ_toJoint (G : MarkovGame 2 S H A) (σ : ProductPolicy 2 S A)
    (i : Fin 2) (s : Fin S) :
    valueJ G (toJoint σ) i 1 H s ≤ bestResponseValueJ G (toJoint σ) i s := by
  have h := valueJ_deviate_le_bestResponseValueJ G (toJoint σ) i (σ i) s
  rwa [valueJ_congr G _ _ i (deviate_toJoint_sum σ i (σ i)) H 1 s, Function.update_eq_self] at h

theorem term_le_gapJ (G : MarkovGame 2 S H A) (π : JointPolicy 2 S A) (i : Fin 2) (s : Fin S) :
    bestResponseValueJ G π i s - valueJ G π i 1 H s ≤ gapJ G π := by
  unfold gapJ
  exact le_ciSup_of_le (Set.finite_range _).bddAbove s
    (le_ciSup (f := fun i => bestResponseValueJ G π i s - valueJ G π i 1 H s)
      (Set.finite_range _).bddAbove i)

/-- CCE ⇒ NE by marginals, factor 2. -/
theorem gap_margProd_le_two_mul (hS : 0 < S) (hA : ∀ k, 0 < A k)
    (G : MarkovGame 2 S H A)
    (hzs : ∀ h, 1 ≤ h → h ≤ H → ∀ s a, G.reward 1 h s a = -G.reward 0 h s a)
    (π : JointPolicy 2 S A) : gap G (margProd π) ≤ 2 * gapJ G π := by
  rw [← gapJ_toJoint]
  haveI : Nonempty (Fin S) := ⟨⟨0, hS⟩⟩
  unfold gapJ
  refine ciSup_le fun s => ciSup_le fun i => ?_
  set j : Fin 2 := if i = 0 then 1 else 0
  have hji := other_ne i
  have hsum : ∀ ρ : JointPolicy 2 S A, valueJ G ρ i 1 H s + valueJ G ρ j 1 H s = 0 := by
    intro ρ
    have := valueJ_zero_sum G hzs ρ H 1 le_rfl (by omega) s
    fin_cases i
    · simp only [j]; simp at this ⊢; linarith
    · simp only [j]; simp at this ⊢; linarith
  have h1 := bestResponseValueJ_margProd hA G π i s
  have h2 := bestResponseValueJ_margProd hA G π j s
  have h3 := valueJ_le_bestResponseValueJ_toJoint G (margProd π) j s
  have h4 := hsum (toJoint (margProd π))
  have h5 := hsum π
  have t1 := term_le_gapJ G π i s
  have t2 := term_le_gapJ G π j s
  rw [h1]
  unfold gapJ at t1 t2
  linarith

end TwoPlayer

/-! ### The main theorem -/

theorem log_nonneg_of_sum {m S H : ℕ} {A : Fin m → ℕ} (hA : ∀ i, 1 ≤ A i) (hS : 1 ≤ S)
    (hH : 1 ≤ H) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (K : ℝ) (hK : 1 ≤ K) :
    0 ≤ (H : ℝ) ^ 4 * S * (∑ i, (A i : ℝ)) / 1 *
      Real.log (K * H * S * (∑ i, (A i : ℝ)) / δ) := by
  rcases sum_A_cases hA with h | h
  · rw [h.1]; simp
  · have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
    have hSr : (1 : ℝ) ≤ S := by exact_mod_cast hS
    refine mul_nonneg (by positivity) (Real.log_nonneg ?_)
    rw [le_div_iff₀ hδ0]
    have : (1 : ℝ) ≤ K * H * S * ∑ i, (A i : ℝ) := by
      have := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le hK hHr) hSr) h
      exact this
    linarith

theorem thm7_7_restricted : Thm7_7_restricted := by
  refine ⟨20000, by norm_num, ?_, ?_⟩
  · -- (b) general-sum CCE
    intro m S H A hS hA δ ε hδ0 hδ1 hε hεH rew hrew
    obtain ⟨al, -, hN, hprob⟩ := core_cce hS hA δ ε hδ0 hδ1 hε hεH rew hrew
    refine ⟨al.N, al.rule, al.out, ?_, hprob⟩
    have hHn : 1 ≤ H := by
      have : (0 : ℝ) < H := lt_of_lt_of_le hε hεH
      exact_mod_cast this
    have h0 := log_nonneg_of_sum hA hS hHn hδ0 hδ1 4 (by norm_num)
    rw [div_one] at h0
    have e : ∀ K : ℝ, K * (H : ℝ) ^ 4 * S * (∑ i, (A i : ℝ)) / ε ^ 2 *
        Real.log (4 * H * S * (∑ i, (A i : ℝ)) / δ) =
        K / ε ^ 2 * ((H : ℝ) ^ 4 * S * (∑ i, (A i : ℝ)) *
          Real.log (4 * H * S * (∑ i, (A i : ℝ)) / δ)) := fun K => by ring
    rw [e] at hN ⊢
    refine hN.trans (mul_le_mul_of_nonneg_right ?_ h0)
    exact div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)
  · -- (a) two-player zero-sum NE
    intro S H A hS hA δ ε hδ0 hδ1 hε hεH rew hzs
    have hHn : 1 ≤ H := by
      have : (0 : ℝ) < H := lt_of_lt_of_le hε hεH
      exact_mod_cast this
    have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hHn
    have hSr : (1 : ℝ) ≤ S := by exact_mod_cast hS
    set rew' : Fin 2 → ℕ → Fin S → JointAction 2 A → ℝ :=
      fun i h s a => rew i h s a + (if i = 1 then 1 else 0) with hrew'
    have hok : ∀ i h s a, 1 ≤ h → h ≤ H → 0 ≤ rew' i h s a ∧ rew' i h s a ≤ 1 := by
      intro i h s a h1 h2
      have := hzs h s a h1 h2
      fin_cases i
      · simp [hrew']; exact ⟨this.1, this.2.1⟩
      · simp [hrew', this.2.2]; constructor <;> linarith [this.1, this.2.1]
    obtain ⟨al, -, hN, hprob⟩ := core_cce hS hA δ (ε / 2) hδ0 hδ1 (by positivity) (by linarith)
      rew' hok
    refine ⟨al.N, al.rule, fun hist => margProd (al.out hist), ?_, ?_⟩
    · -- sample count
      have hsum : (∑ i, (A i : ℝ)) = A 0 + A 1 := Fin.sum_univ_two _
      set Mx : ℝ := ((max (A 0) (A 1) : ℕ) : ℝ) with hMx
      have hMx1 : (1 : ℝ) ≤ Mx := by rw [hMx]; exact_mod_cast le_max_of_le_left (hA 0)
      have hA0 : (A 0 : ℝ) ≤ Mx := by rw [hMx]; exact_mod_cast le_max_left _ _
      have hA1 : (A 1 : ℝ) ≤ Mx := by rw [hMx]; exact_mod_cast le_max_right _ _
      have hA0' : (1 : ℝ) ≤ A 0 := by exact_mod_cast hA 0
      have hA1' : (1 : ℝ) ≤ A 1 := by exact_mod_cast hA 1
      rw [hsum] at hN
      have hlogle : Real.log (4 * H * S * ((A 0 : ℝ) + A 1) / δ) ≤ Real.log (8 * H * S * Mx / δ) := by
        apply Real.log_le_log (by positivity)
        apply div_le_div_of_nonneg_right _ hδ0.le
        have : (0 : ℝ) ≤ H * S := by positivity
        nlinarith
      have hlog0 : 0 ≤ Real.log (4 * H * S * ((A 0 : ℝ) + A 1) / δ) := by
        apply Real.log_nonneg; rw [le_div_iff₀ hδ0]
        have : (1 : ℝ) ≤ H * S := one_le_mul_of_one_le_of_one_le hHr hSr
        nlinarith
      calc (al.N : ℝ) ≤ 2002 * (H : ℝ) ^ 4 * S * ((A 0 : ℝ) + A 1) / (ε / 2) ^ 2 *
            Real.log (4 * H * S * ((A 0 : ℝ) + A 1) / δ) := hN
        _ = 8008 / ε ^ 2 * ((H : ℝ) ^ 4 * S * ((A 0 : ℝ) + A 1) *
            Real.log (4 * H * S * ((A 0 : ℝ) + A 1) / δ)) := by field_simp; ring
        _ ≤ 8008 / ε ^ 2 * ((H : ℝ) ^ 4 * S * (2 * Mx) * Real.log (8 * H * S * Mx / δ)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul _ hlogle hlog0 (by positivity)
            apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ ≤ 20000 * (H : ℝ) ^ 4 * S * Mx / ε ^ 2 * Real.log (8 * H * S * Mx / δ) := by
            have hl : 0 ≤ Real.log (8 * H * S * Mx / δ) := le_trans hlog0 hlogle
            have hX : 0 ≤ (H : ℝ) ^ 4 * S * Mx * Real.log (8 * H * S * Mx / δ) := by positivity
            have e1 : 8008 / ε ^ 2 * ((H : ℝ) ^ 4 * S * (2 * Mx) * Real.log (8 * H * S * Mx / δ)) =
                16016 / ε ^ 2 * ((H : ℝ) ^ 4 * S * Mx * Real.log (8 * H * S * Mx / δ)) := by ring
            have e2 : 20000 * (H : ℝ) ^ 4 * S * Mx / ε ^ 2 * Real.log (8 * H * S * Mx / δ) =
                20000 / ε ^ 2 * ((H : ℝ) ^ 4 * S * Mx * Real.log (8 * H * S * Mx / δ)) := by ring
            rw [e1, e2]
            exact mul_le_mul_of_nonneg_right
              (div_le_div_of_nonneg_right (by norm_num) (sq_nonneg _)) hX
    · -- probability
      intro P
      have hp := hprob P
      have hgen : genEnv (⟨P, rew'⟩ : MarkovGame 2 S H A) = genEnv (⟨P, rew⟩ : MarkovGame 2 S H A) := rfl
      rw [hgen] at hp
      refine hp.trans (sum_le_sum fun hist _ => mul_le_mul_of_nonneg_left ?_
        ((interactionLaw al.rule _ al.N).prob_nonneg hist))
      split_ifs with h1 h2 <;> try norm_num
      exfalso
      apply h2
      have hshift := gapJ_shift (⟨P, rew⟩ : MarkovGame 2 S H A) (⟨P, rew'⟩ : MarkovGame 2 S H A) rfl
        (fun i => hA i) (fun i => if i = 1 then 1 else 0) (fun i h s a => rfl) (al.out hist)
      have hzs' : ∀ h, 1 ≤ h → h ≤ H → ∀ s a, (⟨P, rew⟩ : MarkovGame 2 S H A).reward 1 h s a =
          -(⟨P, rew⟩ : MarkovGame 2 S H A).reward 0 h s a := fun h h1 h2 s a => (hzs h s a h1 h2).2.2
      have := gap_margProd_le_two_mul hS (fun k => hA k) (⟨P, rew⟩ : MarkovGame 2 S H A) hzs'
        (al.out hist)
      rw [hshift] at h1
      linarith

end StatisticalRL.Ch7Rest.Marl77
