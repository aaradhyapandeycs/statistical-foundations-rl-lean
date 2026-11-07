import Formalization.OfflineRL.FiniteLCBQ.Events2

/-!
# Finite-horizon LCB-Q: tail bounds for M1, M2 and Cnt
-/

namespace StatisticalRL.LCBQFinite

open Finset MeasureTheory ProbabilityTheory OnlineRL StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
set_option linter.unusedSectionVars false

noncomputable local instance tlDecS : DecidableEq S := Classical.decEq S
noncomputable local instance tlDecA : DecidableEq A := Classical.decEq A

variable {H K : ℕ} (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
  (ρb ρ : FiniteDistribution S) (πs : Fin H → S → A) (cb L : ℝ) (sel : (A → ℝ) → A)
  (π₀ : Fin H → S → A)

theorem sum_fin_range (G : ℕ → ℝ) : ∑ k : Fin K, G k.val = ∑ k ∈ range K, G k :=
  Fin.sum_univ_eq_sum_range G K

/-- **M1 tail**. -/
theorem m1_tail (hH : 0 < H) (hC : concentrability E πb ρb ρ πs ≠ ⊤)
    (hC1 : 1 ≤ (concentrability E πb ρb ρ πs).toReal) (h : Fin H) {ι : ℝ} :
    ∑ x : Fin K → Traj S A H, prodP E πb ρb x *
      (if ∑ k ∈ range K, Z1 E πb ρb ρ πs cb L sel π₀ x k h +
          2 * (concentrability E πb ρb ρ πs).toReal * (H : ℝ) ^ 2 * ι <
        (1 - 1 / (2 * (H : ℝ))) * ∑ k ∈ range K, a1 E ρ πs cb L sel π₀ x k h then 1 else 0)
      ≤ Real.exp (-ι) := by
  set C := (concentrability E πb ρb ρ πs).toReal
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hC0 : 0 < C := by linarith
  set lam := 1 / (2 * C * (H : ℝ) ^ 2)
  have hl0 : 0 < lam := by positivity
  have hlCH : lam * (C * H) = 1 / (2 * H) := by simp only [lam]; field_simp
  have hl1 : lam * (C * H) ≤ 1 := by
    rw [hlCH, div_le_one (by positivity)]; have : (1 : ℝ) ≤ H := by exact_mod_cast hH
    linarith
  let Φ : Fin K → Iterate S A H → Traj S A H → ℝ := fun _ it τ ↦
    -lam * zOf E πb ρb ρ πs h (fun s ↦ fIt E πs it h s) (τ.1 h.castSucc) (τ.2 h) +
      lam * ∑ t, ds E ρ πs h t * fIt E πs it h t -
      lam ^ 2 * (C * H) * ∑ t, ds E ρ πs h t * fIt E πs it h t
  have hmk := markov_run (K := K) E πb ρb cb L sel π₀ Φ (fun k x ↦ by
    simp only [Φ]
    rw [pair_sum E πb ρb h (fun s0 a0 ↦ Real.exp (-lam * zOf E πb ρb ρ πs h
      (fun s ↦ fIt E πs (it E cb L sel π₀ x k.val) h s) s0 a0 +
      lam * ∑ t, ds E ρ πs h t * fIt E πs (it E cb L sel π₀ x k.val) h t -
      lam ^ 2 * (C * H) * ∑ t, ds E ρ πs h t * fIt E πs (it E cb L sel π₀ x k.val) h t))]
    exact m1_step E πb ρb ρ πs hC h _ (fun s ↦ ⟨fK_nonneg E πs cb L sel π₀ x k.val h s,
      fK_le_H E πs cb L sel π₀ x k.val h s⟩) hl0.le hl1) ι
  refine le_trans (sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left ?_ (prodP_nonneg E πb ρb x)) hmk
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exfalso; apply h2
    have hsum : ∑ k : Fin K, Φ k (it E cb L sel π₀ x k.val) (x k) =
        lam * ((1 - 1 / (2 * (H : ℝ))) * ∑ k ∈ range K, a1 E ρ πs cb L sel π₀ x k h -
          ∑ k ∈ range K, Z1 E πb ρb ρ πs cb L sel π₀ x k h) := by
      have e : ∀ k : Fin K, Φ k (it E cb L sel π₀ x k.val) (x k) =
          lam * ((1 - 1 / (2 * (H : ℝ))) * a1 E ρ πs cb L sel π₀ x k.val h -
            Z1 E πb ρb ρ πs cb L sel π₀ x k.val h) := by
        intro k
        simp only [Φ, Z1, a1]
        rw [sum_vis_eq_zOf E πb ρb ρ πs x h (fun s ↦ fK E πs cb L sel π₀ x k.val h s) k]
        have : lam ^ 2 * (C * H) = lam * (1 / (2 * H)) := by rw [← hlCH]; ring
        rw [this]
        simp only [fK_eq]
        ring
      rw [sum_congr rfl fun k _ ↦ e k, ← mul_sum,
        sum_fin_range (fun k ↦ (1 - 1 / (2 * (H : ℝ))) * a1 E ρ πs cb L sel π₀ x k h -
          Z1 E πb ρb ρ πs cb L sel π₀ x k h), sum_sub_distrib, ← mul_sum]
    rw [hsum]
    have : ι = lam * (2 * C * (H : ℝ) ^ 2 * ι) := by simp only [lam]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) hl0.le
  · positivity
  · exact le_rfl

/-- **M2 tail**. -/
theorem m2_tail (hH : 0 < H) (hC : concentrability E πb ρb ρ πs ≠ ⊤)
    (hC1 : 1 ≤ (concentrability E πb ρb ρ πs).toReal) (h : Fin H) {ι : ℝ} :
    ∑ x : Fin K → Traj S A H, prodP E πb ρb x *
      (if (1 + 1 / (H : ℝ)) * ∑ k ∈ range K, a2 E ρ πs cb L sel π₀ x k h +
          (concentrability E πb ρb ρ πs).toReal * (H : ℝ) ^ 2 * ι <
        ∑ k ∈ range K, Z2 E πb ρb ρ πs cb L sel π₀ x k h then 1 else 0)
      ≤ Real.exp (-ι) := by
  set C := (concentrability E πb ρb ρ πs).toReal
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hC0 : 0 < C := by linarith
  set lam := 1 / (C * (H : ℝ) ^ 2)
  have hl0 : 0 < lam := by positivity
  have hlCH : lam * (C * H) = 1 / H := by simp only [lam]; field_simp
  have hl1 : lam * (C * H) ≤ 1 := by
    rw [hlCH, div_le_one hH0]; exact_mod_cast hH
  let Φ : Fin K → Iterate S A H → Traj S A H → ℝ := fun _ it τ ↦
    lam * zOf E πb ρb ρ πs h (fun s ↦ gIt E πs it h s) (τ.1 h.castSucc) (τ.2 h) -
      lam * ∑ t, ds E ρ πs h t * gIt E πs it h t -
      lam ^ 2 * (C * H) * ∑ t, ds E ρ πs h t * gIt E πs it h t
  have hmk := markov_run (K := K) E πb ρb cb L sel π₀ Φ (fun k x ↦ by
    simp only [Φ]
    rw [pair_sum E πb ρb h (fun s0 a0 ↦ Real.exp (lam * zOf E πb ρb ρ πs h
      (fun s ↦ gIt E πs (it E cb L sel π₀ x k.val) h s) s0 a0 -
      lam * ∑ t, ds E ρ πs h t * gIt E πs (it E cb L sel π₀ x k.val) h t -
      lam ^ 2 * (C * H) * ∑ t, ds E ρ πs h t * gIt E πs (it E cb L sel π₀ x k.val) h t))]
    exact m2_step E πb ρb ρ πs hC h _ (fun s ↦ ⟨gK_nonneg E πs cb L sel π₀ x k.val h s,
      gK_le_H E πs cb L sel π₀ x k.val h s⟩) hl0.le hl1) ι
  refine le_trans (sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left ?_ (prodP_nonneg E πb ρb x)) hmk
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exfalso; apply h2
    have hsum : ∑ k : Fin K, Φ k (it E cb L sel π₀ x k.val) (x k) =
        lam * (∑ k ∈ range K, Z2 E πb ρb ρ πs cb L sel π₀ x k h -
          (1 + 1 / (H : ℝ)) * ∑ k ∈ range K, a2 E ρ πs cb L sel π₀ x k h) := by
      have e : ∀ k : Fin K, Φ k (it E cb L sel π₀ x k.val) (x k) =
          lam * (Z2 E πb ρb ρ πs cb L sel π₀ x k.val h -
            (1 + 1 / (H : ℝ)) * a2 E ρ πs cb L sel π₀ x k.val h) := by
        intro k
        simp only [Φ, Z2, a2]
        rw [sum_vis_eq_zOf E πb ρb ρ πs x h (fun s ↦ gK E πs cb L sel π₀ x k.val h s) k]
        have : lam ^ 2 * (C * H) = lam * (1 / H) := by rw [← hlCH]; ring
        rw [this]
        simp only [gK_eq]
        ring
      rw [sum_congr rfl fun k _ ↦ e k, ← mul_sum,
        sum_fin_range (fun k ↦ Z2 E πb ρb ρ πs cb L sel π₀ x k h -
          (1 + 1 / (H : ℝ)) * a2 E ρ πs cb L sel π₀ x k h), sum_sub_distrib, ← mul_sum]
    rw [hsum]
    have : ι = lam * (C * (H : ℝ) ^ 2 * ι) := by simp only [lam]; field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (by linarith) hl0.le
  · positivity
  · exact le_rfl

theorem cnt_eq_sum (x : Fin K → Traj S A H) (h : Fin H) (s : S) (a : A) :
    (cnt (vis x h s a) K : ℝ) =
      ∑ k : Fin K, (if (x k).1 h.castSucc = s ∧ (x k).2 h = a then 1 else 0) := by
  unfold cnt
  rw [card_filter, Nat.cast_sum, ← sum_fin_range (K := K)
    (fun j ↦ ((if vis x h s a j then 1 else 0 : ℕ) : ℝ))]
  refine sum_congr rfl fun k _ ↦ ?_
  by_cases hv : (x k).1 h.castSucc = s ∧ (x k).2 h = a
  · rw [if_pos hv, if_pos ((vis_fin_iff x h s a k).2 hv)]; simp
  · rw [if_neg hv, if_neg (fun h' ↦ hv ((vis_fin_iff x h s a k).1 h'))]; simp

/-- **Cnt tail**. -/
theorem cnt_tail (h : Fin H) (s : S) {ι : ℝ} :
    ∑ x : Fin K → Traj S A H, prodP E πb ρb x *
      (if 2 * K * db E πb ρb πs h s + ι < (cnt (visA πs x h s) K : ℝ) then 1 else 0)
      ≤ Real.exp (-ι) := by
  let Φ : Fin K → Iterate S A H → Traj S A H → ℝ := fun _ _ τ ↦
    (if τ.1 h.castSucc = s ∧ τ.2 h = πs h s then 1 else 0) - 2 * db E πb ρb πs h s
  have hmk := markov_run (K := K) E πb ρb 0 0 (fun _ ↦ Classical.arbitrary A) πs Φ (fun k x ↦ by
    simp only [Φ]
    rw [pair_sum E πb ρb h (fun s0 a0 ↦ Real.exp
      ((if s0 = s ∧ a0 = πs h s then 1 else 0) - 2 * db E πb ρb πs h s))]
    exact cnt_step E πb ρb πs h s) ι
  refine le_trans (sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left ?_ (prodP_nonneg E πb ρb x)) hmk
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exfalso; apply h2
    have : ∑ k : Fin K, Φ k (it E 0 0 (fun _ ↦ Classical.arbitrary A) πs x k.val) (x k) =
        (cnt (visA πs x h s) K : ℝ) - 2 * K * db E πb ρb πs h s := by
      simp only [Φ, sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [cnt_eq_sum]; ring
    rw [this]; linarith
  · positivity
  · exact le_rfl

end StatisticalRL.LCBQFinite
