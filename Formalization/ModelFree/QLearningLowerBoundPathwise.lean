import Formalization.ModelFree.QLearningLowerBoundValues
import Formalization.ModelFree.QLearningLowerBoundAuxMoments

/-!
# Pathwise Q-learning dynamics on the lower-bound MDP

Step 2 of the proof of `thm:LB-example-Q-generative`
(`chapters/generative_model_model_free.tex:2855–3063`) and the coupling
`eq:Qt-lower-bound-generative` (lines 3330–3334, proof 3567–3592), for synchronous Q-learning
(`qLearningIterate`) on `qLbMDP` with `Q₀ = 0` and constant rate `η`, along any sample stream whose
draws lie in the row supports up to time `N`:
* `Q_t(0,·) = 0`, the dummy actions keep `Q_t(s,dummy) = 0`;
* `V_t(3) = Q_t(3,1) = (1-(1-η(1-γ))^t)/(1-γ)` (`eq:vt-3-Q-lower`, `eq:Vt3-expansion-case3`);
* `V_t(2) = Q_t(2,1) = v_t` with `v_t = (1-η)v_{t-1} + η(1+γ P_t(2∣2) v_{t-1})` (`eq:vt-2-Q-lower`);
* `Q_t(1,a) ≥ Q̂_t(a) - (1-η(1-γ))^t/(1-γ)`.
-/

open scoped BigOperators
namespace StatisticalRL.QLearning

/-- The state-2 value chain `v_t` of `eq:vt-2-Q-lower`, `v_0 = 0`. -/
noncomputable def qLbChain2 (γ η : ℝ) (samples : ℕ → Fin 4 → Bool → Fin 4) : ℕ → ℝ
  | 0 => 0
  | t + 1 => (1 - η) * qLbChain2 γ η samples t +
      η * (1 + γ * qLbStay samples 2 (t + 1) false * qLbChain2 γ η samples t)

/-- Synchronous Q-learning on `qLbMDP` from `Q₀ = 0` with constant rate `η`. -/
noncomputable def qLbRun (γ η : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) : Fin 4 → Bool → ℝ :=
  qLearningIterate (qLbMDP γ hγ hγ1) (fun _ ↦ η) samples (fun _ _ ↦ 0) t

/-- Every draw up to time `N` lies in the support of its row. -/
def qLbValid (M : DiscountedMDP (Fin 4) Bool) (samples : ℕ → Fin 4 → Bool → Fin 4) (N : ℕ) :
    Prop :=
  ∀ k, 1 ≤ k → k ≤ N → ∀ s a, (M.transition s a).prob (samples k s a) ≠ 0

theorem qLbMDP_next (γ : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) (s : Fin 4) (a : Bool)
    (x : Fin 4) (h : ((qLbMDP γ hγ hγ1).transition s a).prob x ≠ 0) :
    (s = 0 → x = 0) ∧ (s ≠ 1 → a = true → x = 0) ∧ (s = 3 → x = 3 ∨ x = 0) ∧
      (s = 2 → x = 2 ∨ x = 0) ∧ (s = 1 → x = 1 ∨ x = 0) := by
  fin_cases s <;> cases a <;> fin_cases x <;> simp_all [qLbMDP, qLbRow, qHardRow]

theorem qLbRun_succ (γ η : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) (s : Fin 4) (a : Bool) :
    qLbRun γ η hγ hγ1 samples (t + 1) s a =
      (1 - η) * qLbRun γ η hγ hγ1 samples t s a +
        η * ((if s = 0 ∨ (s ≠ 1 ∧ a = true) then 0 else 1) + γ *
          max (qLbRun γ η hγ hγ1 samples t (samples (t + 1) s a) false)
            (qLbRun γ η hγ hγ1 samples t (samples (t + 1) s a) true)) := by
  simp only [qLbRun, qLearningIterate]
  rw [qLearningValue_bool]
  rfl

theorem qLbRun_nonneg (γ η : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1) (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) (s : Fin 4) (a : Bool) :
    0 ≤ qLbRun γ η hγ hγ1 samples t s a :=
  (qLearningIterate_bounds (qLbMDP γ hγ hγ1) (fun _ ↦ η) samples (fun _ _ ↦ 0)
    (fun _ _ ↦ ⟨le_rfl, (qLbMDP γ hγ hγ1).effectiveHorizon_nonneg⟩) t
    (fun _ _ _ ↦ ⟨hη0, hη1⟩) s a).1

/-- Pathwise dynamics of Q-learning on `qLbMDP` along a valid sample stream. -/
theorem qLb_pathwise (γ η : ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1) (hη0 : 0 ≤ η)
    (hη1 : η ≤ 1) (samples : ℕ → Fin 4 → Bool → Fin 4) (N : ℕ)
    (hv : qLbValid (qLbMDP γ hγ hγ1) samples N) (t : ℕ) (ht : t ≤ N) :
    qLbRun γ η hγ hγ1 samples t 0 false = 0 ∧ qLbRun γ η hγ hγ1 samples t 0 true = 0 ∧
    qLbRun γ η hγ hγ1 samples t 2 true = 0 ∧ qLbRun γ η hγ hγ1 samples t 3 true = 0 ∧
    qLbRun γ η hγ hγ1 samples t 3 false = (1 - (1 - η * (1 - γ)) ^ t) / (1 - γ) ∧
    qLbRun γ η hγ hγ1 samples t 2 false = qLbChain2 γ η samples t ∧
    ∀ a, qLbAuxIterate γ η samples t a - (1 - η * (1 - γ)) ^ t / (1 - γ) ≤
      qLbRun γ η hγ hγ1 samples t 1 a := by
  have hg : 0 < 1 - γ := by linarith
  have hgne : (1 : ℝ) - γ ≠ 0 := ne_of_gt hg
  have hlam0 : 0 ≤ 1 - η * (1 - γ) := by nlinarith
  have hlam1 : 1 - η ≤ 1 - η * (1 - γ) := by nlinarith
  have hnn := qLbRun_nonneg γ η hγ hγ1 hη0 hη1 samples
  induction t with
  | zero =>
    simp only [qLbRun, qLearningIterate, pow_zero, sub_self, zero_div, qLbChain2, true_and]
    intro a
    simp only [qLbAuxIterate]
    rw [qLb_vstar_eq γ hγ hγ1]
    have : 3 / (4 * (1 - γ)) ≤ 1 / (1 - γ) := by
      rw [div_le_div_iff₀ (by positivity) hg]; linarith
    linarith
  | succ t ih =>
    obtain ⟨h0f, h0t, h2t, h3t, h3f, h2f, h1⟩ := ih (by omega)
    have hnx := fun s a ↦ qLbMDP_next γ hγ hγ1 s a (samples (t + 1) s a)
      (hv (t + 1) (by omega) ht s a)
    have V0 : max (qLbRun γ η hγ hγ1 samples t 0 false) (qLbRun γ η hγ hγ1 samples t 0 true) = 0 := by
      rw [h0f, h0t]; simp
    have V3 : max (qLbRun γ η hγ hγ1 samples t 3 false) (qLbRun γ η hγ hγ1 samples t 3 true) =
        qLbRun γ η hγ hγ1 samples t 3 false := by
      rw [h3t]; exact max_eq_left (hnn t 3 false)
    have V2 : max (qLbRun γ η hγ hγ1 samples t 2 false) (qLbRun γ η hγ hγ1 samples t 2 true) =
        qLbChain2 γ η samples t := by
      rw [h2t, ← h2f]; exact max_eq_left (hnn t 2 false)
    have hzero : ∀ s a, samples (t + 1) s a = 0 →
        (if s = 0 ∨ (s ≠ 1 ∧ a = true) then (0 : ℝ) else 1) = 0 →
        qLbRun γ η hγ hγ1 samples (t + 1) s a = (1 - η) * qLbRun γ η hγ hγ1 samples t s a := by
      intro s a hs hr
      rw [qLbRun_succ, hs, hr, V0]; ring
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hzero 0 false ((hnx 0 false).1 rfl) (by simp), h0f]; ring
    · rw [hzero 0 true ((hnx 0 true).1 rfl) (by simp), h0t]; ring
    · rw [hzero 2 true ((hnx 2 true).2.1 (by decide) rfl) (by simp), h2t]; ring
    · rw [hzero 3 true ((hnx 3 true).2.1 (by decide) rfl) (by simp), h3t]; ring
    · rw [qLbRun_succ]
      rcases (hnx 3 false).2.2.1 rfl with hx | hx
      · rw [hx, V3, h3f]
        simp only [show ¬((3 : Fin 4) = 0 ∨ ((3 : Fin 4) ≠ 1 ∧ false = true)) by decide, ↓reduceIte]
        rw [pow_succ]
        field_simp
        ring
      · exfalso
        have h := hv (t + 1) (by omega) ht 3 false
        rw [hx] at h
        simp [qLbMDP, qLbRow, qHardRow] at h
    · rw [qLbRun_succ]
      simp only [show ¬((2 : Fin 4) = 0 ∨ ((2 : Fin 4) ≠ 1 ∧ false = true)) by decide, ↓reduceIte,
        qLbChain2, qLbStay]
      rcases (hnx 2 false).2.2.2.1 rfl with hx | hx
      · rw [hx, V2, h2f]; simp
      · rw [hx, V0, h2f]; simp
    · intro a
      rw [qLbRun_succ]
      have hif : ¬((1 : Fin 4) = 0 ∨ ((1 : Fin 4) ≠ 1 ∧ a = true)) := by simp
      simp only [hif, ↓reduceIte, qLbAuxIterate, qLbStay]
      have hV1 : max (qLbAuxIterate γ η samples t false) (qLbAuxIterate γ η samples t true) -
          (1 - η * (1 - γ)) ^ t / (1 - γ) ≤
            max (qLbRun γ η hγ hγ1 samples t 1 false) (qLbRun γ η hγ hγ1 samples t 1 true) := by
        rw [← max_sub_sub_right]
        exact max_le_max (h1 false) (h1 true)
      have hQ1 := h1 a
      have hlt : 0 ≤ (1 - η * (1 - γ)) ^ t / (1 - γ) := div_nonneg (pow_nonneg hlam0 t) hg.le
      have hγ0 : 0 ≤ γ := by linarith
      have hpow : (1 - η * (1 - γ)) ^ (t + 1) / (1 - γ) =
          (1 - η * (1 - γ)) * ((1 - η * (1 - γ)) ^ t / (1 - γ)) := by rw [pow_succ]; ring
      rcases (hnx 1 a).2.2.2.2 rfl with hx | hx
      · rw [hx]
        simp only [↓reduceIte, mul_one]
        rw [hpow]
        have e1 := mul_le_mul_of_nonneg_left hQ1 (by linarith : (0 : ℝ) ≤ 1 - η)
        have e2 := mul_le_mul_of_nonneg_left hV1 (mul_nonneg hη0 hγ0)
        nlinarith
      · rw [hx, V0]
        simp only [show ¬((0 : Fin 4) = 1) by decide, ↓reduceIte, zero_mul, mul_zero, add_zero]
        rw [hpow]
        have e1 := mul_le_mul_of_nonneg_left hQ1 (by linarith : (0 : ℝ) ≤ 1 - η)
        have e3 := mul_le_mul_of_nonneg_right hlam1 hlt
        nlinarith

end StatisticalRL.QLearning
