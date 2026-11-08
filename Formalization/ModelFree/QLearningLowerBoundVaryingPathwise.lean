import Formalization.ModelFree.QLearningLowerBoundVaryingDefinitions
import Formalization.ModelFree.QLearningLowerBoundRescaledRates
import Formalization.ModelFree.QLearningLowerBoundTheorem

/-!
# Pathwise Q-learning dynamics on the lower-bound MDP with a learning-rate schedule

Time-varying form of `qLb_pathwise` (Step 2 of the proof of `thm:LB-example-Q-generative`,
`chapters/generative_model_model_free.tex:2855–3063`, and the coupling
`eq:Qt-lower-bound-generative`, lines 3330–3334, proof 3567–3592). Along a valid sample stream:
* `Q_t(0,·) = 0`, the dummy actions keep `Q_t(s,dummy) = 0`;
* `V_t(3) = (1 - Π_{1-γ}(0,t))/(1-γ)` with `Π_x(0,t) = ∏_{j ≤ t} (1 - x η_j)`;
* `V_t(2) = v_t` (`qLbvChain2`);
* `Q_t(1,a) ≥ Q̂_t(a) - Π_{1-γ}(0,t)/(1-γ)`.
Only `0 ≤ η_t ≤ 1` is used.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.QLearning

theorem qLbvRun_succ (γ : ℝ) (η : ℕ → ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) (s : Fin 4) (a : Bool) :
    qLbvRun γ η hγ hγ1 samples (t + 1) s a =
      (1 - η (t + 1)) * qLbvRun γ η hγ hγ1 samples t s a +
        η (t + 1) * ((if s = 0 ∨ (s ≠ 1 ∧ a = true) then 0 else 1) + γ *
          max (qLbvRun γ η hγ hγ1 samples t (samples (t + 1) s a) false)
            (qLbvRun γ η hγ hγ1 samples t (samples (t + 1) s a) true)) := by
  simp only [qLbvRun, qLearningIterate]
  rw [qLearningValue_bool]
  rfl

theorem qLbvRun_nonneg (γ : ℝ) (η : ℕ → ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (hη : ∀ t, 0 ≤ η t ∧ η t ≤ 1) (samples : ℕ → Fin 4 → Bool → Fin 4) (t : ℕ) (s : Fin 4)
    (a : Bool) : 0 ≤ qLbvRun γ η hγ hγ1 samples t s a :=
  (qLearningIterate_bounds (qLbMDP γ hγ hγ1) η samples (fun _ _ ↦ 0)
    (fun _ _ ↦ ⟨le_rfl, (qLbMDP γ hγ hγ1).effectiveHorizon_nonneg⟩) t
    (fun k _ _ ↦ hη k) s a).1

/-- Pathwise dynamics of Q-learning with schedule `η` on `qLbMDP` along a valid sample stream. -/
theorem qLbv_pathwise (γ : ℝ) (η : ℕ → ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (hη : ∀ t, 0 ≤ η t ∧ η t ≤ 1) (samples : ℕ → Fin 4 → Bool → Fin 4) (N : ℕ)
    (hv : qLbValid (qLbMDP γ hγ hγ1) samples N) (t : ℕ) (ht : t ≤ N) :
    qLbvRun γ η hγ hγ1 samples t 0 false = 0 ∧ qLbvRun γ η hγ hγ1 samples t 0 true = 0 ∧
    qLbvRun γ η hγ hγ1 samples t 2 true = 0 ∧ qLbvRun γ η hγ hγ1 samples t 3 true = 0 ∧
    qLbvRun γ η hγ hγ1 samples t 3 false = (1 - qLbvProd η (1 - γ) 0 t) / (1 - γ) ∧
    qLbvRun γ η hγ hγ1 samples t 2 false = qLbvChain2 γ η samples t ∧
    ∀ a, qLbvAuxIterate γ η samples t a - qLbvProd η (1 - γ) 0 t / (1 - γ) ≤
      qLbvRun γ η hγ hγ1 samples t 1 a := by
  have hg : 0 < 1 - γ := by linarith
  have hgne : (1 : ℝ) - γ ≠ 0 := ne_of_gt hg
  have hnn := qLbvRun_nonneg γ η hγ hγ1 hη samples
  have hx1 : ∀ j, (1 - γ) * η j ≤ 1 := fun j ↦ by
    have := hη j; nlinarith
  induction t with
  | zero =>
    simp only [qLbvRun, qLearningIterate, qLbvProd_self, sub_self, zero_div, qLbvChain2,
      true_and]
    intro a
    simp only [qLbvAuxIterate]
    rw [qLb_vstar_eq γ hγ hγ1]
    have : 3 / (4 * (1 - γ)) ≤ 1 / (1 - γ) := by
      rw [div_le_div_iff₀ (by positivity) hg]; linarith
    linarith
  | succ t ih =>
    obtain ⟨h0f, h0t, h2t, h3t, h3f, h2f, h1⟩ := ih (by omega)
    have hnx := fun s a ↦ qLbMDP_next γ hγ hγ1 s a (samples (t + 1) s a)
      (hv (t + 1) (by omega) ht s a)
    have he := hη (t + 1)
    have hP := qLbvProd_succ η (1 - γ) 0 t (Nat.zero_le t)
    have hP0 : 0 ≤ qLbvProd η (1 - γ) 0 t := qLbvProd_nonneg η (1 - γ) 0 t hx1
    have hlam0 : 0 ≤ 1 - (1 - γ) * η (t + 1) := by linarith [hx1 (t + 1)]
    have hlam1 : 1 - η (t + 1) ≤ 1 - (1 - γ) * η (t + 1) := by nlinarith
    have V0 : max (qLbvRun γ η hγ hγ1 samples t 0 false) (qLbvRun γ η hγ hγ1 samples t 0 true) =
        0 := by
      rw [h0f, h0t]; simp
    have V3 : max (qLbvRun γ η hγ hγ1 samples t 3 false) (qLbvRun γ η hγ hγ1 samples t 3 true) =
        qLbvRun γ η hγ hγ1 samples t 3 false := by
      rw [h3t]; exact max_eq_left (hnn t 3 false)
    have V2 : max (qLbvRun γ η hγ hγ1 samples t 2 false) (qLbvRun γ η hγ hγ1 samples t 2 true) =
        qLbvChain2 γ η samples t := by
      rw [h2t, ← h2f]; exact max_eq_left (hnn t 2 false)
    have hzero : ∀ s a, samples (t + 1) s a = 0 →
        (if s = 0 ∨ (s ≠ 1 ∧ a = true) then (0 : ℝ) else 1) = 0 →
        qLbvRun γ η hγ hγ1 samples (t + 1) s a =
          (1 - η (t + 1)) * qLbvRun γ η hγ hγ1 samples t s a := by
      intro s a hs hr
      rw [qLbvRun_succ, hs, hr, V0]; ring
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hzero 0 false ((hnx 0 false).1 rfl) (by simp), h0f]; ring
    · rw [hzero 0 true ((hnx 0 true).1 rfl) (by simp), h0t]; ring
    · rw [hzero 2 true ((hnx 2 true).2.1 (by decide) rfl) (by simp), h2t]; ring
    · rw [hzero 3 true ((hnx 3 true).2.1 (by decide) rfl) (by simp), h3t]; ring
    · rw [qLbvRun_succ]
      rcases (hnx 3 false).2.2.1 rfl with hx | hx
      · rw [hx, V3, h3f, hP]
        simp only [show ¬((3 : Fin 4) = 0 ∨ ((3 : Fin 4) ≠ 1 ∧ false = true)) by decide,
          ↓reduceIte]
        field_simp
        ring
      · exfalso
        have h := hv (t + 1) (by omega) ht 3 false
        rw [hx] at h
        simp [qLbMDP, qLbRow, qHardRow] at h
    · rw [qLbvRun_succ]
      simp only [show ¬((2 : Fin 4) = 0 ∨ ((2 : Fin 4) ≠ 1 ∧ false = true)) by decide,
        ↓reduceIte, qLbvChain2, qLbStay]
      rcases (hnx 2 false).2.2.2.1 rfl with hx | hx
      · rw [hx, V2, h2f]; simp
      · rw [hx, V0, h2f]; simp
    · intro a
      rw [qLbvRun_succ]
      have hif : ¬((1 : Fin 4) = 0 ∨ ((1 : Fin 4) ≠ 1 ∧ a = true)) := by simp
      simp only [hif, ↓reduceIte, qLbvAuxIterate, qLbStay]
      have hV1 : max (qLbvAuxIterate γ η samples t false) (qLbvAuxIterate γ η samples t true) -
          qLbvProd η (1 - γ) 0 t / (1 - γ) ≤
            max (qLbvRun γ η hγ hγ1 samples t 1 false) (qLbvRun γ η hγ hγ1 samples t 1 true) := by
        rw [← max_sub_sub_right]
        exact max_le_max (h1 false) (h1 true)
      have hQ1 := h1 a
      have hlt : 0 ≤ qLbvProd η (1 - γ) 0 t / (1 - γ) := div_nonneg hP0 hg.le
      have hγ0 : 0 ≤ γ := by linarith
      have hpow : qLbvProd η (1 - γ) 0 (t + 1) / (1 - γ) =
          (1 - (1 - γ) * η (t + 1)) * (qLbvProd η (1 - γ) 0 t / (1 - γ)) := by rw [hP]; ring
      rcases (hnx 1 a).2.2.2.2 rfl with hx | hx
      · rw [hx]
        simp only [↓reduceIte, mul_one]
        rw [hpow]
        have e1 := mul_le_mul_of_nonneg_left hQ1 (by linarith : (0 : ℝ) ≤ 1 - η (t + 1))
        have e2 := mul_le_mul_of_nonneg_left hV1 (mul_nonneg he.1 hγ0)
        nlinarith
      · rw [hx, V0]
        simp only [show ¬((0 : Fin 4) = 1) by decide, ↓reduceIte, zero_mul, mul_zero, add_zero]
        rw [hpow]
        have e1 := mul_le_mul_of_nonneg_left hQ1 (by linarith : (0 : ℝ) ≤ 1 - η (t + 1))
        have e3 := mul_le_mul_of_nonneg_right hlam1 hlt
        nlinarith

/-- The Q-learning output values on `qLbMDP` with schedule `η`, almost surely. -/
theorem qLbv_output_ae (γ : ℝ) (η : ℕ → ℝ) (hγ : (1 : ℝ) / 4 < γ) (hγ1 : γ < 1)
    (hη : ∀ t, 0 ≤ η t ∧ η t ≤ 1) (T : ℕ) :
    ∀ᵐ d ∂qSamplingLaw (qLbMDP γ hγ hγ1) T,
      qLearningValue (qLbMDP γ hγ hγ1)
          (qSampledIterate (qLbMDP γ hγ hγ1) η T (fun _ _ ↦ 0) d) 2 =
        qLbvChain2 γ η (qSamplesExtend (qLbMDP γ hγ hγ1) T d) T ∧
      qLearningValue (qLbMDP γ hγ hγ1)
          (qSampledIterate (qLbMDP γ hγ hγ1) η T (fun _ _ ↦ 0) d) 3 =
        (1 - qLbvProd η (1 - γ) 0 T) / (1 - γ) ∧
      qLbvAuxValue γ η (qSamplesExtend (qLbMDP γ hγ hγ1) T d) T -
          qLbvProd η (1 - γ) 0 T / (1 - γ) ≤
        qLearningValue (qLbMDP γ hγ hγ1)
          (qSampledIterate (qLbMDP γ hγ hγ1) η T (fun _ _ ↦ 0) d) 1 := by
  filter_upwards [qLb_valid_ae γ hγ hγ1 T] with d hd
  obtain ⟨-, -, h2t, h3t, h3f, h2f, h1⟩ :=
    qLbv_pathwise γ η hγ hγ1 hη (qSamplesExtend (qLbMDP γ hγ hγ1) T d) T hd T le_rfl
  have hnn := qLbvRun_nonneg γ η hγ hγ1 hη (qSamplesExtend (qLbMDP γ hγ hγ1) T d) T
  change qLearningValue (qLbMDP γ hγ hγ1) (qLbvRun γ η hγ hγ1 (qSamplesExtend _ T d) T) 2 = _ ∧
    qLearningValue (qLbMDP γ hγ hγ1) (qLbvRun γ η hγ hγ1 (qSamplesExtend _ T d) T) 3 = _ ∧
    _ ≤ qLearningValue (qLbMDP γ hγ hγ1) (qLbvRun γ η hγ hγ1 (qSamplesExtend _ T d) T) 1
  simp only [qLearningValue_bool]
  refine ⟨?_, ?_, ?_⟩
  · rw [h2t, max_eq_left (hnn 2 false), h2f]
  · rw [h3t, max_eq_left (hnn 3 false), h3f]
  · unfold qLbvAuxValue
    rw [← max_sub_sub_right]
    exact max_le_max (h1 false) (h1 true)

end StatisticalRL.QLearning
