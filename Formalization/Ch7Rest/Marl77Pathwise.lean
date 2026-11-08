import Formalization.Ch7Rest.Marl77StageBounds

/-!
# Theorem 7.7: the pathwise gap bound on the good event

On `Good`, with `λ = η`, for every player `i` and state `s`,

  `V^{⋆,π̂_{-i}}_{i,1}(s) − V^{π̂}_{i,1}(s) ≤ 40λH² + 16H²L/T + 3HL/(λT) + λH³L/T`,

hence `gapJ G π̂ ≤` the same bound. Upper side: for every deterministic deviation `ρ`,
`V^ρ − f ≤ Eval_ρ(λ·v^ρ + L/(λT))` and F3 (`evalJ_jvarJ_le`) closes the self-bounding. Lower
side: `f − V^{π̂} ≤ Eval_{π̂}(3λ·v^{π̂} + 2L/(λT) + λH²L/T)` and F3 again.
-/

open scoped BigOperators
open Finset

namespace StatisticalRL.Ch7Rest.Marl77

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.Ch7Rest.Marl76
open StatisticalRL.Online.Hedge StatisticalRL.AdaptiveKL

variable {m S H : ℕ} {A : Fin m → ℕ}

/-! ### Generic comparison inductions -/

theorem valueJ_sub_bellJ (G : MarkovGame m S H A) (ρ : JointPolicy m S A) (i : Fin m)
    (f : ℕ → Fin S → ℝ) (h k : ℕ) (s : Fin S) :
    valueJ G ρ i h (k + 1) s - bellJ G ρ i f h s =
      ∑ a, (ρ h s).prob a * (G.transition h s a).expectation
        (fun s' => valueJ G ρ i (h + 1) k s' - f (h + 1) s') := by
  simp only [valueJ, bellJ]
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [FiniteDistribution.expectation_sub]; ring

theorem evalJ_state_succ (G : MarkovGame m S H A) (ρ : JointPolicy m S A) (e : ℕ → Fin S → ℝ)
    (h k : ℕ) (s : Fin S) :
    evalJ G ρ (fun t s _ => e t s) h (k + 1) s =
      e h s + ∑ a, (ρ h s).prob a * (G.transition h s a).expectation
        (evalJ G ρ (fun t s _ => e t s) (h + 1) k) := by
  simp only [evalJ]
  calc ∑ a, (ρ h s).prob a * (e h s + (G.transition h s a).expectation
        (evalJ G ρ (fun t s _ => e t s) (h + 1) k))
      = (∑ a, (ρ h s).prob a) * e h s + ∑ a, (ρ h s).prob a * (G.transition h s a).expectation
        (evalJ G ρ (fun t s _ => e t s) (h + 1) k) := by
        rw [sum_mul, ← sum_add_distrib]; refine sum_congr rfl fun a _ => by ring
    _ = _ := by rw [(ρ h s).sum_prob, one_mul]

/-- Upper comparison: if `bellJ_t − f_t ≤ e_t` on `[1, H]` and `f_{H+1} = 0` then
`V^ρ_h − f_h ≤ Eval_ρ(e)_h`. -/
theorem valueJ_sub_le_evalJ (G : MarkovGame m S H A) (ρ : JointPolicy m S A) (i : Fin m)
    (f e : ℕ → Fin S → ℝ) (hfH : ∀ s, f (H + 1) s = 0)
    (hstep : ∀ t, 1 ≤ t → t ≤ H → ∀ s, bellJ G ρ i f t s - f t s ≤ e t s) :
    ∀ k h, h + k = H + 1 → 1 ≤ h → ∀ s,
      valueJ G ρ i h k s - f h s ≤ evalJ G ρ (fun t s _ => e t s) h k s := by
  intro k
  induction k with
  | zero =>
    intro h hk _ s
    have : h = H + 1 := by omega
    subst this
    simp [valueJ, evalJ, hfH s]
  | succ k ih =>
    intro h hk h1 s
    have hnext := ih (h + 1) (by omega) (by omega)
    have hd := valueJ_sub_bellJ G ρ i f h k s
    rw [evalJ_state_succ]
    have hs := hstep h h1 (by omega) s
    have hsum : ∑ a, (ρ h s).prob a * (G.transition h s a).expectation
        (fun s' => valueJ G ρ i (h + 1) k s' - f (h + 1) s') ≤
        ∑ a, (ρ h s).prob a * (G.transition h s a).expectation
          (evalJ G ρ (fun t s _ => e t s) (h + 1) k) :=
      sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
        (FiniteDistribution.expectation_mono _ hnext) ((ρ h s).prob_nonneg a)
    linarith

/-- Lower comparison: if `f_t − bellJ_t ≤ e_t` on `[1, H]` and `f_{H+1} = 0` then
`f_h − V^ρ_h ≤ Eval_ρ(e)_h`. -/
theorem sub_valueJ_le_evalJ (G : MarkovGame m S H A) (ρ : JointPolicy m S A) (i : Fin m)
    (f e : ℕ → Fin S → ℝ) (hfH : ∀ s, f (H + 1) s = 0)
    (hstep : ∀ t, 1 ≤ t → t ≤ H → ∀ s, f t s - bellJ G ρ i f t s ≤ e t s) :
    ∀ k h, h + k = H + 1 → 1 ≤ h → ∀ s,
      f h s - valueJ G ρ i h k s ≤ evalJ G ρ (fun t s _ => e t s) h k s := by
  intro k
  induction k with
  | zero =>
    intro h hk _ s
    have : h = H + 1 := by omega
    subst this
    simp [valueJ, evalJ, hfH s]
  | succ k ih =>
    intro h hk h1 s
    have hnext := ih (h + 1) (by omega) (by omega)
    have hd := valueJ_sub_bellJ G ρ i f h k s
    rw [evalJ_state_succ]
    have hs := hstep h h1 (by omega) s
    have hsum : ∑ a, (ρ h s).prob a * (G.transition h s a).expectation
        (fun s' => f (h + 1) s' - valueJ G ρ i (h + 1) k s') ≤
        ∑ a, (ρ h s).prob a * (G.transition h s a).expectation
          (evalJ G ρ (fun t s _ => e t s) (h + 1) k) :=
      sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
        (FiniteDistribution.expectation_mono _ hnext) ((ρ h s).prob_nonneg a)
    have hneg : ∑ a, (ρ h s).prob a * (G.transition h s a).expectation
        (fun s' => f (h + 1) s' - valueJ G ρ i (h + 1) k s') =
        -∑ a, (ρ h s).prob a * (G.transition h s a).expectation
        (fun s' => valueJ G ρ i (h + 1) k s' - f (h + 1) s') := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun a _ => ?_
      rw [FiniteDistribution.expectation_sub, FiniteDistribution.expectation_sub]; ring
    linarith

/-- Self-bounding via F3: if `max(−(f − bellJ), 0) ≤ λ·jvar + κ` on `[1,H]`, `2λH ≤ 1/2`,
then `Eval_ρ(jvar)_1 ≤ 10H² + 4H²κ`. -/
theorem evalJ_jvarJ_self_bound (G : MarkovGame m S H A) (ρ : JointPolicy m S A) (i : Fin m)
    (f : ℕ → Fin S → ℝ) (hH : 1 ≤ H)
    (hf : ∀ t, 1 ≤ t → t ≤ H → ∀ s, 0 ≤ f t s ∧ f t s ≤ H) (hfH : ∀ s, f (H + 1) s = 0)
    (hr : ∀ t, 1 ≤ t → t ≤ H → ∀ s a, 0 ≤ G.reward i t s a ∧ G.reward i t s a ≤ 1)
    {lam κ : ℝ} (hlam : 0 ≤ lam) (hlamH : lam * H ≤ 1 / 4)
    (hΔ : ∀ t, 1 ≤ t → t ≤ H → ∀ s,
      max (-(f t s - bellJ G ρ i f t s)) 0 ≤ lam * jvarJ G ρ i f t s + κ) (s : Fin S) :
    evalJ G ρ (fun t s _ => jvarJ G ρ i f t s) 1 H s ≤ 10 * (H : ℝ) ^ 2 + 4 * (H : ℝ) * (H * κ) := by
  have hF3 := evalJ_jvarJ_le G ρ i f hH hf hfH hr s
  have hD := evalJ_le_affine G ρ (fun t s _ => jvarJ G ρ i f t s)
    (fun t s _ => max (-(f t s - bellJ G ρ i f t s)) 0) lam κ H 1
    (fun t h1 h2 s a => hΔ t h1 (by omega) s) s
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  set W := evalJ G ρ (fun t s _ => jvarJ G ρ i f t s) 1 H s
  set D := evalJ G ρ (fun t s _ => max (-(f t s - bellJ G ρ i f t s)) 0) 1 H s
  have h1 : W ≤ 5 * (H : ℝ) ^ 2 + 2 * H * (lam * W + κ * H) := by
    have : 2 * (H : ℝ) * D ≤ 2 * H * (lam * W + κ * H) :=
      mul_le_mul_of_nonneg_left hD (by positivity)
    linarith
  have h2 : 2 * (H : ℝ) * lam * W ≤ W / 2 := by
    have hW : 0 ≤ W := evalJ_nonneg G ρ _ H 1 (fun t _ _ s _ => jvarJ_nonneg G ρ i f t s) s
    nlinarith
  nlinarith

end StatisticalRL.Ch7Rest.Marl77
