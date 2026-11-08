import Formalization.Ch7Rest.Marl76BestResponse
import Formalization.Generative.PolicyLearningVarianceTransfer

/-!
# Theorem 7.6: deterministic policy-evaluation error bound (self-bounding)

For a fixed joint policy `ρ`, player `i`, the true game `G` and a game `Ĝ` with the same rewards,
`V̂_t = valueJ Ĝ ρ i t (H+1-t)` and `V_t = valueJ G ρ i t (H+1-t)`:

* `evalJ G ρ f`: policy evaluation of a per-step reward `f` under the kernels of `G`;
  `evalJ_le_affine`: linearity/monotonicity in the reward.
* `abs_valueJ_sub_le_evalJ`: `|V̂_h − V_h| ≤ Eval_ρ(|(P̂ − P) V̂_{next}|)_h`.
* `evalJ_variance_add_sq_le`: total variance, `Eval_ρ(Var_P(V_next))_h + V_h² ≤ (H+1-h)²`.
* `selfBound`: if `|(P̂_t − P_t)(s,a)·V̂_{t+1}| ≤ √(2L/N)·√Var_{P_t(s,a)}(V̂_{t+1}) + 2HL/(3N)` for
  all `t ∈ [1,H]`, and `H√(2L/N) ≤ 1/2`, then for every `λ > 0`,
  `|V̂_1 − V_1| ≤ λH² + 2HL/(λN) + (4/3)H²L/N`.
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl76

open StatisticalRL StatisticalRL.Ch7Rest.Marl

variable {m S H : ℕ} {A : Fin m → ℕ}

/-- Policy evaluation of the per-step reward `f` under the kernels of `G`. -/
noncomputable def evalJ (G : MarkovGame m S H A) (ρ : JointPolicy m S A)
    (f : ℕ → Fin S → JointAction m A → ℝ) : ℕ → ℕ → Fin S → ℝ
  | _, 0, _ => 0
  | h, k + 1, s => ∑ a, (ρ h s).prob a *
      (f h s a + (G.transition h s a).expectation (evalJ G ρ f (h + 1) k))

theorem sum_prob_mul_affine {Ω : Type*} [Fintype Ω] (d : FiniteDistribution Ω) (X : Ω → ℝ)
    (α C : ℝ) : ∑ x, d.prob x * (α * X x + C) = α * ∑ x, d.prob x * X x + C := by
  have h : ∀ x, d.prob x * (α * X x + C) = α * (d.prob x * X x) + d.prob x * C := fun x => by ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, d.sum_prob, one_mul]

theorem abs_expectation_le_expectation_abs {Ω : Type*} [Fintype Ω] (d : FiniteDistribution Ω)
    (f : Ω → ℝ) : |d.expectation f| ≤ d.expectation (fun x => |f x|) := by
  unfold FiniteDistribution.expectation
  calc |∑ x, d.prob x * f x| ≤ ∑ x, |d.prob x * f x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, d.prob x * |f x| := by simp only [abs_mul, abs_of_nonneg (d.prob_nonneg _)]

/-- `Eval` is monotone and affine in the reward. -/
theorem evalJ_le_affine (G : MarkovGame m S H A) (ρ : JointPolicy m S A)
    (f g : ℕ → Fin S → JointAction m A → ℝ) (α c : ℝ) :
    ∀ k h, (∀ t, h ≤ t → t < h + k → ∀ s a, g t s a ≤ α * f t s a + c) →
      ∀ s, evalJ G ρ g h k s ≤ α * evalJ G ρ f h k s + c * k := by
  intro k
  induction k with
  | zero => intro h _ s; simp [evalJ]
  | succ k ih =>
    intro h hg s
    have hnext := ih (h + 1) (fun t ht1 ht2 => hg t (by omega) (by omega))
    simp only [evalJ]
    calc ∑ a, (ρ h s).prob a * (g h s a + (G.transition h s a).expectation (evalJ G ρ g (h + 1) k))
        ≤ ∑ a, (ρ h s).prob a * (α * (f h s a + (G.transition h s a).expectation
            (evalJ G ρ f (h + 1) k)) + c * ((k : ℝ) + 1)) := by
          refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ ((ρ h s).prob_nonneg a)
          have h1 := hg h le_rfl (by omega) s a
          have h2 : (G.transition h s a).expectation (evalJ G ρ g (h + 1) k) ≤
              α * (G.transition h s a).expectation (evalJ G ρ f (h + 1) k) + c * k := by
            calc (G.transition h s a).expectation (evalJ G ρ g (h + 1) k)
                ≤ (G.transition h s a).expectation
                    (fun x => α * evalJ G ρ f (h + 1) k x + c * k) :=
                  FiniteDistribution.expectation_mono _ hnext
              _ = _ := by
                rw [FiniteDistribution.expectation_add (G.transition h s a)
                    (fun x => α * evalJ G ρ f (h + 1) k x) (fun _ => c * k),
                  FiniteDistribution.expectation_mul, FiniteDistribution.expectation_const]
          nlinarith
      _ = α * ∑ a, (ρ h s).prob a * (f h s a + (G.transition h s a).expectation
            (evalJ G ρ f (h + 1) k)) + c * ((k + 1 : ℕ) : ℝ) := by
          rw [sum_prob_mul_affine]; push_cast; ring

/-- Values are in `[0, k]` when rewards are in `[0,1]` on the window. -/
theorem valueJ_mem_Icc (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m) :
    ∀ k h, (∀ t, h ≤ t → t < h + k → ∀ s a, 0 ≤ G.reward i t s a ∧ G.reward i t s a ≤ 1) →
      ∀ s, 0 ≤ valueJ G π i h k s ∧ valueJ G π i h k s ≤ k := by
  intro k
  induction k with
  | zero => intro h _ s; simp [valueJ]
  | succ k ih =>
    intro h hR s
    have hnext := ih (h + 1) (fun t ht1 ht2 => hR t (by omega) (by omega))
    simp only [valueJ]
    constructor
    · refine Finset.sum_nonneg fun a _ => mul_nonneg ((π h s).prob_nonneg a) ?_
      exact add_nonneg (hR h le_rfl (by omega) s a).1
        (FiniteDistribution.expectation_nonneg _ fun x => (hnext x).1)
    · calc ∑ a, (π h s).prob a * (G.reward i h s a + (G.transition h s a).expectation
            (valueJ G π i (h + 1) k)) ≤ ∑ a, (π h s).prob a * (1 + (k : ℝ)) :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
            (add_le_add (hR h le_rfl (by omega) s a).2
              (FiniteDistribution.expectation_le_const _ fun x => (hnext x).2))
            ((π h s).prob_nonneg a)
        _ = ((k + 1 : ℕ) : ℝ) := by
          rw [← Finset.sum_mul, (π h s).sum_prob]; push_cast; ring

/-- The error identity, in absolute value: `|V̂_h − V_h| ≤ Eval_ρ(|(P̂ − P)·V̂_next|)_h`. -/
theorem abs_valueJ_sub_le_evalJ (G Ĝ : MarkovGame m S H A) (ρ : JointPolicy m S A) (i : Fin m)
    (hr : ∀ t, Ĝ.reward i t = G.reward i t) (E : ℕ) :
    ∀ k h, h + k = E → ∀ s, |valueJ Ĝ ρ i h k s - valueJ G ρ i h k s| ≤
      evalJ G ρ (fun t s a => |(Ĝ.transition t s a).expectation (valueJ Ĝ ρ i (t + 1) (E - (t + 1))) -
        (G.transition t s a).expectation (valueJ Ĝ ρ i (t + 1) (E - (t + 1)))|) h k s := by
  intro k
  induction k with
  | zero => intro h _ s; simp [valueJ, evalJ]
  | succ k ih =>
    intro h hk s
    have hnext := ih (h + 1) (by omega)
    obtain rfl : k = E - (h + 1) := by omega
    simp only [valueJ, evalJ]
    rw [hr h, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [← mul_sub, abs_mul, abs_of_nonneg ((ρ h s).prob_nonneg a)]
    refine mul_le_mul_of_nonneg_left ?_ ((ρ h s).prob_nonneg a)
    set Vh := valueJ Ĝ ρ i (h + 1) (E - (h + 1))
    set V := valueJ G ρ i (h + 1) (E - (h + 1))
    have hsplit : G.reward i h s a + (Ĝ.transition h s a).expectation Vh -
        (G.reward i h s a + (G.transition h s a).expectation V) =
        ((Ĝ.transition h s a).expectation Vh - (G.transition h s a).expectation Vh) +
          (G.transition h s a).expectation (fun x => Vh x - V x) := by
      rw [FiniteDistribution.expectation_sub]; ring
    rw [hsplit]
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    exact (abs_expectation_le_expectation_abs _ _).trans
      (FiniteDistribution.expectation_mono _ hnext)

/-- Total variance: `Eval_ρ(Var_P(V_next))_h + V_h² ≤ k²` with `k` steps to go. -/
theorem evalJ_variance_add_sq_le (G : MarkovGame m S H A) (ρ : JointPolicy m S A) (i : Fin m)
    (E : ℕ) :
    ∀ k h, h + k = E →
      (∀ t, h ≤ t → t < h + k → ∀ s a, 0 ≤ G.reward i t s a ∧ G.reward i t s a ≤ 1) →
      ∀ s, evalJ G ρ (fun t s a => (G.transition t s a).variance
          (valueJ G ρ i (t + 1) (E - (t + 1)))) h k s + (valueJ G ρ i h k s) ^ 2 ≤ (k : ℝ) ^ 2 := by
  intro k
  induction k with
  | zero => intro h _ _ s; simp [valueJ, evalJ]
  | succ k ih =>
    intro h hk hR s
    have hRn : ∀ t, h + 1 ≤ t → t < h + 1 + k → ∀ s a,
        0 ≤ G.reward i t s a ∧ G.reward i t s a ≤ 1 := fun t ht1 ht2 => hR t (by omega) (by omega)
    have hnext := ih (h + 1) (by omega) hRn
    have hV := valueJ_mem_Icc G ρ i k (h + 1) hRn
    obtain rfl : k = E - (h + 1) := by omega
    set V := valueJ G ρ i (h + 1) (E - (h + 1)) with hVdef
    set kk : ℝ := ((E - (h + 1) : ℕ) : ℝ)
    set fv : ℕ → Fin S → JointAction m A → ℝ := fun t s a => (G.transition t s a).variance
          (valueJ G ρ i (t + 1) (E - (t + 1))) with hfv
    let q : JointAction m A → ℝ := fun a => G.reward i h s a + (G.transition h s a).expectation V
    have hval : valueJ G ρ i h (E - (h + 1) + 1) s = (ρ h s).expectation q := rfl
    have hjensen : ((ρ h s).expectation q) ^ 2 ≤ (ρ h s).expectation (fun a => q a ^ 2) := by
      have := FiniteDistribution.variance_nonneg (ρ h s) q
      unfold FiniteDistribution.variance at this
      linarith
    have hev : evalJ G ρ fv h (E - (h + 1) + 1) s ≤
        (ρ h s).expectation (fun a => kk ^ 2 - ((G.transition h s a).expectation V) ^ 2) := by
      simp only [evalJ]
      refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ ((ρ h s).prob_nonneg a)
      have h1 : (G.transition h s a).expectation (evalJ G ρ fv (h + 1) (E - (h + 1))) ≤
          (G.transition h s a).expectation (fun x => kk ^ 2 - V x ^ 2) :=
        FiniteDistribution.expectation_mono _ fun x => by
          have := hnext x
          linarith
      rw [FiniteDistribution.expectation_sub, FiniteDistribution.expectation_const] at h1
      have hvar : fv h s a = (G.transition h s a).expectation (fun x => V x ^ 2) -
          ((G.transition h s a).expectation V) ^ 2 := rfl
      rw [hvar]
      linarith
    rw [hval]
    have hpt : ∀ a, kk ^ 2 - ((G.transition h s a).expectation V) ^ 2 + q a ^ 2 ≤
        (((E - (h + 1) + 1 : ℕ)) : ℝ) ^ 2 := by
      intro a
      have hr := hR h le_rfl (by omega) s a
      have hPV0 : 0 ≤ (G.transition h s a).expectation V :=
        FiniteDistribution.expectation_nonneg _ fun x => (hV x).1
      have hPV1 : (G.transition h s a).expectation V ≤ kk :=
        FiniteDistribution.expectation_le_const _ fun x => (hV x).2
      simp only [q]
      push_cast
      nlinarith
    have hsum : (ρ h s).expectation (fun a => kk ^ 2 - ((G.transition h s a).expectation V) ^ 2) +
        (ρ h s).expectation (fun a => q a ^ 2) ≤ (((E - (h + 1) + 1 : ℕ)) : ℝ) ^ 2 := by
      rw [← FiniteDistribution.expectation_add]
      exact FiniteDistribution.expectation_le_const _ hpt
    linarith

/-- AM-GM in the form used for the Bernstein square-root term. -/
theorem sqrt_mul_sqrt_le_amgm (L Nr v lam : ℝ) (hL : 0 ≤ L) (hN : 0 < Nr) (hv : 0 ≤ v)
    (hlam : 0 < lam) :
    Real.sqrt (2 * L / Nr) * Real.sqrt v ≤ lam / 2 * v + L / (lam * Nr) := by
  set b := Real.sqrt (2 * L / Nr)
  set a := Real.sqrt v
  have hb : b ^ 2 = 2 * L / Nr := Real.sq_sqrt (by positivity)
  have ha : a ^ 2 = v := Real.sq_sqrt hv
  have key : 2 * lam * (a * b) ≤ lam ^ 2 * a ^ 2 + b ^ 2 := by nlinarith [sq_nonneg (lam * a - b)]
  have hLN : L / (lam * Nr) = b ^ 2 / (2 * lam) := by
    rw [hb]; field_simp
  rw [hLN, ← ha]
  rw [show b * a = a * b by ring]
  have h2 : a * b ≤ (lam ^ 2 * a ^ 2 + b ^ 2) / (2 * lam) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  calc a * b ≤ (lam ^ 2 * a ^ 2 + b ^ 2) / (2 * lam) := h2
    _ = lam / 2 * a ^ 2 + b ^ 2 / (2 * lam) := by field_simp

/-- Self-bounding policy-evaluation error (deterministic; the concentration event is a
hypothesis). -/
theorem selfBound (G Ĝ : MarkovGame m S H A) (ρ : JointPolicy m S A) (i : Fin m)
    (hr : ∀ t, Ĝ.reward i t = G.reward i t)
    (hR : ∀ t, 1 ≤ t → t ≤ H → ∀ s a, 0 ≤ G.reward i t s a ∧ G.reward i t s a ≤ 1)
    (L Nr : ℝ) (hL : 0 ≤ L) (hN : 0 < Nr)
    (hev : ∀ t, 1 ≤ t → t ≤ H → ∀ s a,
      |(Ĝ.transition t s a).expectation (valueJ Ĝ ρ i (t + 1) (H + 1 - (t + 1))) -
          (G.transition t s a).expectation (valueJ Ĝ ρ i (t + 1) (H + 1 - (t + 1)))| ≤
        Real.sqrt (2 * L / Nr) *
            Real.sqrt ((G.transition t s a).variance (valueJ Ĝ ρ i (t + 1) (H + 1 - (t + 1)))) +
          2 * H * L / (3 * Nr))
    (hx : H * Real.sqrt (2 * L / Nr) ≤ 1 / 2) (lam : ℝ) (hlam : 0 < lam) (s : Fin S) :
    |valueJ Ĝ ρ i 1 H s - valueJ G ρ i 1 H s| ≤
      lam * H ^ 2 + 2 * H * L / (lam * Nr) + 4 / 3 * H ^ 2 * L / Nr := by
  classical
  set E := H + 1 with hE
  let D : ℕ → Fin S → ℝ := fun t s => valueJ Ĝ ρ i t (E - t) s - valueJ G ρ i t (E - t) s
  let e : ℝ := ⨆ p : Fin H × Fin S, |D ((p.1 : ℕ) + 1) p.2|
  have he0 : 0 ≤ e := Real.iSup_nonneg fun p => abs_nonneg _
  have hDe : ∀ t, 1 ≤ t → t ≤ H → ∀ s, |D t s| ≤ e := by
    intro t ht1 ht2 s
    have := le_ciSup (f := fun p : Fin H × Fin S => |D ((p.1 : ℕ) + 1) p.2|)
      (Set.finite_range _).bddAbove (⟨t - 1, by omega⟩, s)
    have ht : t - 1 + 1 = t := by omega
    simp only [ht] at this
    exact this
  have hnorm : ∀ t, 1 ≤ t → t ≤ H →
      ‖valueJ Ĝ ρ i (t + 1) (E - (t + 1)) - valueJ G ρ i (t + 1) (E - (t + 1))‖ ≤ e := by
    intro t ht1 ht2
    refine (pi_norm_le_iff_of_nonneg he0).mpr fun s => ?_
    rw [Real.norm_eq_abs]
    by_cases hlt : t + 1 ≤ H
    · exact hDe (t + 1) (by omega) hlt s
    · have h0 : E - (t + 1) = 0 := by omega
      simp only [Pi.sub_apply, h0, valueJ, sub_self, abs_zero]
      exact he0
  set b := Real.sqrt (2 * L / Nr)
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  set c : ℝ := L / (lam * Nr) + b * e + 2 * H * L / (3 * Nr)
  have hc0 : 0 ≤ c := by positivity
  -- the per-step error bound in affine form
  have hg : ∀ t, 1 ≤ t → t ≤ H → ∀ s a,
      |(Ĝ.transition t s a).expectation (valueJ Ĝ ρ i (t + 1) (E - (t + 1))) -
          (G.transition t s a).expectation (valueJ Ĝ ρ i (t + 1) (E - (t + 1)))| ≤
        lam / 2 * (G.transition t s a).variance (valueJ G ρ i (t + 1) (E - (t + 1))) + c := by
    intro t ht1 ht2 s a
    have h1 := hev t ht1 ht2 s a
    have htr := (abs_le.mp (FiniteDistribution.abs_sqrt_variance_sub_le_norm (G.transition t s a)
      (valueJ Ĝ ρ i (t + 1) (E - (t + 1))) (valueJ G ρ i (t + 1) (E - (t + 1))))).2
    have h2 := hnorm t ht1 ht2
    have hamgm := sqrt_mul_sqrt_le_amgm L Nr ((G.transition t s a).variance
      (valueJ G ρ i (t + 1) (E - (t + 1)))) lam hL hN
      (FiniteDistribution.variance_nonneg _ _) hlam
    have h3 : b * Real.sqrt ((G.transition t s a).variance (valueJ Ĝ ρ i (t + 1) (E - (t + 1)))) ≤
        b * Real.sqrt ((G.transition t s a).variance (valueJ G ρ i (t + 1) (E - (t + 1)))) +
          b * e := by
      rw [← mul_add]
      exact mul_le_mul_of_nonneg_left (by linarith) hb0
    simp only [c]
    linarith
  -- bound every `|D_t|`
  have hDt : ∀ t, 1 ≤ t → t ≤ H → ∀ s, |D t s| ≤ lam / 2 * (H : ℝ) ^ 2 + c * H := by
    intro t ht1 ht2 s
    have hk : t + (E - t) = E := by omega
    have h1 := abs_valueJ_sub_le_evalJ G Ĝ ρ i hr E (E - t) t hk s
    have h2 := evalJ_le_affine G ρ (fun t s a => (G.transition t s a).variance
        (valueJ G ρ i (t + 1) (E - (t + 1))))
      (fun t s a => |(Ĝ.transition t s a).expectation (valueJ Ĝ ρ i (t + 1) (E - (t + 1))) -
        (G.transition t s a).expectation (valueJ Ĝ ρ i (t + 1) (E - (t + 1)))|)
      (lam / 2) c (E - t) t
      (fun t' ht1' ht2' s a => hg t' (by omega) (by omega) s a) s
    have h3 := evalJ_variance_add_sq_le G ρ i E (E - t) t hk
      (fun t' ht1' ht2' s a => hR t' (by omega) (by omega) s a) s
    have hkH : ((E - t : ℕ) : ℝ) ≤ H := by exact_mod_cast (show E - t ≤ H by omega)
    have hk0 : (0 : ℝ) ≤ ((E - t : ℕ) : ℝ) := Nat.cast_nonneg _
    have hsq : ((E - t : ℕ) : ℝ) ^ 2 ≤ (H : ℝ) ^ 2 := by nlinarith
    have hev2 : evalJ G ρ (fun t s a => (G.transition t s a).variance
        (valueJ G ρ i (t + 1) (E - (t + 1)))) t (E - t) s ≤ (H : ℝ) ^ 2 := by
      nlinarith [sq_nonneg (valueJ G ρ i t (E - t) s)]
    have hlam2 : 0 ≤ lam / 2 := by positivity
    have hcH : c * ((E - t : ℕ) : ℝ) ≤ c * H := mul_le_mul_of_nonneg_left hkH hc0
    have : |D t s| ≤ lam / 2 * evalJ G ρ (fun t s a => (G.transition t s a).variance
        (valueJ G ρ i (t + 1) (E - (t + 1)))) t (E - t) s + c * ((E - t : ℕ) : ℝ) :=
      h1.trans h2
    nlinarith [mul_le_mul_of_nonneg_left hev2 hlam2]
  have heb : e ≤ lam / 2 * (H : ℝ) ^ 2 + c * H := by
    refine Real.iSup_le (fun p => hDt ((p.1 : ℕ) + 1) (by omega) (by omega) p.2) ?_
    positivity
  -- solve the self-bounding inequality
  have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg H
  have hxe : (H : ℝ) * b * e ≤ e / 2 := by
    have := mul_le_mul_of_nonneg_right hx he0
    linarith
  have hlamN : 0 < lam * Nr := mul_pos hlam hN
  have hesolve : e ≤ lam * H ^ 2 + 2 * H * L / (lam * Nr) + 4 / 3 * H ^ 2 * L / Nr := by
    have hce : c * H = L / (lam * Nr) * H + H * b * e + 2 * H * L / (3 * Nr) * H := by
      simp only [c]; ring
    have h1 : 2 * H * L / (lam * Nr) = 2 * (L / (lam * Nr) * H) := by ring
    have h2 : 4 / 3 * (H : ℝ) ^ 2 * L / Nr = 2 * (2 * H * L / (3 * Nr) * H) := by
      field_simp; ring
    rw [h1, h2]
    nlinarith
  -- conclude at step 1
  by_cases hH : 1 ≤ H
  · have h1 := hDe 1 le_rfl hH s
    have hE1 : E - 1 = H := by omega
    simp only [D, hE1] at h1
    exact h1.trans hesolve
  · have hH0' : H = 0 := by omega
    subst hH0'
    simp [valueJ]
end StatisticalRL.Ch7Rest.Marl76
