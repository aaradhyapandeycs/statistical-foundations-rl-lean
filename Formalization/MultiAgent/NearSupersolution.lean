import Formalization.MultiAgent.ModelBased.Evaluation
import Formalization.Probability.MixtureVariance

/-!
# Total variance of near-supersolutions in Markov games

The generic mixture-variance facts are in `Formalization/Probability/MixtureVariance.lean`.
Markov-game facts, for a joint policy `ρ`, player `i` and an arbitrary `f : ℕ → Fin S → ℝ`:
* `bellJ G ρ i f t s = E_{a∼ρ_t(s)}[r_{i,t}(s,a) + P_t(s,a)·f_{t+1}]`;
* `jvarJ G ρ i f t s`: the variance of `r_{i,t}(s,a) + f_{t+1}(s')` over the joint law of
  `(a, s')`, `a ∼ ρ_t(s)`, `s′ ∼ P_t(·|s,a)`;
* `evalJ` linearity, monotonicity and telescoping;
* `evalJ_jvarJ_le` (F3): if `1 ≤ H`, `0 ≤ f_t ≤ H` for `t ∈ [1,H]`, `f_{H+1} = 0` and
  `r_{i,t} ∈ [0,1]` for `t ∈ [1,H]`, then
  `Eval_ρ(v)_1(s) ≤ 5H² + 2H·Eval_ρ(Δ⁻)_1(s)` with `Δ_t = f_t − bellJ_t`, `Δ⁻ = max(−Δ, 0)`.
-/

open scoped BigOperators
open Finset

namespace StatisticalRL.Ch7Rest.Marl77

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.Ch7Rest.Marl76

/-! ### Bellman operator and joint variance -/

variable {m S H : ℕ} {A : Fin m → ℕ}

/-- `E_{a∼ρ_t(s)}[r_{i,t}(s,a) + P_t(s,a)·f_{t+1}]`. -/
noncomputable def bellJ (G : MarkovGame m S H A) (ρ : JointPolicy m S A) (i : Fin m)
    (f : ℕ → Fin S → ℝ) (t : ℕ) (s : Fin S) : ℝ :=
  ∑ a, (ρ t s).prob a * (G.reward i t s a + (G.transition t s a).expectation (f (t + 1)))

/-- Variance of `r_{i,t}(s,a) + f_{t+1}(s')` over `a ∼ ρ_t(s)`, `s' ∼ P_t(·|s,a)`. -/
noncomputable def jvarJ (G : MarkovGame m S H A) (ρ : JointPolicy m S A) (i : Fin m)
    (f : ℕ → Fin S → ℝ) (t : ℕ) (s : Fin S) : ℝ :=
  ∑ a, (ρ t s).prob a * (G.transition t s a).expectation
    (fun s' => (G.reward i t s a + f (t + 1) s' - bellJ G ρ i f t s) ^ 2)

theorem jvarJ_nonneg (G : MarkovGame m S H A) (ρ : JointPolicy m S A) (i : Fin m)
    (f : ℕ → Fin S → ℝ) (t : ℕ) (s : Fin S) : 0 ≤ jvarJ G ρ i f t s :=
  sum_nonneg fun a _ => mul_nonneg ((ρ t s).prob_nonneg a)
    (FiniteDistribution.expectation_nonneg _ fun _ => sq_nonneg _)

/-! ### `evalJ` algebra -/

theorem evalJ_add (G : MarkovGame m S H A) (ρ : JointPolicy m S A)
    (f g : ℕ → Fin S → JointAction m A → ℝ) :
    ∀ k h s, evalJ G ρ (fun t s a => f t s a + g t s a) h k s =
      evalJ G ρ f h k s + evalJ G ρ g h k s := by
  intro k
  induction k with
  | zero => intro h s; simp [evalJ]
  | succ k ih =>
    intro h s
    simp only [evalJ]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun a _ => ?_
    have : evalJ G ρ (fun t s a => f t s a + g t s a) (h + 1) k =
        fun s' => evalJ G ρ f (h + 1) k s' + evalJ G ρ g (h + 1) k s' := funext fun s' => ih _ _
    rw [this, FiniteDistribution.expectation_add]
    ring

theorem evalJ_smul (G : MarkovGame m S H A) (ρ : JointPolicy m S A)
    (f : ℕ → Fin S → JointAction m A → ℝ) (c : ℝ) :
    ∀ k h s, evalJ G ρ (fun t s a => c * f t s a) h k s = c * evalJ G ρ f h k s := by
  intro k
  induction k with
  | zero => intro h s; simp [evalJ]
  | succ k ih =>
    intro h s
    simp only [evalJ]
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    have : evalJ G ρ (fun t s a => c * f t s a) (h + 1) k =
        fun s' => c * evalJ G ρ f (h + 1) k s' := funext fun s' => ih _ _
    rw [this, FiniteDistribution.expectation_mul]
    ring

theorem evalJ_mono (G : MarkovGame m S H A) (ρ : JointPolicy m S A)
    (f g : ℕ → Fin S → JointAction m A → ℝ) :
    ∀ k h, (∀ t, h ≤ t → t < h + k → ∀ s a, f t s a ≤ g t s a) →
      ∀ s, evalJ G ρ f h k s ≤ evalJ G ρ g h k s := by
  intro k h hfg s
  have := evalJ_le_affine G ρ g f 1 0 k h (fun t h1 h2 s a => by simpa using hfg t h1 h2 s a) s
  simpa using this

theorem evalJ_nonneg (G : MarkovGame m S H A) (ρ : JointPolicy m S A)
    (f : ℕ → Fin S → JointAction m A → ℝ) :
    ∀ k h, (∀ t, h ≤ t → t < h + k → ∀ s a, 0 ≤ f t s a) → ∀ s, 0 ≤ evalJ G ρ f h k s := by
  intro k h hf s
  have := evalJ_mono G ρ (fun _ _ _ => 0) f k h hf s
  have h0 : ∀ k h s, evalJ G ρ (fun _ _ _ => (0 : ℝ)) h k s = 0 := by
    intro k
    induction k with
    | zero => intro h s; simp [evalJ]
    | succ k ih =>
      intro h s
      simp only [evalJ]
      have : evalJ G ρ (fun _ _ _ => (0 : ℝ)) (h + 1) k = fun _ => 0 := funext fun s' => ih _ _
      rw [this]; simp
  rw [h0] at this
  exact this

theorem evalJ_le_const (G : MarkovGame m S H A) (ρ : JointPolicy m S A)
    (f : ℕ → Fin S → JointAction m A → ℝ) (c : ℝ) :
    ∀ k h, (∀ t, h ≤ t → t < h + k → ∀ s a, f t s a ≤ c) → ∀ s, evalJ G ρ f h k s ≤ c * k := by
  intro k h hf s
  have := evalJ_le_affine G ρ (fun _ _ _ => 0) f 0 c k h
    (fun t h1 h2 s a => by simpa using hf t h1 h2 s a) s
  simpa using this

/-- Telescoping: `Eval_ρ(P F_{next} − F)_h = −F_h` when `F_{h+k} = 0`. -/
theorem evalJ_telescope (G : MarkovGame m S H A) (ρ : JointPolicy m S A) (F : ℕ → Fin S → ℝ) :
    ∀ k h, (∀ s, F (h + k) s = 0) → ∀ s,
      evalJ G ρ (fun t s a => (G.transition t s a).expectation (F (t + 1)) - F t s) h k s =
        -F h s := by
  intro k
  induction k with
  | zero =>
    intro h hF s
    have := hF s
    simp only [add_zero] at this
    simp [evalJ, this]
  | succ k ih =>
    intro h hF s
    have hnext : evalJ G ρ (fun t s a => (G.transition t s a).expectation (F (t + 1)) - F t s)
        (h + 1) k = fun s' => -F (h + 1) s' :=
      funext fun s' => ih (h + 1) (fun s'' => by rw [show h + 1 + k = h + (k + 1) by omega]; exact hF s'') s'
    simp only [evalJ]
    rw [hnext]
    have : ∀ a, (G.transition h s a).expectation (F (h + 1)) - F h s +
        (G.transition h s a).expectation (fun s' => -F (h + 1) s') = -F h s := by
      intro a
      have := FiniteDistribution.expectation_mul (G.transition h s a) (-1) (F (h + 1))
      simp only [neg_one_mul] at this
      rw [this]; ring
    simp_rw [this]
    rw [← sum_mul, (ρ h s).sum_prob, one_mul]

/-! ### F3: total variance of a near-supersolution -/

/-- Per-step inequality behind F3: with `Δ = f_t − bellJ_t`,
`v_t ≤ E_ρ[r(1 + 2 P f_{t+1}) + P f_{t+1}²] − f_t² + 2 f_t Δ`. -/
theorem jvarJ_le_step (G : MarkovGame m S H A) (ρ : JointPolicy m S A) (i : Fin m)
    (f : ℕ → Fin S → ℝ) (t : ℕ) (s : Fin S)
    (hr : ∀ a, 0 ≤ G.reward i t s a ∧ G.reward i t s a ≤ 1) :
    jvarJ G ρ i f t s ≤ ∑ a, (ρ t s).prob a *
        (G.reward i t s a * (1 + 2 * (G.transition t s a).expectation (f (t + 1))) +
          (G.transition t s a).expectation (fun s' => f (t + 1) s' ^ 2)) -
      f t s ^ 2 + 2 * f t s * (f t s - bellJ G ρ i f t s) := by
  set B := bellJ G ρ i f t s with hB
  -- expand the square inside each expectation
  have hexp : ∀ a, (G.transition t s a).expectation
      (fun s' => (G.reward i t s a + f (t + 1) s' - B) ^ 2) =
      G.reward i t s a ^ 2 + 2 * G.reward i t s a * (G.transition t s a).expectation (f (t + 1)) +
        (G.transition t s a).expectation (fun s' => f (t + 1) s' ^ 2) -
        2 * B * (G.reward i t s a + (G.transition t s a).expectation (f (t + 1))) + B ^ 2 := by
    intro a
    simp only [FiniteDistribution.expectation]
    have h1 : ∀ s', (G.transition t s a).prob s' * (G.reward i t s a + f (t + 1) s' - B) ^ 2 =
        (G.reward i t s a ^ 2 - 2 * B * G.reward i t s a + B ^ 2) * (G.transition t s a).prob s' +
        (2 * G.reward i t s a - 2 * B) * ((G.transition t s a).prob s' * f (t + 1) s') +
        (G.transition t s a).prob s' * f (t + 1) s' ^ 2 := fun s' => by ring
    simp_rw [h1]
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, (G.transition t s a).sum_prob]
    ring
  have hjv : jvarJ G ρ i f t s = ∑ a, (ρ t s).prob a *
      (G.reward i t s a ^ 2 + 2 * G.reward i t s a * (G.transition t s a).expectation (f (t + 1)) +
        (G.transition t s a).expectation (fun s' => f (t + 1) s' ^ 2)) - B ^ 2 := by
    unfold jvarJ
    rw [← hB]
    simp_rw [hexp]
    have h2 : ∀ a, (ρ t s).prob a * (G.reward i t s a ^ 2 + 2 * G.reward i t s a *
        (G.transition t s a).expectation (f (t + 1)) +
        (G.transition t s a).expectation (fun s' => f (t + 1) s' ^ 2) -
        2 * B * (G.reward i t s a + (G.transition t s a).expectation (f (t + 1))) + B ^ 2) =
        (ρ t s).prob a * (G.reward i t s a ^ 2 + 2 * G.reward i t s a *
          (G.transition t s a).expectation (f (t + 1)) +
          (G.transition t s a).expectation (fun s' => f (t + 1) s' ^ 2)) -
        2 * B * ((ρ t s).prob a * (G.reward i t s a + (G.transition t s a).expectation (f (t + 1))))
        + B ^ 2 * (ρ t s).prob a := fun a => by ring
    simp_rw [h2]
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, (ρ t s).sum_prob]
    rw [show ∑ a, (ρ t s).prob a * (G.reward i t s a + (G.transition t s a).expectation (f (t + 1)))
      = B from rfl]
    ring
  rw [hjv]
  have hr2 : ∑ a, (ρ t s).prob a *
      (G.reward i t s a ^ 2 + 2 * G.reward i t s a * (G.transition t s a).expectation (f (t + 1)) +
        (G.transition t s a).expectation (fun s' => f (t + 1) s' ^ 2)) ≤
      ∑ a, (ρ t s).prob a *
        (G.reward i t s a * (1 + 2 * (G.transition t s a).expectation (f (t + 1))) +
          (G.transition t s a).expectation (fun s' => f (t + 1) s' ^ 2)) := by
    refine sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ ((ρ t s).prob_nonneg a)
    have := hr a
    nlinarith
  nlinarith [sq_nonneg (f t s - B)]

/-- Policy evaluation of a state-only integrand is dominated by that of an action-dependent one whose
`ρ`-average dominates it. -/
theorem evalJ_state_le (G : MarkovGame m S H A) (ρ : JointPolicy m S A) (v : ℕ → Fin S → ℝ)
    (g : ℕ → Fin S → JointAction m A → ℝ) :
    ∀ k h, (∀ t, h ≤ t → t < h + k → ∀ s, v t s ≤ ∑ a, (ρ t s).prob a * g t s a) →
      ∀ s, evalJ G ρ (fun t s _ => v t s) h k s ≤ evalJ G ρ g h k s := by
  intro k
  induction k with
  | zero => intro h _ s; simp [evalJ]
  | succ k ih =>
    intro h hv s
    have hnext := ih (h + 1) (fun t h1 h2 => hv t (by omega) (by omega))
    simp only [evalJ]
    calc ∑ a, (ρ h s).prob a * (v h s + (G.transition h s a).expectation
          (evalJ G ρ (fun t s _ => v t s) (h + 1) k))
        = (∑ a, (ρ h s).prob a) * v h s + ∑ a, (ρ h s).prob a * (G.transition h s a).expectation
          (evalJ G ρ (fun t s _ => v t s) (h + 1) k) := by
          rw [sum_mul, ← sum_add_distrib]; refine sum_congr rfl fun a _ => by ring
      _ = v h s + ∑ a, (ρ h s).prob a * (G.transition h s a).expectation
          (evalJ G ρ (fun t s _ => v t s) (h + 1) k) := by rw [(ρ h s).sum_prob, one_mul]
      _ ≤ ∑ a, (ρ h s).prob a * g h s a + ∑ a, (ρ h s).prob a * (G.transition h s a).expectation
          (evalJ G ρ g (h + 1) k) :=
          add_le_add (hv h le_rfl (by omega) s) (sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
            (FiniteDistribution.expectation_mono _ hnext) ((ρ h s).prob_nonneg a))
      _ = _ := by rw [← sum_add_distrib]; refine sum_congr rfl fun a _ => by ring

/-- F3: total variance of a near-supersolution. -/
theorem evalJ_jvarJ_le (G : MarkovGame m S H A) (ρ : JointPolicy m S A) (i : Fin m)
    (f : ℕ → Fin S → ℝ) (hH : 1 ≤ H)
    (hf : ∀ t, 1 ≤ t → t ≤ H → ∀ s, 0 ≤ f t s ∧ f t s ≤ H) (hfH : ∀ s, f (H + 1) s = 0)
    (hr : ∀ t, 1 ≤ t → t ≤ H → ∀ s a, 0 ≤ G.reward i t s a ∧ G.reward i t s a ≤ 1) (s : Fin S) :
    evalJ G ρ (fun t s _ => jvarJ G ρ i f t s) 1 H s ≤
      5 * (H : ℝ) ^ 2 +
        2 * H * evalJ G ρ (fun t s _ => max (-(f t s - bellJ G ρ i f t s)) 0) 1 H s := by
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hH
  let g1 : ℕ → Fin S → JointAction m A → ℝ := fun t s a =>
    G.reward i t s a * (1 + 2 * (G.transition t s a).expectation (f (t + 1)))
  let g2 : ℕ → Fin S → JointAction m A → ℝ := fun t s a =>
    (G.transition t s a).expectation (fun s' => f (t + 1) s' ^ 2) - f t s ^ 2
  let g3 : ℕ → Fin S → JointAction m A → ℝ := fun t s a =>
    (G.transition t s a).expectation (f (t + 1)) - f t s
  let gR : ℕ → Fin S → JointAction m A → ℝ := fun t s a => G.reward i t s a
  let gD : ℕ → Fin S → JointAction m A → ℝ := fun t s _ => max (-(f t s - bellJ G ρ i f t s)) 0
  let c : ℝ := -(2 * H)
  let gA : ℕ → Fin S → JointAction m A → ℝ := fun t s a => g1 t s a + g2 t s a
  let gB : ℕ → Fin S → JointAction m A → ℝ := fun t s a => gA t s a + c * g3 t s a
  let gC : ℕ → Fin S → JointAction m A → ℝ := fun t s a => gB t s a + c * gR t s a
  let gAll : ℕ → Fin S → JointAction m A → ℝ := fun t s a => gC t s a + (2 * H) * gD t s a
  -- step comparison
  have hstep : ∀ t, 1 ≤ t → t < 1 + H → ∀ s,
      jvarJ G ρ i f t s ≤ ∑ a, (ρ t s).prob a * gAll t s a := by
    intro t ht1 ht2 s
    have htH : t ≤ H := by omega
    have hv := jvarJ_le_step G ρ i f t s (fun a => hr t ht1 htH s a)
    have hfh := hf t ht1 htH s
    have havg : ∑ a, (ρ t s).prob a * gAll t s a =
        ∑ a, (ρ t s).prob a * (G.reward i t s a * (1 + 2 * (G.transition t s a).expectation
          (f (t + 1))) + (G.transition t s a).expectation (fun s' => f (t + 1) s' ^ 2)) -
        f t s ^ 2 + 2 * H * (f t s - bellJ G ρ i f t s) + 2 * H * max (-(f t s - bellJ G ρ i f t s)) 0 := by
      have e1 : ∀ a, (ρ t s).prob a * gAll t s a =
          (ρ t s).prob a * (G.reward i t s a * (1 + 2 * (G.transition t s a).expectation
            (f (t + 1))) + (G.transition t s a).expectation (fun s' => f (t + 1) s' ^ 2)) +
          (-(f t s ^ 2) + 2 * H * f t s + 2 * H * max (-(f t s - bellJ G ρ i f t s)) 0) * (ρ t s).prob a -
          2 * H * ((ρ t s).prob a * (G.reward i t s a +
            (G.transition t s a).expectation (f (t + 1)))) := by
        intro a
        simp only [gAll, gC, gB, gA, g1, g2, g3, gR, gD, c]
        ring
      simp_rw [e1]
      rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, (ρ t s).sum_prob]
      unfold bellJ
      ring
    have hD : 2 * f t s * (f t s - bellJ G ρ i f t s) ≤
        2 * H * (f t s - bellJ G ρ i f t s) + 2 * H * max (-(f t s - bellJ G ρ i f t s)) 0 := by
      rcases le_total 0 (f t s - bellJ G ρ i f t s) with hpos | hneg
      · rw [max_eq_right (by linarith)]
        nlinarith
      · rw [max_eq_left (by linarith)]
        nlinarith
    rw [havg]
    linarith
  have hcmp := evalJ_state_le G ρ (fun t s => jvarJ G ρ i f t s) gAll H 1 hstep s
  -- linearity
  have l1 := evalJ_add G ρ gC (fun t s a => (2 * H) * gD t s a) H 1 s
  have l2 := evalJ_smul G ρ gD (2 * H) H 1 s
  have l3 := evalJ_add G ρ gB (fun t s a => c * gR t s a) H 1 s
  have l4 := evalJ_smul G ρ gR c H 1 s
  have l5 := evalJ_add G ρ gA (fun t s a => c * g3 t s a) H 1 s
  have l6 := evalJ_smul G ρ g3 c H 1 s
  have l7 := evalJ_add G ρ g1 g2 H 1 s
  -- the pieces
  have hfH' : ∀ s, f (1 + H) s = 0 := fun s => by rw [add_comm]; exact hfH s
  have p2 : evalJ G ρ g2 1 H s = -(f 1 s ^ 2) :=
    evalJ_telescope G ρ (fun t s => f t s ^ 2) H 1 (fun s => by simp [hfH' s]) s
  have p3 : evalJ G ρ g3 1 H s = -f 1 s := evalJ_telescope G ρ f H 1 hfH' s
  have pR : 0 ≤ evalJ G ρ gR 1 H s :=
    evalJ_nonneg G ρ gR H 1 (fun t h1 h2 s a => (hr t h1 (by omega) s a).1) s
  have p1 : evalJ G ρ g1 1 H s ≤ (1 + 2 * H) * H := by
    refine evalJ_le_const G ρ g1 (1 + 2 * H) H 1 (fun t h1 h2 s a => ?_) s
    have hra := hr t h1 (by omega) s a
    have hPf0 : 0 ≤ (G.transition t s a).expectation (f (t + 1)) := by
      rcases Nat.lt_or_ge (t + 1) (H + 1) with hlt | hge
      · exact FiniteDistribution.expectation_nonneg _ fun s' => (hf (t + 1) (by omega) (by omega) s').1
      · have : t + 1 = H + 1 := by omega
        rw [this]; exact FiniteDistribution.expectation_nonneg _ fun s' => by rw [hfH s']
    have hPf1 : (G.transition t s a).expectation (f (t + 1)) ≤ H := by
      rcases Nat.lt_or_ge (t + 1) (H + 1) with hlt | hge
      · exact FiniteDistribution.expectation_le_const _ fun s' => (hf (t + 1) (by omega) (by omega) s').2
      · have : t + 1 = H + 1 := by omega
        rw [this]; exact FiniteDistribution.expectation_le_const _ fun s' => by rw [hfH s']; positivity
    simp only [g1]
    nlinarith
  have hf1 := hf 1 le_rfl hH s
  have hgD : evalJ G ρ gD 1 H s =
      evalJ G ρ (fun t s _ => max (-(f t s - bellJ G ρ i f t s)) 0) 1 H s := rfl
  rw [← hgD]
  have : evalJ G ρ gAll 1 H s = evalJ G ρ g1 1 H s + evalJ G ρ g2 1 H s + c * evalJ G ρ g3 1 H s +
      c * evalJ G ρ gR 1 H s + 2 * H * evalJ G ρ gD 1 H s := by
    rw [show gAll = fun t s a => gC t s a + (2 * H) * gD t s a from rfl, l1, l2,
      show gC = fun t s a => gB t s a + c * gR t s a from rfl, l3, l4,
      show gB = fun t s a => gA t s a + c * g3 t s a from rfl, l5, l6,
      show gA = fun t s a => g1 t s a + g2 t s a from rfl, l7]
  rw [this, p2, p3] at hcmp
  simp only [c] at hcmp
  nlinarith

end StatisticalRL.Ch7Rest.Marl77
