import Formalization.OfflineRL.FiniteLCBQ.Supermart

/-!
# Finite-horizon LCB-Q: the probabilistic events (Step 2 of the plan)

Each event family is an instance of `markovG` (lemma G) with a one-step exponential bound:
* **E1** (`(h,s,a,n)`, both signs): symmetric-chord (Hoeffding-type) bound for the next-state
  value `V^k_{h+1}(s') ∈ [0,H]`; failure `e^{-ι}` each;
* **M1/M2** (`h`): change of measure from `d^b_h` to `d⋆_h` for predictable `[0,H]`-valued
  functions, with `e^{-y} ≤ 1 - y + y²` and `e^{y} ≤ 1 + y + y²` on `[0,1]`;
* **Cnt** (`(h,s)`): `E e^{X} ≤ e^{2 d^b}` for the visit indicator of `(h,s,π⋆_h(s))`.
-/

namespace StatisticalRL.LCBQFinite

open Finset MeasureTheory ProbabilityTheory OnlineRL StatisticalRL.FiniteVILCB

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
set_option linter.unusedSectionVars false

noncomputable local instance evDecS' : DecidableEq S := Classical.decEq S
noncomputable local instance evDecA' : DecidableEq A := Classical.decEq A

variable {H K : ℕ} (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
  (ρb ρ : FiniteDistribution S) (πs : Fin H → S → A) (cb L : ℝ) (sel : (A → ℝ) → A)
  (π₀ : Fin H → S → A)

/-- Product weight of a data set. -/
noncomputable def prodP (x : Fin K → Traj S A H) : ℝ := ∏ j, trajProb E πb ρb (x j)

theorem prodP_nonneg (x : Fin K → Traj S A H) : 0 ≤ prodP E πb ρb x :=
  prod_nonneg fun j _ ↦ trajProb_nonneg E πb ρb (x j)

theorem sum_occupancy (h : Fin H) : ∑ s, ∑ a, occupancy E πb ρb h s a = 1 := by
  have := sum_traj_triple E πb ρb h (fun _ _ _ ↦ 1)
  simp only [mul_one, FiniteDistribution.sum_prob] at this
  rw [← this, sum_trajProb]

/-- Lemma G specialised to functions of (iterate before episode `k`, trajectory `k`). -/
theorem markov_run (Φ : Fin K → Iterate S A H → Traj S A H → ℝ)
    (hΦ : ∀ (k : Fin K) (x : Fin K → Traj S A H), ∑ τ, trajProb E πb ρb τ *
      Real.exp (Φ k (it E cb L sel π₀ x k.val) τ) ≤ 1) (t : ℝ) :
    ∑ x : Fin K → Traj S A H, prodP E πb ρb x *
      (if t ≤ ∑ k, Φ k (it E cb L sel π₀ x k.val) (x k) then 1 else 0) ≤ Real.exp (-t) := by
  have hupd : ∀ (k : Fin K) (x : Fin K → Traj S A H) τ,
      it E cb L sel π₀ (Function.update x k τ) k.val = it E cb L sel π₀ x k.val := by
    intro k x τ
    refine (itr_congr cb L sel (rw' E) π₀ x (Function.update x k τ) k.val fun j hj ↦ ?_).symm
    rw [Function.update_of_ne (fun e ↦ by subst e; exact lt_irrefl _ hj)]
  refine markovG (fun τ ↦ trajProb E πb ρb τ) (fun τ ↦ trajProb_nonneg E πb ρb τ)
    (sum_trajProb E πb ρb) K (fun k x ↦ Φ k (it E cb L sel π₀ x k.val) (x k)) ?_ ?_ t
  · intro k x y hxy
    have := itr_congr cb L sel (rw' E) π₀ x y k.val fun j hj ↦ hxy j (le_of_lt hj)
    simp only [it] at this ⊢
    rw [this, hxy k le_rfl]
  · intro k x
    simp only [hupd, Function.update_self]
    exact hΦ k x

/-! ## Elementary exponential inequalities -/

theorem exp_le_quad {y : ℝ} (hy : |y| ≤ 1) : Real.exp y ≤ 1 + y + y ^ 2 := by
  have := Real.abs_exp_sub_one_sub_id_le hy
  have := (abs_le.1 this).2
  linarith

/-- Symmetric-chord bound for a centered bounded function under a finite distribution. -/
theorem chord_mgf (d : FiniteDistribution S) (f : S → ℝ) {B : ℝ} (hB : 0 < B)
    (hf : ∀ s, 0 ≤ f s ∧ f s ≤ B) (t : ℝ) :
    ∑ s, d.prob s * Real.exp (t * (d.expectation f - f s)) ≤ Real.exp (t ^ 2 * B ^ 2 / 2) := by
  have hE0 : 0 ≤ d.expectation f := d.expectation_nonneg fun s ↦ (hf s).1
  have hEB : d.expectation f ≤ B := d.expectation_le_const fun s ↦ (hf s).2
  have hx : ∀ s, |d.expectation f - f s| ≤ B := fun s ↦ abs_le.2
    ⟨by linarith [(hf s).2], by linarith [(hf s).1]⟩
  calc ∑ s, d.prob s * Real.exp (t * (d.expectation f - f s))
      ≤ ∑ s, d.prob s * (Real.cosh (t * B) + (Real.sinh (t * B) / B) * (d.expectation f - f s)) :=
        sum_le_sum fun s _ ↦ mul_le_mul_of_nonneg_left
          (azuma_exp_symmetric_chord B _ t hB (hx s)) (d.prob_nonneg s)
    _ = Real.cosh (t * B) := by
        have h1 : ∑ s, d.prob s * (d.expectation f - f s) = 0 := by
          simp only [mul_sub, sum_sub_distrib, ← sum_mul, d.sum_prob, one_mul]
          unfold FiniteDistribution.expectation; ring
        simp only [mul_add, sum_add_distrib, ← sum_mul, d.sum_prob, one_mul]
        rw [show ∑ s, d.prob s * (Real.sinh (t * B) / B * (d.expectation f - f s)) =
          Real.sinh (t * B) / B * ∑ s, d.prob s * (d.expectation f - f s) by
            rw [mul_sum]; refine sum_congr rfl fun s _ ↦ by ring, h1, mul_zero, add_zero]
    _ ≤ _ := azuma_cosh_bound B t

/-! ## E1 -/

variable (x : Fin K → Traj S A H)

/-- The E1 increment for `(h,s,a,n)`, sign `σ`, scale `λ`, as a function of the iterate before
the episode and the episode's stage-`h` triple `(s0,a0,s1)`. -/
noncomputable def psiE1 (h : Fin H) (s : S) (a : A) (n : ℕ) (σ lam : ℝ) (it : Iterate S A H)
    (s0 : S) (a0 : A) (s1 : S) : ℝ :=
  if s0 = s ∧ a0 = a then
    lam * σ * onlineQRateWeight H n (it.N h s a + 1) *
      (((E h).transition s a).expectation (nextV it h) - nextV it h s1) -
    lam ^ 2 * (H : ℝ) ^ 2 * (onlineQRateWeight H n (it.N h s a + 1)) ^ 2 / 2
  else 0

theorem nextV_mem (hcb : 0 ≤ cb) (k : ℕ) (h : Fin H) (t : S) :
    0 ≤ nextV (it E cb L sel π₀ x k) h t ∧ nextV (it E cb L sel π₀ x k) h t ≤ H := by
  refine ⟨nextV_nonneg cb L sel (rw' E) π₀ x k h t, ?_⟩
  unfold nextV
  split_ifs with hh
  · have := (le_bound (cb := cb) (L := L) (sel := sel) (r := rw' E) (π₀ := π₀) (x := x) hcb
      (fun h ↦ (E h).reward_le_one) k ⟨h.val + 1, hh⟩ t).2
    simp only at this
    have : (0 : ℝ) ≤ ((h.val + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    simp only [it]; push_cast at *; linarith
  · exact Nat.cast_nonneg H

/-- Generic one-step bound from a pointwise bound on the inner next-state sums. -/
theorem triple_step (h : Fin H) (ψ : S → A → S → ℝ)
    (hψ : ∀ s0 a0, ∑ s', ((E h).transition s0 a0).prob s' * Real.exp (ψ s0 a0 s') ≤ 1) :
    ∑ τ, trajProb E πb ρb τ * Real.exp (ψ (τ.1 h.castSucc) (τ.2 h) (τ.1 h.succ)) ≤ 1 := by
  rw [sum_traj_triple E πb ρb h (fun s0 a0 s1 ↦ Real.exp (ψ s0 a0 s1)), ← sum_occupancy E πb ρb h]
  exact sum_le_sum fun s0 _ ↦ sum_le_sum fun a0 _ ↦ by
    simpa using mul_le_mul_of_nonneg_left (hψ s0 a0) (occupancy_nonneg E πb ρb h s0 a0)

theorem psiE1_step (hH : 0 < H) (hcb : 0 ≤ cb) (h : Fin H) (s : S) (a : A) (n : ℕ) {σ : ℝ}
    (hσ : σ ^ 2 = 1) (lam : ℝ) (k : ℕ) (s0 : S) (a0 : A) :
    ∑ s', ((E h).transition s0 a0).prob s' *
      Real.exp (psiE1 E h s a n σ lam (it E cb L sel π₀ x k) s0 a0 s') ≤ 1 := by
  unfold psiE1
  by_cases hsa : s0 = s ∧ a0 = a
  · obtain ⟨rfl, rfl⟩ := hsa
    simp only [and_self, if_true]
    have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
    have hf := fun u ↦ nextV_mem E cb L sel π₀ x hcb k h u
    generalize onlineQRateWeight H n ((it E cb L sel π₀ x k).N h s0 a0 + 1) = ω
    generalize nextV (it E cb L sel π₀ x k) h = f at hf ⊢
    have hc := chord_mgf ((E h).transition s0 a0) f hH0 hf (lam * σ * ω)
    have key : ∀ s', Real.exp (lam * σ * ω * (((E h).transition s0 a0).expectation f - f s') -
        lam ^ 2 * (H : ℝ) ^ 2 * ω ^ 2 / 2) = Real.exp ((lam * σ * ω) *
          (((E h).transition s0 a0).expectation f - f s')) *
        Real.exp (-((lam * σ * ω) ^ 2 * (H : ℝ) ^ 2 / 2)) := by
      intro s'; rw [← Real.exp_add]; congr 1; rw [mul_pow, mul_pow, hσ]; ring
    simp only [key, ← mul_assoc]
    rw [← sum_mul]
    calc _ ≤ Real.exp ((lam * σ * ω) ^ 2 * (H : ℝ) ^ 2 / 2) *
          Real.exp (-((lam * σ * ω) ^ 2 * (H : ℝ) ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  · simp only [hsa, if_false, Real.exp_zero, mul_one, FiniteDistribution.sum_prob, le_refl]

/-- Sum of squared weights over the visits: `≤ 2H/n`. -/
theorem sq_weight_sum_le (hH : 0 < H) (h : Fin H) (s : S) (a : A) {n : ℕ} (hn : 0 < n) :
    ∑ j ∈ range K, (if vis x h s a j then
      (onlineQRateWeight H n (cnt (vis x h s a) j + 1)) ^ 2 else 0) ≤ 2 * (H : ℝ) / n := by
  rw [sum_range_visits (vis x h s a) (fun i ↦ (onlineQRateWeight H n (i + 1)) ^ 2) K]
  refine (sum_range_le_of_vanish (fun i ↦ (onlineQRateWeight H n (i + 1)) ^ 2)
    (fun i ↦ sq_nonneg _) n _ fun i hi ↦ ?_).trans ?_
  · simp only; rw [onlineQRateWeight_eq_zero_of_lt (by omega)]; ring
  · rw [sum_range_succ_shift (fun i ↦ (onlineQRateWeight H n i) ^ 2)]
    exact onlineQRateWeight_sq_sum_le H n hH hn

theorem vis_fin_iff (h : Fin H) (s : S) (a : A) (k : Fin K) :
    vis x h s a k.val ↔ (x k).1 h.castSucc = s ∧ (x k).2 h = a := by
  constructor
  · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨k.isLt, h1, h2⟩

theorem nxt_fin (h : Fin H) (k : Fin K) : nxt x h k.val = (x k).1 h.succ := by
  simp [nxt, k.isLt]

/-- The E1 sum is `λσ M_n - (λ²H²/2) Σ ω²`. -/
theorem sum_psiE1 (h : Fin H) (s : S) (a : A) (n : ℕ) (σ lam : ℝ) :
    ∑ k : Fin K, psiE1 E h s a n σ lam (it E cb L sel π₀ x k.val)
        ((x k).1 h.castSucc) ((x k).2 h) ((x k).1 h.succ) =
      lam * σ * mart E cb L sel π₀ x h s a n - lam ^ 2 * (H : ℝ) ^ 2 / 2 *
        ∑ j ∈ range K, (if vis x h s a j then
          (onlineQRateWeight H n (cnt (vis x h s a) j + 1)) ^ 2 else 0) := by
  unfold mart
  rw [mul_sum, mul_sum, ← sum_sub_distrib, ← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun k _ ↦ ?_
  unfold psiE1
  rw [N_eq_cnt cb L sel (rw' E) π₀ x h s a k.val]
  by_cases hv : (x k).1 h.castSucc = s ∧ (x k).2 h = a
  · have hv' := (vis_fin_iff x h s a k).2 hv
    rw [if_pos hv, if_pos hv', if_pos hv', nxt_fin]
    simp only [Vn]; ring
  · have hv' : ¬ vis x h s a k.val := fun h' ↦ hv ((vis_fin_iff x h s a k).1 h')
    rw [if_neg hv, if_neg hv', if_neg hv']; ring

/-- **E1 tail**: `P(σ M_n ≥ 2√(H³ι/n)) ≤ e^{-ι}`. -/
theorem e1_tail (hH : 0 < H) (hcb : 0 ≤ cb) (h : Fin H) (s : S) (a : A) {n : ℕ} (hn : 0 < n)
    {σ : ℝ} (hσ : σ ^ 2 = 1) {ι : ℝ} (hι : 0 < ι) :
    ∑ x : Fin K → Traj S A H, prodP E πb ρb x *
      (if 2 * Real.sqrt ((H : ℝ) ^ 3 * ι / n) ≤ σ * mart E cb L sel π₀ x h s a n then 1 else 0)
      ≤ Real.exp (-ι) := by
  have hH0 : (0 : ℝ) < H := by exact_mod_cast hH
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set lam := Real.sqrt (n * ι / (H : ℝ) ^ 3)
  have hlam : 0 < lam := Real.sqrt_pos.2 (by positivity)
  have hmk := markov_run (K := K) E πb ρb cb L sel π₀
    (fun _ it τ ↦ psiE1 E h s a n σ lam it (τ.1 h.castSucc) (τ.2 h) (τ.1 h.succ))
    (fun k x ↦ triple_step E πb ρb h _ fun s0 a0 ↦
      psiE1_step E cb L sel π₀ x hH hcb h s a n hσ lam k.val s0 a0) ι
  refine le_trans (sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left ?_ (prodP_nonneg E πb ρb x)) hmk
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exfalso; apply h2
    rw [sum_psiE1]
    have hsq := sq_weight_sum_le x hH h s a (K := K) hn
    -- λ·2√(H³ι/n) - λ²H²/2·(2H/n) = ι
    have hkey : lam * (2 * Real.sqrt ((H : ℝ) ^ 3 * ι / n)) - lam ^ 2 * (H : ℝ) ^ 2 / 2 *
        (2 * (H : ℝ) / n) = ι := by
      have e1 : lam * Real.sqrt ((H : ℝ) ^ 3 * ι / n) = ι := by
        simp only [lam]
        rw [← Real.sqrt_mul (by positivity)]
        have : n * ι / (H : ℝ) ^ 3 * ((H : ℝ) ^ 3 * ι / n) = ι ^ 2 := by field_simp
        rw [this, Real.sqrt_sq hι.le]
      have e2 : lam ^ 2 = n * ι / (H : ℝ) ^ 3 := Real.sq_sqrt (by positivity)
      rw [e2]
      have e3 : n * ι / (H : ℝ) ^ 3 * (H : ℝ) ^ 2 / 2 * (2 * H / n) = ι := by field_simp
      linarith
    have hA : lam * (2 * Real.sqrt ((H : ℝ) ^ 3 * ι / n)) ≤ lam * (σ * mart E cb L sel π₀ x h s a n) :=
      mul_le_mul_of_nonneg_left h1 hlam.le
    have hB : lam ^ 2 * (H : ℝ) ^ 2 / 2 * ∑ j ∈ range K, (if vis x h s a j then
        (onlineQRateWeight H n (cnt (vis x h s a) j + 1)) ^ 2 else 0) ≤
        lam ^ 2 * (H : ℝ) ^ 2 / 2 * (2 * (H : ℝ) / n) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have : lam * σ * mart E cb L sel π₀ x h s a n = lam * (σ * mart E cb L sel π₀ x h s a n) := by ring
    linarith
  · positivity
  · exact le_rfl

end StatisticalRL.LCBQFinite
