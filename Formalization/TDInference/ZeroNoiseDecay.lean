import Formalization.TDInference.Kernel

/-!
# Theorem 7.11 support (M8): second-moment decay of the zero-noise TD recursion

Source: `chapters/inference.tex:52–64` (i.i.d. sampling), :72 (update), :104–117 (`A`), :134
(`η_t = η₀ t^{-2/3}`). Library infrastructure for the leave-one-out step (route D-half, H3, of the
corrected-7.11 plan); no source result is claimed.

The difference of two TD runs driven by the same samples after a time `m` obeys the *zero-noise*
recursion `δ' = δ − η A_x δ` (`zeroNoiseStep`), coordinatewise

  `δ'(s) = (1−η)δ(s) + ηγ δ(s')` if `s = x.1`, and `δ'(s) = δ(s)` otherwise.

The random maps `I − ηA_x` are only sup-norm *nonexpansive*, so a pathwise contraction is not
available; instead the **max-coordinate second-moment mechanism** of `tdSecondMoment_succ_le`
(Jensen on the convex combination, then averaging the sampled state) gives, with noise `0`,

  `max_s E δ_{t+1}(s)² ≤ (1 − μmin(1−γ)η'_t) max_s E δ_t(s)²`.

Main results:
* `sum_pathWeight_mul_eq_sum_update`: on the product path law, `E g = E ∑ₓ p(x) g(ω[k ↦ x])`
  (resampling one coordinate), for every path functional `g`.
* `sum_tupleProb_mul_sq_zeroNoiseStep_le`: the one-step conditional bound.
* `secondMoment_zeroNoiseStep_le`: the one-step bound in expectation, for any `δ` not depending on
  the coordinate `k` that drives the step.
* `max_secondMoment_zeroNoise_le`: iterated, `E δ_t(s)² ≤ p_{m,t} Q` for `m ≤ t ≤ T` with
  `p_{m,t} = ∏_{j∈[m,t)} (1 − μmin(1−γ)η'_j)` (`contrProd`), whenever `E δ_m(s)² ≤ Q` for all `s`.
-/

open Finset Matrix
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.Probability StatisticalRL.Analysis

variable {State Action : Type} [Fintype State] [Fintype Action]

/-! ## Resampling one coordinate of the product path law -/

theorem pathWeight_update_mul (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {T : ℕ} (ω : Fin T → Tuple State Action) (k : Fin T)
    (x : Tuple State Action) :
    pathWeight M π μ (Function.update ω k x) * tupleProb M π μ (ω k) =
      pathWeight M π μ ω * tupleProb M π μ x := by
  have h : ∀ ω' : Fin T → Tuple State Action, pathWeight M π μ ω' =
      tupleProb M π μ (ω' k) * ∏ t ∈ univ.erase k, tupleProb M π μ (ω' t) := fun ω' ↦
    (mul_prod_erase univ (fun t ↦ tupleProb M π μ (ω' t)) (mem_univ k)).symm
  have hr : ∏ t ∈ univ.erase k, tupleProb M π μ (Function.update ω k x t) =
      ∏ t ∈ univ.erase k, tupleProb M π μ (ω t) :=
    prod_congr rfl fun t ht ↦ by rw [Function.update_of_ne (ne_of_mem_erase ht)]
  rw [h (Function.update ω k x), h ω, hr, Function.update_self]
  ring

/-- **Resampling identity.** On the i.i.d. path law, replacing coordinate `k` by an independent
draw does not change expectations: `E g = E ∑ₓ p(x) g(ω[k ↦ x])`. -/
theorem sum_pathWeight_mul_eq_sum_update (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {T : ℕ} (k : Fin T)
    (g : (Fin T → Tuple State Action) → ℝ) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * g ω =
      ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        ∑ x, tupleProb M π μ x * g (Function.update ω k x) := by
  have hinv : Function.Involutive (fun p : (Fin T → Tuple State Action) × Tuple State Action ↦
      (Function.update p.1 k p.2, p.1 k)) := by
    rintro ⟨ω, x⟩
    simp only [Function.update_idem, Function.update_eq_self, Function.update_self]
  have key := Fintype.sum_equiv (hinv.toPerm _)
    (fun p ↦ pathWeight M π μ (Function.update p.1 k p.2) * tupleProb M π μ (p.1 k) *
      g (Function.update p.1 k p.2))
    (fun p ↦ pathWeight M π μ p.1 * tupleProb M π μ p.2 * g p.1) (fun p ↦ rfl)
  have h1 : ∑ ω : Fin T → Tuple State Action, ∑ x, pathWeight M π μ (Function.update ω k x) *
        tupleProb M π μ (ω k) * g (Function.update ω k x) =
      ∑ p : (Fin T → Tuple State Action) × Tuple State Action,
        pathWeight M π μ (Function.update p.1 k p.2) * tupleProb M π μ (p.1 k) *
          g (Function.update p.1 k p.2) :=
    (Fintype.sum_prod_type' (fun ω x ↦ pathWeight M π μ (Function.update ω k x) *
        tupleProb M π μ (ω k) * g (Function.update ω k x))).symm
  have h2 : ∑ ω : Fin T → Tuple State Action, ∑ x, pathWeight M π μ ω * tupleProb M π μ x * g ω =
      ∑ p : (Fin T → Tuple State Action) × Tuple State Action,
        pathWeight M π μ p.1 * tupleProb M π μ p.2 * g p.1 :=
    (Fintype.sum_prod_type' (fun ω x ↦ pathWeight M π μ ω * tupleProb M π μ x * g ω)).symm
  have lhs : ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
      ∑ x, tupleProb M π μ x * g (Function.update ω k x) =
      ∑ ω : Fin T → Tuple State Action, ∑ x, pathWeight M π μ (Function.update ω k x) *
        tupleProb M π μ (ω k) * g (Function.update ω k x) := by
    refine sum_congr rfl fun ω _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [pathWeight_update_mul]; ring
  have rhs : ∑ ω : Fin T → Tuple State Action, ∑ x, pathWeight M π μ ω * tupleProb M π μ x * g ω =
      ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * g ω := by
    refine sum_congr rfl fun ω _ ↦ ?_
    calc ∑ x, pathWeight M π μ ω * tupleProb M π μ x * g ω
        = ∑ x, tupleProb M π μ x * (pathWeight M π μ ω * g ω) := sum_congr rfl fun x _ ↦ by ring
      _ = pathWeight M π μ ω * g ω := by rw [← sum_mul, sum_tupleProb, one_mul]
  rw [lhs, h1, key, ← h2, rhs]

/-! ## The zero-noise step -/

/-- The zero-noise TD step `δ ↦ δ − η A_x δ` (`A_x = sampleA M x`). -/
noncomputable def zeroNoiseStep [DecidableEq State] (M : DiscountedMDP State Action) (η : ℝ)
    (v : State → ℝ) (x : Tuple State Action) : State → ℝ :=
  v - η • sampleA M x v

theorem zeroNoiseStep_apply [DecidableEq State] (M : DiscountedMDP State Action) (η : ℝ)
    (v : State → ℝ) (x : Tuple State Action) (s : State) :
    zeroNoiseStep M η v x s =
      if s = x.1 then (1 - η) * v s + η * M.discount * v x.2.2 else v s := by
  simp only [zeroNoiseStep, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sampleA_apply]
  split_ifs <;> ring

/-- Jensen for the zero-noise step: `((1−η)d + ηγe)² ≤ (1−η)d² + ηγe²` for `η, γ ∈ [0,1]`. -/
theorem sq_zeroNoise_le {η γ d e : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    ((1 - η) * d + η * γ * e) ^ 2 ≤ (1 - η) * d ^ 2 + η * γ * e ^ 2 := by
  have k1 : 0 ≤ (1 - η) * η * γ * (d - e) ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) h0) hγ0) (sq_nonneg _)
  have k2 : 0 ≤ (1 - η) * η * (1 - γ) * d ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (by linarith) h0) (by linarith)) (sq_nonneg _)
  have k3 : 0 ≤ η ^ 2 * γ * (1 - γ) * e ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hγ0) (by linarith)) (sq_nonneg _)
  have e : (1 - η) * d ^ 2 + η * γ * e ^ 2 - ((1 - η) * d + η * γ * e) ^ 2 =
      (1 - η) * η * γ * (d - e) ^ 2 + (1 - η) * η * (1 - γ) * d ^ 2 +
        η ^ 2 * γ * (1 - γ) * e ^ 2 := by ring
  linarith

/-- One-step conditional second moment of the zero-noise step at coordinate `s`:
`E_x (δ − ηA_xδ)(s)² ≤ (1−μ(s))δ(s)² + μ(s)((1−η)δ(s)² + ηγ E_{P_π(s,·)} δ²)`. -/
theorem sum_tupleProb_mul_sq_zeroNoiseStep_le [DecidableEq State]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η : ℝ} (h0 : 0 ≤ η) (h1 : η ≤ 1) (v : State → ℝ)
    (s : State) :
    ∑ x, tupleProb M π μ x * zeroNoiseStep M η v x s ^ 2 ≤
      (1 - μ.prob s) * v s ^ 2 + μ.prob s * ((1 - η) * v s ^ 2 +
        η * M.discount * ∑ s', (M.policyTransition π s).prob s' * v s' ^ 2) := by
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one.le
  set H : Action → State → ℝ := fun a s' ↦
    (1 - η) * v s ^ 2 + η * M.discount * (fun s'' ↦ v s'' ^ 2) s' +
      0 * (fun (_ : Action) (_ : State) ↦ (0 : ℝ)) a s' with hH
  have hpt : ∀ x : Tuple State Action, zeroNoiseStep M η v x s ^ 2 ≤
      if s = x.1 then H x.2.1 x.2.2 else v s ^ 2 := by
    rintro ⟨s₀, a, s'⟩
    rw [zeroNoiseStep_apply]
    dsimp only
    split_ifs with h
    · subst h
      simp only [hH, zero_mul, add_zero]
      exact sq_zeroNoise_le h0 h1 hγ0 hγ1
    · exact le_rfl
  calc ∑ x, tupleProb M π μ x * zeroNoiseStep M η v x s ^ 2
      ≤ ∑ x : Tuple State Action, tupleProb M π μ x *
          (if s = x.1 then H x.2.1 x.2.2 else v s ^ 2) :=
        sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hpt x) (tupleProb_nonneg M π μ x)
    _ = (1 - μ.prob s) * v s ^ 2 + μ.prob s * tupleCondExp M π s H :=
        sum_tupleProb_mul_ite M π μ s H _
    _ = _ := by
        rw [hH, tupleCondExp_affine, FiniteDistribution.expectation]
        ring

/-- **One zero-noise step in expectation.** If the path functional `g` does not depend on the
coordinate `k`, `E g(s)² ≤ Q` for every `s`, `η ∈ [0,1]` and `μmin ≤ μ(s)` for every `s`, then
`E (g − ηA_{ω k} g)(s)² ≤ (1 − μmin(1−γ)η) Q` for every `s` (any sign of `μmin`). -/
theorem secondMoment_zeroNoiseStep_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η μmin Q : ℝ}
    (h0 : 0 ≤ η) (h1 : η ≤ 1) (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ}
    (k : Fin T) (g : (Fin T → Tuple State Action) → State → ℝ)
    (hg : ∀ ω x, g (Function.update ω k x) = g ω)
    (hQ : ∀ s, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * g ω s ^ 2 ≤ Q)
    (s : State) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * zeroNoiseStep M η (g ω) (ω k) s ^ 2 ≤
      (1 - μmin * (1 - M.discount) * η) * Q := by
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  have hμ1 := prob_le_one μ s
  have hμ0 := μ.prob_nonneg s
  have hQ0 : 0 ≤ Q := (sum_nonneg fun ω _ ↦
    mul_nonneg (pathWeight_nonneg M π μ ω) (sq_nonneg _)).trans (hQ s)
  set α := (1 - μ.prob s) + μ.prob s * (1 - η) with hα
  set β := μ.prob s * (η * M.discount) with hβ
  have hα0 : 0 ≤ α := by
    have : 0 ≤ 1 - μ.prob s := by linarith
    have : 0 ≤ 1 - η := by linarith
    positivity
  have hβ0 : 0 ≤ β := by positivity
  rw [sum_pathWeight_mul_eq_sum_update M π μ k
    (fun ω ↦ zeroNoiseStep M η (g ω) (ω k) s ^ 2)]
  simp only [hg, Function.update_self]
  calc ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
        ∑ x, tupleProb M π μ x * zeroNoiseStep M η (g ω) x s ^ 2
      ≤ ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω *
          (α * g ω s ^ 2 + β * ∑ s', (M.policyTransition π s).prob s' * g ω s' ^ 2 + 0) := by
        refine sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left ?_ (pathWeight_nonneg M π μ ω)
        refine (sum_tupleProb_mul_sq_zeroNoiseStep_le M π μ h0 h1 (g ω) s).trans (le_of_eq ?_)
        simp only [hα, hβ]
        ring
    _ = α * ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * g ω s ^ 2 +
          β * ∑ s', (M.policyTransition π s).prob s' *
            ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * g ω s' ^ 2 + 0 :=
        sum_mul_affine_eq (sum_pathWeight M π μ T) _ _ _ _ _ _
    _ ≤ α * Q + β * ∑ s', (M.policyTransition π s).prob s' * Q + 0 := by
        have hsum : ∑ s', (M.policyTransition π s).prob s' *
              ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * g ω s' ^ 2 ≤
            ∑ s', (M.policyTransition π s).prob s' * Q :=
          sum_le_sum fun s' _ ↦
            mul_le_mul_of_nonneg_left (hQ s') ((M.policyTransition π s).prob_nonneg s')
        nlinarith [mul_le_mul_of_nonneg_left (hQ s) hα0, mul_le_mul_of_nonneg_left hsum hβ0]
    _ ≤ (1 - μmin * (1 - M.discount) * η) * Q := by
        rw [← sum_mul, (M.policyTransition π s).sum_prob, one_mul, add_zero]
        have e1 : α + β = 1 - μ.prob s * η * (1 - M.discount) := by
          simp only [hα, hβ]; ring
        have e2 : μmin * (1 - M.discount) * η ≤ μ.prob s * η * (1 - M.discount) := by
          have := mul_le_mul_of_nonneg_right (hμmin s) (mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 1 - M.discount))
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_right e2 hQ0]

/-- **Second-moment decay of the zero-noise recursion** (CHECK-plan F6). Let `δ_t` be path
functionals with `δ_{t+1} = δ_t − η'_t A_{ω t} δ_t` for `m ≤ t < T` (`η'_t = stepSize η₀ (t+1)`),
each `δ_t` (`m ≤ t < T`) independent of the coordinate `ω t` that drives its step, and `E δ_m(s)² ≤ Q` for all `s`.
Then for `0 ≤ η₀ ≤ 1`, `μmin ≤ μ(s)` and every `m ≤ t ≤ T` and `s`,
`E δ_t(s)² ≤ p_{m,t} Q` with `p_{m,t} = ∏_{j∈[m,t)} (1 − μmin(1−γ)η'_j)`. -/
theorem max_secondMoment_zeroNoise_le [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {η₀ μmin Q : ℝ}
    (h0 : 0 ≤ η₀) (h1 : η₀ ≤ 1) (hμmin : ∀ s, μmin ≤ μ.prob s) {T : ℕ}
    (δ : ℕ → (Fin T → Tuple State Action) → State → ℝ) (m : ℕ)
    (hrec : ∀ t (ht : t < T), m ≤ t → ∀ ω,
      δ (t + 1) ω = zeroNoiseStep M (stepSize η₀ (t + 1)) (δ t ω) (ω ⟨t, ht⟩))
    (hinv : ∀ t (ht : t < T), m ≤ t → ∀ ω x, δ t (Function.update ω ⟨t, ht⟩ x) = δ t ω)
    (hQ : ∀ s, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * δ m ω s ^ 2 ≤ Q) :
    ∀ t, m ≤ t → t ≤ T → ∀ s, ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * δ t ω s ^ 2 ≤
      contrProd (linRate M μmin) (linStepSeq η₀) m t * Q := by
  intro t hmt
  induction t, hmt using Nat.le_induction with
  | base => intro _ s; rw [contrProd_self, one_mul]; exact hQ s
  | succ t hmt ih =>
    intro htT s
    have ht : t < T := by omega
    have ih' := ih ht.le
    have hstep := secondMoment_zeroNoiseStep_le M π μ (stepSize_nonneg h0 (t + 1))
      (stepSize_succ_le_one h0 h1 t) hμmin ⟨t, ht⟩ (δ t) (hinv t ht hmt) ih' s
    have hrw : (fun ω : Fin T → Tuple State Action ↦ pathWeight M π μ ω * δ (t + 1) ω s ^ 2) =
        fun ω ↦ pathWeight M π μ ω *
          zeroNoiseStep M (stepSize η₀ (t + 1)) (δ t ω) (ω ⟨t, ht⟩) s ^ 2 := by
      funext ω; rw [hrec t ht hmt ω]
    rw [hrw]
    refine hstep.trans (le_of_eq ?_)
    rw [contrProd_succ_top hmt, linRate, linStepSeq]
    ring

end StatisticalRL.Ch7Rest.TDInference
