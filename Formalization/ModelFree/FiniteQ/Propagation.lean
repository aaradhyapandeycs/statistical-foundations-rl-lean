import Formalization.ModelFree.FiniteQ.Stability
import Formalization.ModelFree.FiniteQ.Weights

/-! # Deterministic propagation on the good event

Finite-horizon analogue of the comparison argument of `sec:sharp-analysis-Q-generative`
(paper proof `B.5` in `CHECK-Thm4_12-4_13.md`). The only random input is the family of weighted
one-sample fluctuations
`ξ^±_{t,h}(s,a) = Σ_{i ∈ (t₀,t]} η_i^{(t)} (V^±_{h+1}(s_{i,h}(s,a)) - P_h(·|s,a) V^±_{h+1})`
of the *deterministic* comparison values `V^±_{h+1}`; on the event where every such fluctuation is
at most `√(ρ Var) + ρK`, it is absorbed by the comparison residual, and a triangular recursion over
`(t, h)` with the explicit super-solution `K 2^k ∏ (1 - η_j/2)` controls `Q_{t,h} - Q^±_h`. -/

open Finset StatisticalRL.QLearning

namespace StatisticalRL.FiniteQLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The weighted fluctuation `Σ_{i ∈ (t₀,t]} η_i^{(t)} (V(s_i) - P V)` of a fixed value vector `V`
along the draws of stage `x` at `(s,a)`; iteration `i` uses `x.sample (i - 1)`. -/
noncomputable def fluct (η : ℕ → ℝ) (t₀ : ℕ) (x : LearningStage State Action) (V : State → ℝ)
    (s : State) (a : Action) (t : ℕ) : ℝ :=
  ∑ i ∈ Ioc t₀ t, weight η i t * (V (x.sample (i - 1) s a) - (x.env.transition s a).expectation V)

/-- The good event at a single stage: for both comparison values of the following stages
(`es`), every `(s,a)` and every `t ≤ T`, the fluctuation is at most `√(ρ Var) + ρK`. -/
def GoodHead (η : ℕ → ℝ) (t₀ T : ℕ) (ρ K : ℝ) (x : LearningStage State Action)
    (es : List (EnvironmentStage State Action)) : Prop :=
  ∀ s a t, t ≤ T →
    |fluct η t₀ x (plusV ρ (2 * ρ * K) es) s a t| ≤
        Real.sqrt (ρ * (x.env.transition s a).variance (plusV ρ (2 * ρ * K) es)) + ρ * K ∧
    |fluct η t₀ x (minusV ρ (2 * ρ * K) es) s a t| ≤
        Real.sqrt (ρ * (x.env.transition s a).variance (minusV ρ (2 * ρ * K) es)) + ρ * K

/-- The good event at every stage of a list. -/
def AllGood (η : ℕ → ℝ) (t₀ T : ℕ) (ρ K : ℝ) : List (LearningStage State Action) → Prop
  | [] => True
  | x :: xs => GoodHead η t₀ T ρ K x (xs.map LearningStage.env) ∧ AllGood η t₀ T ρ K xs

theorem allGood_iff (η : ℕ → ℝ) (t₀ T : ℕ) (ρ K : ℝ) (L : List (LearningStage State Action)) :
    AllGood η t₀ T ρ K L ↔ ∀ k (hk : k < L.length),
      GoodHead η t₀ T ρ K L[k] ((L.drop (k + 1)).map LearningStage.env) := by
  induction L with
  | nil => simp [AllGood]
  | cons x xs ih =>
    simp only [AllGood, ih, List.length_cons]
    constructor
    · rintro ⟨h0, hrest⟩ k hk
      cases k with
      | zero => simpa using h0
      | succ k => simpa using hrest k (by omega)
    · intro h
      exact ⟨by simpa using h 0 (by omega), fun k hk ↦ by simpa using h (k + 1) (by omega)⟩

theorem AllGood.drop {η : ℕ → ℝ} {t₀ T : ℕ} {ρ K : ℝ} {L : List (LearningStage State Action)}
    (hL : AllGood η t₀ T ρ K L) (n : ℕ) : AllGood η t₀ T ρ K (L.drop n) := by
  induction n generalizing L with
  | zero => simpa using hL
  | succ n ih =>
    cases L with
    | nil => simp [AllGood]
    | cons x xs => simpa using ih hL.2

/-- The closed form with a split increment `d_i + f_i - R`. -/
theorem unrolled_split (η : ℕ → ℝ) {t₀ t : ℕ} (ht : t₀ ≤ t) (A R : ℝ) (d f : ℕ → ℝ) :
    unrolled η t₀ t A (fun i ↦ d i + f i - R) =
      tailProd η t₀ t * (A + R) + ∑ i ∈ Ioc t₀ t, weight η i t * d i +
        ∑ i ∈ Ioc t₀ t, weight η i t * f i - R := by
  have hs := tailProd_add_sum_weight η ht
  unfold unrolled
  have : ∑ i ∈ Ioc t₀ t, weight η i t * (d i + f i - R) =
      ∑ i ∈ Ioc t₀ t, weight η i t * d i + ∑ i ∈ Ioc t₀ t, weight η i t * f i -
        (∑ i ∈ Ioc t₀ t, weight η i t) * R := by
    rw [sum_mul, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun i _ ↦ by ring
  rw [this]
  have hR : (∑ i ∈ Ioc t₀ t, weight η i t) * R = (1 - tailProd η t₀ t) * R := by
    rw [← hs]; ring
  rw [hR]
  ring

/-- One step of the iterate at the head stage, at iteration `j ≥ 1`. -/
theorem iterate_cons_step (η : ℕ → ℝ) (x : LearningStage State Action)
    (xs : List (LearningStage State Action)) {j : ℕ} (hj : 1 ≤ j) (s : State) (a : Action) :
    iterate η (x :: xs) j s a = (1 - η j) * iterate η (x :: xs) (j - 1) s a +
      η j * (x.env.reward s a + letI : Nonempty Action := x.env.action_nonempty
        actionMaximum (iterate η xs j (x.sample (j - 1) s a))) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rfl

section Propagation

variable [Nonempty Action]

/-- Triangular propagation: on the good event, for every stage list of length `k ≤ K` and every
`t₀ ≤ t ≤ T`, both `Q_{t} - Q⁺` and `Q⁻ - Q_{t}` are at most `K 2^k ∏_{(t₀,t]} (1 - η_j/2)`. -/
theorem propagation {η : ℕ → ℝ} {t₀ T : ℕ} {ρ K : ℝ} (hρ : 0 ≤ ρ) (hK : 0 < K)
    (hη : ∀ t, 1 ≤ t → t ≤ T → 0 ≤ η t ∧ η t ≤ 1) :
    ∀ L : List (LearningStage State Action), InitBounded L → AllGood η t₀ T ρ K L →
      (L.length : ℝ) ≤ K → ∀ t, t₀ ≤ t → t ≤ T → ∀ s a,
        iterate η L t s a - plusQ ρ (2 * ρ * K) (L.map LearningStage.env) s a ≤
          K * 2 ^ L.length * halfProd η t₀ t ∧
        minusQ ρ (2 * ρ * K) (L.map LearningStage.env) s a - iterate η L t s a ≤
          K * 2 ^ L.length * halfProd η t₀ t := by
  have hunit : ∀ t, t ≤ T → UnitRates η t₀ t := fun t ht j hj hjt ↦ hη j (by omega) (hjt.trans ht)
  intro L
  induction L with
  | nil =>
    intro _ _ _ t _ htT s a
    have := halfProd_nonneg (hunit t htT)
    simp only [iterate, List.map_nil, plusQ, minusQ, sub_self, List.length_nil, pow_zero, mul_one]
    exact ⟨mul_nonneg hK.le this, mul_nonneg hK.le this⟩
  | cons x xs ih =>
    intro hinit hgood hlen t ht₀ htT s a
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hlen
    have hxs : (xs.length : ℝ) ≤ K := by linarith
    have ih' := ih hinit.2 hgood.2 hxs
    set es := xs.map LearningStage.env with hes
    have hesl : (es.length : ℝ) ≤ K := by simpa [es] using hxs
    set e := x.env
    set b := 2 * ρ * K with hb
    have hb0 : 0 ≤ b := by positivity
    set p := e.transition s a
    set Q := fun j ↦ iterate η (x :: xs) j s a with hQ
    set next := fun j ↦ actionMaximum (iterate η xs j (x.sample (j - 1) s a)) with hnext
    have hrange := iterate_mem_range η T hη (x :: xs) hinit
    have hstep : ∀ j, 1 ≤ j → Q j = (1 - η j) * Q (j - 1) + η j * (e.reward s a + next j) :=
      fun j hj ↦ iterate_cons_step η x xs hj s a
    have hmap : (x :: xs).map LearningStage.env = e :: es := rfl
    have hG : 0 ≤ K * 2 ^ xs.length := by positivity
    have hhalf : ∀ i, t₀ < i → i ≤ t → ∀ s' a',
        iterate η xs i s' a' - plusQ ρ b es s' a' ≤ K * 2 ^ xs.length * halfProd η t₀ i ∧
        minusQ ρ b es s' a' - iterate η xs i s' a' ≤ K * 2 ^ xs.length * halfProd η t₀ i :=
      fun i hi hit s' a' ↦ ih' i hi.le (hit.trans htT) s' a'
    have hK2 : K ≤ 2 * (K * 2 ^ xs.length) := by
      have : (1 : ℝ) ≤ 2 ^ xs.length := one_le_pow₀ (by norm_num)
      nlinarith
    rw [hmap]
    constructor
    · -- upper comparison
      set Vp := plusV ρ b es
      set R := plusQ ρ b (e :: es) s a - e.reward s a - p.expectation Vp with hR
      set d := fun i ↦ next i - Vp (x.sample (i - 1) s a)
      set f := fun i ↦ Vp (x.sample (i - 1) s a) - p.expectation Vp
      have hrec : ∀ j, t₀ < j → j ≤ t → Q j - plusQ ρ b (e :: es) s a =
          (1 - η j) * (Q (j - 1) - plusQ ρ b (e :: es) s a) + η j * (d j + f j - R) := by
        intro j hj _
        rw [hstep j (by omega)]
        simp only [d, f, hR]
        ring
      have hun := eq_unrolled η t₀ (fun j ↦ Q j - plusQ ρ b (e :: es) s a)
        (fun i ↦ d i + f i - R) ht₀ hrec
      simp only at hun
      rw [unrolled_split η ht₀] at hun
      have hfl : ∑ i ∈ Ioc t₀ t, weight η i t * f i = fluct η t₀ x Vp s a t := rfl
      rw [hfl] at hun
      have hgood' : |fluct η t₀ x Vp s a t| ≤ Real.sqrt (ρ * p.variance Vp) + ρ * K :=
        (hgood.1 s a t htT).1
      have hres : Real.sqrt (ρ * p.variance Vp) + ρ * K ≤ R := plus_residual_ge hρ hK e es hesl s a
      have hA : Q t₀ - plusQ ρ b (e :: es) s a + R ≤ K := by
        have hQ0 := (hrange t₀ (ht₀.trans htT) s a).2
        have hVp : 0 ≤ p.expectation Vp := p.expectation_nonneg fun y ↦
          le_trans (mul_nonneg (Nat.cast_nonneg _) hb0) ((plus_mem_range hρ es).2 y).1
        have hr0 := e.reward_nonneg s a
        simp only [List.length_cons, Nat.cast_add, Nat.cast_one] at hQ0
        simp only [hR]
        linarith
      have hd : ∀ i, t₀ < i → i ≤ t → d i ≤ K * 2 ^ xs.length * halfProd η t₀ i := by
        intro i hi hit
        simp only [d, next, Vp]
        rw [plusV_eq]
        refine (actionMaximum_sub_le _ _).trans (actionMaximum_le_of_forall fun a' ↦ ?_)
        exact (hhalf i hi hit _ a').1
      have hmono := unrolled_mono (hunit t htT) hA hd
      have hsuper := unrolled_halfProd_le ht₀ (hunit t htT) hG hK2
      have hsum : ∑ i ∈ Ioc t₀ t, weight η i t * d i ≤
          ∑ i ∈ Ioc t₀ t, weight η i t * (K * 2 ^ xs.length * halfProd η t₀ i) :=
        sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (hd i (mem_Ioc.mp hi).1 (mem_Ioc.mp hi).2)
          (weight_nonneg (hunit t htT) hi)
      have htp := tailProd_nonneg (hunit t htT)
      have hA' := mul_le_mul_of_nonneg_left hA htp
      have hflle := (le_abs_self (fluct η t₀ x Vp s a t)).trans hgood'
      unfold unrolled at hsuper
      have hQt : Q t = iterate η (x :: xs) t s a := rfl
      rw [List.length_cons, pow_succ]
      simp only at hsuper
      linarith
    · -- lower comparison
      set Vm := minusV ρ b es
      set R := e.reward s a + p.expectation Vm - minusQ ρ b (e :: es) s a with hR
      set d := fun i ↦ Vm (x.sample (i - 1) s a) - next i
      set f := fun i ↦ p.expectation Vm - Vm (x.sample (i - 1) s a)
      have hrec : ∀ j, t₀ < j → j ≤ t → minusQ ρ b (e :: es) s a - Q j =
          (1 - η j) * (minusQ ρ b (e :: es) s a - Q (j - 1)) + η j * (d j + f j - R) := by
        intro j hj _
        rw [hstep j (by omega)]
        simp only [d, f, hR]
        ring
      have hun := eq_unrolled η t₀ (fun j ↦ minusQ ρ b (e :: es) s a - Q j)
        (fun i ↦ d i + f i - R) ht₀ hrec
      simp only at hun
      rw [unrolled_split η ht₀] at hun
      have hfl : ∑ i ∈ Ioc t₀ t, weight η i t * f i = -fluct η t₀ x Vm s a t := by
        unfold fluct
        rw [← sum_neg_distrib]
        exact sum_congr rfl fun i _ ↦ by simp only [f]; ring
      rw [hfl] at hun
      have hgood' : |fluct η t₀ x Vm s a t| ≤ Real.sqrt (ρ * p.variance Vm) + ρ * K :=
        (hgood.1 s a t htT).2
      have hres : Real.sqrt (ρ * p.variance Vm) + ρ * K ≤ R := minus_residual_ge hρ hK e es hesl s a
      have hA : minusQ ρ b (e :: es) s a - Q t₀ + R ≤ K := by
        have hQ0 := (hrange t₀ (ht₀.trans htT) s a).1
        have hVm : p.expectation Vm ≤ es.length := p.expectation_le_const fun y ↦ by
          have := ((minus_mem_range (b := b) hρ es).2 y).2
          nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) es.length) hb0]
        have hr1 := e.reward_le_one s a
        have hlen' : (es.length : ℝ) + 1 ≤ K := by simpa [es] using hlen
        simp only [hR]
        linarith
      have hd : ∀ i, t₀ < i → i ≤ t → d i ≤ K * 2 ^ xs.length * halfProd η t₀ i := by
        intro i hi hit
        simp only [d, next, Vm]
        rw [minusV_eq]
        refine (actionMaximum_sub_le _ _).trans (actionMaximum_le_of_forall fun a' ↦ ?_)
        exact (hhalf i hi hit _ a').2
      have hsuper := unrolled_halfProd_le ht₀ (hunit t htT) hG hK2
      have hsum : ∑ i ∈ Ioc t₀ t, weight η i t * d i ≤
          ∑ i ∈ Ioc t₀ t, weight η i t * (K * 2 ^ xs.length * halfProd η t₀ i) :=
        sum_le_sum fun i hi ↦ mul_le_mul_of_nonneg_left (hd i (mem_Ioc.mp hi).1 (mem_Ioc.mp hi).2)
          (weight_nonneg (hunit t htT) hi)
      have htp := tailProd_nonneg (hunit t htT)
      have hA' := mul_le_mul_of_nonneg_left hA htp
      have hflle := (neg_le_abs (fluct η t₀ x Vm s a t)).trans hgood'
      unfold unrolled at hsuper
      have hQt : Q t = iterate η (x :: xs) t s a := rfl
      rw [List.length_cons, pow_succ]
      simp only at hsuper
      linarith

/-- Deterministic accuracy on the good event:
`|Q_{T,h} - Q⋆_h| ≤ K 2^k ∏_{(t₀,T]} (1 - η_j/2) + D` for a stage list of length `k ≤ K`. -/
theorem deterministic_accuracy {η : ℕ → ℝ} {t₀ T : ℕ} {ρ K lam D : ℝ} (hρ : 0 ≤ ρ) (hK : 0 < K)
    (hlam : 0 < lam) (hD0 : 0 ≤ D)
    (hD : K * (2 * ρ * K + Real.sqrt (2 * ρ) * D + ρ / (2 * lam)) + lam * K ^ 2 ≤ D)
    (hη : ∀ t, 1 ≤ t → t ≤ T → 0 ≤ η t ∧ η t ≤ 1) (ht₀ : t₀ ≤ T)
    (L : List (LearningStage State Action)) (hinit : InitBounded L)
    (hgood : AllGood η t₀ T ρ K L) (hlen : (L.length : ℝ) ≤ K) (s : State) (a : Action) :
    |iterate η L T s a - EnvironmentStage.optimalQ (L.map LearningStage.env) s a| ≤
      K * 2 ^ L.length * halfProd η t₀ T + D := by
  have hp := propagation hρ hK hη L hinit hgood hlen T ht₀ le_rfl s a
  have hs := comparators_near_optimal hρ (by positivity : 0 ≤ 2 * ρ * K) hlam hD0 hD
    (L.map LearningStage.env) (by simpa using hlen) s a
  rw [abs_le]
  constructor <;> linarith [hp.1, hp.2, hs.1.1, hs.1.2, hs.2.1, hs.2.2]

end Propagation

end StatisticalRL.FiniteQLearning
