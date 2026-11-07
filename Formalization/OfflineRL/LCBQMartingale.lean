import Formalization.OfflineRL.LCBQRecursion
import Formalization.Probability.AzumaFiltrationSource
import Formalization.Online.Regret.MVP.Probability.MVPRevealIncrement
import Formalization.OfflineRL.JointRowLaw
import Mathlib.Probability.Independence.Basic

/-!
# LCB-Q: probability of the martingale event (Lemma 6.9) and Lemmas 6.9, 6.10

`lemma:Q-recursion-pessimistic-Q` (`offlineRL.tex:1866–1893`, proof `:4415–4528`) and
`lemma:pessimistic-Q` (`:1907–1916`, proof `:4530–4672`), under the independent data model
`eq:sampling-offline-inf-iid` (`:28–39`): `T` iid triples `((s_t,a_t),s_t')` with
`(s_t,a_t) ~ d^b` and `s_t' ~ P(·|s_t,a_t)`.

The printed proof applies Azuma–Hoeffding at the random visit times `k_i(s,a)` "for fixed `ℓ`"
(`:4478`). This file uses a different, complete route (it does not validate the printed step):

1. condition on the label sequence `l = (s_t,a_t)_{t<T}`. Given `l`, the successors are
   independent with laws `P(·|l_t)` (`onlineStackProductLaw`); the visit ranks and the weights
   `γ η^n_{c+1}` are deterministic, and `V_t` depends only on `s'_0, …, s'_{t-1}` (causality);
2. for each `(s,a,n)` the martingale term is a sum of centred revealed-prefix increments, and
   Azuma–Hoeffding (`azuma_filtration_strict`) with `Σ(γη_i^n)²/(1-γ)² ≤ 2H/(n(1-γ)²)` gives the
   radius `2√(H log(2SAT/δ)/(n(1-γ)²))` at confidence `δ/(SAT)`; a union over the `SAT` triples
   `(s,a,n)` gives conditional failure probability `< δ`;
3. the actual law of the data is `Σ_l d^b(l) ⊗ (fixed-label law)`, so the failure probability
   is `< δ`.

On the resulting event the recursions hold for `c_b ≥ 4` (`recursion_of_martingaleEvent`), and
Lemma 6.10 follows pathwise (`pessimism_of_lowerRecursion`).
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.OfflineRL.LCBQ

open StatisticalRL StatisticalRL.OnlineRL
open Classical

set_option linter.unusedSectionVars false

section ProductMass

variable {α : Type*} [Fintype α]

local instance lcbqProductAtomMeasurable : MeasurableSpace α := ⊤

/-- Real mass of any set under a finite product of row laws. -/
theorem pi_rowMeasure_real {T : ℕ} (d : Fin T → FiniteDistribution α) (C : Set (Fin T → α)) :
    (Measure.pi (fun t => (d t).rowMeasure)).real C =
      ∑ y : Fin T → α, (∏ t, (d t).prob (y t)) * C.indicator 1 y := by
  have hs (t : Fin T) (x : α) : (d t).rowMeasure {x} = ENNReal.ofReal ((d t).prob x) := by
    rw [FiniteDistribution.rowMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    exact (d t).toPMF_apply x
  rw [← integral_indicator_one ((Set.toFinite C).measurableSet),
    integral_fintype _ Integrable.of_finite]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [smul_eq_mul, Measure.real, Measure.pi_singleton, ENNReal.toReal_prod, hs,
    ENNReal.toReal_ofReal ((d _).prob_nonneg _)]

end ProductMass

variable {S A : Type*} [Fintype S] [Fintype A]

local instance lcbqStateMeasurable : MeasurableSpace S := ⊤

/-- The data sequence with labels `l` and successors `y`. -/
def zipData {T : ℕ} (l : Fin T → S × A) (y : Fin T → S) : Fin T → (S × A) × S :=
  fun t => (l t, y t)

theorem mem_revealedPrefix_id {T : ℕ} (i : Fin T) (j : ℕ) :
    i ∈ mvpRevealedPrefix (id : Fin T → Fin T) j ↔ i.val < j := by
  simp only [mvpRevealedPrefix, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and,
    id]
  constructor
  · rintro ⟨-, k, hk, rfl⟩
    exact hk
  · intro h
    exact ⟨⟨i, rfl⟩, i, h, rfl⟩

/-- Extend a revealed prefix of successors to a full successor sequence (by `s₀`). -/
noncomputable def extendCode (s₀ : S) {T : ℕ} (j : ℕ)
    (code : (i : mvpRevealedPrefix (id : Fin T → Fin T) j) → S) : Fin T → S :=
  fun i => if h : i ∈ mvpRevealedPrefix (id : Fin T → Fin T) j then code ⟨i, h⟩ else s₀

theorem extendCode_revealed (s₀ : S) {T : ℕ} (j : ℕ) (y : Fin T → S) (i : Fin T)
    (hi : i.val < j) :
    extendCode s₀ j (onlineRevealedCode (mvpRevealedPrefix (id : Fin T → Fin T) j) y) i = y i := by
  unfold extendCode
  rw [dif_pos ((mem_revealedPrefix_id i j).2 hi)]
  rfl

theorem martWeight_zipData (M : DiscountedMDP S A) (δ : ℝ) {T : ℕ} (l : Fin T → S × A)
    (y y' : Fin T → S) (sa : S × A) (n : ℕ) (u : Fin T) :
    martWeight M δ (zipData l y) sa n u = martWeight M δ (zipData l y') sa n u := rfl

theorem martWeight_nonneg (M : DiscountedMDP S A) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) {T : ℕ}
    (data : Fin T → (S × A) × S) (sa : S × A) (n : ℕ) (u : Fin T) :
    0 ≤ martWeight M δ data sa n u := by
  unfold martWeight
  split_ifs
  · exact mul_nonneg M.discount_nonneg (onlineQRateWeight_nonneg
      (horizon_pos M (by have := u.isLt; omega) hδ hδ1) _ _)
  · exact le_rfl

/-- The revealed-prefix test of the martingale for `(sa, n)` given labels `l`:
`F_k(code, x) = γ η^n_{c_k+1} 1{…} V_k(x)`, with `V_k` computed from the revealed successors. -/
noncomputable def martTest (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
    (s₀ : S) {T : ℕ} (l : Fin T → S × A) (sa : S × A) (n : ℕ) (k : Fin T)
    (code : (i : mvpRevealedPrefix (id : Fin T → Fin T) k.val) → S) (x : S) : ℝ :=
  martWeight M δ (zipData l (extendCode s₀ k.val code)) sa n k *
    (run M cb δ sel π₀ (zipData l (extendCode s₀ k.val code)) k.val).V x

/-- Per-step range of a padded increment for tests valued in `[0, C_j]`. -/
theorem paddedRevealIncrement_bound_step {Index : Type*} [Fintype Index] {N : ℕ}
    (order : Fin N → Index) (d : Index → FiniteDistribution S)
    (F : (j : Fin N) → ((i : mvpRevealedPrefix order j.val) → S) → S → ℝ)
    (C : Fin N → ℝ) (hF : ∀ j code x, 0 ≤ F j code x ∧ F j code x ≤ C j)
    (k : ℕ) (y : Index → S) :
    |mvpPaddedRevealIncrement order d F k y| ≤ (if h : k < N then C ⟨k, h⟩ else 0) := by
  by_cases hk : k < N
  · let j : Fin N := ⟨k, hk⟩
    let code := onlineRevealedCode (mvpRevealedPrefix order k) y
    have hlow : 0 ≤ (d (order j)).expectation (F j code) :=
      (d (order j)).expectation_nonneg (fun x => (hF j code x).1)
    have hhigh : (d (order j)).expectation (F j code) ≤ C j :=
      (d (order j)).expectation_le_const (fun x => (hF j code x).2)
    have hv := hF j code (y (order j))
    simp only [mvpPaddedRevealIncrement, dif_pos hk]
    change |F j code (y (order j)) - (d (order j)).expectation (F j code)| ≤ C j
    rw [abs_le]
    constructor <;> linarith
  · simp [mvpPaddedRevealIncrement, hk]

/-- The visit-rank weights have square sum at most `Σ_{i<n} f(i)`. -/
theorem sum_visits_le {T : ℕ} (data : Fin T → (S × A) × S) (sa : S × A) (n : ℕ) (f : ℕ → ℝ)
    (hf : ∀ i, 0 ≤ f i) :
    ∑ u : Fin T, (if (data u).1 = sa ∧ Nat.count (visitPred data sa) u.val < n then
        f (Nat.count (visitPred data sa) u.val) else 0) ≤ ∑ i ∈ Finset.range n, f i := by
  rw [← Finset.sum_filter, ← Finset.sum_image (g := fun u : Fin T => Nat.count (visitPred data sa) u.val)]
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i hi
      rw [Finset.mem_image] at hi
      obtain ⟨u, hu, rfl⟩ := hi
      rw [Finset.mem_filter] at hu
      exact Finset.mem_range.2 hu.2.2
    · intro i _ _
      exact hf i
  · intro u hu v hv huv
    rw [Finset.coe_filter, Set.mem_setOf_eq] at hu hv
    have hpu : visitPred data sa u.val := ⟨u.isLt, hu.2.1⟩
    have hpv : visitPred data sa v.val := ⟨v.isLt, hv.2.1⟩
    apply Fin.ext
    rw [← Nat.nth_count (p := visitPred data sa) hpu, ← Nat.nth_count (p := visitPred data sa) hpv]
    exact congrArg _ huv

section Fixed

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)

/-- The sum of the padded increments is the martingale term of the zipped data. -/
theorem sum_increment_eq_martSum (s₀ : S) {T : ℕ} (l : Fin T → S × A) (sa : S × A) (n : ℕ)
    (y : Fin T → S) :
    ∑ i ∈ Finset.range T, mvpPaddedRevealIncrement (id : Fin T → Fin T)
        (fun t => M.transition (l t).1 (l t).2) (martTest M cb δ sel π₀ s₀ l sa n) i y =
      martSum M cb δ sel π₀ (zipData l y) sa n := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => mvpPaddedRevealIncrement (id : Fin T → Fin T)
    (fun t => M.transition (l t).1 (l t).2) (martTest M cb δ sel π₀ s₀ l sa n) i y)]
  unfold martSum
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [mvpPaddedRevealIncrement, dif_pos u.isLt, Fin.eta, id]
  have hrun : run M cb δ sel π₀ (zipData l (extendCode s₀ u.val
      (onlineRevealedCode (mvpRevealedPrefix (id : Fin T → Fin T) u.val) y))) u.val =
      run M cb δ sel π₀ (zipData l y) u.val := by
    apply run_congr_prefix M cb δ sel π₀ _ (u := u.val) _ le_rfl
    intro i hi
    simp only [zipData]
    rw [extendCode_revealed s₀ u.val y i hi]
  unfold martTest
  rw [hrun, martWeight_zipData M δ l _ y, FiniteDistribution.expectation_mul]
  simp only [zipData]
  ring

/-- Azuma–Hoeffding for the martingale term of one `(sa, n)`, conditionally on the labels. -/
theorem fixedLabel_martSum_prob (hcb : 0 ≤ cb) (hδ : 0 < δ) (hδ1 : δ < 1) (s₀ : S) {T : ℕ}
    (l : Fin T → S × A) (sa : S × A) (n : ℕ) (hn : 1 ≤ n) (δ' : ℝ) (hδ' : 0 < δ')
    (hδ'1 : δ' < 1) :
    1 - δ' < (onlineStackProductLaw (fun t => M.transition (l t).1 (l t).2)).real
      {y | |martSum M cb δ sel π₀ (zipData l y) sa n| ≤
        2 * Real.sqrt (horizon M.discount (iota S A T δ) * Real.log (2 / δ') /
          (n * (1 - M.discount) ^ 2))} := by
  set d : Fin T → FiniteDistribution S := fun t => M.transition (l t).1 (l t).2 with hd
  set ν := onlineStackProductLaw d with hν
  haveI : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  set F := martTest M cb δ sel π₀ s₀ l sa n with hF
  set H := horizon M.discount (iota S A T δ) with hH
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  have h1γ : 0 < 1 - M.discount := by linarith
  set w : Fin T → ℝ := fun k => martWeight M δ (zipData l (fun _ => s₀)) sa n k with hw
  set C : Fin T → ℝ := fun k => w k / (1 - M.discount) with hC
  have hFb : ∀ j code x, 0 ≤ F j code x ∧ F j code x ≤ C j := by
    intro j code x
    have hb := (run_bounds M cb δ sel π₀ (zipData l (extendCode s₀ j.val code)) hcb j.val).2 x
    have hw0 : 0 ≤ martWeight M δ (zipData l (extendCode s₀ j.val code)) sa n j :=
      martWeight_nonneg M hδ hδ1 _ sa n j
    have hwe : martWeight M δ (zipData l (extendCode s₀ j.val code)) sa n j = w j :=
      martWeight_zipData M δ l _ _ sa n j
    simp only [hF, martTest, hC]
    rw [hwe] at hw0 ⊢
    refine ⟨mul_nonneg hw0 hb.1, ?_⟩
    calc w j * (run M cb δ sel π₀ (zipData l (extendCode s₀ j.val code)) j.val).V x
        ≤ w j * (1 / (1 - M.discount)) := mul_le_mul_of_nonneg_left hb.2 hw0
      _ = w j / (1 - M.discount) := by ring
  set X : ℕ → (Fin T → S) → ℝ := fun i => mvpPaddedRevealIncrement (id : Fin T → Fin T) d F i
    with hX
  set B : ℕ → ℝ := fun i => if h : i < T then C ⟨i, h⟩ else 0 with hB
  have hXm : ∀ i, Measurable (X i) := fun i => measurable_of_countable _
  have hXb : ∀ i y, |X i y| ≤ B i := fun i y =>
    paddedRevealIncrement_bound_step (id : Fin T → Fin T) d F C hFb i y
  have hXc : ∀ i, ν[X i | mvpRevealFiltration (Outcome := S) (id : Fin T → Fin T) i] =ᵐ[ν] 0 :=
    fun i => mvp_paddedRevealIncrement_centered (id : Fin T → Fin T) Function.injective_id d F i
  have hXa : ∀ i, StronglyMeasurable[mvpRevealFiltration (Outcome := S) (id : Fin T → Fin T) (i + 1)]
      (X i) := fun i => mvp_paddedRevealIncrement_adapted (id : Fin T → Fin T) d F i
  have hAz := azuma_filtration_strict ν (mvpRevealFiltration (Outcome := S) (id : Fin T → Fin T))
    X B hXm hXb hXc hXa T δ' hδ' hδ'1
  refine lt_of_lt_of_le hAz (measureReal_mono ?_)
  intro y hy
  simp only [Set.mem_setOf_eq] at hy ⊢
  have hsum : ∑ i ∈ Finset.range T, X i y = martSum M cb δ sel π₀ (zipData l y) sa n :=
    sum_increment_eq_martSum M cb δ sel π₀ s₀ l sa n y
  rw [hsum] at hy
  refine hy.trans ?_
  -- the variance proxy
  have hsq : ∑ i ∈ Finset.range T, (B i) ^ 2 ≤ 2 * H / (n * (1 - M.discount) ^ 2) := by
    rcases Nat.eq_zero_or_pos T with hT0 | hT0
    · subst hT0
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
    have hHpos : 0 < H := horizon_pos M hT0 hδ hδ1
    rw [← Fin.sum_univ_eq_sum_range (fun i => (B i) ^ 2)]
    have hBk : ∀ k : Fin T, (B k.val) ^ 2 ≤
        (if (zipData l (fun _ => s₀) k).1 = sa ∧
            Nat.count (visitPred (zipData l (fun _ => s₀)) sa) k.val < n then
          (onlineQRateWeight H n (Nat.count (visitPred (zipData l (fun _ => s₀)) sa) k.val + 1)) ^ 2
        else 0) / (1 - M.discount) ^ 2 := by
      intro k
      simp only [hB, dif_pos k.isLt, Fin.eta, hC, hw, martWeight]
      rw [div_pow]
      apply div_le_div_of_nonneg_right _ (by positivity)
      split_ifs
      · rw [mul_pow]
        have hγ2 : M.discount ^ 2 ≤ 1 := by nlinarith
        have := sq_nonneg (onlineQRateWeight H n
          (Nat.count (visitPred (zipData l (fun _ => s₀)) sa) k.val + 1))
        nlinarith
      · simp
    calc ∑ k : Fin T, (B k.val) ^ 2
        ≤ ∑ k : Fin T, (if (zipData l (fun _ => s₀) k).1 = sa ∧
            Nat.count (visitPred (zipData l (fun _ => s₀)) sa) k.val < n then
          (onlineQRateWeight H n (Nat.count (visitPred (zipData l (fun _ => s₀)) sa) k.val + 1)) ^ 2
          else 0) / (1 - M.discount) ^ 2 := Finset.sum_le_sum fun k _ => hBk k
      _ = (∑ k : Fin T, (if (zipData l (fun _ => s₀) k).1 = sa ∧
            Nat.count (visitPred (zipData l (fun _ => s₀)) sa) k.val < n then
          (fun i => (onlineQRateWeight H n (i + 1)) ^ 2)
            (Nat.count (visitPred (zipData l (fun _ => s₀)) sa) k.val)
          else 0)) / (1 - M.discount) ^ 2 := by rw [Finset.sum_div]
      _ ≤ (∑ i ∈ Finset.range n, (onlineQRateWeight H n (i + 1)) ^ 2) / (1 - M.discount) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact sum_visits_le (zipData l (fun _ => s₀)) sa n
            (fun i => (onlineQRateWeight H n (i + 1)) ^ 2) (fun i => sq_nonneg _)
      _ = (∑ j ∈ Finset.Icc 1 n, (onlineQRateWeight H n j) ^ 2) / (1 - M.discount) ^ 2 := by
          rw [sum_Icc_one_eq_sum_range (fun j => (onlineQRateWeight H n j) ^ 2)]
      _ ≤ (2 * H / n) / (1 - M.discount) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact onlineQRateWeight_sq_sum_le H n hHpos (by omega)
      _ = 2 * H / (n * (1 - M.discount) ^ 2) := by
          rw [div_div]
  have hlog : 0 ≤ Real.log (2 / δ') := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hδ']
    linarith
  have h2 : 2 * Real.sqrt (H * Real.log (2 / δ') / (n * (1 - M.discount) ^ 2)) =
      Real.sqrt (2 ^ 2 * (H * Real.log (2 / δ') / (n * (1 - M.discount) ^ 2))) := by
    rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [h2]
  apply Real.sqrt_le_sqrt
  have hD : 0 < (n : ℝ) * (1 - M.discount) ^ 2 := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    positivity
  calc 2 * (∑ i ∈ Finset.range T, (B i) ^ 2) * Real.log (2 / δ')
      ≤ 2 * (2 * H / (n * (1 - M.discount) ^ 2)) * Real.log (2 / δ') := by gcongr
    _ = 2 ^ 2 * (H * Real.log (2 / δ') / (n * (1 - M.discount) ^ 2)) := by ring

/-- Conditionally on the labels (`T ≥ 1`), the martingale event fails with probability `< δ`. -/
theorem fixedLabel_event_prob (hcb : 0 ≤ cb) (hδ : 0 < δ) (hδ1 : δ < 1) (s₀ : S) {T : ℕ}
    (hT : 1 ≤ T) (l : Fin T → S × A) :
    (onlineStackProductLaw (fun t => M.transition (l t).1 (l t).2)).real
      {y | ¬ martingaleEvent M cb δ sel π₀ (zipData l y) δ} < δ := by
  set ν := onlineStackProductLaw (fun t => M.transition (l t).1 (l t).2) with hν
  haveI : IsProbabilityMeasure ν := by rw [hν]; infer_instance
  haveI := M.action_nonempty
  haveI := M.state_nonempty
  have hS : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos (α := S)
  have hA : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  set K : ℝ := (Fintype.card S : ℝ) * Fintype.card A * T with hK
  have hK1 : 1 ≤ K := by
    have h1 : (1 : ℝ) ≤ (Fintype.card S : ℝ) * Fintype.card A := by nlinarith
    nlinarith
  set δ' := δ / K with hδ'
  have hδ'0 : 0 < δ' := div_pos hδ (by linarith)
  have hδ'1 : δ' < 1 := by
    rw [hδ', div_lt_one (by linarith)]
    linarith
  have hlogeq : Real.log (2 / δ') =
      Real.log (2 * Fintype.card S * Fintype.card A * T / δ) := by
    congr 1
    rw [hδ', hK]
    field_simp
  set I : Finset ((S × A) × ℕ) := Finset.univ ×ˢ Finset.Icc 1 T with hI
  set bad : (S × A) × ℕ → Set (Fin T → S) := fun p => {y | ¬ |martSum M cb δ sel π₀ (zipData l y)
      p.1 p.2| ≤ 2 * Real.sqrt (horizon M.discount (iota S A T δ) *
        Real.log (2 / δ') / (p.2 * (1 - M.discount) ^ 2))} with hbad
  have hsub : {y | ¬ martingaleEvent M cb δ sel π₀ (zipData l y) δ} ⊆ ⋃ p ∈ I, bad p := by
    intro y hy
    simp only [Set.mem_setOf_eq, martingaleEvent, not_forall] at hy
    obtain ⟨s, a, n, hn1, hnT, hfail⟩ := hy
    simp only [Set.mem_iUnion, hI, Finset.mem_product, Finset.mem_univ, true_and,
      Finset.mem_Icc]
    refine ⟨((s, a), n), ⟨hn1, hnT⟩, ?_⟩
    simp only [hbad, Set.mem_setOf_eq, hlogeq]
    exact hfail
  have hbadp : ∀ p ∈ I, ν.real (bad p) < δ' := by
    intro p hp
    simp only [hI, Finset.mem_product, Finset.mem_Icc] at hp
    have h := fixedLabel_martSum_prob M cb δ sel π₀ hcb hδ hδ1 s₀ l p.1 p.2 hp.2.1 δ' hδ'0 hδ'1
    have hc : bad p = {y | |martSum M cb δ sel π₀ (zipData l y) p.1 p.2| ≤
        2 * Real.sqrt (horizon M.discount (iota S A T δ) * Real.log (2 / δ') /
          (p.2 * (1 - M.discount) ^ 2))}ᶜ := rfl
    rw [hc, probReal_compl_eq_one_sub ((Set.toFinite _).measurableSet)]
    linarith
  have hcard : (I.card : ℝ) = K := by
    simp only [hI, Finset.card_product, Finset.card_univ, Fintype.card_prod, Nat.card_Icc,
      Nat.add_sub_cancel, hK]
    push_cast
    ring
  have hIne : I.Nonempty := by
    obtain ⟨sa⟩ : Nonempty (S × A) := ⟨(M.state_nonempty.some, M.action_nonempty.some)⟩
    exact ⟨(sa, 1), by simp [hI]; omega⟩
  calc ν.real {y | ¬ martingaleEvent M cb δ sel π₀ (zipData l y) δ}
      ≤ ν.real (⋃ p ∈ I, bad p) := measureReal_mono hsub (measure_ne_top ν _)
    _ ≤ ∑ p ∈ I, ν.real (bad p) := measureReal_biUnion_finset_le I bad
    _ < ∑ _p ∈ I, δ' := Finset.sum_lt_sum_of_nonempty hIne hbadp
    _ = δ := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard, hδ']
      field_simp

end Fixed

section Lift

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)

/-- **Martingale event under the actual iid data law** (proof of Lemma 6.9, `offlineRL.tex:
4478–4491`, via label conditioning): `1 − δ < P(martingaleEvent)`. -/
theorem martingaleEvent_prob (hcb : 0 ≤ cb) (db : FiniteDistribution (S × A)) (T : ℕ)
    (hδ : 0 < δ) (hδ1 : δ < 1) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    letI : MeasurableSpace ((S × A) × S) := ⊤
    ∀ X : Ω → Fin T → (S × A) × S, Measurable X → iIndepFun (fun i ω => X ω i) μ →
      (∀ i, μ.map (fun ω => X ω i) = ∑ x : (S × A) × S,
        ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) • Measure.dirac x) →
      1 - δ < μ.real {ω | martingaleEvent M cb δ sel π₀ (X ω) δ} := by
  letI : MeasurableSpace ((S × A) × S) := ⊤
  intro X hX hind hmarg
  rcases Nat.eq_zero_or_pos T with hT0 | hT
  · subst hT0
    have huniv : {ω | martingaleEvent M cb δ sel π₀ (X ω) δ} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      intro s a n hn hnT
      omega
    rw [huniv, probReal_univ]
    linarith
  -- the actual law of the data
  have hrow : (∑ x : (S × A) × S,
      ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) • Measure.dirac x) =
      (JointRow.jointRow db M.transition).rowMeasure := by
    refine Measure.ext_iff_singleton.2 fun x => ?_
    rw [Measure.finset_sum_apply]
    simp only [Measure.smul_apply, smul_eq_mul,
      Measure.dirac_apply' _ (measurableSet_singleton x), Set.indicator_apply,
      Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ x, if_pos (Finset.mem_univ x)]
    unfold FiniteDistribution.rowMeasure
    rw [@PMF.toMeasure_apply_singleton _ ⊤ _ x MeasurableSpace.measurableSet_top]
    unfold FiniteDistribution.toPMF
    rw [PMF.ofFintype_apply]
    rfl
  have hlaw : μ.map X = Measure.pi (fun _ : Fin T => (JointRow.jointRow db M.transition).rowMeasure) := by
    have h := (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (measurable_pi_apply i).comp hX |>.aemeasurable)).1 hind
    simp only [Function.comp_def] at h
    calc μ.map X = μ.map (fun ω i => X ω i) := rfl
      _ = Measure.pi (fun i => μ.map (fun ω => X ω i)) := h
      _ = _ := by
        congr 1
        funext i
        rw [hmarg i, hrow]
  set G : Set (Fin T → (S × A) × S) := {x | martingaleEvent M cb δ sel π₀ x δ} with hG
  have hGm : MeasurableSet G := (Set.toFinite G).measurableSet
  have hbad : μ.real (X ⁻¹' Gᶜ) < δ := by
    rw [← map_measureReal_apply hX hGm.compl, hlaw, pi_rowMeasure_real]
    -- regroup by labels
    set e := Equiv.arrowProdEquivProdArrow (Fin T) (fun _ => S × A) (fun _ => S) with he
    set g : (Fin T → (S × A) × S) → ℝ := fun x =>
      (∏ t, (JointRow.jointRow db M.transition).prob (x t)) * Gᶜ.indicator 1 x with hg
    have hregroup : ∑ x, g x = ∑ l : Fin T → S × A, (∏ t, db.prob (l t)) *
        (onlineStackProductLaw (fun t => M.transition (l t).1 (l t).2)).real
          {y | ¬ martingaleEvent M cb δ sel π₀ (zipData l y) δ} := by
      rw [← Fintype.sum_equiv e.symm (fun p => g (e.symm p)) g (fun _ => rfl),
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun l _ => ?_
      unfold onlineStackProductLaw
      rw [pi_rowMeasure_real, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp only [hg, he, Equiv.arrowProdEquivProdArrow_symm_apply, JointRow.jointRow,
        Finset.prod_mul_distrib]
      have hind : Gᶜ.indicator (1 : (Fin T → (S × A) × S) → ℝ)
          ((Equiv.arrowProdEquivProdArrow (Fin T) (fun _ => S × A) (fun _ => S)).symm (l, y)) =
          {y | ¬ martingaleEvent M cb δ sel π₀ (zipData l y) δ}.indicator 1 y := by
        simp only [Set.indicator_apply, Set.mem_compl_iff, hG, Set.mem_setOf_eq]
        rfl
      rw [hind]
      ring
    rw [hregroup]
    haveI := M.state_nonempty
    obtain ⟨s₀⟩ := M.state_nonempty
    have hw0 : ∀ l : Fin T → S × A, 0 ≤ ∏ t, db.prob (l t) :=
      fun l => Finset.prod_nonneg fun t _ => db.prob_nonneg _
    have hw1 : ∑ l : Fin T → S × A, ∏ t, db.prob (l t) = 1 := by
      rw [← Fintype.prod_sum (fun _ : Fin T => db.prob), db.sum_prob, Finset.prod_const_one]
    have hpos : ∃ l ∈ (Finset.univ : Finset (Fin T → S × A)), 0 < ∏ t, db.prob (l t) := by
      by_contra hcon
      push_neg at hcon
      have : ∑ l : Fin T → S × A, ∏ t, db.prob (l t) ≤ 0 :=
        Finset.sum_nonpos fun l hl => hcon l hl
      linarith
    calc ∑ l : Fin T → S × A, (∏ t, db.prob (l t)) *
          (onlineStackProductLaw (fun t => M.transition (l t).1 (l t).2)).real
            {y | ¬ martingaleEvent M cb δ sel π₀ (zipData l y) δ}
        < ∑ l : Fin T → S × A, (∏ t, db.prob (l t)) * δ := by
          apply Finset.sum_lt_sum
          · intro l _
            exact mul_le_mul_of_nonneg_left
              (fixedLabel_event_prob M cb δ sel π₀ hcb hδ hδ1 s₀ hT l).le (hw0 l)
          · obtain ⟨l, hl, hlpos⟩ := hpos
            exact ⟨l, hl, mul_lt_mul_of_pos_left
              (fixedLabel_event_prob M cb δ sel π₀ hcb hδ hδ1 s₀ hT l) hlpos⟩
      _ = δ := by rw [← Finset.sum_mul, hw1, one_mul]
  have hc : {ω | martingaleEvent M cb δ sel π₀ (X ω) δ} = X ⁻¹' G := rfl
  have hcompl : X ⁻¹' Gᶜ = (X ⁻¹' G)ᶜ := Set.preimage_compl
  rw [hcompl, probReal_compl_eq_one_sub (hX hGm)] at hbad
  rw [hc]
  linarith

/-- **Lemma 6.9 (library form)**: for `c_b ≥ 4`, with probability exceeding `1 − δ` the
recursions `eq:qstar-recursion-lcbq` and `eq:uniform-policy-pessimism-recursion` hold for all
`1 ≤ t ≤ T`, all `(s,a)` and all deterministic `π`. -/
theorem lemma69_prob (hcb : 4 ≤ cb) (db : FiniteDistribution (S × A)) (T : ℕ)
    (hδ : 0 < δ) (hδ1 : δ < 1) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    letI : MeasurableSpace ((S × A) × S) := ⊤
    ∀ X : Ω → Fin T → (S × A) × S, Measurable X → iIndepFun (fun i ω => X ω i) μ →
      (∀ i, μ.map (fun ω => X ω i) = ∑ x : (S × A) × S,
        ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) • Measure.dirac x) →
      1 - δ < μ.real {ω | upperRecursion M cb δ sel π₀ (X ω) ∧
        lowerRecursion M cb δ sel π₀ (X ω)} := by
  intro X hX hind hmarg
  have h := martingaleEvent_prob M cb δ sel π₀ (by linarith) db T hδ hδ1 μ X hX hind hmarg
  refine lt_of_lt_of_le h (measureReal_mono ?_)
  intro ω hω
  exact recursion_of_martingaleEvent M cb δ sel π₀ (X ω) hcb hδ hδ1 hω

/-- **Lemma 6.10 (library form)**: for `c_b ≥ 4` and any arg-max selector, with probability
exceeding `1 − δ`, `Q_t ≤ Q⋆` and `V_t ≤ V^{π_t} ≤ V⋆` for all `1 ≤ t ≤ T`. -/
theorem lemma610_prob (hcb : 4 ≤ cb) (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f))
    (db : FiniteDistribution (S × A)) (T : ℕ)
    (hδ : 0 < δ) (hδ1 : δ < 1) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    letI : MeasurableSpace ((S × A) × S) := ⊤
    ∀ X : Ω → Fin T → (S × A) × S, Measurable X → iIndepFun (fun i ω => X ω i) μ →
      (∀ i, μ.map (fun ω => X ω i) = ∑ x : (S × A) × S,
        ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) • Measure.dirac x) →
      1 - δ < μ.real {ω | ∀ t, 1 ≤ t → t ≤ T →
        (∀ s a, (run M cb δ sel π₀ (X ω) t).Q s a ≤ M.optimalityFixedPoint s a) ∧
        ∀ s, (run M cb δ sel π₀ (X ω) t).V s ≤
            M.trajectoryExpectedValue (detPolicy (run M cb δ sel π₀ (X ω) t).policy) s ∧
          M.trajectoryExpectedValue (detPolicy (run M cb δ sel π₀ (X ω) t).policy) s ≤
            M.trajectoryExpectedValue M.optimalGreedyPolicy s} := by
  intro X hX hind hmarg
  have h := lemma69_prob M cb δ sel π₀ hcb db T hδ hδ1 μ X hX hind hmarg
  refine lt_of_lt_of_le h (measureReal_mono ?_)
  intro ω hω
  exact pessimism_of_lowerRecursion M cb δ sel π₀ (X ω) hsel hδ hδ1 hω.2

end Lift

end StatisticalRL.OfflineRL.LCBQ
