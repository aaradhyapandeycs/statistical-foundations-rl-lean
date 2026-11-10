import Formalization.Probability.AzumaScalarChord
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Azuma–Hoeffding on a finite i.i.d. path space

Library infrastructure for the Azuma route (check fix F6) of the corrected Theorem 7.11 plan;
no source result is claimed here.

The path space is `Fin T → α` with `α` finite and the i.i.d. product weight
`prodWeight p ω = ∏_t p(ω t)` of a probability vector `p` (`0 ≤ p`, `∑ p = 1`). The probability
of an event is the finite sum `prodProb p T E = ∑_ω prodWeight p ω · 1_E(ω)`. This is literally
the form of `pathWeight`/`pathProb` of `TDInference/Definitions.lean` (`pathWeight = prodWeight tupleProb`
by `rfl`), so no measure-theoretic bridge is needed.

The natural filtration of the coordinates is encoded by `DependsBelow n f`: `f` depends only on
the coordinates `ω i` with `i < n`. A *bounded martingale-difference sequence*
(`IsBoundedMartDiff p d c`) is `d : ℕ → (Fin T → α) → ℝ` such that for every `k < T`
* `d k` depends only on the coordinates `≤ k` (adapted);
* resampling coordinate `k` from `p` averages `d k` to zero (centred: `E[d_k | F_{k−1}] = 0`,
  since coordinate `k` is independent of the coordinates `< k`);
* `|d k| ≤ c k` pathwise.

Results:
* `sum_prodWeight_mul_eq_sum_update`: resampling identity `E g = E ∑ₓ p(x) g(ω[k ↦ x])`.
* `sum_mul_exp_le_of_centred`: Hoeffding's lemma for a centred finite law on `[−c, c]`.
* `sum_prodWeight_mul_exp_le` (Azuma MGF): `E exp(t S_n) ≤ exp(t² ∑_{k<n} c_k² / 2)` for
  `n ≤ T`, `S_n = ∑_{k<n} d_k`.
* `prodProb_le_sum_le_exp`, `prodProb_le_abs_sum_le_exp`: `P(r ≤ S_n) ≤ exp(−r²/(2v))`,
  `P(r ≤ |S_n|) ≤ 2 exp(−r²/(2v))` for any `v > 0` with `∑_{k<n} c_k² ≤ v`.
* `prodProb_sqrt_le_abs_sum_le`: `P(√(2v log(2/δ)) ≤ |S_n|) ≤ δ` for `0 < δ ≤ 1`.
* `prodProb_mono`, `prodProb_biUnion_le`: monotonicity and the finite union bound.
-/

open Finset
open scoped BigOperators

namespace StatisticalRL.Probability.PathAzuma

variable {α : Type*} [Fintype α]

/-- The i.i.d. product weight `∏_t p(ω t)` of a path `ω : Fin T → α`. -/
def prodWeight (p : α → ℝ) {T : ℕ} (ω : Fin T → α) : ℝ := ∏ t, p (ω t)

/-- The probability `∑_ω prodWeight p ω · 1_E(ω)` of a path event `E`. -/
noncomputable def prodProb (p : α → ℝ) (T : ℕ) (E : Set (Fin T → α)) : ℝ :=
  ∑ ω : Fin T → α, prodWeight p ω * E.indicator (fun _ ↦ (1 : ℝ)) ω

/-- `f` depends only on the coordinates `ω i` with `i < n` (measurability with respect to the
natural filtration `F_{n−1}` of the coordinates). -/
def DependsBelow {T : ℕ} (n : ℕ) (f : (Fin T → α) → ℝ) : Prop :=
  ∀ ω ω' : Fin T → α, (∀ i : Fin T, (i : ℕ) < n → ω i = ω' i) → f ω = f ω'

/-- A bounded martingale-difference sequence on the i.i.d. path space (see the module doc). -/
structure IsBoundedMartDiff (p : α → ℝ) {T : ℕ} (d : ℕ → (Fin T → α) → ℝ) (c : ℕ → ℝ) :
    Prop where
  adapted : ∀ k, k < T → DependsBelow (k + 1) (d k)
  centred : ∀ k (hk : k < T) (ω : Fin T → α),
    ∑ x, p x * d k (Function.update ω ⟨k, hk⟩ x) = 0
  bounded : ∀ k, k < T → ∀ ω, |d k ω| ≤ c k

variable {p : α → ℝ} {T : ℕ}

omit [Fintype α] in
theorem prodWeight_nonneg (hp0 : ∀ x, 0 ≤ p x) (ω : Fin T → α) : 0 ≤ prodWeight p ω :=
  prod_nonneg fun _ _ ↦ hp0 _

theorem sum_prodWeight (hp1 : ∑ x, p x = 1) (T : ℕ) : ∑ ω : Fin T → α, prodWeight p ω = 1 := by
  have h := Finset.prod_univ_sum (fun _ : Fin T ↦ (Finset.univ : Finset α)) (fun _ x ↦ p x)
  rw [Fintype.piFinset_univ] at h
  simp only [prodWeight, ← h, hp1, Finset.prod_const_one]

omit [Fintype α] in
theorem prodWeight_update_mul (p : α → ℝ) (ω : Fin T → α) (k : Fin T) (x : α) :
    prodWeight p (Function.update ω k x) * p (ω k) = prodWeight p ω * p x := by
  have h : ∀ ω' : Fin T → α, prodWeight p ω' = p (ω' k) * ∏ t ∈ univ.erase k, p (ω' t) :=
    fun ω' ↦ (mul_prod_erase univ (fun t ↦ p (ω' t)) (mem_univ k)).symm
  have hr : ∏ t ∈ univ.erase k, p (Function.update ω k x t) = ∏ t ∈ univ.erase k, p (ω t) :=
    prod_congr rfl fun t ht ↦ by rw [Function.update_of_ne (ne_of_mem_erase ht)]
  rw [h (Function.update ω k x), h ω, hr, Function.update_self]
  ring

/-- **Resampling identity.** Replacing coordinate `k` by an independent draw from `p` does not
change expectations: `E g = E ∑ₓ p(x) g(ω[k ↦ x])`. -/
theorem sum_prodWeight_mul_eq_sum_update (hp1 : ∑ x, p x = 1) (k : Fin T)
    (g : (Fin T → α) → ℝ) :
    ∑ ω : Fin T → α, prodWeight p ω * g ω =
      ∑ ω : Fin T → α, prodWeight p ω * ∑ x, p x * g (Function.update ω k x) := by
  have hinv : Function.Involutive (fun q : (Fin T → α) × α ↦
      (Function.update q.1 k q.2, q.1 k)) := by
    rintro ⟨ω, x⟩
    simp only [Function.update_idem, Function.update_eq_self, Function.update_self]
  have key := Fintype.sum_equiv (hinv.toPerm _)
    (fun q ↦ prodWeight p (Function.update q.1 k q.2) * p (q.1 k) *
      g (Function.update q.1 k q.2))
    (fun q ↦ prodWeight p q.1 * p q.2 * g q.1) (fun q ↦ rfl)
  have h1 : ∑ ω : Fin T → α, ∑ x, prodWeight p (Function.update ω k x) * p (ω k) *
        g (Function.update ω k x) =
      ∑ q : (Fin T → α) × α, prodWeight p (Function.update q.1 k q.2) * p (q.1 k) *
          g (Function.update q.1 k q.2) :=
    (Fintype.sum_prod_type' (fun ω x ↦ prodWeight p (Function.update ω k x) * p (ω k) *
        g (Function.update ω k x))).symm
  have h2 : ∑ ω : Fin T → α, ∑ x, prodWeight p ω * p x * g ω =
      ∑ q : (Fin T → α) × α, prodWeight p q.1 * p q.2 * g q.1 :=
    (Fintype.sum_prod_type' (fun ω x ↦ prodWeight p ω * p x * g ω)).symm
  have lhs : ∑ ω : Fin T → α, prodWeight p ω * ∑ x, p x * g (Function.update ω k x) =
      ∑ ω : Fin T → α, ∑ x, prodWeight p (Function.update ω k x) * p (ω k) *
        g (Function.update ω k x) := by
    refine sum_congr rfl fun ω _ ↦ ?_
    rw [mul_sum]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [prodWeight_update_mul]; ring
  have rhs : ∑ ω : Fin T → α, ∑ x, prodWeight p ω * p x * g ω =
      ∑ ω : Fin T → α, prodWeight p ω * g ω := by
    refine sum_congr rfl fun ω _ ↦ ?_
    calc ∑ x, prodWeight p ω * p x * g ω
        = ∑ x, p x * (prodWeight p ω * g ω) := sum_congr rfl fun x _ ↦ by ring
      _ = prodWeight p ω * g ω := by rw [← sum_mul, hp1, one_mul]
  rw [lhs, h1, key, ← h2, rhs]

/-! ## The natural filtration -/

omit [Fintype α] in
theorem DependsBelow.mono {n m : ℕ} {f : (Fin T → α) → ℝ} (hf : DependsBelow n f) (h : n ≤ m) :
    DependsBelow m f :=
  fun ω ω' hω ↦ hf ω ω' fun i hi ↦ hω i (by omega)

omit [Fintype α] in
/-- Updating a coordinate `k ≥ n` does not change a function of the coordinates `< n`. -/
theorem DependsBelow.update_eq {n : ℕ} {f : (Fin T → α) → ℝ} (hf : DependsBelow n f)
    (ω : Fin T → α) (k : Fin T) (hk : n ≤ k) (x : α) : f (Function.update ω k x) = f ω :=
  hf _ _ fun i hi ↦ Function.update_of_ne (fun h ↦ by rw [h] at hi; omega) _ _

omit [Fintype α] in
theorem dependsBelow_sum {n : ℕ} (hn : n ≤ T) {d : ℕ → (Fin T → α) → ℝ}
    (hd : ∀ k, k < T → DependsBelow (k + 1) (d k)) :
    DependsBelow n (fun ω ↦ ∑ k ∈ range n, d k ω) := by
  intro ω ω' hω
  refine sum_congr rfl fun k hk ↦ ?_
  have hkn := mem_range.1 hk
  exact (hd k (by omega)).mono (show k + 1 ≤ n by omega) ω ω' hω

theorem IsBoundedMartDiff.neg {d : ℕ → (Fin T → α) → ℝ} {c : ℕ → ℝ}
    (hd : IsBoundedMartDiff p d c) : IsBoundedMartDiff p (fun k ω ↦ -d k ω) c where
  adapted k hk ω ω' h := by simp only [hd.adapted k hk ω ω' h]
  centred k hk ω := by
    simp only [mul_neg, sum_neg_distrib, hd.centred k hk ω, neg_zero]
  bounded k hk ω := by rw [abs_neg]; exact hd.bounded k hk ω

/-! ## Hoeffding's lemma and the Azuma MGF bound -/

/-- **Hoeffding's lemma** for a finite law: if `∑ₓ p(x) f(x) = 0` and `|f| ≤ c`, then
`∑ₓ p(x) exp(t f(x)) ≤ exp(t² c² / 2)`. -/
theorem sum_mul_exp_le_of_centred {β : Type*} [Fintype β] {q : β → ℝ} (hq0 : ∀ x, 0 ≤ q x)
    (hq1 : ∑ x, q x = 1) {f : β → ℝ} {c : ℝ} (hf : ∀ x, |f x| ≤ c) (hc : ∑ x, q x * f x = 0)
    (t : ℝ) : ∑ x, q x * Real.exp (t * f x) ≤ Real.exp (t ^ 2 * c ^ 2 / 2) := by
  by_cases hc0 : 0 < c
  · calc ∑ x, q x * Real.exp (t * f x)
        ≤ ∑ x, q x * (Real.cosh (t * c) + (Real.sinh (t * c) / c) * f x) :=
          sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left
            (StatisticalRL.azuma_exp_symmetric_chord c (f x) t hc0 (hf x)) (hq0 x)
      _ = Real.cosh (t * c) * ∑ x, q x + (Real.sinh (t * c) / c) * ∑ x, q x * f x := by
          rw [mul_sum, mul_sum, ← sum_add_distrib]
          exact sum_congr rfl fun x _ ↦ by ring
      _ = Real.cosh (t * c) := by rw [hq1, hc]; ring
      _ ≤ Real.exp (t ^ 2 * c ^ 2 / 2) := StatisticalRL.azuma_cosh_bound c t
  · have h0 : ∀ x, f x = 0 := fun x ↦
      abs_eq_zero.mp (le_antisymm ((hf x).trans (not_lt.mp hc0)) (abs_nonneg _))
    simp only [h0, mul_zero, Real.exp_zero, mul_one, hq1]
    exact Real.one_le_exp (by positivity)

/-- **Azuma's MGF bound** on the i.i.d. path space:
`E exp(t ∑_{k<n} d_k) ≤ exp(t² ∑_{k<n} c_k² / 2)` for `n ≤ T`. -/
theorem sum_prodWeight_mul_exp_le (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {d : ℕ → (Fin T → α) → ℝ} {c : ℕ → ℝ} (hd : IsBoundedMartDiff p d c) (t : ℝ) :
    ∀ n, n ≤ T → ∑ ω : Fin T → α, prodWeight p ω * Real.exp (t * ∑ k ∈ range n, d k ω) ≤
      Real.exp (t ^ 2 * (∑ k ∈ range n, c k ^ 2) / 2) := by
  intro n
  induction n with
  | zero =>
    intro _
    simp only [sum_range_zero, mul_zero, Real.exp_zero, mul_one, zero_div]
    rw [sum_prodWeight hp1]
  | succ n ih =>
    intro hn
    set k : Fin T := ⟨n, by omega⟩ with hk
    have hS := dependsBelow_sum (show n ≤ T by omega) hd.adapted
    set K := Real.exp (t ^ 2 * c n ^ 2 / 2)
    have hinner : ∀ ω : Fin T → α,
        ∑ x, p x * Real.exp (t * ∑ j ∈ range (n + 1), d j (Function.update ω k x)) ≤
          Real.exp (t * ∑ j ∈ range n, d j ω) * K := by
      intro ω
      have he : ∀ x, Real.exp (t * ∑ j ∈ range (n + 1), d j (Function.update ω k x)) =
          Real.exp (t * ∑ j ∈ range n, d j ω) * Real.exp (t * d n (Function.update ω k x)) := by
        intro x
        rw [sum_range_succ, ← Real.exp_add]
        congr 1
        have := hS.update_eq ω k le_rfl x
        simp only at this
        rw [this]; ring
      rw [sum_congr rfl fun x _ ↦ by rw [he x]]
      have hrw : ∑ x, p x * (Real.exp (t * ∑ j ∈ range n, d j ω) *
          Real.exp (t * d n (Function.update ω k x))) =
          Real.exp (t * ∑ j ∈ range n, d j ω) *
            ∑ x, p x * Real.exp (t * d n (Function.update ω k x)) := by
        rw [Finset.mul_sum univ]; exact sum_congr rfl fun x _ ↦ by ring
      rw [hrw]
      exact mul_le_mul_of_nonneg_left
        (sum_mul_exp_le_of_centred hp0 hp1 (fun x ↦ hd.bounded n (by omega) _)
          (hd.centred n (by omega) ω) t) (Real.exp_pos _).le
    rw [sum_prodWeight_mul_eq_sum_update hp1 k]
    calc ∑ ω : Fin T → α, prodWeight p ω *
          ∑ x, p x * Real.exp (t * ∑ j ∈ range (n + 1), d j (Function.update ω k x))
        ≤ ∑ ω : Fin T → α, prodWeight p ω * (Real.exp (t * ∑ j ∈ range n, d j ω) * K) :=
          sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (hinner ω) (prodWeight_nonneg hp0 ω)
      _ = K * ∑ ω : Fin T → α, prodWeight p ω * Real.exp (t * ∑ j ∈ range n, d j ω) := by
          rw [Finset.mul_sum univ]; exact sum_congr rfl fun ω _ ↦ by ring
      _ ≤ K * Real.exp (t ^ 2 * (∑ j ∈ range n, c j ^ 2) / 2) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) (Real.exp_pos _).le
      _ = Real.exp (t ^ 2 * (∑ j ∈ range (n + 1), c j ^ 2) / 2) := by
          rw [← Real.exp_add, sum_range_succ]; congr 1; ring

/-! ## Tails -/

theorem prodProb_le_sum_of_indicator_le (hp0 : ∀ x, 0 ≤ p x) {E : Set (Fin T → α)}
    {g : (Fin T → α) → ℝ} (hg : ∀ ω, E.indicator (fun _ ↦ (1 : ℝ)) ω ≤ g ω) :
    prodProb p T E ≤ ∑ ω : Fin T → α, prodWeight p ω * g ω :=
  sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (hg ω) (prodWeight_nonneg hp0 ω)

theorem prodProb_mono (hp0 : ∀ x, 0 ≤ p x) {E F : Set (Fin T → α)} (h : E ⊆ F) :
    prodProb p T E ≤ prodProb p T F :=
  prodProb_le_sum_of_indicator_le hp0 fun ω ↦
    Set.indicator_le_indicator_of_subset h (fun _ ↦ zero_le_one) ω

/-- The finite union bound. -/
theorem prodProb_biUnion_le (hp0 : ∀ x, 0 ≤ p x) {ι : Type*} (s : Finset ι)
    (E : ι → Set (Fin T → α)) :
    prodProb p T (⋃ i ∈ s, E i) ≤ ∑ i ∈ s, prodProb p T (E i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [prodProb]
  | insert a s ha ih =>
    rw [sum_insert ha, Finset.set_biUnion_insert]
    refine (prodProb_le_sum_of_indicator_le hp0 (g := fun ω ↦
      (E a).indicator (fun _ ↦ (1 : ℝ)) ω +
        (⋃ i ∈ s, E i).indicator (fun _ ↦ (1 : ℝ)) ω) fun ω ↦ ?_).trans ?_
    · dsimp only
      by_cases h1 : ω ∈ E a
      · rw [Set.indicator_of_mem (Set.mem_union_left _ h1), Set.indicator_of_mem h1]
        have := Set.indicator_nonneg (s := ⋃ i ∈ s, E i) (fun _ _ ↦ (zero_le_one : (0 : ℝ) ≤ 1)) ω
        linarith
      · by_cases h2 : ω ∈ ⋃ i ∈ s, E i
        · rw [Set.indicator_of_mem (Set.mem_union_right _ h2), Set.indicator_of_mem h2,
            Set.indicator_of_notMem h1]; norm_num
        · rw [Set.indicator_of_notMem (by simp [h1, h2] : ω ∉ E a ∪ ⋃ i ∈ s, E i)]
          exact add_nonneg (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)
            (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)
    · simp only [mul_add, sum_add_distrib]
      exact add_le_add le_rfl ih

/-- The Chernoff step: `E exp(λ(S_n − r)) ≤ exp(−r²/(2v))` with `λ = r/v`. -/
theorem sum_prodWeight_mul_exp_sub_le (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {d : ℕ → (Fin T → α) → ℝ} {c : ℕ → ℝ} (hd : IsBoundedMartDiff p d c) {n : ℕ} (hn : n ≤ T)
    {r v : ℝ} (hv : 0 < v) (hcv : ∑ k ∈ range n, c k ^ 2 ≤ v) :
    ∑ ω : Fin T → α, prodWeight p ω * Real.exp (r / v * (∑ k ∈ range n, d k ω - r)) ≤
      Real.exp (-r ^ 2 / (2 * v)) := by
  have hrw : ∀ ω : Fin T → α, prodWeight p ω * Real.exp (r / v * (∑ k ∈ range n, d k ω - r)) =
      Real.exp (-(r / v * r)) * (prodWeight p ω * Real.exp (r / v * ∑ k ∈ range n, d k ω)) := by
    intro ω
    rw [mul_sub, sub_eq_add_neg, Real.exp_add]; ring
  simp_rw [hrw]
  rw [← mul_sum]
  calc Real.exp (-(r / v * r)) *
        ∑ ω : Fin T → α, prodWeight p ω * Real.exp (r / v * ∑ k ∈ range n, d k ω)
      ≤ Real.exp (-(r / v * r)) * Real.exp ((r / v) ^ 2 * (∑ k ∈ range n, c k ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left (sum_prodWeight_mul_exp_le hp0 hp1 hd (r / v) n hn)
          (Real.exp_pos _).le
    _ ≤ Real.exp (-(r / v * r)) * Real.exp ((r / v) ^ 2 * v / 2) := by
        gcongr
    _ = Real.exp (-r ^ 2 / (2 * v)) := by
        rw [← Real.exp_add]; congr 1; field_simp; ring

/-- **Azuma upper tail**: `P(r ≤ S_n) ≤ exp(−r²/(2v))` whenever `∑_{k<n} c_k² ≤ v`, `v > 0`. -/
theorem prodProb_le_sum_le_exp (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {d : ℕ → (Fin T → α) → ℝ} {c : ℕ → ℝ} (hd : IsBoundedMartDiff p d c) {n : ℕ} (hn : n ≤ T)
    {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v) (hcv : ∑ k ∈ range n, c k ^ 2 ≤ v) :
    prodProb p T {ω | r ≤ ∑ k ∈ range n, d k ω} ≤ Real.exp (-r ^ 2 / (2 * v)) := by
  refine (prodProb_le_sum_of_indicator_le hp0 fun ω ↦ ?_).trans
    (sum_prodWeight_mul_exp_sub_le hp0 hp1 hd hn (r := r) hv hcv)
  by_cases h : r ≤ ∑ k ∈ range n, d k ω
  · rw [Set.indicator_of_mem (show ω ∈ {ω | r ≤ ∑ k ∈ range n, d k ω} from h)]
    exact Real.one_le_exp (mul_nonneg (div_nonneg hr hv.le) (by linarith))
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | r ≤ ∑ k ∈ range n, d k ω} from h)]
    exact (Real.exp_pos _).le

/-- **Azuma two-sided tail**: `P(r ≤ |S_n|) ≤ 2 exp(−r²/(2v))`. -/
theorem prodProb_le_abs_sum_le_exp (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {d : ℕ → (Fin T → α) → ℝ} {c : ℕ → ℝ} (hd : IsBoundedMartDiff p d c) {n : ℕ} (hn : n ≤ T)
    {r v : ℝ} (hr : 0 ≤ r) (hv : 0 < v) (hcv : ∑ k ∈ range n, c k ^ 2 ≤ v) :
    prodProb p T {ω | r ≤ |∑ k ∈ range n, d k ω|} ≤ 2 * Real.exp (-r ^ 2 / (2 * v)) := by
  have hpos := sum_prodWeight_mul_exp_sub_le hp0 hp1 hd hn (r := r) hv hcv
  have hneg := sum_prodWeight_mul_exp_sub_le hp0 hp1 hd.neg hn (r := r) hv hcv
  refine (prodProb_le_sum_of_indicator_le hp0 (g := fun ω ↦
      Real.exp (r / v * (∑ k ∈ range n, d k ω - r)) +
        Real.exp (r / v * (∑ k ∈ range n, -d k ω - r))) fun ω ↦ ?_).trans ?_
  · have h1 := (Real.exp_pos (r / v * (∑ k ∈ range n, d k ω - r))).le
    have h2 := (Real.exp_pos (r / v * (∑ k ∈ range n, -d k ω - r))).le
    have hl : 0 ≤ r / v := div_nonneg hr hv.le
    by_cases h : r ≤ |∑ k ∈ range n, d k ω|
    · rw [Set.indicator_of_mem (show ω ∈ {ω | r ≤ |∑ k ∈ range n, d k ω|} from h)]
      simp only [sum_neg_distrib] at h2 ⊢
      rcases le_abs'.mp h with h' | h'
      · have := Real.one_le_exp (mul_nonneg hl (show 0 ≤ -∑ k ∈ range n, d k ω - r by linarith))
        linarith
      · have := Real.one_le_exp (mul_nonneg hl (show 0 ≤ ∑ k ∈ range n, d k ω - r by linarith))
        linarith
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | r ≤ |∑ k ∈ range n, d k ω|} from h)]
      exact add_nonneg h1 h2
  · simp only [mul_add, sum_add_distrib]
    linarith

/-- **Azuma radius form**: `P(√(2v log(2/δ)) ≤ |S_n|) ≤ δ` for `0 < δ ≤ 1`. -/
theorem prodProb_sqrt_le_abs_sum_le (hp0 : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    {d : ℕ → (Fin T → α) → ℝ} {c : ℕ → ℝ} (hd : IsBoundedMartDiff p d c) {n : ℕ} (hn : n ≤ T)
    {v δ : ℝ} (hv : 0 < v) (hcv : ∑ k ∈ range n, c k ^ 2 ≤ v) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    prodProb p T {ω | Real.sqrt (2 * v * Real.log (2 / δ)) ≤ |∑ k ∈ range n, d k ω|} ≤ δ := by
  have hlog : 0 ≤ Real.log (2 / δ) :=
    Real.log_nonneg ((le_div_iff₀ hδ).2 (by linarith))
  have h := prodProb_le_abs_sum_le_exp hp0 hp1 hd hn (Real.sqrt_nonneg (2 * v * Real.log (2 / δ))) hv hcv
  rw [Real.sq_sqrt (by positivity)] at h
  have he : -(2 * v * Real.log (2 / δ)) / (2 * v) = -Real.log (2 / δ) := by
    field_simp
  rw [he, Real.exp_neg, Real.exp_log (by positivity)] at h
  calc _ ≤ 2 * (2 / δ)⁻¹ := h
    _ = δ := by field_simp

end StatisticalRL.Probability.PathAzuma
