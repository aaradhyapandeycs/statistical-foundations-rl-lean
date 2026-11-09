import Formalization.Probability.SteinGaussian

/-!
# Berry–Esseen bound by Stein's method (independent, non-identical summands)

Setting: a finite product of finite laws. Coordinates `ω i ∈ X i` (`X i` finite) are independent
with laws `p i : X i → ℝ` (`p i ≥ 0`, `∑ₓ p i x = 1`); the expectation of `F : (∀ i, X i) → ℝ` is
`pexp p F = ∑_ω (∏ᵢ p i (ω i)) F ω`. The summands are `ξ i (ω i)` with `ξ i : X i → ℝ`, so they are
independent, arbitrary (non-identically distributed) and finitely supported. Every finite
family of independent finitely supported real random variables has this form.

Main results (normalised so that `∑ᵢ E ξᵢ² = 1`, with `β = ∑ᵢ E|ξᵢ|³`):

* `pexp_comp_coord` (independence / conditioning on one coordinate);
* `pexp_mul_eq_sum_resample` (the Stein identity `E[W g(W)] = ∑ᵢ E ∑_y pᵢ(y) ξᵢ(y)(g(W⁽ⁱ⁾+ξᵢ(y)) -
  g(W⁽ⁱ⁾))`, `W⁽ⁱ⁾ = W - ξᵢ`), valid for every `g : ℝ → ℝ`;
* `pexp_intervalInd_sumStat_mul_le` (concentration inequality for a general family) and
  `pexp_intervalInd_looStat_le` (`P(a ≤ W⁽ⁱ⁾ ≤ b) ≤ 2(b - a) + 8β` when `β ≤ 1/8`);
* `berryEsseen_stein`: `|P(W ≤ z) - Φ(z)| ≤ 26 β` for every `z`.
-/

open MeasureTheory ProbabilityTheory Real Set Finset
open scoped Interval

namespace StatisticalRL.Probability.Stein

/-! ## Weighted sums -/

section Weighted

variable {α : Type*} [Fintype α]

/-- `∑ q (f - ∑ q f)² = ∑ q f² - (∑ q f)²` for probability weights `q`. -/
theorem sum_mul_sub_mean_sq {q : α → ℝ} (hq1 : ∑ a, q a = 1) (f : α → ℝ) :
    ∑ a, q a * (f a - ∑ b, q b * f b) ^ 2 = ∑ a, q a * f a ^ 2 - (∑ a, q a * f a) ^ 2 := by
  set m := ∑ b, q b * f b
  have h : ∀ a, q a * (f a - m) ^ 2 = q a * f a ^ 2 - 2 * m * (q a * f a) + m ^ 2 * q a :=
    fun a ↦ by ring
  simp only [h, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hq1]
  ring

/-- Weighted Cauchy–Schwarz: `(∑ q |f|)² ≤ ∑ q f²`. -/
theorem sq_sum_mul_abs_le {q : α → ℝ} (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∑ a, q a = 1) (f : α → ℝ) :
    (∑ a, q a * |f a|) ^ 2 ≤ ∑ a, q a * f a ^ 2 := by
  have h := sum_mul_sub_mean_sq hq1 fun a ↦ |f a|
  have h0 : 0 ≤ ∑ a, q a * (|f a| - ∑ b, q b * |f b|) ^ 2 :=
    Finset.sum_nonneg fun a _ ↦ mul_nonneg (hq0 a) (sq_nonneg _)
  simp only [sq_abs] at h
  linarith

/-- `E|f| ≤ 1` when `E f² ≤ 1`. -/
theorem sum_mul_abs_le_one {q : α → ℝ} (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∑ a, q a = 1) {f : α → ℝ}
    (h : ∑ a, q a * f a ^ 2 ≤ 1) : ∑ a, q a * |f a| ≤ 1 := by
  have h1 := (sq_sum_mul_abs_le hq0 hq1 f).trans h
  have h2 : 0 ≤ ∑ a, q a * |f a| := Finset.sum_nonneg fun a _ ↦ mul_nonneg (hq0 a) (abs_nonneg _)
  nlinarith

/-- Chebyshev's association inequality for `|x|` and `x²`: `E|f| · E f² ≤ E|f|³`. -/
theorem sum_abs_mul_sum_sq_le {q : α → ℝ} (hq0 : ∀ a, 0 ≤ q a) (hq1 : ∑ a, q a = 1) (f : α → ℝ) :
    (∑ a, q a * |f a|) * (∑ a, q a * f a ^ 2) ≤ ∑ a, q a * |f a| ^ 3 := by
  have hterm : ∀ a b, 0 ≤ q a * q b * ((|f a| - |f b|) * (f a ^ 2 - f b ^ 2)) := by
    intro a b
    refine mul_nonneg (mul_nonneg (hq0 a) (hq0 b)) ?_
    have : f a ^ 2 - f b ^ 2 = (|f a| - |f b|) * (|f a| + |f b|) := by
      rw [← sq_abs (f a), ← sq_abs (f b)]; ring
    rw [this, ← mul_assoc]
    exact mul_nonneg (mul_self_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  have h0 : 0 ≤ ∑ a, ∑ b, q a * q b * ((|f a| - |f b|) * (f a ^ 2 - f b ^ 2)) :=
    Finset.sum_nonneg fun a _ ↦ Finset.sum_nonneg fun b _ ↦ hterm a b
  have hexp : ∑ a, ∑ b, q a * q b * ((|f a| - |f b|) * (f a ^ 2 - f b ^ 2)) =
      (∑ a, q a * |f a| ^ 3) * (∑ b, q b) - (∑ a, q a * |f a|) * (∑ b, q b * f b ^ 2) -
        (∑ a, q a * f a ^ 2) * (∑ b, q b * |f b|) + (∑ a, q a) * (∑ b, q b * |f b| ^ 3) := by
    simp only [Finset.sum_mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
    have ha : f a ^ 2 = |f a| ^ 2 := (sq_abs _).symm
    have hb : f b ^ 2 = |f b| ^ 2 := (sq_abs _).symm
    rw [ha, hb]
    ring
  rw [hexp, hq1] at h0
  linarith

end Weighted

/-! ## Product expectation -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]

/-- Expectation under the product of the finite laws `p i`. -/
def pexp (p : ∀ i, X i → ℝ) (F : (∀ i, X i) → ℝ) : ℝ := ∑ ω, (∏ i, p i (ω i)) * F ω

omit [DecidableEq ι] [∀ i, Fintype (X i)] in
theorem prod_weight_nonneg {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x) (ω : ∀ i, X i) :
    0 ≤ ∏ i, p i (ω i) :=
  Finset.prod_nonneg fun i _ ↦ hp0 i (ω i)

theorem sum_prod_weight {p : ∀ i, X i → ℝ} (hp1 : ∀ i, ∑ x, p i x = 1) :
    ∑ ω : ∀ i, X i, ∏ i, p i (ω i) = 1 := by
  have h := Finset.prod_univ_sum (fun i ↦ (Finset.univ : Finset (X i))) (fun i x ↦ p i x)
  rw [Fintype.piFinset_univ] at h
  rw [← h]
  simp [hp1]

theorem pexp_add (p : ∀ i, X i → ℝ) (F G : (∀ i, X i) → ℝ) :
    pexp p (fun ω ↦ F ω + G ω) = pexp p F + pexp p G := by
  simp only [pexp, mul_add, Finset.sum_add_distrib]

theorem pexp_sub (p : ∀ i, X i → ℝ) (F G : (∀ i, X i) → ℝ) :
    pexp p (fun ω ↦ F ω - G ω) = pexp p F - pexp p G := by
  simp only [pexp, mul_sub, Finset.sum_sub_distrib]

theorem pexp_const_mul (p : ∀ i, X i → ℝ) (c : ℝ) (F : (∀ i, X i) → ℝ) :
    pexp p (fun ω ↦ c * F ω) = c * pexp p F := by
  simp only [pexp, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ω _ ↦ by ring

theorem pexp_const {p : ∀ i, X i → ℝ} (hp1 : ∀ i, ∑ x, p i x = 1) (c : ℝ) :
    pexp p (fun _ ↦ c) = c := by
  rw [pexp, ← Finset.sum_mul, sum_prod_weight hp1, one_mul]

theorem pexp_sum {κ : Type*} (s : Finset κ) (p : ∀ i, X i → ℝ) (F : κ → (∀ i, X i) → ℝ) :
    pexp p (fun ω ↦ ∑ k ∈ s, F k ω) = ∑ k ∈ s, pexp p (F k) := by
  simp only [pexp, Finset.mul_sum]
  exact Finset.sum_comm

theorem pexp_mono {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x) {F G : (∀ i, X i) → ℝ}
    (h : ∀ ω, F ω ≤ G ω) : pexp p F ≤ pexp p G :=
  Finset.sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left (h ω) (prod_weight_nonneg hp0 ω)

theorem pexp_nonneg {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x) {F : (∀ i, X i) → ℝ}
    (h : ∀ ω, 0 ≤ F ω) : 0 ≤ pexp p F :=
  Finset.sum_nonneg fun ω _ ↦ mul_nonneg (prod_weight_nonneg hp0 ω) (h ω)

theorem abs_pexp_le {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x) (F : (∀ i, X i) → ℝ) :
    |pexp p F| ≤ pexp p (fun ω ↦ |F ω|) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [abs_mul, abs_of_nonneg (prod_weight_nonneg hp0 ω)]

/-- `(E|F|)² ≤ E F²` under the product law. -/
theorem sq_pexp_abs_le {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x) (hp1 : ∀ i, ∑ x, p i x = 1)
    (F : (∀ i, X i) → ℝ) : pexp p (fun ω ↦ |F ω|) ^ 2 ≤ pexp p (fun ω ↦ F ω ^ 2) :=
  sq_sum_mul_abs_le (prod_weight_nonneg hp0) (sum_prod_weight hp1) F

/-! ## Independence: splitting off one coordinate -/

theorem pexp_split (p : ∀ i, X i → ℝ) (i : ι) (G : (∀ j, X j) → ℝ) :
    pexp p G = ∑ r : (∀ j : {j : ι // j ≠ i}, X j), (∏ j : {j : ι // j ≠ i}, p j (r j)) *
      ∑ c, p i c * G ((Equiv.piSplitAt i X).symm (c, r)) := by
  set e := Equiv.piSplitAt i X
  rw [pexp, ← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ ↦ ?_
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  have h1 : e.symm (c, r) i = c := by simp [e, Equiv.piSplitAt]
  have h2 : ∀ j : {j : ι // j ≠ i}, e.symm (c, r) j.1 = r j := by
    intro j; simp [e, Equiv.piSplitAt, j.2]
  rw [h1]
  simp only [h2]
  ring

omit [Fintype ι] [∀ i, Fintype (X i)] in
theorem update_piSplitAt_symm (i : ι) (c b : X i) (r : ∀ j : {j : ι // j ≠ i}, X j) :
    Function.update ((Equiv.piSplitAt i X).symm (c, r)) i b = (Equiv.piSplitAt i X).symm (b, r) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [Equiv.piSplitAt]
  · rw [Function.update_of_ne hj]; simp [Equiv.piSplitAt, hj]

/-- **Resampling one coordinate** does not change expectations. -/
theorem pexp_resample {p : ∀ i, X i → ℝ} (hp1 : ∀ i, ∑ x, p i x = 1) (i : ι)
    (H : (∀ j, X j) → ℝ) :
    pexp p H = pexp p (fun ω ↦ ∑ y, p i y * H (Function.update ω i y)) := by
  rw [pexp_split p i H, pexp_split p i]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  congr 1
  simp only [update_piSplitAt_symm]
  rw [← Finset.sum_mul, hp1, one_mul]

/-- **Independence of one coordinate from the others.** If `F y ω` does not depend on `ω i`,
then `E F(ω i, ω) = E ∑_y p i y F(y, ω)`. -/
theorem pexp_comp_coord {p : ∀ i, X i → ℝ} (hp1 : ∀ i, ∑ x, p i x = 1) (i : ι)
    (F : X i → (∀ j, X j) → ℝ) (hF : ∀ y ω b, F y (Function.update ω i b) = F y ω) :
    pexp p (fun ω ↦ F (ω i) ω) = pexp p (fun ω ↦ ∑ y, p i y * F y ω) := by
  rw [pexp_resample hp1 i]
  unfold pexp
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  congr 1
  refine Finset.sum_congr rfl fun y _ ↦ ?_
  rw [Function.update_self, hF]

/-- Marginal law of one coordinate. -/
theorem pexp_coord {p : ∀ i, X i → ℝ} (hp1 : ∀ i, ∑ x, p i x = 1) (i : ι) (g : X i → ℝ) :
    pexp p (fun ω ↦ g (ω i)) = ∑ y, p i y * g y := by
  rw [pexp_comp_coord hp1 i (fun y _ ↦ g y) (fun _ _ _ ↦ rfl), pexp_const hp1]

/-! ## Sums of independent summands -/

/-- `W = ∑ᵢ ξᵢ(ωᵢ)`. -/
def sumStat (ξ : ∀ i, X i → ℝ) (ω : ∀ i, X i) : ℝ := ∑ j, ξ j (ω j)

/-- The leave-one-out sum `W⁽ⁱ⁾ = W - ξᵢ(ωᵢ)`. -/
def looStat (ξ : ∀ i, X i → ℝ) (i : ι) (ω : ∀ i, X i) : ℝ := sumStat ξ ω - ξ i (ω i)

omit [∀ i, Fintype (X i)] in
theorem looStat_eq (ξ : ∀ i, X i → ℝ) (i : ι) (ω : ∀ i, X i) :
    looStat ξ i ω = ∑ j ∈ Finset.univ.erase i, ξ j (ω j) := by
  rw [looStat, sumStat, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  ring

omit [∀ i, Fintype (X i)] in
theorem looStat_update (ξ : ∀ i, X i → ℝ) (i : ι) (ω : ∀ i, X i) (b : X i) :
    looStat ξ i (Function.update ω i b) = looStat ξ i ω := by
  rw [looStat_eq, looStat_eq]
  exact Finset.sum_congr rfl fun j hj ↦ by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

omit [DecidableEq ι] [∀ i, Fintype (X i)] in
theorem looStat_add (ξ : ∀ i, X i → ℝ) (i : ι) (ω : ∀ i, X i) :
    looStat ξ i ω + ξ i (ω i) = sumStat ξ ω := by
  rw [looStat]; ring

omit [∀ i, Fintype (X i)] in
/-- The leave-`i`-out sum is the full sum of the family with `ξᵢ` replaced by `0`. -/
theorem sumStat_dropCoord (ξ : ∀ i, X i → ℝ) (i : ι) (ω : ∀ i, X i) :
    sumStat (fun j x ↦ if j = i then 0 else ξ j x) ω = looStat ξ i ω := by
  rw [looStat_eq, sumStat, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [if_true, zero_add]
  exact Finset.sum_congr rfl fun j hj ↦ by rw [if_neg (Finset.ne_of_mem_erase hj)]

/-- **Stein identity, pathwise form.** For mean-zero summands and any `g`,
`E[W g(W)] = ∑ᵢ E[ξᵢ (g(W) - g(W⁽ⁱ⁾))]`. -/
theorem pexp_mul_eq_sum_loo {p : ∀ i, X i → ℝ} (hp1 : ∀ i, ∑ x, p i x = 1)
    {ξ : ∀ i, X i → ℝ} (hmean : ∀ i, ∑ x, p i x * ξ i x = 0) (g : ℝ → ℝ) :
    pexp p (fun ω ↦ sumStat ξ ω * g (sumStat ξ ω)) =
      ∑ i, pexp p (fun ω ↦ ξ i (ω i) * (g (sumStat ξ ω) - g (looStat ξ i ω))) := by
  have hzero : ∀ i, pexp p (fun ω ↦ ξ i (ω i) * g (looStat ξ i ω)) = 0 := by
    intro i
    rw [pexp_comp_coord hp1 i (fun y ω ↦ ξ i y * g (looStat ξ i ω))
      (fun y ω b ↦ by simp only [looStat_update])]
    have : ∀ ω, ∑ y, p i y * (ξ i y * g (looStat ξ i ω)) = 0 := fun ω ↦ by
      simp only [← mul_assoc, ← Finset.sum_mul, hmean i, zero_mul]
    simp only [this]
    exact pexp_const hp1 0
  have h1 : pexp p (fun ω ↦ sumStat ξ ω * g (sumStat ξ ω)) =
      ∑ i, pexp p (fun ω ↦ ξ i (ω i) * g (sumStat ξ ω)) := by
    rw [← pexp_sum]
    unfold sumStat
    simp only [Finset.sum_mul]
  rw [h1]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [mul_sub]
  rw [pexp_sub, hzero, sub_zero]

/-- **Stein identity, resampled form.**
`E[W g(W)] = ∑ᵢ E ∑_y pᵢ(y) ξᵢ(y) (g(W⁽ⁱ⁾ + ξᵢ(y)) - g(W⁽ⁱ⁾))`. -/
theorem pexp_mul_eq_sum_resample {p : ∀ i, X i → ℝ} (hp1 : ∀ i, ∑ x, p i x = 1)
    {ξ : ∀ i, X i → ℝ} (hmean : ∀ i, ∑ x, p i x * ξ i x = 0) (g : ℝ → ℝ) :
    pexp p (fun ω ↦ sumStat ξ ω * g (sumStat ξ ω)) =
      ∑ i, pexp p (fun ω ↦ ∑ y, p i y * (ξ i y *
        (g (looStat ξ i ω + ξ i y) - g (looStat ξ i ω)))) := by
  rw [pexp_mul_eq_sum_loo hp1 hmean]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have := pexp_comp_coord hp1 i
    (fun y ω ↦ ξ i y * (g (looStat ξ i ω + ξ i y) - g (looStat ξ i ω)))
    (fun y ω b ↦ by simp only [looStat_update])
  simp only [looStat_add] at this
  exact this

/-- `E W² = ∑ᵢ E ξᵢ²` for independent mean-zero summands. -/
theorem pexp_sumStat_sq {p : ∀ i, X i → ℝ} (hp1 : ∀ i, ∑ x, p i x = 1)
    {ξ : ∀ i, X i → ℝ} (hmean : ∀ i, ∑ x, p i x * ξ i x = 0) :
    pexp p (fun ω ↦ sumStat ξ ω ^ 2) = ∑ i, ∑ x, p i x * ξ i x ^ 2 := by
  have h := pexp_mul_eq_sum_resample hp1 hmean id
  simp only [id, add_sub_cancel_left] at h
  rw [show (fun ω ↦ sumStat ξ ω ^ 2) = fun ω ↦ sumStat ξ ω * sumStat ξ ω from
    funext fun ω ↦ sq _, h]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [pexp_const hp1]
  exact Finset.sum_congr rfl fun x _ ↦ by ring

/-! ## Concentration inequality -/

theorem neg_abs_le_mul_of_mem_unit {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) (y : ℝ) : -|y| ≤ t * y := by
  have : |t * y| ≤ |y| := by
    rw [abs_mul, abs_of_nonneg h0]; exact mul_le_of_le_one_left (abs_nonneg y) h1
  exact (abs_le.1 this).1

/-- **Concentration inequality** for a sum of independent mean-zero summands `η` with
`B² = ∑ E ηᵢ² ≤ 1` and `β = ∑ E|ηᵢ|³`: for `a ≤ b` and `δ > 0`,
`P(a ≤ W ≤ b) (B² - β/(4δ)) ≤ (b - a)/2 + 2δ`. -/
theorem pexp_intervalInd_sumStat_mul_le {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {η : ∀ i, X i → ℝ} (hmean : ∀ i, ∑ x, p i x * η i x = 0)
    (hB : ∑ i, ∑ x, p i x * η i x ^ 2 ≤ 1) {a b δ : ℝ} (hab : a ≤ b) (hδ : 0 < δ) :
    pexp p (fun ω ↦ intervalInd a b (sumStat η ω)) *
        (∑ i, ∑ x, p i x * η i x ^ 2 - (∑ i, ∑ x, p i x * |η i x| ^ 3) / (4 * δ)) ≤
      (b - a) / 2 + 2 * δ := by
  set g := ramp a b δ with hg
  set P := pexp p (fun ω ↦ intervalInd a b (sumStat η ω)) with hP
  set h : ℝ → ℝ := fun x ↦ |x| * min δ |x| with hh
  set H : (∀ i, X i) → ℝ := fun ω ↦ ∑ i, h (η i (ω i)) with hH
  set mi : ι → ℝ := fun i ↦ ∑ x, p i x * h (η i x) with hmi
  set m := ∑ i, mi i with hm
  set c := (b - a) / 2 + δ with hc
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have hP0 : 0 ≤ P := pexp_nonneg hp0 fun ω ↦ intervalInd_nonneg _ _ _
  -- upper bound for `E[W g(W)]`
  have hEV : pexp p (fun ω ↦ |sumStat η ω|) ≤ 1 :=
    sum_mul_abs_le_one (prod_weight_nonneg hp0) (sum_prod_weight hp1)
      (show pexp p (fun ω ↦ sumStat η ω ^ 2) ≤ 1 by rw [pexp_sumStat_sq hp1 hmean]; exact hB)
  have hup : pexp p (fun ω ↦ sumStat η ω * g (sumStat η ω)) ≤ c := by
    calc pexp p (fun ω ↦ sumStat η ω * g (sumStat η ω))
          ≤ pexp p (fun ω ↦ c * |sumStat η ω|) := pexp_mono hp0 fun ω ↦ by
            calc sumStat η ω * g (sumStat η ω) ≤ |sumStat η ω * g (sumStat η ω)| := le_abs_self _
              _ = |sumStat η ω| * |g (sumStat η ω)| := abs_mul _ _
              _ ≤ |sumStat η ω| * c :=
                  mul_le_mul_of_nonneg_left (abs_ramp_le hab hδ.le _) (abs_nonneg _)
              _ = c * |sumStat η ω| := mul_comm _ _
      _ = c * pexp p (fun ω ↦ |sumStat η ω|) := pexp_const_mul p c _
      _ ≤ c * 1 := mul_le_mul_of_nonneg_left hEV hc0
      _ = c := mul_one c
  -- lower bound: `E[1_A H] ≤ E[W g(W)]`
  have hlow : pexp p (fun ω ↦ intervalInd a b (sumStat η ω) * H ω) ≤
      pexp p (fun ω ↦ sumStat η ω * g (sumStat η ω)) := by
    rw [pexp_mul_eq_sum_loo hp1 hmean, ← pexp_sum]
    refine pexp_mono hp0 fun ω ↦ ?_
    simp only [looStat]
    unfold intervalInd
    split_ifs with hA
    · rw [one_mul]
      exact Finset.sum_le_sum fun i _ ↦ abs_mul_min_le_mul_ramp_sub hδ hA.1 hA.2 _
    · rw [zero_mul]
      exact Finset.sum_nonneg fun i _ ↦ mul_ramp_sub_nonneg _ _ _ _ _
  -- `E|H - m| ≤ δ`
  set u : ∀ i, X i → ℝ := fun i x ↦ h (η i x) - mi i with hu
  have humean : ∀ i, ∑ x, p i x * u i x = 0 := by
    intro i
    simp only [hu, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]
    simp [hmi]
  have hsumu : ∀ ω, sumStat u ω = H ω - m := by
    intro ω
    simp only [sumStat, hu, Finset.sum_sub_distrib, hH, hm]
  have hvaru : pexp p (fun ω ↦ (H ω - m) ^ 2) ≤ δ ^ 2 := by
    have h1 := pexp_sumStat_sq hp1 humean
    simp only [hsumu] at h1
    rw [h1]
    calc ∑ i, ∑ x, p i x * u i x ^ 2 ≤ ∑ i, ∑ x, p i x * (δ ^ 2 * η i x ^ 2) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have hv := sum_mul_sub_mean_sq (hp1 i) fun x ↦ h (η i x)
          have hv' : ∑ x, p i x * u i x ^ 2 ≤ ∑ x, p i x * h (η i x) ^ 2 := by
            simp only [hu, hmi]
            rw [hv]
            nlinarith [sq_nonneg (∑ x, p i x * h (η i x))]
          refine hv'.trans (Finset.sum_le_sum fun x _ ↦ ?_)
          exact mul_le_mul_of_nonneg_left (sq_abs_mul_min_le hδ.le _) (hp0 i x)
      _ = δ ^ 2 * ∑ i, ∑ x, p i x * η i x ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun x _ ↦ by ring
      _ ≤ δ ^ 2 * 1 := mul_le_mul_of_nonneg_left hB (sq_nonneg δ)
      _ = δ ^ 2 := mul_one _
  have hdev : pexp p (fun ω ↦ |H ω - m|) ≤ δ := by
    have h1 := (sq_pexp_abs_le hp0 hp1 fun ω ↦ H ω - m).trans hvaru
    have h2 : 0 ≤ pexp p (fun ω ↦ |H ω - m|) := pexp_nonneg hp0 fun ω ↦ abs_nonneg _
    nlinarith
  -- `P m ≤ E[1_A H] + E|H - m|`
  have hPm : P * m ≤ pexp p (fun ω ↦ intervalInd a b (sumStat η ω) * H ω) +
      pexp p (fun ω ↦ |H ω - m|) := by
    rw [← pexp_add, hP, mul_comm, ← pexp_const_mul]
    refine pexp_mono hp0 fun ω ↦ ?_
    have := neg_abs_le_mul_of_mem_unit (intervalInd_nonneg a b (sumStat η ω))
      (intervalInd_le_one a b (sumStat η ω)) (H ω - m)
    nlinarith
  -- `m ≥ B² - β/(4δ)`
  have hmlow : ∑ i, ∑ x, p i x * η i x ^ 2 - (∑ i, ∑ x, p i x * |η i x| ^ 3) / (4 * δ) ≤ m := by
    have : ∑ i, ∑ x, p i x * η i x ^ 2 - (∑ i, ∑ x, p i x * |η i x| ^ 3) / (4 * δ) =
        ∑ i, ∑ x, p i x * (η i x ^ 2 - |η i x| ^ 3 / (4 * δ)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_div, mul_div_assoc]
    rw [this, hm]
    exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun x _ ↦
      mul_le_mul_of_nonneg_left (sq_sub_le_abs_mul_min hδ _) (hp0 i x)
  calc P * (∑ i, ∑ x, p i x * η i x ^ 2 - (∑ i, ∑ x, p i x * |η i x| ^ 3) / (4 * δ))
        ≤ P * m := mul_le_mul_of_nonneg_left hmlow hP0
    _ ≤ c + δ := by linarith
    _ = (b - a) / 2 + 2 * δ := by rw [hc]; ring

omit [DecidableEq ι] [∀ i, Fintype (X i)] in
theorem sum_ite_eq_zero_sub (S : ι → ℝ) (i : ι) [DecidableEq ι] :
    ∑ j, (if j = i then 0 else S j) = ∑ j, S j - S i := by
  rw [← Finset.add_sum_erase _ S (Finset.mem_univ i),
    ← Finset.add_sum_erase _ (fun j ↦ if j = i then 0 else S j) (Finset.mem_univ i)]
  simp only [if_true, zero_add, add_sub_cancel_left]
  exact Finset.sum_congr rfl fun j hj ↦ by rw [if_neg (Finset.ne_of_mem_erase hj)]

theorem sq_le_quarter_add (x : ℝ) : x ^ 2 ≤ 1 / 4 + 2 * |x| ^ 3 := by
  have ha := abs_nonneg x
  rw [← sq_abs x]
  rcases le_total |x| (1 / 2) with h | h
  · nlinarith
  · nlinarith [mul_nonneg ha ha]

omit [DecidableEq ι] in
/-- The third-moment sum is positive when the variances sum to `1`. -/
theorem lyapunov_pos {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x) {ξ : ∀ i, X i → ℝ}
    (hvar : ∑ i, ∑ x, p i x * ξ i x ^ 2 = 1) : 0 < ∑ i, ∑ x, p i x * |ξ i x| ^ 3 := by
  by_contra hneg
  push_neg at hneg
  have hnn : ∀ i x, 0 ≤ p i x * |ξ i x| ^ 3 := fun i x ↦ mul_nonneg (hp0 i x) (by positivity)
  have hβ0 : ∑ i, ∑ x, p i x * |ξ i x| ^ 3 = 0 :=
    le_antisymm hneg (Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun x _ ↦ hnn i x)
  have h1 : ∀ i x, p i x * |ξ i x| ^ 3 = 0 := by
    intro i x
    have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦
      Finset.sum_nonneg fun x _ ↦ hnn i x).1 hβ0 i (Finset.mem_univ _)
    exact (Finset.sum_eq_zero_iff_of_nonneg fun x _ ↦ hnn i x).1 this x (Finset.mem_univ _)
  have h2 : ∀ i x, p i x * ξ i x ^ 2 = 0 := by
    intro i x
    rcases mul_eq_zero.1 (h1 i x) with h | h
    · rw [h, zero_mul]
    · have : ξ i x = 0 := by simpa using h
      rw [this]; ring
  simp [h2] at hvar

/-- **Concentration inequality for the leave-one-out sum.** If `∑ E ξ² = 1` and
`β = ∑ E|ξ|³ ≤ 1/8`, then `P(a ≤ W⁽ⁱ⁾ ≤ b) ≤ 2(b - a) + 8β`. -/
theorem pexp_intervalInd_looStat_le {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → ℝ} (hmean : ∀ i, ∑ x, p i x * ξ i x = 0)
    (hvar : ∑ i, ∑ x, p i x * ξ i x ^ 2 = 1)
    (hβ : ∑ i, ∑ x, p i x * |ξ i x| ^ 3 ≤ 1 / 8) (i : ι) {a b : ℝ} (hab : a ≤ b) :
    pexp p (fun ω ↦ intervalInd a b (looStat ξ i ω)) ≤
      2 * (b - a) + 8 * ∑ i, ∑ x, p i x * |ξ i x| ^ 3 := by
  set β := ∑ i, ∑ x, p i x * |ξ i x| ^ 3 with hβdef
  have hβpos : 0 < β := lyapunov_pos hp0 hvar
  set η : ∀ j, X j → ℝ := fun j x ↦ if j = i then 0 else ξ j x with hη
  have hηmean : ∀ j, ∑ x, p j x * η j x = 0 := by
    intro j
    by_cases hj : j = i
    · simp [hη, hj]
    · simp only [hη, hj, if_false]; exact hmean j
  set si := ∑ x, p i x * ξ i x ^ 2 with hsi
  have hsi0 : 0 ≤ si := Finset.sum_nonneg fun x _ ↦ mul_nonneg (hp0 i x) (sq_nonneg _)
  have hB : ∑ j, ∑ x, p j x * η j x ^ 2 = 1 - si := by
    have : ∀ j, ∑ x, p j x * η j x ^ 2 =
        if j = i then 0 else ∑ x, p j x * ξ j x ^ 2 := by
      intro j
      by_cases hj : j = i
      · simp [hη, hj]
      · simp [hη, hj]
    simp only [this]
    rw [sum_ite_eq_zero_sub (fun j ↦ ∑ x, p j x * ξ j x ^ 2) i, hvar]
  have hγ : ∑ j, ∑ x, p j x * |η j x| ^ 3 ≤ β := by
    refine Finset.sum_le_sum fun j _ ↦ Finset.sum_le_sum fun x _ ↦ ?_
    by_cases hj : j = i
    · subst hj
      simp only [hη, if_true, abs_zero]
      norm_num
      exact mul_nonneg (hp0 _ x) (by positivity)
    · simp only [hη, hj, if_false, le_refl]
  have hsi : si ≤ 1 / 4 + 2 * β := by
    have hγi : ∑ x, p i x * |ξ i x| ^ 3 ≤ β :=
      Finset.single_le_sum (f := fun j ↦ ∑ x, p j x * |ξ j x| ^ 3)
        (fun j _ ↦ Finset.sum_nonneg fun x _ ↦ mul_nonneg (hp0 j x) (by positivity))
        (Finset.mem_univ i)
    calc si ≤ ∑ x, p i x * (1 / 4 + 2 * |ξ i x| ^ 3) :=
          Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (sq_le_quarter_add _) (hp0 i x)
      _ = 1 / 4 + 2 * ∑ x, p i x * |ξ i x| ^ 3 := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul,
            Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun x _ ↦ by ring
      _ ≤ 1 / 4 + 2 * β := by linarith
  have hconc := pexp_intervalInd_sumStat_mul_le hp0 hp1 hηmean (by rw [hB]; linarith) hab hβpos
  have hstat : (fun ω ↦ intervalInd a b (sumStat η ω)) =
      fun ω ↦ intervalInd a b (looStat ξ i ω) := by
    funext ω; rw [hη, sumStat_dropCoord]
  rw [hstat, hB] at hconc
  set P := pexp p (fun ω ↦ intervalInd a b (looStat ξ i ω))
  have hP0 : 0 ≤ P := pexp_nonneg hp0 fun ω ↦ intervalInd_nonneg _ _ _
  have hq : (∑ j, ∑ x, p j x * |η j x| ^ 3) / (4 * β) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hbr : 1 / 4 ≤ 1 - si - (∑ j, ∑ x, p j x * |η j x| ^ 3) / (4 * β) := by linarith
  nlinarith

/-! ## Berry–Esseen bound -/

/-- `E (W⁽ⁱ⁾)² = ∑ⱼ E ξⱼ² - E ξᵢ²`. -/
theorem pexp_looStat_sq {p : ∀ i, X i → ℝ} (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → ℝ}
    (hmean : ∀ i, ∑ x, p i x * ξ i x = 0) (i : ι) :
    pexp p (fun ω ↦ looStat ξ i ω ^ 2) =
      ∑ j, ∑ x, p j x * ξ j x ^ 2 - ∑ x, p i x * ξ i x ^ 2 := by
  set η : ∀ j, X j → ℝ := fun j x ↦ if j = i then 0 else ξ j x with hη
  have hηmean : ∀ j, ∑ x, p j x * η j x = 0 := by
    intro j
    by_cases hj : j = i
    · simp [hη, hj]
    · simp only [hη, hj, if_false]; exact hmean j
  have hstat : (fun ω ↦ looStat ξ i ω ^ 2) = fun ω ↦ sumStat η ω ^ 2 := by
    funext ω; rw [hη, sumStat_dropCoord]
  rw [hstat, pexp_sumStat_sq hp1 hηmean]
  have : ∀ j, ∑ x, p j x * η j x ^ 2 = if j = i then 0 else ∑ x, p j x * ξ j x ^ 2 := by
    intro j
    by_cases hj : j = i
    · simp [hη, hj]
    · simp [hη, hj]
  simp only [this]
  exact sum_ite_eq_zero_sub (fun j ↦ ∑ x, p j x * ξ j x ^ 2) i

theorem pexp_abs_looStat_le_one {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → ℝ} (hmean : ∀ i, ∑ x, p i x * ξ i x = 0)
    (hvar : ∑ i, ∑ x, p i x * ξ i x ^ 2 = 1) (i : ι) :
    pexp p (fun ω ↦ |looStat ξ i ω|) ≤ 1 := by
  refine sum_mul_abs_le_one (prod_weight_nonneg hp0) (sum_prod_weight hp1) ?_
  show pexp p (fun ω ↦ looStat ξ i ω ^ 2) ≤ 1
  rw [pexp_looStat_sq hp1 hmean, hvar]
  have : 0 ≤ ∑ x, p i x * ξ i x ^ 2 :=
    Finset.sum_nonneg fun x _ ↦ mul_nonneg (hp0 i x) (sq_nonneg _)
  linarith

/-- Exchange of the product expectation and an interval integral. -/
theorem pexp_intervalIntegral (p : ∀ i, X i → ℝ) (G : (∀ i, X i) → ℝ → ℝ) (u : ℝ)
    (hG : ∀ ω, IntervalIntegrable (G ω) volume 0 u) :
    pexp p (fun ω ↦ ∫ t in (0 : ℝ)..u, G ω t) = ∫ t in (0 : ℝ)..u, pexp p (fun ω ↦ G ω t) := by
  unfold pexp
  rw [intervalIntegral.integral_finset_sum fun ω _ ↦ (hG ω).const_mul _]
  exact Finset.sum_congr rfl fun ω _ ↦ (intervalIntegral.integral_const_mul _ _).symm

/-- `u c - E[f_z(V+u) - f_z(V)] = ∫₀ᵘ E[c - f_z'(V+t)] dt`. -/
theorem mul_sub_pexp_steinSol_eq {p : ∀ i, X i → ℝ} (hp1 : ∀ i, ∑ x, p i x = 1) (z : ℝ)
    (V : (∀ i, X i) → ℝ) (c u : ℝ) :
    u * c - pexp p (fun ω ↦ steinSol z (V ω + u) - steinSol z (V ω)) =
      ∫ t in (0 : ℝ)..u, pexp p (fun ω ↦ c - steinDeriv z (V ω + t)) := by
  rw [← pexp_intervalIntegral p (fun ω t ↦ c - steinDeriv z (V ω + t)) u fun ω ↦
    IntervalIntegrable.sub intervalIntegrable_const (intervalIntegrable_steinDeriv_comp z (V ω) 0 u)]
  have : ∀ ω, ∫ t in (0 : ℝ)..u, (c - steinDeriv z (V ω + t)) =
      u * c - (steinSol z (V ω + u) - steinSol z (V ω)) := by
    intro ω
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (intervalIntegrable_steinDeriv_comp z (V ω) 0 u), intervalIntegral.integral_const,
      smul_eq_mul, sub_zero, steinSol_add_sub_eq_integral]
  simp only [this]
  rw [pexp_sub p (fun _ ↦ u * c) (fun ω ↦ steinSol z (V ω + u) - steinSol z (V ω)),
    pexp_const hp1]

theorem abs_le_abs_of_mem_uIoc {t u : ℝ} (ht : t ∈ Ι 0 u) : |t| ≤ |u| := by
  rcases Set.mem_uIoc.1 ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [abs_le]; constructor <;> linarith [neg_abs_le u, le_abs_self u]
  · rw [abs_le]; constructor <;> linarith [neg_abs_le u, le_abs_self u, abs_nonneg u]

/-- The basic smoothing estimate of the Stein argument:
`|E[f_z'(W⁽ⁱ⁾+u) - f_z'(W⁽ⁱ⁾+t)]| ≤ 9(|u| + |t|) + 8β`. -/
theorem abs_pexp_steinDeriv_sub_le {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → ℝ} (hmean : ∀ i, ∑ x, p i x * ξ i x = 0)
    (hvar : ∑ i, ∑ x, p i x * ξ i x ^ 2 = 1)
    (hβ : ∑ i, ∑ x, p i x * |ξ i x| ^ 3 ≤ 1 / 8) (z : ℝ) (i : ι) (u t : ℝ) :
    |pexp p (fun ω ↦ steinDeriv z (looStat ξ i ω + u) - steinDeriv z (looStat ξ i ω + t))| ≤
      9 * (|u| + |t|) + 8 * ∑ i, ∑ x, p i x * |ξ i x| ^ 3 := by
  set β := ∑ i, ∑ x, p i x * |ξ i x| ^ 3
  have hut : 0 ≤ |u| + |t| := by positivity
  have hlen : (z - min u t) - (z - max u t) ≤ |u| + |t| := by
    rcases le_total u t with h | h
    · rw [min_eq_left h, max_eq_right h]; linarith [neg_abs_le u, le_abs_self t]
    · rw [min_eq_right h, max_eq_left h]; linarith [neg_abs_le t, le_abs_self u]
  have hconc := pexp_intervalInd_looStat_le hp0 hp1 hmean hvar hβ i
    (a := z - max u t) (b := z - min u t) (by linarith [min_le_max (a := u) (b := t)])
  have hEV := pexp_abs_looStat_le_one hp0 hp1 hmean hvar i
  calc _ ≤ pexp p (fun ω ↦ |steinDeriv z (looStat ξ i ω + u) -
          steinDeriv z (looStat ξ i ω + t)|) := abs_pexp_le hp0 _
    _ ≤ pexp p (fun ω ↦ (|u| + |t|) * 2 * |looStat ξ i ω| + (5 * (|u| + |t|) +
          intervalInd (z - max u t) (z - min u t) (looStat ξ i ω))) :=
        pexp_mono hp0 fun ω ↦ by
          have := abs_steinDeriv_sub_le z (looStat ξ i ω) u t
          linarith
    _ = (|u| + |t|) * 2 * pexp p (fun ω ↦ |looStat ξ i ω|) + (5 * (|u| + |t|) +
          pexp p (fun ω ↦ intervalInd (z - max u t) (z - min u t) (looStat ξ i ω))) := by
        rw [pexp_add, pexp_const_mul, pexp_add, pexp_const hp1]
    _ ≤ (|u| + |t|) * 2 * 1 + (5 * (|u| + |t|) + (2 * (|u| + |t|) + 8 * β)) := by
        gcongr
        exact hconc.trans (by linarith)
    _ = 9 * (|u| + |t|) + 8 * β := by ring

/-- **Berry–Esseen bound via Stein's method.** Let `ξᵢ(ωᵢ)` be independent (coordinates of a
finite product of finite laws `p i`), mean zero, with `∑ᵢ E ξᵢ² = 1`, and `W = ∑ᵢ ξᵢ`. Then for
every `z`,
`|P(W ≤ z) - Φ(z)| ≤ 26 ∑ᵢ E|ξᵢ|³`,
where `Φ(z) = (gaussianReal 0 1).real (Iic z)` is the standard normal distribution function. -/
theorem berryEsseen_stein {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → ℝ} (hmean : ∀ i, ∑ x, p i x * ξ i x = 0)
    (hvar : ∑ i, ∑ x, p i x * ξ i x ^ 2 = 1) (z : ℝ) :
    |pexp p (fun ω ↦ if sumStat ξ ω ≤ z then 1 else 0) - (gaussianReal 0 1).real (Iic z)| ≤
      26 * ∑ i, ∑ x, p i x * |ξ i x| ^ 3 := by
  rw [gaussianReal_real_Iic]
  set β := ∑ i, ∑ x, p i x * |ξ i x| ^ 3 with hβdef
  have hβpos : 0 < β := lyapunov_pos hp0 hvar
  set Pz := pexp p (fun ω ↦ if sumStat ξ ω ≤ z then 1 else 0) with hPz
  have hPz0 : 0 ≤ Pz := pexp_nonneg hp0 fun ω ↦ by split_ifs <;> norm_num
  have hPz1 : Pz ≤ 1 := by
    rw [← pexp_const hp1 (1 : ℝ)]
    exact pexp_mono hp0 fun ω ↦ by split_ifs <;> norm_num
  by_cases hβ : β ≤ 1 / 8
  swap
  · push_neg at hβ
    rw [abs_le]
    constructor <;> linarith [stdCDF_nonneg z, stdCDF_le_one z]
  set f := steinSol z
  set D := steinDeriv z
  set V : ι → (∀ i, X i) → ℝ := fun i ω ↦ looStat ξ i ω
  set s : ι → ℝ := fun i ↦ ∑ x, p i x * ξ i x ^ 2 with hs
  set c : ι → ℝ := fun i ↦ pexp p (fun ω ↦ ∑ x, p i x * D (V i ω + ξ i x)) with hc
  -- Step 1: `P(W ≤ z) - Φ(z) = E f'(W) - E W f(W)`.
  have h1 : Pz - stdCDF z =
      pexp p (fun ω ↦ D (sumStat ξ ω)) - pexp p (fun ω ↦ sumStat ξ ω * f (sumStat ξ ω)) := by
    have : pexp p (fun ω ↦ D (sumStat ξ ω)) =
        pexp p (fun ω ↦ sumStat ξ ω * f (sumStat ξ ω)) + Pz - stdCDF z := by
      simp only [D, steinDeriv]
      rw [pexp_sub, pexp_add, pexp_const hp1]
      rfl
    linarith
  -- Step 2: the Stein identity.
  have h2 : pexp p (fun ω ↦ sumStat ξ ω * f (sumStat ξ ω)) =
      ∑ i, ∑ y, p i y * ξ i y * pexp p (fun ω ↦ f (V i ω + ξ i y) - f (V i ω)) := by
    rw [pexp_mul_eq_sum_resample hp1 hmean f]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [pexp_sum]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [← pexp_const_mul]
    congr 1
    funext ω
    ring
  -- Step 3: `E f'(W) = ∑ᵢ ∑_y pᵢ(y) ξᵢ(y) (ξᵢ(y) cᵢ)`.
  have h3 : ∀ i, pexp p (fun ω ↦ D (sumStat ξ ω)) = c i := by
    intro i
    have := pexp_comp_coord hp1 i (fun y ω ↦ D (looStat ξ i ω + ξ i y))
      (fun y ω b ↦ by simp only [looStat_update])
    simp only [looStat_add] at this
    exact this
  have h3' : pexp p (fun ω ↦ D (sumStat ξ ω)) =
      ∑ i, ∑ y, p i y * ξ i y * (ξ i y * c i) := by
    calc pexp p (fun ω ↦ D (sumStat ξ ω))
          = (∑ i, s i) * pexp p (fun ω ↦ D (sumStat ξ ω)) := by rw [hs, hvar, one_mul]
      _ = ∑ i, s i * c i := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ ↦ by rw [h3 i]
      _ = _ := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [hs, Finset.sum_mul]
          exact Finset.sum_congr rfl fun y _ ↦ by ring
  -- Step 4: the integral representation.
  have h4 : Pz - stdCDF z = ∑ i, ∑ y, p i y * ξ i y *
      ∫ t in (0 : ℝ)..ξ i y, pexp p (fun ω ↦ c i - D (V i ω + t)) := by
    rw [h1, h2, h3', ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ ↦ ?_
    rw [← mul_sub, mul_sub_pexp_steinSol_eq hp1 z (V i) (c i) (ξ i y)]
  -- Step 5: the pointwise bound on the integrand.
  set m : ι → ℝ := fun i ↦ ∑ x, p i x * |ξ i x| with hm
  have h5 : ∀ i t, |pexp p (fun ω ↦ c i - D (V i ω + t))| ≤ 9 * m i + 9 * |t| + 8 * β := by
    intro i t
    have hrw : (fun ω ↦ c i - D (V i ω + t)) = fun ω ↦
        ∑ x, p i x * (pexp p (fun ω' ↦ D (V i ω' + ξ i x) - D (V i ω' + t))) -
          (D (V i ω + t) - pexp p (fun ω' ↦ D (V i ω' + t))) := by
      funext ω
      have hsum : ∑ x, p i x * pexp p (fun ω' ↦ D (V i ω' + ξ i x) - D (V i ω' + t)) =
          c i - pexp p (fun ω' ↦ D (V i ω' + t)) := by
        simp only [pexp_sub, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul,
          hc]
        rw [pexp_sum]
        congr 1
        exact Finset.sum_congr rfl fun x _ ↦ (pexp_const_mul p _ _).symm
      rw [hsum]
      ring
    rw [hrw, pexp_sub, pexp_const hp1, pexp_sub, pexp_const hp1, sub_self, sub_zero]
    calc |∑ x, p i x * pexp p (fun ω' ↦ D (V i ω' + ξ i x) - D (V i ω' + t))|
          ≤ ∑ x, |p i x * pexp p (fun ω' ↦ D (V i ω' + ξ i x) - D (V i ω' + t))| :=
            Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, p i x * (9 * (|ξ i x| + |t|) + 8 * β) := by
          refine Finset.sum_le_sum fun x _ ↦ ?_
          rw [abs_mul, abs_of_nonneg (hp0 i x)]
          exact mul_le_mul_of_nonneg_left
            (abs_pexp_steinDeriv_sub_le hp0 hp1 hmean hvar hβ z i (ξ i x) t) (hp0 i x)
      _ = 9 * m i + 9 * |t| + 8 * β := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp1, one_mul, hm,
            Finset.mul_sum]
          ring_nf
  -- Step 6: assemble.
  have h6 : ∀ i y, |p i y * ξ i y * ∫ t in (0 : ℝ)..ξ i y, pexp p (fun ω ↦ c i - D (V i ω + t))|
      ≤ (9 * m i + 8 * β) * (p i y * ξ i y ^ 2) + 9 * (p i y * |ξ i y| ^ 3) := by
    intro i y
    have hint : |∫ t in (0 : ℝ)..ξ i y, pexp p (fun ω ↦ c i - D (V i ω + t))| ≤
        (9 * m i + 9 * |ξ i y| + 8 * β) * |ξ i y - 0| := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := fun t ↦ pexp p (fun ω ↦ c i - D (V i ω + t))) (a := 0) (b := ξ i y)
        (C := 9 * m i + 9 * |ξ i y| + 8 * β) fun t ht ↦ by
          rw [Real.norm_eq_abs]
          exact (h5 i t).trans (by linarith [abs_le_abs_of_mem_uIoc ht])
      simpa [Real.norm_eq_abs] using this
    rw [sub_zero] at hint
    rw [abs_mul, abs_mul, abs_of_nonneg (hp0 i y)]
    calc p i y * |ξ i y| * |∫ t in (0 : ℝ)..ξ i y, pexp p (fun ω ↦ c i - D (V i ω + t))|
          ≤ p i y * |ξ i y| * ((9 * m i + 9 * |ξ i y| + 8 * β) * |ξ i y|) :=
            mul_le_mul_of_nonneg_left hint (mul_nonneg (hp0 i y) (abs_nonneg _))
      _ = (9 * m i + 8 * β) * (p i y * ξ i y ^ 2) + 9 * (p i y * |ξ i y| ^ 3) := by
          rw [← sq_abs (ξ i y)]; ring
  have hcheb : ∀ i, m i * s i ≤ ∑ x, p i x * |ξ i x| ^ 3 := fun i ↦
    sum_abs_mul_sum_sq_le (hp0 i) (hp1 i) (ξ i)
  have hm0 : ∀ i, 0 ≤ m i := fun i ↦
    Finset.sum_nonneg fun x _ ↦ mul_nonneg (hp0 i x) (abs_nonneg _)
  rw [h4]
  calc |∑ i, ∑ y, p i y * ξ i y * ∫ t in (0 : ℝ)..ξ i y, pexp p (fun ω ↦ c i - D (V i ω + t))|
        ≤ ∑ i, ∑ y, |p i y * ξ i y * ∫ t in (0 : ℝ)..ξ i y,
            pexp p (fun ω ↦ c i - D (V i ω + t))| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ ↦ Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ y, ((9 * m i + 8 * β) * (p i y * ξ i y ^ 2) + 9 * (p i y * |ξ i y| ^ 3)) :=
          Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun y _ ↦ h6 i y
    _ = ∑ i, (9 * (m i * s i) + 8 * β * s i + 9 * ∑ y, p i y * |ξ i y| ^ 3) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hs]
          ring
    _ ≤ ∑ i, (9 * ∑ y, p i y * |ξ i y| ^ 3 + 8 * β * s i + 9 * ∑ y, p i y * |ξ i y| ^ 3) :=
          Finset.sum_le_sum fun i _ ↦ by linarith [hcheb i]
    _ = 18 * β + 8 * β * ∑ i, s i := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← hβdef]
          ring
    _ = 26 * β := by rw [hvar]; ring

/-- **Berry–Esseen bound, general variance.** If `∑ᵢ E ξᵢ² = σ²` with `σ > 0`, then
`|P(W ≤ z) - Φ(z/σ)| ≤ 26 ∑ᵢ E|ξᵢ|³ / σ³`. -/
theorem berryEsseen_stein_of_var {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → ℝ} (hmean : ∀ i, ∑ x, p i x * ξ i x = 0)
    {σ : ℝ} (hσ : 0 < σ) (hvar : ∑ i, ∑ x, p i x * ξ i x ^ 2 = σ ^ 2) (z : ℝ) :
    |pexp p (fun ω ↦ if sumStat ξ ω ≤ z then 1 else 0) - (gaussianReal 0 1).real (Iic (z / σ))| ≤
      26 * (∑ i, ∑ x, p i x * |ξ i x| ^ 3) / σ ^ 3 := by
  set ξ' : ∀ i, X i → ℝ := fun i x ↦ ξ i x / σ with hξ'
  have hmean' : ∀ i, ∑ x, p i x * ξ' i x = 0 := by
    intro i
    simp only [hξ', mul_div_assoc', ← Finset.sum_div, hmean i, zero_div]
  have hσ2 : σ ^ 2 ≠ 0 := by positivity
  have hvar' : ∑ i, ∑ x, p i x * ξ' i x ^ 2 = 1 := by
    simp only [hξ', div_pow, mul_div_assoc', ← Finset.sum_div, hvar, div_self hσ2]
  have hβ' : ∑ i, ∑ x, p i x * |ξ' i x| ^ 3 = (∑ i, ∑ x, p i x * |ξ i x| ^ 3) / σ ^ 3 := by
    simp only [hξ', abs_div, abs_of_pos hσ, div_pow, mul_div_assoc', ← Finset.sum_div]
  have hind : (fun ω ↦ if sumStat ξ ω ≤ z then (1 : ℝ) else 0) =
      fun ω ↦ if sumStat ξ' ω ≤ z / σ then 1 else 0 := by
    funext ω
    have : sumStat ξ' ω = sumStat ξ ω / σ := by
      simp only [sumStat, hξ', Finset.sum_div]
    simp only [this, div_le_div_iff_of_pos_right hσ]
  rw [hind, mul_div_assoc, ← hβ']
  exact berryEsseen_stein hp0 hp1 hmean' hvar' (z / σ)

/-- **Sanity instance (Rademacher sums).** For `n ≥ 1` independent fair signs `εᵢ = ±1`, the
hypotheses of `berryEsseen_stein_of_var` hold with `σ = √n`, giving
`|P(ε₁ + ⋯ + εₙ ≤ z) - Φ(z/√n)| ≤ 26/√n`. -/
theorem berryEsseen_rademacher (n : ℕ) (hn : 0 < n) (z : ℝ) :
    |pexp (X := fun _ : Fin n ↦ Bool) (fun _ _ ↦ (1 / 2 : ℝ))
        (fun ω ↦ if sumStat (fun _ b ↦ if b then (1 : ℝ) else -1) ω ≤ z then 1 else 0) -
      (gaussianReal 0 1).real (Iic (z / √n))| ≤ 26 / √n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < √(n : ℝ) := Real.sqrt_pos.2 hn0
  have h := berryEsseen_stein_of_var (X := fun _ : Fin n ↦ Bool) (p := fun _ _ ↦ (1 / 2 : ℝ))
    (fun _ _ ↦ by norm_num) (fun _ ↦ by norm_num [Fintype.sum_bool])
    (ξ := fun _ b ↦ if b then (1 : ℝ) else -1) (fun _ ↦ by norm_num [Fintype.sum_bool]) hs
    (by norm_num [Fintype.sum_bool, Real.sq_sqrt hn0.le]) z
  refine h.trans (le_of_eq ?_)
  have hsum : (∑ _i : Fin n, ∑ x : Bool, (1 / 2 : ℝ) * |if x = true then (1 : ℝ) else -1| ^ 3) =
      n := by
    norm_num [Fintype.sum_bool]
  have h3 : √(n : ℝ) ^ 3 = n * √n := by
    rw [pow_succ, Real.sq_sqrt hn0.le]
  rw [hsum, h3]
  field_simp

end StatisticalRL.Probability.Stein
