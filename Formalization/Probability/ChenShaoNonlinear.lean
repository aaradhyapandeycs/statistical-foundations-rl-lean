import Formalization.Probability.SteinRandomConcentration

/-!
# Normal approximation for nonlinear statistics (Chen–Shao)

Setting of `BerryEsseenStein`: a finite product of finite laws `p i` on coordinates `ω i ∈ X i`,
independent mean-zero summands `ξ i (ω i)` with `∑ᵢ E ξᵢ² = 1`, `W = sumStat ξ`,
`β = ∑ᵢ E|ξᵢ|³`. The statistic is `T = W + Δ` with `Δ = Δ(ω)` arbitrary, and `Δ⁽ⁱ⁾ = Δi i`
are arbitrary random variables not depending on the coordinate `ω i`.

Main result `chenShao_nonlinear`: for every `z`,

`|P(W + Δ ≤ z) - Φ(z)| ≤ 28β + E|WΔ| + ∑ᵢ E|ξᵢ (Δ - Δ⁽ⁱ⁾)|`.

The proof is the sandwich `P(W ≤ z - |Δ|) ≤ P(T ≤ z) ≤ P(W ≤ z + |Δ|)`, the Stein Berry–Esseen
bound `berryEsseen_stein` (`26β`) for `W`, and the randomized concentration inequality
`pexp_intervalInd_random_le` with endpoints `z, z + |Δ|` (resp. `z - |Δ|, z`).

Further exports:
* `chenShao_nonlinear_update`: `Δ⁽ⁱ⁾(ω) = Δ(ω with coordinate i replaced by a fixed x⋆ᵢ)`;
* `chenShao_nonlinear_of_var`: general variance `∑ᵢ E ξᵢ² = σ² > 0`, compared with `Φ(z/σ)`;
* `chenShao_nonlinear_zero`: the sanity instance `Δ = 0` recovers `berryEsseen_stein` up to the
  constant (`28` instead of `26`);
* Gaussian-side lemmas (N4): `stdPDF_le_half`, `abs_mul_stdPDF_le_half`,
  `abs_stdCDF_sub_le` (`Φ` is `1/2`-Lipschitz) and `abs_stdCDF_div_sub_le`
  (`|Φ(z/a) - Φ(z/b)| ≤ 2 |a²/b² - 1|` for `a, b > 0`).
-/

open MeasureTheory ProbabilityTheory Real Set Finset

namespace StatisticalRL.Probability.Stein

/-! ## Gaussian-side lemmas (N4) -/

theorem two_le_sqrt_two_pi : 2 ≤ √(2 * π) := by
  rw [Real.le_sqrt (by norm_num) (by positivity)]
  nlinarith [pi_gt_three]

/-- `φ(x) ≤ (2π)^{-1/2}`. -/
theorem stdPDF_le_inv_sqrt (x : ℝ) : stdPDF x ≤ (√(2 * π))⁻¹ := by
  rw [stdPDF_eq]
  have h : exp (-x ^ 2 / 2) ≤ 1 := exp_le_one_iff.2 (by nlinarith [sq_nonneg x])
  have h0 : 0 ≤ (√(2 * π))⁻¹ := inv_nonneg.2 (sqrt_nonneg _)
  calc (√(2 * π))⁻¹ * exp (-x ^ 2 / 2) ≤ (√(2 * π))⁻¹ * 1 := mul_le_mul_of_nonneg_left h h0
    _ = _ := mul_one _

theorem inv_sqrt_two_pi_le_half : (√(2 * π))⁻¹ ≤ 1 / 2 := by
  rw [one_div]
  exact inv_anti₀ (by norm_num) two_le_sqrt_two_pi

/-- `φ(x) ≤ 1/2`. -/
theorem stdPDF_le_half (x : ℝ) : stdPDF x ≤ 1 / 2 :=
  (stdPDF_le_inv_sqrt x).trans inv_sqrt_two_pi_le_half

/-- `|x| φ(x) ≤ 1/2`. -/
theorem abs_mul_stdPDF_le_half (x : ℝ) : |x| * stdPDF x ≤ 1 / 2 := by
  rw [stdPDF_eq]
  have hexp : |x| ≤ exp (x ^ 2 / 2) := by
    have h1 := add_one_le_exp (x ^ 2 / 2)
    have h2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    nlinarith [sq_nonneg (|x| - 1)]
  have hprod : |x| * exp (-x ^ 2 / 2) ≤ 1 := by
    have he : exp (-x ^ 2 / 2) * exp (x ^ 2 / 2) = 1 := by
      rw [← exp_add]; ring_nf; exact exp_zero
    have hp : 0 < exp (-x ^ 2 / 2) := exp_pos _
    nlinarith
  have h0 : 0 ≤ (√(2 * π))⁻¹ := inv_nonneg.2 (sqrt_nonneg _)
  calc |x| * ((√(2 * π))⁻¹ * exp (-x ^ 2 / 2)) = (√(2 * π))⁻¹ * (|x| * exp (-x ^ 2 / 2)) := by
        ring
    _ ≤ (√(2 * π))⁻¹ * 1 := mul_le_mul_of_nonneg_left hprod h0
    _ ≤ 1 / 2 := by rw [mul_one]; exact inv_sqrt_two_pi_le_half

/-- Mean value bound: a function with derivative bounded by `C` on `[a, b]` changes by at most
`C (b - a)`. -/
theorem abs_sub_le_of_hasDerivAt {f f' : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x) (hC : ∀ x ∈ Icc a b, |f' x| ≤ C) :
    |f b - f a| ≤ C * (b - a) := by
  rcases hab.lt_or_eq with hlt | heq
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope f f' hlt
      (fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt)
      (fun x hx ↦ hf x (Ioo_subset_Icc_self hx))
    have hba : 0 < b - a := sub_pos.2 hlt
    have : f b - f a = f' c * (b - a) := by rw [hcd]; field_simp
    rw [this, abs_mul, abs_of_pos hba]
    exact mul_le_mul_of_nonneg_right (hC c (Ioo_subset_Icc_self hc)) hba.le
  · subst heq; simp

/-- `Φ` is `1/2`-Lipschitz. -/
theorem abs_stdCDF_sub_le (a b : ℝ) : |stdCDF b - stdCDF a| ≤ |b - a| / 2 := by
  rcases le_total a b with hab | hab
  · have := abs_sub_le_of_hasDerivAt (f := stdCDF) (f' := stdPDF) (C := 1 / 2) hab
      (fun x _ ↦ hasDerivAt_stdCDF x)
      (fun x _ ↦ by rw [abs_of_pos (stdPDF_pos x)]; exact stdPDF_le_half x)
    rw [abs_of_nonneg (sub_nonneg.2 hab)]; linarith
  · have := abs_sub_le_of_hasDerivAt (f := stdCDF) (f' := stdPDF) (C := 1 / 2) hab
      (fun x _ ↦ hasDerivAt_stdCDF x)
      (fun x _ ↦ by rw [abs_of_pos (stdPDF_pos x)]; exact stdPDF_le_half x)
    rw [abs_sub_comm, abs_of_nonpos (sub_nonpos.2 hab)]; linarith

/-- Scale comparison for `0 < a ≤ b`: `|Φ(z/a) - Φ(z/b)| ≤ (b - a)/(2a)`. -/
theorem abs_stdCDF_div_sub_le_of_le (z : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    |stdCDF (z / b) - stdCDF (z / a)| ≤ (b - a) / (2 * a) := by
  have hd : ∀ s ∈ Icc a b, HasDerivAt (fun s ↦ stdCDF (z / s))
      (stdPDF (z / s) * (z * -(s ^ 2)⁻¹)) s := by
    intro s hs
    have hs0 : s ≠ 0 := (ha.trans_le hs.1).ne'
    have h1 := (hasDerivAt_inv hs0).const_mul z
    have h2 := (hasDerivAt_stdCDF (z * s⁻¹)).comp s h1
    simp only [div_eq_mul_inv]
    exact h2
  have hC : ∀ s ∈ Icc a b, |stdPDF (z / s) * (z * -(s ^ 2)⁻¹)| ≤ 1 / (2 * a) := by
    intro s hs
    have hs0 : 0 < s := ha.trans_le hs.1
    have heq : |stdPDF (z / s) * (z * -(s ^ 2)⁻¹)| = (|z / s| * stdPDF (z / s)) / s := by
      rw [abs_mul, abs_of_pos (stdPDF_pos _), abs_mul, abs_neg, abs_inv, abs_div,
        abs_of_pos hs0, abs_of_pos (pow_pos hs0 2)]
      field_simp
    rw [heq, div_le_div_iff₀ hs0 (by positivity)]
    have := abs_mul_stdPDF_le_half (z / s)
    nlinarith [hs.1]
  have := abs_sub_le_of_hasDerivAt (f := fun s ↦ stdCDF (z / s)) hab hd hC
  calc _ ≤ 1 / (2 * a) * (b - a) := this
    _ = (b - a) / (2 * a) := by ring

theorem abs_stdCDF_sub_stdCDF_le_one (a b : ℝ) : |stdCDF a - stdCDF b| ≤ 1 := by
  rw [abs_le]
  constructor <;> linarith [stdCDF_nonneg a, stdCDF_le_one a, stdCDF_nonneg b, stdCDF_le_one b]

/-- **Variance comparison for `Φ`** (N4). For `a, b > 0` and every `z`,
`|Φ(z/a) - Φ(z/b)| ≤ 2 |a²/b² - 1|`. -/
theorem abs_stdCDF_div_sub_le (z : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |stdCDF (z / a) - stdCDF (z / b)| ≤ 2 * |a ^ 2 / b ^ 2 - 1| := by
  have hb2 : 0 < b ^ 2 := by positivity
  have hrat : a ^ 2 / b ^ 2 - 1 = (a - b) * (a + b) / b ^ 2 := by field_simp; ring
  rcases le_total b a with hba | hab
  · -- `b ≤ a`
    have h := abs_stdCDF_div_sub_le_of_le z hb hba
    rw [hrat, abs_div, abs_of_pos hb2, abs_of_nonneg (mul_nonneg (sub_nonneg.2 hba) (by linarith))]
    calc |stdCDF (z / a) - stdCDF (z / b)| ≤ (a - b) / (2 * b) := h
      _ ≤ 2 * ((a - b) * (a + b) / b ^ 2) := by
          rw [div_le_iff₀ (by positivity)]
          field_simp
          nlinarith [sub_nonneg.2 hba]
  · -- `a ≤ b`
    rcases le_total (2 * a) b with hsmall | hbig
    · -- `a ≤ b/2`: the trivial bound
      have hr : a ^ 2 / b ^ 2 ≤ 1 / 4 := by
        rw [div_le_iff₀ hb2]; nlinarith
      calc |stdCDF (z / a) - stdCDF (z / b)| ≤ 1 := abs_stdCDF_sub_stdCDF_le_one _ _
        _ ≤ 2 * |a ^ 2 / b ^ 2 - 1| := by
            rw [abs_of_nonpos (by linarith)]; linarith
    · have h := abs_stdCDF_div_sub_le_of_le z ha hab
      rw [abs_sub_comm, hrat, abs_div, abs_of_pos hb2,
        abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hab) (by linarith))]
      calc |stdCDF (z / b) - stdCDF (z / a)| ≤ (b - a) / (2 * a) := h
        _ ≤ 2 * (-((a - b) * (a + b)) / b ^ 2) := by
            rw [div_le_iff₀ (by positivity)]
            field_simp
            have hk : b ^ 2 ≤ 4 * a * (a + b) := by nlinarith
            nlinarith [mul_le_mul_of_nonneg_left hk (sub_nonneg.2 hab)]

/-! ## The sandwich (N6) -/

theorem ite_add_le_ite_add_intervalInd (w d z : ℝ) :
    (if w + d ≤ z then (1 : ℝ) else 0) ≤ (if w ≤ z then 1 else 0) + intervalInd z (z + |d|) w := by
  have h1 := neg_abs_le d
  have h0 := intervalInd_nonneg z (z + |d|) w
  by_cases hT : w + d ≤ z
  · by_cases hW : w ≤ z
    · simp only [hT, hW, if_true]; linarith
    · have hI : intervalInd z (z + |d|) w = 1 := by
        unfold intervalInd
        rw [if_pos]
        constructor <;> linarith
      simp only [hT, hW, if_true, if_false, hI]; norm_num
  · simp only [hT, if_false]
    split_ifs <;> linarith

theorem ite_le_ite_add_add_intervalInd (w d z : ℝ) :
    (if w ≤ z then (1 : ℝ) else 0) ≤ (if w + d ≤ z then 1 else 0) + intervalInd (z - |d|) z w := by
  have h1 := le_abs_self d
  have h0 := intervalInd_nonneg (z - |d|) z w
  by_cases hW : w ≤ z
  · by_cases hT : w + d ≤ z
    · simp only [hT, hW, if_true]; linarith
    · have hI : intervalInd (z - |d|) z w = 1 := by
        unfold intervalInd
        rw [if_pos]
        constructor <;> linarith
      simp only [hT, hW, if_true, if_false, hI]; norm_num
  · simp only [hW, if_false]
    split_ifs <;> linarith

/-! ## The Chen–Shao bound -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]

/-- `P(z ≤ W ≤ z + |Δ|) ≤ E|WΔ| + 2β + ∑ᵢ E|ξᵢ (Δ - Δ⁽ⁱ⁾)|`. -/
theorem pexp_intervalInd_add_abs_le {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → ℝ} (hmean : ∀ i, ∑ x, p i x * ξ i x = 0)
    (hvar : ∑ i, ∑ x, p i x * ξ i x ^ 2 = 1) (Δ : (∀ i, X i) → ℝ) (Δi : ι → (∀ i, X i) → ℝ)
    (hΔi : ∀ i ω b, Δi i (Function.update ω i b) = Δi i ω) (z : ℝ) :
    pexp p (fun ω ↦ intervalInd z (z + |Δ ω|) (sumStat ξ ω)) ≤
      pexp p (fun ω ↦ |sumStat ξ ω * Δ ω|) + 2 * ∑ i, ∑ x, p i x * |ξ i x| ^ 3 +
        ∑ i, pexp p (fun ω ↦ |ξ i (ω i) * (Δ ω - Δi i ω)|) := by
  have h := pexp_intervalInd_random_le hp0 hp1 hmean hvar (fun _ ↦ z) (fun ω ↦ z + |Δ ω|)
    (fun ω ↦ by simp only; linarith [abs_nonneg (Δ ω)]) (fun _ _ ↦ z)
    (fun i ω ↦ z + |Δi i ω|) (fun _ _ _ ↦ rfl) (fun i ω b ↦ by simp only [hΔi])
  refine h.trans (add_le_add (add_le_add (le_of_eq ?_) le_rfl)
    (Finset.sum_le_sum fun i _ ↦ pexp_mono hp0 fun ω ↦ ?_))
  · congr 1; funext ω; simp only [add_sub_cancel_left, abs_mul, abs_abs]
  · simp only [sub_self, abs_zero, zero_add, add_sub_add_left_eq_sub, abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub _ _) (abs_nonneg _)

/-- `P(z - |Δ| ≤ W ≤ z) ≤ E|WΔ| + 2β + ∑ᵢ E|ξᵢ (Δ - Δ⁽ⁱ⁾)|`. -/
theorem pexp_intervalInd_sub_abs_le {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → ℝ} (hmean : ∀ i, ∑ x, p i x * ξ i x = 0)
    (hvar : ∑ i, ∑ x, p i x * ξ i x ^ 2 = 1) (Δ : (∀ i, X i) → ℝ) (Δi : ι → (∀ i, X i) → ℝ)
    (hΔi : ∀ i ω b, Δi i (Function.update ω i b) = Δi i ω) (z : ℝ) :
    pexp p (fun ω ↦ intervalInd (z - |Δ ω|) z (sumStat ξ ω)) ≤
      pexp p (fun ω ↦ |sumStat ξ ω * Δ ω|) + 2 * ∑ i, ∑ x, p i x * |ξ i x| ^ 3 +
        ∑ i, pexp p (fun ω ↦ |ξ i (ω i) * (Δ ω - Δi i ω)|) := by
  have h := pexp_intervalInd_random_le hp0 hp1 hmean hvar (fun ω ↦ z - |Δ ω|) (fun _ ↦ z)
    (fun ω ↦ by simp only; linarith [abs_nonneg (Δ ω)]) (fun i ω ↦ z - |Δi i ω|)
    (fun _ _ ↦ z) (fun i ω b ↦ by simp only [hΔi]) (fun _ _ _ ↦ rfl)
  refine h.trans (add_le_add (add_le_add (le_of_eq ?_) le_rfl)
    (Finset.sum_le_sum fun i _ ↦ pexp_mono hp0 fun ω ↦ ?_))
  · congr 1; funext ω; simp only [sub_sub_cancel, abs_mul, abs_abs]
  · simp only [sub_self, abs_zero, add_zero, sub_sub_sub_cancel_left, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rw [abs_sub_comm (Δ ω)]
    exact abs_abs_sub_abs_le_abs_sub _ _

/-- **Chen–Shao normal approximation for nonlinear statistics.** Let `ξᵢ(ωᵢ)` be independent
(coordinates of a finite product of finite laws `p i`), mean zero, with `∑ᵢ E ξᵢ² = 1`, and
`W = ∑ᵢ ξᵢ`. Let `Δ` be any random variable and, for each `i`, let `Δ⁽ⁱ⁾ = Δi i` be any random
variable that does not depend on the coordinate `ω i`. Then for every `z`,

`|P(W + Δ ≤ z) - Φ(z)| ≤ 28 ∑ᵢ E|ξᵢ|³ + E|WΔ| + ∑ᵢ E|ξᵢ (Δ - Δ⁽ⁱ⁾)|`,

where `Φ(z) = (gaussianReal 0 1).real (Iic z)`. -/
theorem chenShao_nonlinear {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → ℝ} (hmean : ∀ i, ∑ x, p i x * ξ i x = 0)
    (hvar : ∑ i, ∑ x, p i x * ξ i x ^ 2 = 1) (Δ : (∀ i, X i) → ℝ) (Δi : ι → (∀ i, X i) → ℝ)
    (hΔi : ∀ i ω b, Δi i (Function.update ω i b) = Δi i ω) (z : ℝ) :
    |pexp p (fun ω ↦ if sumStat ξ ω + Δ ω ≤ z then 1 else 0) - (gaussianReal 0 1).real (Iic z)| ≤
      28 * ∑ i, ∑ x, p i x * |ξ i x| ^ 3 + pexp p (fun ω ↦ |sumStat ξ ω * Δ ω|) +
        ∑ i, pexp p (fun ω ↦ |ξ i (ω i) * (Δ ω - Δi i ω)|) := by
  have hBE := berryEsseen_stein hp0 hp1 hmean hvar z
  have hup := pexp_intervalInd_add_abs_le hp0 hp1 hmean hvar Δ Δi hΔi z
  have hlow := pexp_intervalInd_sub_abs_le hp0 hp1 hmean hvar Δ Δi hΔi z
  set PT := pexp p (fun ω ↦ if sumStat ξ ω + Δ ω ≤ z then (1 : ℝ) else 0)
  set PW := pexp p (fun ω ↦ if sumStat ξ ω ≤ z then (1 : ℝ) else 0)
  have h1 : PT ≤ PW + pexp p (fun ω ↦ intervalInd z (z + |Δ ω|) (sumStat ξ ω)) := by
    rw [← pexp_add]
    exact pexp_mono hp0 fun ω ↦ ite_add_le_ite_add_intervalInd _ _ _
  have h2 : PW ≤ PT + pexp p (fun ω ↦ intervalInd (z - |Δ ω|) z (sumStat ξ ω)) := by
    rw [← pexp_add]
    exact pexp_mono hp0 fun ω ↦ ite_le_ite_add_add_intervalInd _ _ _
  rw [abs_le] at hBE ⊢
  constructor <;> linarith [hBE.1, hBE.2]

/-- **Chen–Shao bound, replace-one-coordinate form.** With `Δ⁽ⁱ⁾(ω) = Δ(ω[i ↦ x⋆ᵢ])` for any fixed
`x⋆ : ∀ i, X i`, for every `z`,
`|P(W + Δ ≤ z) - Φ(z)| ≤ 28β + E|WΔ| + ∑ᵢ E|ξᵢ (Δ(ω) - Δ(ω[i ↦ x⋆ᵢ]))|`. -/
theorem chenShao_nonlinear_update {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → ℝ} (hmean : ∀ i, ∑ x, p i x * ξ i x = 0)
    (hvar : ∑ i, ∑ x, p i x * ξ i x ^ 2 = 1) (Δ : (∀ i, X i) → ℝ) (xs : ∀ i, X i) (z : ℝ) :
    |pexp p (fun ω ↦ if sumStat ξ ω + Δ ω ≤ z then 1 else 0) - (gaussianReal 0 1).real (Iic z)| ≤
      28 * ∑ i, ∑ x, p i x * |ξ i x| ^ 3 + pexp p (fun ω ↦ |sumStat ξ ω * Δ ω|) +
        ∑ i, pexp p (fun ω ↦ |ξ i (ω i) * (Δ ω - Δ (Function.update ω i (xs i)))|) :=
  chenShao_nonlinear hp0 hp1 hmean hvar Δ (fun i ω ↦ Δ (Function.update ω i (xs i)))
    (fun i ω b ↦ by simp only [Function.update_idem]) z

/-- **Sanity instance.** With `Δ = 0` the Chen–Shao bound recovers the Berry–Esseen bound
`berryEsseen_stein` up to the constant: `|P(W ≤ z) - Φ(z)| ≤ 28β`. -/
theorem chenShao_nonlinear_zero {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → ℝ} (hmean : ∀ i, ∑ x, p i x * ξ i x = 0)
    (hvar : ∑ i, ∑ x, p i x * ξ i x ^ 2 = 1) (z : ℝ) :
    |pexp p (fun ω ↦ if sumStat ξ ω ≤ z then 1 else 0) - (gaussianReal 0 1).real (Iic z)| ≤
      28 * ∑ i, ∑ x, p i x * |ξ i x| ^ 3 := by
  have h := chenShao_nonlinear hp0 hp1 hmean hvar (fun _ ↦ 0) (fun _ _ ↦ 0)
    (fun _ _ _ ↦ rfl) z
  simp only [add_zero, mul_zero, sub_self, abs_zero] at h
  rw [show pexp p (fun _ ↦ (0 : ℝ)) = 0 from pexp_const hp1 0] at h
  simpa using h

/-- **Chen–Shao bound, general variance.** If `∑ᵢ E ξᵢ² = σ²` with `σ > 0`, then for every `z`,
`|P(W + Δ ≤ z) - Φ(z/σ)| ≤ 28β/σ³ + E|WΔ|/σ² + ∑ᵢ E|ξᵢ (Δ - Δ⁽ⁱ⁾)|/σ²`. -/
theorem chenShao_nonlinear_of_var {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → ℝ} (hmean : ∀ i, ∑ x, p i x * ξ i x = 0)
    {σ : ℝ} (hσ : 0 < σ) (hvar : ∑ i, ∑ x, p i x * ξ i x ^ 2 = σ ^ 2)
    (Δ : (∀ i, X i) → ℝ) (Δi : ι → (∀ i, X i) → ℝ)
    (hΔi : ∀ i ω b, Δi i (Function.update ω i b) = Δi i ω) (z : ℝ) :
    |pexp p (fun ω ↦ if sumStat ξ ω + Δ ω ≤ z then 1 else 0) -
        (gaussianReal 0 1).real (Iic (z / σ))| ≤
      28 * (∑ i, ∑ x, p i x * |ξ i x| ^ 3) / σ ^ 3 +
        pexp p (fun ω ↦ |sumStat ξ ω * Δ ω|) / σ ^ 2 +
        (∑ i, pexp p (fun ω ↦ |ξ i (ω i) * (Δ ω - Δi i ω)|)) / σ ^ 2 := by
  set ξ' : ∀ i, X i → ℝ := fun i x ↦ ξ i x / σ with hξ'
  have hmean' : ∀ i, ∑ x, p i x * ξ' i x = 0 := by
    intro i
    simp only [hξ', mul_div_assoc', ← Finset.sum_div, hmean i, zero_div]
  have hσ2 : σ ^ 2 ≠ 0 := by positivity
  have hvar' : ∑ i, ∑ x, p i x * ξ' i x ^ 2 = 1 := by
    simp only [hξ', div_pow, mul_div_assoc', ← Finset.sum_div, hvar, div_self hσ2]
  have hβ' : ∑ i, ∑ x, p i x * |ξ' i x| ^ 3 = (∑ i, ∑ x, p i x * |ξ i x| ^ 3) / σ ^ 3 := by
    simp only [hξ', abs_div, abs_of_pos hσ, div_pow, mul_div_assoc', ← Finset.sum_div]
  have hW : ∀ ω, sumStat ξ' ω = sumStat ξ ω / σ := fun ω ↦ by
    simp only [sumStat, hξ', Finset.sum_div]
  have h := chenShao_nonlinear hp0 hp1 hmean' hvar' (fun ω ↦ Δ ω / σ) (fun i ω ↦ Δi i ω / σ)
    (fun i ω b ↦ by simp only [hΔi]) (z / σ)
  have hind : (fun ω ↦ if sumStat ξ' ω + Δ ω / σ ≤ z / σ then (1 : ℝ) else 0) =
      fun ω ↦ if sumStat ξ ω + Δ ω ≤ z then 1 else 0 := by
    funext ω
    simp only [hW, ← add_div, div_le_div_iff_of_pos_right hσ]
  have hWΔ : pexp p (fun ω ↦ |sumStat ξ' ω * (Δ ω / σ)|) =
      pexp p (fun ω ↦ |sumStat ξ ω * Δ ω|) / σ ^ 2 := by
    rw [div_eq_mul_inv, mul_comm, ← pexp_const_mul]
    congr 1
    funext ω
    rw [hW, show sumStat ξ ω / σ * (Δ ω / σ) = (σ ^ 2)⁻¹ * (sumStat ξ ω * Δ ω) by
      field_simp, abs_mul, abs_of_pos (inv_pos.2 (by positivity))]
  have hloo : ∑ i, pexp p (fun ω ↦ |ξ' i (ω i) * (Δ ω / σ - Δi i ω / σ)|) =
      (∑ i, pexp p (fun ω ↦ |ξ i (ω i) * (Δ ω - Δi i ω)|)) / σ ^ 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [div_eq_mul_inv, mul_comm, ← pexp_const_mul]
    congr 1
    funext ω
    rw [show ξ' i (ω i) * (Δ ω / σ - Δi i ω / σ) = (σ ^ 2)⁻¹ * (ξ i (ω i) * (Δ ω - Δi i ω)) by
      simp only [hξ']; field_simp, abs_mul, abs_of_pos (inv_pos.2 (by positivity))]
  rw [hind, hWΔ, hloo, hβ'] at h
  rw [mul_div_assoc]
  exact h

end StatisticalRL.Probability.Stein
