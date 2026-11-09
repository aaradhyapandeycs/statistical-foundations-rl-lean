import Formalization.Probability.BerryEsseenStein

/-!
# Randomized concentration inequality (Chen–Shao)

Setting of `BerryEsseenStein`: a finite product of finite laws `p i` on coordinates `ω i ∈ X i`,
independent mean-zero summands `ξ i (ω i)` with `∑ᵢ E ξᵢ² = 1`, `W = sumStat ξ`,
`β = ∑ᵢ E|ξᵢ|³`.

Main result `pexp_intervalInd_random_le` (Chen–Shao's randomized concentration inequality): for
random endpoints `Δ₁ ≤ Δ₂` and leave-one-out endpoints `D₁ i, D₂ i` that do not depend on the
coordinate `ω i`,

`P(Δ₁ ≤ W ≤ Δ₂) ≤ E|W (Δ₂ - Δ₁)| + 2β + ∑ᵢ E[|ξᵢ| (|Δ₁ - D₁ i| + |Δ₂ - D₂ i|)]`.

Supporting lemmas:
* `pexp_mul_eq_zero_of_update` — Stein identity with a random factor not depending on `ω i` (N1);
* `abs_ramp_sub_ramp_le` — the clipped ramp is Lipschitz in its endpoints (N2);
* `sq_pexp_abs_mul_le`, `pexp_abs_mul_le_sqrt` — Cauchy–Schwarz under `pexp` (N3);
* `pexp_mul_steinH_le` — the variance part of the concentration argument for a general random
  weight `A ∈ [0, 1]`.
-/

open MeasureTheory ProbabilityTheory Real Set Finset

namespace StatisticalRL.Probability.Stein

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, Fintype (X i)]

/-! ## N1: Stein identity with a random factor -/

/-- **Independence with a random factor.** If `G` does not depend on the coordinate `ω i` and
`ξᵢ` has mean zero, then `E[ξᵢ(ωᵢ) G(ω)] = 0`. -/
theorem pexp_mul_eq_zero_of_update {p : ∀ i, X i → ℝ} (hp1 : ∀ i, ∑ x, p i x = 1)
    {ξ : ∀ i, X i → ℝ} (hmean : ∀ i, ∑ x, p i x * ξ i x = 0) (i : ι)
    (G : (∀ j, X j) → ℝ) (hG : ∀ ω b, G (Function.update ω i b) = G ω) :
    pexp p (fun ω ↦ ξ i (ω i) * G ω) = 0 := by
  rw [pexp_comp_coord hp1 i (fun y ω ↦ ξ i y * G ω) (fun y ω b ↦ by simp only [hG])]
  have : ∀ ω, ∑ y, p i y * (ξ i y * G ω) = 0 := fun ω ↦ by
    simp only [← mul_assoc, ← Finset.sum_mul, hmean i, zero_mul]
  simp only [this]
  exact pexp_const hp1 0

/-- **Stein identity with a random function** (N1): if `g ω` does not depend on `ω i`, then
`E[ξᵢ g_ω(W⁽ⁱ⁾)] = 0`. -/
theorem pexp_mul_looStat_eq_zero {p : ∀ i, X i → ℝ} (hp1 : ∀ i, ∑ x, p i x = 1)
    {ξ : ∀ i, X i → ℝ} (hmean : ∀ i, ∑ x, p i x * ξ i x = 0) (i : ι)
    (g : (∀ j, X j) → ℝ → ℝ) (hg : ∀ ω b, g (Function.update ω i b) = g ω) :
    pexp p (fun ω ↦ ξ i (ω i) * g ω (looStat ξ i ω)) = 0 :=
  pexp_mul_eq_zero_of_update hp1 hmean i (fun ω ↦ g ω (looStat ξ i ω))
    (fun ω b ↦ by simp only [hg, looStat_update])

/-! ## N2: the ramp is Lipschitz in its endpoints -/

theorem abs_clamp_sub_clamp_le (x y x' y' : ℝ) :
    |max (-y) (min x y) - max (-y') (min x' y')| ≤ max |x - x'| |y - y'| := by
  refine (abs_max_sub_max_le_max _ _ _ _).trans (max_le ?_ ?_)
  · rw [show -y - -y' = -(y - y') by ring, abs_neg]
    exact le_max_right _ _
  · exact abs_min_sub_min_le_max _ _ _ _

/-- **The clipped ramp is Lipschitz in its endpoints** (N2):
`|ramp a b δ w - ramp a' b' δ w| ≤ (|a - a'| + |b - b'|)/2`. No ordering of the endpoints is
needed. -/
theorem abs_ramp_sub_ramp_le (a b a' b' δ w : ℝ) :
    |ramp a b δ w - ramp a' b' δ w| ≤ (|a - a'| + |b - b'|) / 2 := by
  unfold ramp
  refine (abs_clamp_sub_clamp_le _ _ _ _).trans (max_le ?_ ?_)
  · rw [show w - (a + b) / 2 - (w - (a' + b') / 2) = ((a' - a) + (b' - b)) / 2 by ring, abs_div,
      abs_two]
    gcongr
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_sub_comm a' a, abs_sub_comm b' b]
  · rw [show (b - a) / 2 + δ - ((b' - a') / 2 + δ) = ((b - b') + -(a - a')) / 2 by ring, abs_div,
      abs_two]
    gcongr
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_neg]; ring

/-! ## N3: Cauchy–Schwarz under the product law -/

/-- **Cauchy–Schwarz** under the product law, squared form: `(E|FG|)² ≤ E F² · E G²`. -/
theorem sq_pexp_abs_mul_le {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (F G : (∀ i, X i) → ℝ) :
    pexp p (fun ω ↦ |F ω * G ω|) ^ 2 ≤ pexp p (fun ω ↦ F ω ^ 2) * pexp p (fun ω ↦ G ω ^ 2) := by
  unfold pexp
  refine Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul _
    (fun ω _ ↦ mul_nonneg (prod_weight_nonneg hp0 ω) (sq_nonneg _))
    (fun ω _ ↦ mul_nonneg (prod_weight_nonneg hp0 ω) (sq_nonneg _)) fun ω _ ↦ ?_
  rw [mul_pow, sq_abs]
  ring

/-- **Cauchy–Schwarz** under the product law: `E|FG| ≤ √(E F²) √(E G²)`. -/
theorem pexp_abs_mul_le_sqrt {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (F G : (∀ i, X i) → ℝ) :
    pexp p (fun ω ↦ |F ω * G ω|) ≤
      √(pexp p (fun ω ↦ F ω ^ 2)) * √(pexp p (fun ω ↦ G ω ^ 2)) := by
  rw [← Real.sqrt_mul (pexp_nonneg hp0 fun ω ↦ sq_nonneg _)]
  exact (le_abs_self _).trans (Real.abs_le_sqrt (sq_pexp_abs_mul_le hp0 F G))

/-! ## The variance part of the concentration argument -/

/-- `H = ∑ᵢ |ξᵢ| min(δ, |ξᵢ|)`, the lower envelope of the Stein increments. -/
def steinH (δ : ℝ) (ξ : ∀ i, X i → ℝ) (ω : ∀ i, X i) : ℝ :=
  ∑ i, |ξ i (ω i)| * min δ |ξ i (ω i)|

/-- **Variance part of the concentration inequality.** For any random weight `A ∈ [0, 1]`,
`E[A] (B² - β/(4δ)) ≤ E[A H] + δ`, where `B² = ∑ E ξ² ≤ 1` and `β = ∑ E|ξ|³`. -/
theorem pexp_mul_steinH_le {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → ℝ}
    (hB : ∑ i, ∑ x, p i x * ξ i x ^ 2 ≤ 1) {δ : ℝ} (hδ : 0 < δ) (A : (∀ i, X i) → ℝ)
    (hA0 : ∀ ω, 0 ≤ A ω) (hA1 : ∀ ω, A ω ≤ 1) :
    pexp p A * (∑ i, ∑ x, p i x * ξ i x ^ 2 - (∑ i, ∑ x, p i x * |ξ i x| ^ 3) / (4 * δ)) ≤
      pexp p (fun ω ↦ A ω * steinH δ ξ ω) + δ := by
  set h : ℝ → ℝ := fun x ↦ |x| * min δ |x| with hh
  set H : (∀ i, X i) → ℝ := steinH δ ξ with hH
  set mi : ι → ℝ := fun i ↦ ∑ x, p i x * h (ξ i x) with hmi
  set m := ∑ i, mi i with hm
  set P := pexp p A with hP
  have hP0 : 0 ≤ P := pexp_nonneg hp0 hA0
  set u : ∀ i, X i → ℝ := fun i x ↦ h (ξ i x) - mi i with hu
  have humean : ∀ i, ∑ x, p i x * u i x = 0 := by
    intro i
    simp only [hu, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]
    simp [hmi]
  have hsumu : ∀ ω, sumStat u ω = H ω - m := by
    intro ω
    simp only [sumStat, hu, Finset.sum_sub_distrib, hH, hm, steinH, hh]
  have hvaru : pexp p (fun ω ↦ (H ω - m) ^ 2) ≤ δ ^ 2 := by
    have h1 := pexp_sumStat_sq hp1 humean
    simp only [hsumu] at h1
    rw [h1]
    calc ∑ i, ∑ x, p i x * u i x ^ 2 ≤ ∑ i, ∑ x, p i x * (δ ^ 2 * ξ i x ^ 2) := by
          refine Finset.sum_le_sum fun i _ ↦ ?_
          have hv := sum_mul_sub_mean_sq (hp1 i) fun x ↦ h (ξ i x)
          have hv' : ∑ x, p i x * u i x ^ 2 ≤ ∑ x, p i x * h (ξ i x) ^ 2 := by
            simp only [hu, hmi]
            rw [hv]
            nlinarith [sq_nonneg (∑ x, p i x * h (ξ i x))]
          refine hv'.trans (Finset.sum_le_sum fun x _ ↦ ?_)
          exact mul_le_mul_of_nonneg_left (sq_abs_mul_min_le hδ.le _) (hp0 i x)
      _ = δ ^ 2 * ∑ i, ∑ x, p i x * ξ i x ^ 2 := by
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
  have hPm : P * m ≤ pexp p (fun ω ↦ A ω * H ω) + pexp p (fun ω ↦ |H ω - m|) := by
    rw [← pexp_add, hP, mul_comm, ← pexp_const_mul]
    refine pexp_mono hp0 fun ω ↦ ?_
    have := neg_abs_le_mul_of_mem_unit (hA0 ω) (hA1 ω) (H ω - m)
    nlinarith
  have hmlow : ∑ i, ∑ x, p i x * ξ i x ^ 2 - (∑ i, ∑ x, p i x * |ξ i x| ^ 3) / (4 * δ) ≤ m := by
    have : ∑ i, ∑ x, p i x * ξ i x ^ 2 - (∑ i, ∑ x, p i x * |ξ i x| ^ 3) / (4 * δ) =
        ∑ i, ∑ x, p i x * (ξ i x ^ 2 - |ξ i x| ^ 3 / (4 * δ)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_div, mul_div_assoc]
    rw [this, hm]
    exact Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun x _ ↦
      mul_le_mul_of_nonneg_left (sq_sub_le_abs_mul_min hδ _) (hp0 i x)
  calc P * (∑ i, ∑ x, p i x * ξ i x ^ 2 - (∑ i, ∑ x, p i x * |ξ i x| ^ 3) / (4 * δ))
        ≤ P * m := mul_le_mul_of_nonneg_left hmlow hP0
    _ ≤ pexp p (fun ω ↦ A ω * H ω) + δ := by linarith

/-! ## N5: the randomized concentration inequality -/

omit [DecidableEq ι] [∀ i, Fintype (X i)] in
/-- Pathwise lower bound for the Stein increments of a ramp with (pathwise fixed) endpoints:
`1{a ≤ W ≤ b} H ≤ ∑ᵢ ξᵢ (g(W) - g(W - ξᵢ))`. -/
theorem intervalInd_mul_steinH_le (δ : ℝ) (hδ : 0 < δ) (ξ : ∀ i, X i → ℝ) (ω : ∀ i, X i)
    (a b : ℝ) :
    intervalInd a b (sumStat ξ ω) * steinH δ ξ ω ≤
      ∑ i, ξ i (ω i) * (ramp a b δ (sumStat ξ ω) - ramp a b δ (sumStat ξ ω - ξ i (ω i))) := by
  unfold intervalInd steinH
  split_ifs with hA
  · rw [one_mul]
    exact Finset.sum_le_sum fun i _ ↦ abs_mul_min_le_mul_ramp_sub hδ hA.1 hA.2 _
  · rw [zero_mul]
    exact Finset.sum_nonneg fun i _ ↦ mul_ramp_sub_nonneg _ _ _ _ _

/-- **Randomized concentration inequality** (Chen–Shao). Let `∑ᵢ E ξᵢ² = 1`,
`β = ∑ᵢ E|ξᵢ|³`, and let `Δ₁ ≤ Δ₂` be arbitrary random endpoints. For each `i` let `D₁ i, D₂ i`
be random variables that do not depend on the coordinate `ω i`. Then

`P(Δ₁ ≤ W ≤ Δ₂) ≤ E|W (Δ₂ - Δ₁)| + 2β + ∑ᵢ E[|ξᵢ| (|Δ₁ - D₁ i| + |Δ₂ - D₂ i|)]`. -/
theorem pexp_intervalInd_random_le {p : ∀ i, X i → ℝ} (hp0 : ∀ i x, 0 ≤ p i x)
    (hp1 : ∀ i, ∑ x, p i x = 1) {ξ : ∀ i, X i → ℝ} (hmean : ∀ i, ∑ x, p i x * ξ i x = 0)
    (hvar : ∑ i, ∑ x, p i x * ξ i x ^ 2 = 1) (Δ₁ Δ₂ : (∀ i, X i) → ℝ)
    (h12 : ∀ ω, Δ₁ ω ≤ Δ₂ ω) (D₁ D₂ : ι → (∀ i, X i) → ℝ)
    (hD₁ : ∀ i ω b, D₁ i (Function.update ω i b) = D₁ i ω)
    (hD₂ : ∀ i ω b, D₂ i (Function.update ω i b) = D₂ i ω) :
    pexp p (fun ω ↦ intervalInd (Δ₁ ω) (Δ₂ ω) (sumStat ξ ω)) ≤
      pexp p (fun ω ↦ |sumStat ξ ω * (Δ₂ ω - Δ₁ ω)|) + 2 * ∑ i, ∑ x, p i x * |ξ i x| ^ 3 +
        ∑ i, pexp p (fun ω ↦ |ξ i (ω i)| * (|Δ₁ ω - D₁ i ω| + |Δ₂ ω - D₂ i ω|)) := by
  set β := ∑ i, ∑ x, p i x * |ξ i x| ^ 3 with hβdef
  have hβpos : 0 < β := lyapunov_pos hp0 hvar
  set δ := β / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set W := sumStat ξ with hW
  set g : (∀ i, X i) → ℝ → ℝ := fun ω ↦ ramp (Δ₁ ω) (Δ₂ ω) δ with hg
  set gi : ι → (∀ i, X i) → ℝ → ℝ := fun i ω ↦ ramp (D₁ i ω) (D₂ i ω) δ with hgi
  set A : (∀ i, X i) → ℝ := fun ω ↦ intervalInd (Δ₁ ω) (Δ₂ ω) (W ω) with hA
  set Q := pexp p (fun ω ↦ |W ω * (Δ₂ ω - Δ₁ ω)|) with hQ
  set R := ∑ i, pexp p (fun ω ↦ |ξ i (ω i)| * (|Δ₁ ω - D₁ i ω| + |Δ₂ ω - D₂ i ω|)) with hR
  -- upper bound `E[W g(W)] ≤ Q/2 + δ`
  have hEV : pexp p (fun ω ↦ |W ω|) ≤ 1 :=
    sum_mul_abs_le_one (prod_weight_nonneg hp0) (sum_prod_weight hp1)
      (show pexp p (fun ω ↦ W ω ^ 2) ≤ 1 by rw [hW, pexp_sumStat_sq hp1 hmean, hvar])
  have hup : pexp p (fun ω ↦ W ω * g ω (W ω)) ≤ Q / 2 + δ := by
    calc pexp p (fun ω ↦ W ω * g ω (W ω))
          ≤ pexp p (fun ω ↦ (1 / 2) * |W ω * (Δ₂ ω - Δ₁ ω)| + δ * |W ω|) :=
            pexp_mono hp0 fun ω ↦ by
              have hr := abs_ramp_le (h12 ω) hδ.le (W ω)
              have hd : 0 ≤ Δ₂ ω - Δ₁ ω := sub_nonneg.2 (h12 ω)
              rw [abs_mul, abs_of_nonneg hd]
              calc W ω * g ω (W ω) ≤ |W ω * g ω (W ω)| := le_abs_self _
                _ = |W ω| * |g ω (W ω)| := abs_mul _ _
                _ ≤ |W ω| * ((Δ₂ ω - Δ₁ ω) / 2 + δ) :=
                    mul_le_mul_of_nonneg_left hr (abs_nonneg _)
                _ = _ := by ring
      _ = (1 / 2) * Q + δ * pexp p (fun ω ↦ |W ω|) := by
          rw [pexp_add, pexp_const_mul, pexp_const_mul]
      _ ≤ (1 / 2) * Q + δ * 1 := by gcongr
      _ = Q / 2 + δ := by ring
  -- Stein decomposition with the leave-one-out ramps
  have hzero : ∀ i, pexp p (fun ω ↦ ξ i (ω i) * gi i ω (looStat ξ i ω)) = 0 := fun i ↦
    pexp_mul_looStat_eq_zero hp1 hmean i (gi i) (fun ω b ↦ by simp only [hgi, hD₁, hD₂])
  have hdecomp : pexp p (fun ω ↦ W ω * g ω (W ω)) =
      pexp p (fun ω ↦ ∑ i, ξ i (ω i) * (g ω (W ω) - gi i ω (looStat ξ i ω))) := by
    rw [pexp_sum]
    have h1 : pexp p (fun ω ↦ W ω * g ω (W ω)) =
        ∑ i, pexp p (fun ω ↦ ξ i (ω i) * g ω (W ω)) := by
      rw [← pexp_sum]
      simp only [hW, sumStat, Finset.sum_mul]
    rw [h1]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp only [mul_sub]
    rw [pexp_sub, hzero, sub_zero]
  -- pathwise lower bound
  have hpath : ∀ ω, A ω * steinH δ ξ ω -
      (1 / 2) * ∑ i, |ξ i (ω i)| * (|Δ₁ ω - D₁ i ω| + |Δ₂ ω - D₂ i ω|) ≤
      ∑ i, ξ i (ω i) * (g ω (W ω) - gi i ω (looStat ξ i ω)) := by
    intro ω
    have hmain := intervalInd_mul_steinH_le δ hδ ξ ω (Δ₁ ω) (Δ₂ ω)
    have hsplit : ∀ i, ξ i (ω i) * (g ω (W ω) - gi i ω (looStat ξ i ω)) =
        ξ i (ω i) * (ramp (Δ₁ ω) (Δ₂ ω) δ (sumStat ξ ω) -
          ramp (Δ₁ ω) (Δ₂ ω) δ (sumStat ξ ω - ξ i (ω i))) +
        ξ i (ω i) * (ramp (Δ₁ ω) (Δ₂ ω) δ (looStat ξ i ω) -
          ramp (D₁ i ω) (D₂ i ω) δ (looStat ξ i ω)) := by
      intro i
      simp only [hg, hgi, hW, looStat]
      ring
    have herr : ∀ i, -((1 / 2) * (|ξ i (ω i)| * (|Δ₁ ω - D₁ i ω| + |Δ₂ ω - D₂ i ω|))) ≤
        ξ i (ω i) * (ramp (Δ₁ ω) (Δ₂ ω) δ (looStat ξ i ω) -
          ramp (D₁ i ω) (D₂ i ω) δ (looStat ξ i ω)) := by
      intro i
      have hl := abs_ramp_sub_ramp_le (Δ₁ ω) (Δ₂ ω) (D₁ i ω) (D₂ i ω) δ (looStat ξ i ω)
      have hb : |ξ i (ω i) * (ramp (Δ₁ ω) (Δ₂ ω) δ (looStat ξ i ω) -
          ramp (D₁ i ω) (D₂ i ω) δ (looStat ξ i ω))| ≤
          (1 / 2) * (|ξ i (ω i)| * (|Δ₁ ω - D₁ i ω| + |Δ₂ ω - D₂ i ω|)) := by
        rw [abs_mul]
        calc |ξ i (ω i)| * |ramp (Δ₁ ω) (Δ₂ ω) δ (looStat ξ i ω) -
              ramp (D₁ i ω) (D₂ i ω) δ (looStat ξ i ω)|
              ≤ |ξ i (ω i)| * ((|Δ₁ ω - D₁ i ω| + |Δ₂ ω - D₂ i ω|) / 2) :=
                mul_le_mul_of_nonneg_left hl (abs_nonneg _)
          _ = _ := by ring
      exact (abs_le.1 hb).1
    simp only [hsplit, Finset.sum_add_distrib, Finset.mul_sum]
    have h2 := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) ↦ herr i
    simp only [Finset.sum_neg_distrib] at h2
    simp only [hA]
    linarith
  have hlow : pexp p (fun ω ↦ A ω * steinH δ ξ ω) - (1 / 2) * R ≤
      pexp p (fun ω ↦ W ω * g ω (W ω)) := by
    rw [hdecomp, hR, ← pexp_sum, ← pexp_const_mul, ← pexp_sub]
    refine pexp_mono hp0 fun ω ↦ ?_
    simpa only [Finset.mul_sum] using hpath ω
  -- variance part
  have hcore := pexp_mul_steinH_le hp0 hp1 (le_of_eq hvar) hδ A
    (fun ω ↦ intervalInd_nonneg _ _ _) (fun ω ↦ intervalInd_le_one _ _ _)
  rw [hvar] at hcore
  have hq : β / (4 * δ) = 1 / 2 := by
    rw [hδdef]; field_simp; ring
  rw [hq] at hcore
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun i _ ↦ pexp_nonneg hp0 fun ω ↦
    mul_nonneg (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  show pexp p A ≤ Q + 2 * β + R
  have : 2 * β = 4 * δ := by rw [hδdef]; ring
  rw [this]
  linarith

end StatisticalRL.Probability.Stein
