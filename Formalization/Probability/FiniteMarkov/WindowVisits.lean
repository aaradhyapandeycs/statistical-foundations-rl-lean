import Formalization.Probability.FiniteMarkov.Path
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Window visit counts of a uniformly mixing finite chain (Lemma V)

Self-contained replacement for the concentration step cited (not proved) at
`chapters/generative_model_model_free.tex:2126`. For a block of `b` consecutive times and a pair
`z` with `b μ(z) ≥ 8 t̄`, the number of visits `V` satisfies, from **any** initial law,
`E e^{-θV} ≤ 23/25` at `θ b μ(z) = 4/25` (second-moment bound via the Markov property and the
mixing distances). Peeling `J` blocks gives `P(visits < J b μ(z)/4) ≤ e^{-J/25}`. -/

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false

namespace StatisticalRL.FiniteMarkov

theorem exp_neg_le_quad {u : ℝ} (hu : 0 ≤ u) : Real.exp (-u) ≤ 1 - u + u ^ 2 / 2 := by
  have hd : ∀ v : ℝ, HasDerivAt (fun v : ℝ ↦ Real.exp v * (1 - v + v ^ 2 / 2))
      (Real.exp v * (v ^ 2 / 2)) v := fun v ↦ by
    have h1 := Real.hasDerivAt_exp v
    have h2 : HasDerivAt (fun v : ℝ ↦ 1 - v + v ^ 2 / 2) (-1 + (2 * v) / 2) v := by
      have := ((hasDerivAt_id v).const_sub 1).add ((hasDerivAt_pow 2 v).div_const 2)
      simpa using this
    convert h1.mul h2 using 1
    ring
  have hmono : Monotone (fun v : ℝ ↦ Real.exp v * (1 - v + v ^ 2 / 2)) :=
    monotone_of_deriv_nonneg (fun v ↦ (hd v).differentiableAt)
      (fun v ↦ by rw [(hd v).deriv]; positivity)
  have h := hmono hu
  simp only [Real.exp_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_div, add_zero, mul_one] at h
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos u)]
  linarith [mul_comm (Real.exp u) (1 - u + u ^ 2 / 2)]

variable {X : Type*} [Fintype X] [DecidableEq X] {K : X → X → ℝ}

/-- Indicator of the state `z`. -/
def ind (z y : X) : ℝ := if y = z then 1 else 0

theorem ind_nonneg (z y : X) : 0 ≤ ind z y := by unfold ind; split_ifs <;> norm_num

theorem ind_le_one (z y : X) : ind z y ≤ 1 := by unfold ind; split_ifs <;> norm_num

theorem ind_sq (z y : X) : ind z y * ind z y = ind z y := by unfold ind; split_ifs <;> norm_num

theorem sum_kpow_mul_ind (t : ℕ) (u z : X) : ∑ y, kpow K t u y * ind z y = kpow K t u z := by
  simp [ind]

/-- Visit probability of `z` at time `i` from the initial law `lam`. -/
noncomputable def visitProb (K : X → X → ℝ) (lam : X → ℝ) (z : X) (i : ℕ) : ℝ :=
  ∑ x, lam x * kpow K i x z

theorem pathExp_ind (hK : IsStochastic K) {lam : X → ℝ} {n i : ℕ} (hi : i ≤ n) (z : X) :
    pathExp lam K n (fun x ↦ ind z (pathAt x i)) = visitProb K lam z i := by
  rw [pathExp_coord hK hi]
  simp [visitProb, sum_kpow_mul_ind]

theorem pathExp_ind_pair (hK : IsStochastic K) {lam : X → ℝ} {n i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ n) (z : X) :
    pathExp lam K n (fun x ↦ ind z (pathAt x i) * ind z (pathAt x j)) =
      visitProb K lam z i * kpow K (j - i) z z := by
  have h := pathExp_markov_iter (ν := lam) (n := n) hK (j - i) i (by omega)
    (fun x ↦ ind z (pathAt x i)) (dependsUpTo_coord _ le_rfl) (ind z)
  rw [show i + (j - i) = j by omega] at h
  rw [h]
  simp_rw [sum_kpow_mul_ind]
  have : ∀ x : Fin (n + 1) → X, ind z (pathAt x i) * kpow K (j - i) (pathAt x i) z =
      kpow K (j - i) z z * ind z (pathAt x i) := fun x ↦ by
    unfold ind; split_ifs with h <;> simp [h, mul_comm]
  simp_rw [this]
  rw [pathExp_smul, pathExp_ind hK (by omega), mul_comm]

/-- Second moment of the block visit count. -/
theorem pathExp_visits_sq_le (hK : IsStochastic K) {lam : X → ℝ} (hlam : ∀ x, 0 ≤ lam x)
    {n b : ℕ} (hb : b ≤ n + 1) (z : X) :
    pathExp lam K n (fun x ↦ (∑ i ∈ range b, ind z (pathAt x i)) ^ 2) ≤
      2 * (∑ i ∈ range b, visitProb K lam z i) * ∑ m ∈ range b, kpow K m z z := by
  set a : ℕ → ℕ → ℝ := fun i j ↦ pathExp lam K n (fun x ↦ ind z (pathAt x i) * ind z (pathAt x j))
  have hsq : ∀ x : Fin (n + 1) → X, (∑ i ∈ range b, ind z (pathAt x i)) ^ 2 =
      ∑ i ∈ range b, ∑ j ∈ range b, ind z (pathAt x i) * ind z (pathAt x j) := fun x ↦ by
    rw [sq, sum_mul_sum]
  simp_rw [hsq, pathExp_sum]
  set B : ℕ → ℕ → ℝ := fun i j ↦ if i ≤ j then a i j else 0
  have ha0 : ∀ i j, 0 ≤ a i j := fun i j ↦
    pathExp_nonneg hK hlam fun x ↦ mul_nonneg (ind_nonneg _ _) (ind_nonneg _ _)
  have hB0 : ∀ i j, 0 ≤ B i j := fun i j ↦ by simp only [B]; split_ifs <;> simp [ha0]
  have hsymm : ∀ i j, a i j = a j i := fun i j ↦ by
    simp only [a]; congr 1; funext x; ring
  have hle : ∀ i j, a i j ≤ B i j + B j i := fun i j ↦ by
    simp only [B]
    by_cases hij : i ≤ j
    · simp only [hij, if_true]; split_ifs <;> linarith [ha0 j i]
    · simp only [hij, if_false, zero_add]
      rw [if_pos (by omega), hsymm]
  have hBsum : ∀ i ∈ range b, ∑ j ∈ range b, B i j ≤
      visitProb K lam z i * ∑ m ∈ range b, kpow K m z z := fun i hi ↦ by
    have hib := mem_range.mp hi
    have hfull : ∑ j ∈ range b, B i j = ∑ m ∈ range (b - i), visitProb K lam z i * kpow K m z z := by
      conv_lhs => rw [show b = i + (b - i) by omega]
      rw [sum_range_add]
      have h0 : ∑ j ∈ range i, B i j = 0 :=
        sum_eq_zero fun j hj ↦ by simp only [B]; rw [if_neg (by have := mem_range.mp hj; omega)]
      rw [h0, zero_add]
      refine sum_congr rfl fun m hm ↦ ?_
      have hm' := mem_range.mp hm
      simp only [B, a]
      rw [if_pos (by omega), pathExp_ind_pair hK (by omega) (by omega)]
      congr 2; omega
    rw [hfull, ← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ ?_
    · exact sum_le_sum_of_subset_of_nonneg (range_mono (Nat.sub_le b i))
        fun m _ _ ↦ kpow_nonneg hK m z z
    · exact sum_nonneg fun x _ ↦ mul_nonneg (hlam x) (kpow_nonneg hK i x z)
  calc ∑ i ∈ range b, ∑ j ∈ range b, a i j
      ≤ ∑ i ∈ range b, ∑ j ∈ range b, (B i j + B j i) :=
        sum_le_sum fun i _ ↦ sum_le_sum fun j _ ↦ hle i j
    _ = 2 * ∑ i ∈ range b, ∑ j ∈ range b, B i j := by
        simp_rw [sum_add_distrib]; rw [sum_comm (f := fun i j ↦ B j i)]; ring
    _ ≤ 2 * ∑ i ∈ range b, visitProb K lam z i * ∑ m ∈ range b, kpow K m z z := by
        gcongr with i hi; exact hBsum i hi
    _ = 2 * (∑ i ∈ range b, visitProb K lam z i) * ∑ m ∈ range b, kpow K m z z := by
        rw [mul_assoc, sum_mul]

variable [Nonempty X]

/-- Block exponential moment: from any initial law, `E e^{-θ V} ≤ 23/25` when
`θ b μ(z) = 4/25` and `b μ(z) ≥ 8 t̄`. -/
theorem block_exp_moment_le (hK : IsStochastic K) {μ : X → ℝ} (hμ : IsProb μ)
    (hst : ∀ y, ∑ x, μ x * K x y = μ y) {tb : ℕ} (htb1 : 1 ≤ tb)
    (htb : mixDist K μ tb ≤ 1 / 4) {z : X} (hz : 0 < μ z) {c : ℕ}
    (hb : 8 * (tb : ℝ) ≤ (c + 1) * μ z) {lam : X → ℝ} (hlam : IsProb lam) :
    ∑ x, lam x * blockValue K (fun y ↦ Real.exp (-((4 / 25) / ((c + 1) * μ z)) * ind z y))
      (c + 1) x ≤ 23 / 25 := by
  set w := μ z
  set bw : ℝ := (c + 1) * w with hbw
  have hbw0 : 0 < bw := by positivity
  set θ : ℝ := (4 / 25) / bw with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hsumd := sum_mixDist_le hK hμ hst htb1 htb (c + 1)
  set V : (Fin (c + 1) → X) → ℝ := fun x ↦ ∑ i ∈ range (c + 1), ind z (pathAt x i)
  have hprod : ∀ x : Fin (c + 1) → X, ∏ i ∈ range (c + 1), Real.exp (-θ * ind z (pathAt x i)) =
      Real.exp (-(θ * V x)) := fun x ↦ by
    rw [← Real.exp_sum]; congr 1; simp only [V, mul_sum, neg_mul, sum_neg_distrib]
  rw [blockValue_eq_pathExp hK]
  simp_rw [hprod]
  have hV0 : ∀ x, 0 ≤ V x := fun x ↦ sum_nonneg fun i _ ↦ ind_nonneg _ _
  have hEV : pathExp lam K c V = ∑ i ∈ range (c + 1), visitProb K lam z i := by
    simp only [V]; rw [pathExp_sum]
    exact sum_congr rfl fun i hi ↦ pathExp_ind hK (by have := mem_range.mp hi; omega) z
  have hP : ∀ i, |visitProb K lam z i - w| ≤ mixDist K μ i := fun i ↦
    abs_marginal_sub_le hK hμ hlam i z
  have hEV_lo : (3 / 4) * bw ≤ pathExp lam K c V := by
    rw [hEV]
    have : ∑ i ∈ range (c + 1), (w - mixDist K μ i) ≤ ∑ i ∈ range (c + 1), visitProb K lam z i :=
      sum_le_sum fun i _ ↦ by linarith [(abs_le.mp (hP i)).1]
    rw [sum_sub_distrib] at this
    simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at this
    nlinarith
  have hEV_hi : pathExp lam K c V ≤ (5 / 4) * bw := by
    rw [hEV]
    have : ∑ i ∈ range (c + 1), visitProb K lam z i ≤ ∑ i ∈ range (c + 1), (w + mixDist K μ i) :=
      sum_le_sum fun i _ ↦ by linarith [(abs_le.mp (hP i)).2]
    rw [sum_add_distrib] at this
    simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at this
    nlinarith
  have hS : ∑ m ∈ range (c + 1), kpow K m z z ≤ (5 / 4) * bw := by
    have hk : ∀ m, kpow K m z z ≤ w + mixDist K μ m := fun m ↦ by
      have := abs_sub_le_tvDist (p := kpow K m z) (q := μ)
        (by rw [kpow_row_sum hK, hμ.sum_eq]) z
      linarith [(abs_le.mp (this.trans (tvDist_le_mixDist μ m z))).2]
    have : ∑ m ∈ range (c + 1), kpow K m z z ≤ ∑ m ∈ range (c + 1), (w + mixDist K μ m) :=
      sum_le_sum fun m _ ↦ hk m
    rw [sum_add_distrib] at this
    simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at this
    nlinarith
  have hEV2 := pathExp_visits_sq_le hK hlam.nonneg (n := c) (b := c + 1) le_rfl z
  rw [← hEV] at hEV2
  have hS0 : 0 ≤ ∑ m ∈ range (c + 1), kpow K m z z := sum_nonneg fun m _ ↦ kpow_nonneg hK m z z
  have hEV2' : pathExp lam K c (fun x ↦ V x ^ 2) ≤ 2 * ((5 / 4) * bw) * ((5 / 4) * bw) := by
    refine hEV2.trans ?_
    have := hEV_lo
    gcongr
  calc pathExp lam K c (fun x ↦ Real.exp (-(θ * V x)))
      ≤ pathExp lam K c (fun x ↦ 1 + (-θ) * V x + (θ ^ 2 / 2) * V x ^ 2) :=
        pathExp_mono hK hlam.nonneg fun x ↦ by
          have := exp_neg_le_quad (mul_nonneg hθ0 (hV0 x)); nlinarith
    _ = 1 + (-θ) * pathExp lam K c V + (θ ^ 2 / 2) * pathExp lam K c (fun x ↦ V x ^ 2) := by
        rw [pathExp_add, pathExp_add, pathExp_smul, pathExp_smul, pathExp_one hK hlam]
    _ ≤ 1 + (-θ) * ((3 / 4) * bw) + (θ ^ 2 / 2) * (2 * ((5 / 4) * bw) * ((5 / 4) * bw)) := by
        have h1 : (-θ) * pathExp lam K c V ≤ (-θ) * ((3 / 4) * bw) := by nlinarith
        have h2 := mul_le_mul_of_nonneg_left hEV2' (by positivity : (0 : ℝ) ≤ θ ^ 2 / 2)
        linarith
    _ = 23 / 25 := by rw [hθ]; field_simp; ring

/-- **Lemma V.** For blocks of length `c + 1` with `(c+1) μ(z) ≥ 8 t̄`, starting at time `τ`,
the probability that the first `J` blocks contain fewer than `J (c+1) μ(z) / 4` visits to `z` is
at most `e^{-J/25}`, from any initial law `ν`. -/
theorem window_visits_tail (hK : IsStochastic K) {ν : X → ℝ} (hν : IsProb ν) {μ : X → ℝ}
    (hμ : IsProb μ) (hst : ∀ y, ∑ x, μ x * K x y = μ y) {tb : ℕ} (htb1 : 1 ≤ tb)
    (htb : mixDist K μ tb ≤ 1 / 4) {z : X} (hz : 0 < μ z) {c : ℕ}
    (hb : 8 * (tb : ℝ) ≤ (c + 1) * μ z) {n : ℕ} (τ J : ℕ) (hJ : τ + J * (c + 1) ≤ n + 1) :
    pathExp ν K n (fun x ↦ if (∑ i ∈ range (J * (c + 1)), ind z (pathAt x (τ + i))) <
        J * ((c + 1) * μ z) / 4 then 1 else 0) ≤ Real.exp (-(J / 25)) := by
  set bw : ℝ := (c + 1) * μ z with hbw
  have hbw0 : 0 < bw := by positivity
  set θ : ℝ := (4 / 25) / bw with hθ
  have hθ0 : 0 ≤ θ := by positivity
  set φ : X → ℝ := fun y ↦ Real.exp (-θ * ind z y)
  have hφ : ∀ y, 0 ≤ φ y := fun y ↦ (Real.exp_pos _).le
  have hwin := pathExp_window_prod_le (ν := ν) hK hν hφ (b := c + 1) (by omega) τ
    (ρ := 23 / 25) (by norm_num)
    (fun y ↦ block_exp_moment_le hK hμ hst htb1 htb hz hb ⟨hK.nonneg y, hK.row_sum y⟩)
    (block_exp_moment_le hK hμ hst htb1 htb hz hb hν) J hJ
  set N : (Fin (n + 1) → X) → ℝ := fun x ↦ ∑ i ∈ range (J * (c + 1)), ind z (pathAt x (τ + i))
  have hind : ∀ x, (if N x < J * bw / 4 then (1 : ℝ) else 0) ≤
      Real.exp (θ * (J * bw / 4)) * ∏ i ∈ range (J * (c + 1)), φ (pathAt x (τ + i)) := fun x ↦ by
    have hprod : ∏ i ∈ range (J * (c + 1)), φ (pathAt x (τ + i)) = Real.exp (-(θ * N x)) := by
      rw [← Real.exp_sum]; congr 1; simp only [N, mul_sum, neg_mul, sum_neg_distrib]
    rw [hprod, ← Real.exp_add]
    split_ifs with h
    · exact Real.one_le_exp (by nlinarith)
    · exact (Real.exp_pos _).le
  calc pathExp ν K n (fun x ↦ if N x < J * bw / 4 then 1 else 0)
      ≤ pathExp ν K n (fun x ↦ Real.exp (θ * (J * bw / 4)) *
          ∏ i ∈ range (J * (c + 1)), φ (pathAt x (τ + i))) := pathExp_mono hK hν.nonneg hind
    _ ≤ Real.exp (θ * (J * bw / 4)) * (23 / 25) ^ J := by
        rw [pathExp_smul]; exact mul_le_mul_of_nonneg_left hwin (Real.exp_pos _).le
    _ ≤ Real.exp (J / 25) * Real.exp (-(2 / 25)) ^ J := by
        have he : θ * (J * bw / 4) = J / 25 := by rw [hθ]; field_simp
        rw [he]
        gcongr
        have := Real.add_one_le_exp (-(2 / 25))
        linarith
    _ = Real.exp (-(J / 25)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

end StatisticalRL.FiniteMarkov
