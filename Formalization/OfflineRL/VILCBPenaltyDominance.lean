import Formalization.OfflineRL.BernsteinInfiniteData
import Formalization.OfflineRL.PreliminaryFacts

/-!
# Theorem 6.3, Step 1: the Bernstein penalty dominates the empirical deviation

Source: `chapters/offlineRL.tex:1134–1196` (`eq:infitnie-bernstein-b-bound-diff`, `:1174–1177`,
zero-count branch `:1182–1194`) and the penalty upper bound of Step 4.2
(`eq:infinite-bernstein-large-result-middle`, `:1456–1466`).

Deterministic statements about one VI-LCB run `I : Input S A`. With `L = log(N/((1-γ)δ))`
(the penalty log) and `ℓ = log(4N/((1-γ)δ))` (the Lemma 6.6 log), `γ ≥ 1/2` gives `ℓ ≤ 3L`.
If the two Lemma 6.6 conclusions (`Input.Lemma66Bound`) hold at a pair with `N_{s,a} > 0` for a
vector `0 ≤ V ≤ 1/(1-γ)`, and `c_b ≥ 96`, then
* `|(P̂_{s,a} − P_{s,a}) V| + 5/N ≤ b(s,a;V)` (also at zero-count pairs, where no bound is needed);
* `b(s,a;V) ≤ √(2 c_b L Var_{P_{s,a}}(V)/N_{s,a}) + 4 c_b L/((1-γ) N_{s,a})`.
-/

open scoped BigOperators

namespace StatisticalRL.OfflineVILCB.Theorem63

open StatisticalRL StatisticalRL.OfflineVILCB

variable {S A : Type*} [Fintype S] [Fintype A]

/-- Two expectations of a vector with values in `[0, R]` differ by at most `R`. -/
theorem abs_expectation_sub_le_of_mem_Icc (d₁ d₂ : FiniteDistribution S) (V : S → ℝ) {R : ℝ}
    (h0 : ∀ t, 0 ≤ V t) (h1 : ∀ t, V t ≤ R) :
    |d₁.expectation V - d₂.expectation V| ≤ R := by
  have a0 := d₁.expectation_nonneg h0
  have a1 := d₁.expectation_le_const h1
  have b0 := d₂.expectation_nonneg h0
  have b1 := d₂.expectation_le_const h1
  rw [abs_le]
  constructor <;> linarith

variable (I : Input S A)

/-- `log 2 ≤ L = log(N/((1-γ)δ))` when `γ ≥ 1/2`. -/
theorem log_two_le_logTerm (hγ : 1 / 2 ≤ I.γ) : Real.log 2 ≤ I.logTerm := by
  unfold Input.logTerm
  have hk := I.one_sub_γ_pos
  have hkδ : 0 < (1 - I.γ) * I.δ := mul_pos hk I.δ_pos
  have hN : (1 : ℝ) ≤ I.N := by exact_mod_cast I.N_pos
  have hkδ1 : (1 - I.γ) * I.δ ≤ 1 / 2 := by nlinarith [I.δ_pos, I.δ_lt_one]
  apply Real.log_le_log (by norm_num)
  rw [le_div_iff₀ hkδ]
  nlinarith

/-- `ℓ = log(4N/((1-γ)δ)) = log 4 + L`. -/
theorem log_four_mul_eq : Real.log (4 * I.N / ((1 - I.γ) * I.δ)) = Real.log 4 + I.logTerm := by
  unfold Input.logTerm
  have hk := I.one_sub_γ_pos
  have hN : (0 : ℝ) < I.N := by exact_mod_cast I.N_pos
  have hx : (0 : ℝ) < I.N / ((1 - I.γ) * I.δ) := by have := I.δ_pos; positivity
  rw [mul_div_assoc, Real.log_mul (by norm_num) hx.ne']

/-- `ℓ ≤ 3L` when `γ ≥ 1/2`. -/
theorem ell_le_three_logTerm (hγ : 1 / 2 ≤ I.γ) :
    Real.log (4 * I.N / ((1 - I.γ) * I.δ)) ≤ 3 * I.logTerm := by
  rw [log_four_mul_eq I]
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have := log_two_le_logTerm I hγ
  linarith

/-- The penalty never exceeds `1/(1-γ) + 5/N`. -/
theorem bonus_le_bound (s : S) (a : A) (V : S → ℝ) :
    I.bonus s a V ≤ 1 / (1 - I.γ) + 5 / I.N := by
  unfold Input.bonus
  split_ifs
  · exact le_rfl
  · have := min_le_right (max (Real.sqrt (I.cb * I.logTerm / I.count s a * (I.Phat s a).variance V))
      (2 * I.cb * I.logTerm / ((1 - I.γ) * I.count s a))) (1 / (1 - I.γ))
    linarith

/-- **Step 1** (`eq:infitnie-bernstein-b-bound-diff`, `offlineRL.tex:1174–1194`) for one pair:
on the Lemma 6.6 bound (needed only when `N_{s,a} > 0`), `c_b ≥ 96` gives
`|(P̂_{s,a} − d) V| + 5/N ≤ b(s,a;V)` for `0 ≤ V ≤ 1/(1-γ)`. -/
theorem bonus_dominates (hγ : 1 / 2 ≤ I.γ) (hcb : 96 ≤ I.cb) (d : FiniteDistribution S)
    (s : S) (a : A) (V : S → ℝ) (hV0 : ∀ t, 0 ≤ V t) (hV1 : ∀ t, V t ≤ 1 / (1 - I.γ))
    (hgood : 0 < I.count s a →
      I.Lemma66Bound d s a (Real.log (4 * I.N / ((1 - I.γ) * I.δ))) V) :
    |(I.Phat s a).expectation V - d.expectation V| + 5 / I.N ≤ I.bonus s a V := by
  have hbox := abs_expectation_sub_le_of_mem_Icc (I.Phat s a) d V hV0 hV1
  unfold Input.bonus
  split_ifs with h0
  · linarith
  · have hpos : 0 < I.count s a := Nat.pos_of_ne_zero h0
    obtain ⟨hdev, -⟩ := hgood hpos
    set n : ℝ := (I.count s a : ℝ) with hn
    have hn0 : 0 < n := by rw [hn]; exact_mod_cast hpos
    set L := I.logTerm with hL
    set ℓ := Real.log (4 * I.N / ((1 - I.γ) * I.δ)) with hℓ
    set v := (I.Phat s a).variance V with hv
    have hv0 : 0 ≤ v := (I.Phat s a).variance_nonneg V
    have hk := I.one_sub_γ_pos
    have hL0 : 0 < L := I.logTerm_pos
    have hℓL : ℓ ≤ 3 * L := ell_le_three_logTerm I hγ
    have hcbL : 32 * ℓ ≤ I.cb * L := by nlinarith
    -- the square-root term
    have hsq : Real.sqrt (8 * ℓ / n * v) ≤ Real.sqrt (I.cb * L / n * v) / 2 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      rw [div_pow, Real.sq_sqrt (by have := I.cb_pos; positivity)]
      have : 8 * ℓ / n * v * 4 ≤ I.cb * L / n * v := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
          div_le_div_iff_of_pos_right hn0]
        nlinarith
      linarith
    -- the linear term
    have hlin : 26 * ℓ / ((1 - I.γ) * n) ≤ (2 * I.cb * L / ((1 - I.γ) * n)) / 2 := by
      have h2 : (2 * I.cb * L / ((1 - I.γ) * n)) / 2 = I.cb * L / ((1 - I.γ) * n) := by ring
      rw [h2]
      exact div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    have hmax : Real.sqrt (I.cb * L / n * v) / 2 + (2 * I.cb * L / ((1 - I.γ) * n)) / 2 ≤
        max (Real.sqrt (I.cb * L / n * v)) (2 * I.cb * L / ((1 - I.γ) * n)) := by
      have := le_max_left (Real.sqrt (I.cb * L / n * v)) (2 * I.cb * L / ((1 - I.γ) * n))
      have := le_max_right (Real.sqrt (I.cb * L / n * v)) (2 * I.cb * L / ((1 - I.γ) * n))
      linarith
    have hD : |(I.Phat s a).expectation V - d.expectation V| ≤
        min (max (Real.sqrt (I.cb * L / n * v)) (2 * I.cb * L / ((1 - I.γ) * n)))
          (1 / (1 - I.γ)) := by
      refine le_min ?_ hbox
      have : |(I.Phat s a).expectation V - d.expectation V| ≤
          Real.sqrt (8 * ℓ / n * v) + 26 * ℓ / ((1 - I.γ) * n) := hdev
      linarith
    linarith

/-- `√(a + b²) ≤ √a + b` for `a, b ≥ 0`. -/
theorem sqrt_add_sq_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b ^ 2) ≤ Real.sqrt a + b := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have h := Real.sq_sqrt ha
  have : 0 ≤ Real.sqrt a * b := by positivity
  nlinarith

/-- **Step 4.2 penalty upper bound** (`offlineRL.tex:1456–1466`): at a pair with
`0 < N_{s,a} ≤ N` on the Lemma 6.6 bound, for `c_b ≥ 96`,
`b(s,a;V) ≤ √(2 c_b L Var_d(V)/N_{s,a}) + 4 c_b L/((1-γ) N_{s,a})`. -/
theorem bonus_le_of_lemma66 (hγ : 1 / 2 ≤ I.γ) (hcb : 96 ≤ I.cb) (d : FiniteDistribution S)
    (s : S) (a : A) (V : S → ℝ) (hpos : 0 < I.count s a) (hnN : I.count s a ≤ I.N)
    (hgood : I.Lemma66Bound d s a (Real.log (4 * I.N / ((1 - I.γ) * I.δ))) V) :
    I.bonus s a V ≤ Real.sqrt (2 * I.cb * I.logTerm * d.variance V / I.count s a) +
      4 * I.cb * I.logTerm / ((1 - I.γ) * I.count s a) := by
  obtain ⟨-, hvar⟩ := hgood
  have h0 : I.count s a ≠ 0 := hpos.ne'
  unfold Input.bonus
  rw [if_neg h0]
  set n : ℝ := (I.count s a : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast hpos
  have hnN' : n ≤ I.N := by rw [hn]; exact_mod_cast hnN
  set L := I.logTerm with hL
  set ℓ := Real.log (4 * I.N / ((1 - I.γ) * I.δ)) with hℓ
  have hk := I.one_sub_γ_pos
  have hk1 : 1 - I.γ ≤ 1 / 2 := by linarith
  have hL0 : 0 < L := I.logTerm_pos
  have hL2 : Real.log 2 ≤ L := log_two_le_logTerm I hγ
  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hℓL : ℓ ≤ 3 * L := ell_le_three_logTerm I hγ
  have hcb0 : 0 < I.cb := I.cb_pos
  set v := (I.Phat s a).variance V with hv
  set w := d.variance V with hw
  have hw0 : 0 ≤ w := d.variance_nonneg V
  set W := I.cb * L / ((1 - I.γ) * n) with hW
  have hW0 : 0 < W := by positivity
  -- variance transfer inside the square root
  have hv' : v ≤ 2 * w + 72 * L / ((1 - I.γ) ^ 2 * n) := by
    have : 24 * ℓ / ((1 - I.γ) ^ 2 * n) ≤ 72 * L / ((1 - I.γ) ^ 2 * n) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hinside : I.cb * L / n * v ≤ 2 * I.cb * L * w / n + W ^ 2 := by
    have h1 : I.cb * L / n * v ≤ I.cb * L / n * (2 * w + 72 * L / ((1 - I.γ) ^ 2 * n)) :=
      mul_le_mul_of_nonneg_left hv' (by positivity)
    have h2 : I.cb * L / n * (2 * w + 72 * L / ((1 - I.γ) ^ 2 * n)) =
        2 * I.cb * L * w / n + (72 / I.cb) * W ^ 2 := by
      rw [hW]; field_simp
    have h3 : (72 / I.cb) * W ^ 2 ≤ W ^ 2 := by
      have : 72 / I.cb ≤ 1 := by rw [div_le_one hcb0]; linarith
      nlinarith [sq_nonneg W]
    linarith
  have hx : Real.sqrt (I.cb * L / n * v) ≤ Real.sqrt (2 * I.cb * L * w / n) + W :=
    (Real.sqrt_le_sqrt hinside).trans (sqrt_add_sq_le (by positivity) hW0.le)
  have hy : 2 * I.cb * L / ((1 - I.γ) * n) = 2 * W := by rw [hW]; ring
  have h5 : 5 / (I.N : ℝ) ≤ W := by
    have h5n : 5 / (I.N : ℝ) ≤ 5 / n := div_le_div_of_nonneg_left (by norm_num) hn0 hnN'
    have : 5 / n ≤ W := by
      rw [hW, div_le_div_iff₀ hn0 (by positivity)]
      have : 5 * (1 - I.γ) ≤ I.cb * L := by nlinarith
      nlinarith
    linarith
  have hfinal : 4 * I.cb * L / ((1 - I.γ) * n) = 4 * W := by rw [hW]; ring
  rw [hfinal]
  have hmin := min_le_left (max (Real.sqrt (I.cb * L / n * v)) (2 * I.cb * L / ((1 - I.γ) * n)))
    (1 / (1 - I.γ))
  have hmax : max (Real.sqrt (I.cb * L / n * v)) (2 * I.cb * L / ((1 - I.γ) * n)) ≤
      Real.sqrt (2 * I.cb * L * w / n) + 2 * W := by
    rw [hy]
    refine max_le (by linarith) ?_
    have := Real.sqrt_nonneg (2 * I.cb * L * w / n)
    linarith
  linarith

end StatisticalRL.OfflineVILCB.Theorem63
