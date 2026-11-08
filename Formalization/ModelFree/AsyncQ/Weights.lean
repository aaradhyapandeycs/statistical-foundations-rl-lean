import Formalization.Probability.FiniteMarkov.Mixing

/-! # Asynchronous weights: visit counts, the `n`-indexed predictable weights and unrolling

Generic deterministic sequences for §3.3/§3.6 of the plan. A window step `k` is a visit when
`v k` holds; `cnt v k` counts visits among the first `k` steps. The fluctuation `accum` obeys the
recursion `ξ_{k+1} = (1-η)ξ_k + η d_k` at visits (and is unchanged otherwise); it equals the
predictable-weight sum `∑ weight n i · d i` when `n = cnt k` (`accum_eq_sum_weight`), and the squared
weights sum to at most `η` (`sum_weight_sq_le`). `unroll_le` is the one-sided unrolled bound. -/

open scoped BigOperators
open Finset

namespace StatisticalRL.AsyncQ

variable (v : ℕ → Prop) [DecidablePred v]

/-- Number of visits among the first `k` window steps. -/
def cnt (k : ℕ) : ℕ := ((range k).filter v).card

theorem cnt_zero : cnt v 0 = 0 := by simp [cnt]

theorem cnt_succ (k : ℕ) : cnt v (k + 1) = cnt v k + if v k then 1 else 0 := by
  unfold cnt
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem cnt_mono {k k' : ℕ} (h : k ≤ k') : cnt v k ≤ cnt v k' :=
  card_le_card (filter_subset_filter _ (range_mono h))

theorem cnt_cast (k : ℕ) : (cnt v k : ℝ) = ∑ i ∈ range k, if v i then (1 : ℝ) else 0 := by
  unfold cnt; rw [sum_boole]

/-- Predictable weight `η 1{v i} (1-η)^{n - cnt(i+1)} 1{cnt(i+1) ≤ n}`. -/
noncomputable def weight (η : ℝ) (n i : ℕ) : ℝ :=
  if v i ∧ cnt v (i + 1) ≤ n then η * (1 - η) ^ (n - cnt v (i + 1)) else 0

/-- `ξ₀ = 0`, `ξ_{k+1} = (1-η) ξ_k + η d_k` at a visit, `ξ_{k+1} = ξ_k` otherwise. -/
noncomputable def accum (η : ℝ) (d : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => if v k then (1 - η) * accum η d k + η * d k else accum η d k

theorem accum_eq_sum_weight (η : ℝ) (d : ℕ → ℝ) (k n : ℕ) (hn : cnt v k ≤ n) :
    (1 - η) ^ (n - cnt v k) * accum v η d k = ∑ i ∈ range k, weight v η n i * d i := by
  induction k generalizing n with
  | zero => simp [accum]
  | succ k ih =>
    rw [sum_range_succ, cnt_succ] at *
    by_cases hk : v k
    · simp only [hk, if_true] at hn ⊢
      have ih' := ih n (by omega)
      have hw : weight v η n k = η * (1 - η) ^ (n - (cnt v k + 1)) := by
        unfold weight; rw [cnt_succ, if_pos ⟨hk, by simp [hk]; omega⟩]; simp [hk]
      rw [hw, accum, if_pos hk, ← ih']
      have : n - cnt v k = (n - (cnt v k + 1)) + 1 := by omega
      rw [this, pow_succ]
      ring
    · simp only [hk, if_false, add_zero] at hn ⊢
      have hw : weight v η n k = 0 := by unfold weight; simp [hk]
      rw [hw, zero_mul, add_zero, accum, if_neg hk]
      exact ih n hn

theorem accum_eq (η : ℝ) (d : ℕ → ℝ) (k : ℕ) :
    accum v η d k = ∑ i ∈ range k, weight v η (cnt v k) i * d i := by
  have := accum_eq_sum_weight v η d k (cnt v k) le_rfl
  simpa using this

theorem abs_weight_le {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (n i : ℕ) : |weight v η n i| ≤ η := by
  unfold weight
  split_ifs
  · rw [abs_of_nonneg (mul_nonneg hη0 (pow_nonneg (by linarith) _))]
    exact mul_le_of_le_one_right hη0 (pow_le_one₀ (by linarith) (by linarith))
  · simp [hη0]

theorem weight_nonneg {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (n i : ℕ) : 0 ≤ weight v η n i := by
  unfold weight; split_ifs
  · exact mul_nonneg hη0 (pow_nonneg (by linarith) _)
  · exact le_rfl

theorem sum_weight_sq_le {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) (n k : ℕ) :
    ∑ i ∈ range k, weight v η n i ^ 2 ≤ η := by
  set q : ℝ := (1 - η) ^ 2
  have hq0 : 0 ≤ q := sq_nonneg _
  have hq1 : 0 < 1 - q := by simp only [q]; nlinarith
  have hqle : q ≤ 1 := by linarith
  have key : ∀ k, ∑ i ∈ range k, weight v η n i ^ 2 ≤
      η ^ 2 * q ^ (n - min (cnt v k) n) / (1 - q) := by
    intro k
    induction k with
    | zero => simp; positivity
    | succ k ih =>
      rw [sum_range_succ]
      by_cases hk : v k
      · by_cases hn : cnt v (k + 1) ≤ n
        · have hc : cnt v (k + 1) = cnt v k + 1 := by rw [cnt_succ]; simp [hk]
          have hw : weight v η n k = η * (1 - η) ^ (n - cnt v (k + 1)) := by
            unfold weight; rw [if_pos ⟨hk, hn⟩]
          have hn' : cnt v k + 1 ≤ n := hc ▸ hn
          rw [hw, hc, min_eq_left hn']
          rw [min_eq_left (by omega)] at ih
          have he : n - cnt v k = (n - (cnt v k + 1)) + 1 := by omega
          rw [he, pow_succ q] at ih
          have hp : (η * (1 - η) ^ (n - (cnt v k + 1))) ^ 2 = η ^ 2 * q ^ (n - (cnt v k + 1)) := by
            simp only [q]; rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm 2]
          rw [hp]
          have hpos : 0 ≤ η ^ 2 * q ^ (n - (cnt v k + 1)) := by positivity
          rw [div_eq_mul_inv] at ih ⊢
          have : η ^ 2 * (q ^ (n - (cnt v k + 1)) * q) * (1 - q)⁻¹ + η ^ 2 * q ^ (n - (cnt v k + 1)) =
              η ^ 2 * q ^ (n - (cnt v k + 1)) * (1 - q)⁻¹ := by field_simp; ring
          linarith
        · have hw : weight v η n k = 0 := by unfold weight; rw [if_neg (by tauto)]
          rw [hw]
          have hc : n ≤ cnt v (k + 1) := by omega
          have hck : n ≤ cnt v k := by rw [cnt_succ] at hn; simp [hk] at hn; omega
          rw [min_eq_right hck] at ih; rw [min_eq_right hc]
          simpa using ih
      · have hw : weight v η n k = 0 := by unfold weight; simp [hk]
        have hc : cnt v (k + 1) = cnt v k := by rw [cnt_succ]; simp [hk]
        rw [hw, hc]; simpa using ih
  refine (key k).trans ?_
  have : q ^ (n - min (cnt v k) n) ≤ 1 := pow_le_one₀ hq0 hqle
  have h1q : 1 - q = η * (2 - η) := by simp only [q]; ring
  rw [div_le_iff₀ hq1, h1q]
  nlinarith

/-- One-sided unrolling: if `e_{k+1} = (1-η) e_k + η (γ g_k + d_k - R)` at visits and
`e_{k+1} = e_k` otherwise, with `g_k ≤ B`, then
`e_k ≤ (1-η)^{cnt k} e₀ + (1 - (1-η)^{cnt k})(γ B - R) + ξ_k`. -/
theorem unroll_le {η γ B R : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hγ : 0 ≤ γ) (e g d : ℕ → ℝ) (K : ℕ)
    (hstep : ∀ k < K, e (k + 1) = if v k then (1 - η) * e k + η * (γ * g k + d k - R) else e k)
    (hg : ∀ k < K, v k → g k ≤ B) :
    e K ≤ (1 - η) ^ cnt v K * e 0 + (1 - (1 - η) ^ cnt v K) * (γ * B - R) + accum v η d K := by
  induction K with
  | zero => simp [cnt_zero, accum]
  | succ K ih =>
    have ih' := ih (fun k hk ↦ hstep k (by omega)) (fun k hk ↦ hg k (by omega))
    rw [hstep K (by omega), cnt_succ, accum]
    by_cases hv : v K
    · simp only [hv, if_true, pow_succ]
      have := hg K (by omega) hv
      have h1 : 0 ≤ 1 - η := by linarith
      have := mul_le_mul_of_nonneg_left ih' h1
      have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hg K (by omega) hv) hγ) hη0
      nlinarith
    · simp only [hv, if_false, add_zero]; exact ih'

end StatisticalRL.AsyncQ
