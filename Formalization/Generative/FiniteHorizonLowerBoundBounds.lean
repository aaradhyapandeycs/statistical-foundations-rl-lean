import Formalization.Generative.FiniteHorizonLowerBoundFamily

/-!
# Information and loss bounds for the hard family

* `bhattacharyya_flip_ge`: the Bhattacharyya coefficient of the sampling laws of `σ` and its flip
  at step `h` is at least `1 − N ε₀² / H³`.
* `gap_ge_weighted_loss`: for any deterministic policy `f`, the stage-1 gap at state `0` is at least
  `∑_h w_h 1[decodeBit f h ≠ σ h]`, with `w_h = ε₀ (H − h − 1)/(16 H²)` (Lemma 5.20).
* `sum_weight_ge`: `∑_h w_h ≥ ε₀/64`.
-/

open MeasureTheory Finset
open scoped BigOperators

namespace StatisticalRL.FiniteHorizonLowerBound

open StatisticalRL OnlineLowerBound FiniteHorizonGenerative Assouad

variable {S A H : ℕ}
variable (hS : 2 ≤ S) (hA : 2 ≤ A) (hH : 2 ≤ H) {ε₀ : ℝ} (hε : 0 < ε₀) (hεH : ε₀ ≤ (H : ℝ) / 2)

include hS hA hH hε hεH in
/-- **Information bound.** Flipping one hidden bit keeps the Bhattacharyya coefficient of the
sampling laws above `1 − N ε₀² / H³`. -/
theorem bhattacharyya_flip_ge (N : ℕ) (σ : Fin H → Bool) (h : Fin H) :
    1 - (N : ℝ) * ε₀ ^ 2 / (H : ℝ) ^ 3 ≤
      ∑ x, Real.sqrt (samplingAtom (hardStages hS hA hH ε₀ hε hεH σ) N x *
        samplingAtom (hardStages hS hA hH ε₀ hε hεH (flipAt h σ)) N x) := by
  rw [sum_sqrt_samplingAtom]
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
  set u : ℝ := ε₀ / (H : ℝ) ^ 2 with hu
  have hu0 : 0 ≤ u := by positivity
  have huH : u * H ≤ 1 / 2 := by
    rw [hu, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  have hu4 : u ≤ 1 / 4 := by nlinarith
  set β : ℝ := 1 - u ^ 2 * ((H : ℝ) + 1) / 2 with hβ
  have hdef : u ^ 2 * ((H : ℝ) + 1) / 2 ≤ u ^ 2 * H := by nlinarith [sq_nonneg u]
  have hβ0 : 0 ≤ β := by
    have : u ^ 2 * H ≤ 1 / 8 := by nlinarith
    linarith
  have huH3 : u ^ 2 * H = ε₀ ^ 2 / (H : ℝ) ^ 3 := by rw [hu]; field_simp
  let row : Fin H × Fin S × Fin A := (h, ⟨0, by omega⟩, ⟨1, by omega⟩)
  -- Lower bound on every coordinate coefficient.
  have hcoord : ∀ i : SampleIndex (Fin S) (Fin A) H N,
      (if i.1 = row then β else 1) ≤ ∑ y, Real.sqrt
        (((hardStages hS hA hH ε₀ hε hεH σ i.1.1).transition i.1.2.1 i.1.2.2).prob y *
          ((hardStages hS hA hH ε₀ hε hεH (flipAt h σ) i.1.1).transition i.1.2.1
            i.1.2.2).prob y) := by
    rintro ⟨⟨h', s, a⟩, k⟩
    by_cases hi : (h', s, a) = row
    · rw [if_pos hi]
      simp only [row, Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl, rfl⟩ := hi
      exact flipped_row_ge hS hA hH hε hεH σ h'
    · rw [if_neg hi]
      have hne : ¬ (h' = h ∧ (s : ℕ) = 0 ∧ (a : ℕ) = 1) := by
        rintro ⟨rfl, hs, ha⟩
        exact hi (by simp [row, Fin.ext_iff, hs, ha])
      rw [← hardStages_prob_eq_of_ne hS hA hH hε hεH σ h h' s a hne, sum_sqrt_self]
  have hprod := Finset.prod_le_prod (s := Finset.univ)
    (fun i _ ↦ by split_ifs <;> linarith) (fun i _ ↦ hcoord i)
  have hpow : ∏ i : SampleIndex (Fin S) (Fin A) H N, (if i.1 = row then β else 1) = β ^ N := by
    rw [Fintype.prod_prod_type]
    calc (∏ x : Fin H × Fin S × Fin A, ∏ _k : Fin N, (if x = row then β else 1))
        = ∏ x : Fin H × Fin S × Fin A, (if x = row then β ^ N else 1) :=
          Finset.prod_congr rfl fun x _ ↦ by split_ifs <;> simp
      _ = β ^ N := by rw [Finset.prod_ite_eq']; simp
  rw [hpow] at hprod
  have hbern := one_add_mul_le_pow (a := β - 1) (by linarith) N
  rw [add_sub_cancel] at hbern
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hK : (N : ℝ) * ε₀ ^ 2 / (H : ℝ) ^ 3 = N * (u ^ 2 * H) := by rw [huH3]; ring
  have : (N : ℝ) * (β - 1) ≥ -((N : ℝ) * ε₀ ^ 2 / (H : ℝ) ^ 3) := by
    rw [hK, hβ]
    have := mul_le_mul_of_nonneg_left hdef hN0
    linarith
  linarith

/-- The loss weights `w_h = ε₀ (H − (h+1))/(16 H²)` of Lemma 5.20. -/
noncomputable def weight (H : ℕ) (ε₀ : ℝ) (h : Fin H) : ℝ :=
  ε₀ * ((H : ℝ) - ((h : ℕ) + 1)) / (16 * (H : ℝ) ^ 2)

omit hS hA hH hε hεH in
theorem weight_nonneg (hε : 0 < ε₀) (h : Fin H) : 0 ≤ weight H ε₀ h := by
  unfold weight
  have : ((h : ℕ) : ℝ) + 1 ≤ H := by exact_mod_cast h.isLt
  have : 0 ≤ (H : ℝ) - ((h : ℕ) + 1) := by linarith
  positivity

omit hS hA hH hε hεH in
theorem sum_range_succ_cast (n : ℕ) :
    ∑ i ∈ Finset.range n, ((i : ℝ) + 1) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

omit hS hA hε hεH in
include hH in
/-- The weights sum to at least `ε₀/64`. -/
theorem sum_weight_ge (hε : 0 < ε₀) : ε₀ / 64 ≤ ∑ h, weight H ε₀ h := by
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hsum : ∑ h : Fin H, weight H ε₀ h =
      ε₀ / (16 * (H : ℝ) ^ 2) * ((H : ℝ) * H - (H : ℝ) * ((H : ℝ) + 1) / 2) := by
    unfold weight
    rw [← Finset.sum_div, ← Finset.mul_sum,
      Fin.sum_univ_eq_sum_range (fun i ↦ (H : ℝ) - ((i : ℝ) + 1)) H, Finset.sum_sub_distrib,
      sum_range_succ_cast]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  rw [hsum]
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith [mul_pos hε hHpos]

omit hS hH hε hεH in
include hA in
/-- Decoded bit: whether the policy plays action `1` at state `0` at step `h`. -/
def decodeBit (f : ℕ → Fin S → Fin A) (hS0 : 0 < S) (h : Fin H) : Bool :=
  decide (f h ⟨0, hS0⟩ = ⟨1, by omega⟩)

omit hS hA hH hε hεH in
theorem pointMass_prob {α : Type*} [Fintype α] [DecidableEq α] (a b : α) :
    (EnvironmentStage.pointMass a).prob b = if b = a then 1 else 0 := by
  by_cases hb : b = a <;> simp [EnvironmentStage.pointMass, hb]

include hS hA hH hε hεH in
/-- **Loss bound** (Lemma 5.20 specialized to deterministic policies). -/
theorem gap_ge_weighted_loss (σ : Fin H → Bool) (f : ℕ → Fin S → Fin A) :
    ∑ h, weight H ε₀ h * (if decodeBit hA f (by omega) h ≠ σ h then 1 else 0) ≤
      EnvironmentStage.optimalValue (List.ofFn (hardStages hS hA hH ε₀ hε hεH σ)) ⟨0, by omega⟩ -
        policyTrajectorySuffix (List.ofFn (hardStages hS hA hH ε₀ hε hεH σ)) f 0
          ⟨0, by omega⟩ := by
  have hgap := onlineLBStages_value_gap S H A hS hH ε₀ hε hεH (hiddenAction hA σ)
    (deterministicPolicy f) ⟨0, by omega⟩
  refine le_trans ?_ hgap
  refine Finset.sum_le_sum fun h _ ↦ ?_
  refine mul_le_mul_of_nonneg_left ?_ (weight_nonneg hε h)
  simp only [deterministicPolicy, pointMass_prob]
  unfold decodeBit hiddenAction
  cases hσ : σ h
  · by_cases hf : f h ⟨0, by omega⟩ = ⟨1, by omega⟩
    · simp [hf, Fin.ext_iff]
    · simp [hf]
      split_ifs <;> norm_num
  · by_cases hf : f h ⟨0, by omega⟩ = ⟨1, by omega⟩
    · simp [hf]
    · have hf' : ¬ (⟨1, by omega⟩ : Fin A) = f h ⟨0, by omega⟩ := fun e ↦ hf e.symm
      simp [hf, hf']

end StatisticalRL.FiniteHorizonLowerBound
