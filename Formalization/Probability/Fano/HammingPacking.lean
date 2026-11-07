import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.Powerset
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Gilbert–Varshamov packing of the Boolean hypercube

The offline minimax lower bound (`thm:infinite-lwoer-bound`, `chapters/offlineRL.tex:2520–2530`,
`eq:property-Theta`) uses a set `Θ ⊆ {0,1}^{S-1}` with `|Θ| ≥ e^{(S-1)/8}` and pairwise Hamming
distance at least `(S-1)/8`, citing Gilbert–Varshamov. This file proves that packing statement for
every `n`:

1. a maximal `d`-separated code exists, and its radius-`(d-1)` Hamming balls cover `{0,1}^n`;
2. a radius-`r` ball has at most `∑_{k ≤ r} C(n,k)` points;
3. `∑_{k ≤ r} C(n,k) ≤ 7^r (8/7)^n` for `r ≤ n`;
4. with `d = ⌊n/8⌋ + 1`, the code has at least `e^{n/8}` elements (compared through eighth powers).
-/

open scoped BigOperators
open Finset

namespace StatisticalRL.Packing

/-- A Hamming ball of radius `r` in `{0,1}^n` has at most `∑_{k ≤ r} C(n,k)` points. -/
theorem card_hammingBall_le (n r : ℕ) (c : Fin n → Bool) :
    (univ.filter fun x : Fin n → Bool => hammingDist x c ≤ r).card ≤
      ∑ k ∈ range (r + 1), n.choose k := by
  classical
  set B := univ.filter fun x : Fin n → Bool => hammingDist x c ≤ r
  set T := (range (r + 1)).biUnion fun k => powersetCard k (univ : Finset (Fin n))
  set f : (Fin n → Bool) → Finset (Fin n) := fun x => univ.filter fun i => x i ≠ c i
  have hmaps : Set.MapsTo f B T := by
    intro x hx
    have hx' : hammingDist x c ≤ r := (mem_filter.mp hx).2
    show f x ∈ T
    rw [mem_biUnion]
    exact ⟨hammingDist x c, mem_range.mpr (Nat.lt_succ_of_le hx'),
      mem_powersetCard.mpr ⟨subset_univ _, rfl⟩⟩
  have hinj : Set.InjOn f B := by
    intro x _ y _ hxy
    funext i
    have h := Finset.ext_iff.mp hxy i
    simp only [f, mem_filter, mem_univ, true_and] at h
    have key : ∀ a b e : Bool, (a ≠ e ↔ b ≠ e) → a = b := by decide
    exact key _ _ _ h
  calc B.card ≤ T.card := card_le_card_of_injOn f hmaps hinj
    _ ≤ ∑ k ∈ range (r + 1), (powersetCard k (univ : Finset (Fin n))).card := card_biUnion_le
    _ = ∑ k ∈ range (r + 1), n.choose k := by simp [card_powersetCard]

/-- `∑_{k ≤ r} C(n,k) ≤ 7^r (8/7)^n` for `r ≤ n`. -/
theorem sum_choose_le_seven_pow (n r : ℕ) (hr : r ≤ n) :
    ((∑ k ∈ range (r + 1), n.choose k : ℕ) : ℝ) ≤ 7 ^ r * (8 / 7 : ℝ) ^ n := by
  push_cast
  have hterm : ∀ k ∈ range (r + 1),
      (n.choose k : ℝ) ≤ 7 ^ r * ((1 / 7 : ℝ) ^ k * (n.choose k : ℝ)) := by
    intro k hk
    have hk' : k ≤ r := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have h7 : (7 : ℝ) ^ k ≤ 7 ^ r := pow_le_pow_right₀ (by norm_num) hk'
    have hpos : (0 : ℝ) < 7 ^ k := by positivity
    have hq : (7 : ℝ) ^ r * ((1 / 7 : ℝ) ^ k * (n.choose k : ℝ)) =
        (7 ^ r / 7 ^ k) * (n.choose k : ℝ) := by
      rw [one_div, inv_pow]; ring
    rw [hq]
    have h1 : 1 ≤ (7 : ℝ) ^ r / 7 ^ k := by rw [le_div_iff₀ hpos]; simpa using h7
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) h1
  calc (∑ k ∈ range (r + 1), (n.choose k : ℝ))
      ≤ ∑ k ∈ range (r + 1), 7 ^ r * ((1 / 7 : ℝ) ^ k * (n.choose k : ℝ)) := sum_le_sum hterm
    _ = 7 ^ r * ∑ k ∈ range (r + 1), (1 / 7 : ℝ) ^ k * (n.choose k : ℝ) := by rw [mul_sum]
    _ ≤ 7 ^ r * ∑ k ∈ range (n + 1), (1 / 7 : ℝ) ^ k * (n.choose k : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by omega))
        intro k _ _
        positivity
    _ = 7 ^ r * (8 / 7 : ℝ) ^ n := by
        congr 1
        rw [show (8 / 7 : ℝ) = 1 / 7 + 1 by norm_num, add_pow]
        simp

/-- A maximal `d`-separated code in `{0,1}^n` (`d ≥ 1`): its size times the volume of a
radius-`(d-1)` ball is at least `2^n`. -/
theorem exists_separated_code (n d : ℕ) (hd : 1 ≤ d) :
    ∃ Θ : Finset (Fin n → Bool), (∀ θ ∈ Θ, ∀ θ' ∈ Θ, θ ≠ θ' → d ≤ hammingDist θ θ') ∧
      2 ^ n ≤ Θ.card * ∑ k ∈ range d, n.choose k := by
  classical
  let Sep : Finset (Fin n → Bool) → Prop :=
    fun Θ => ∀ θ ∈ Θ, ∀ θ' ∈ Θ, θ ≠ θ' → d ≤ hammingDist θ θ'
  let codes : Finset (Finset (Fin n → Bool)) := univ.filter Sep
  have hne : codes.Nonempty := ⟨∅, mem_filter.mpr ⟨mem_univ _, by simp [Sep]⟩⟩
  obtain ⟨Θ, hΘ, hmax⟩ := exists_max_image codes card hne
  have hsep : Sep Θ := (mem_filter.mp hΘ).2
  refine ⟨Θ, hsep, ?_⟩
  have hcover : ∀ x : Fin n → Bool, ∃ c ∈ Θ, hammingDist x c < d := by
    intro x
    by_contra h
    push_neg at h
    have hx : x ∉ Θ := by
      intro hx
      have := h x hx
      simp only [hammingDist_self, nonpos_iff_eq_zero] at this
      omega
    have hsep' : Sep (insert x Θ) := by
      intro θ hθ θ' hθ' hne
      rw [mem_insert] at hθ hθ'
      rcases hθ with hθ | hθ <;> rcases hθ' with hθ' | hθ'
      · exact absurd (hθ.trans hθ'.symm) hne
      · rw [hθ]; exact h θ' hθ'
      · rw [hθ', hammingDist_comm]; exact h θ hθ
      · exact hsep θ hθ θ' hθ' hne
    have := hmax (insert x Θ) (mem_filter.mpr ⟨mem_univ _, hsep'⟩)
    rw [card_insert_of_notMem hx] at this
    omega
  have hsub : (univ : Finset (Fin n → Bool)) ⊆
      Θ.biUnion (fun c => univ.filter fun x => hammingDist x c ≤ d - 1) := by
    intro x _
    obtain ⟨c, hc, hxc⟩ := hcover x
    exact mem_biUnion.mpr ⟨c, hc, mem_filter.mpr ⟨mem_univ _, by omega⟩⟩
  calc 2 ^ n = (univ : Finset (Fin n → Bool)).card := by simp
    _ ≤ (Θ.biUnion (fun c => univ.filter fun x => hammingDist x c ≤ d - 1)).card :=
        card_le_card hsub
    _ ≤ ∑ c ∈ Θ, (univ.filter fun x : Fin n → Bool => hammingDist x c ≤ d - 1).card :=
        card_biUnion_le
    _ ≤ ∑ _c ∈ Θ, ∑ k ∈ range (d - 1 + 1), n.choose k :=
        sum_le_sum fun c _ => card_hammingBall_le n (d - 1) c
    _ = Θ.card * ∑ k ∈ range d, n.choose k := by
        rw [sum_const, smul_eq_mul, Nat.sub_add_cancel hd]

/-- **Gilbert–Varshamov packing** (`eq:property-Theta`, `chapters/offlineRL.tex:2520–2530`):
for every `n` there is `Θ ⊆ {0,1}^n` with `|Θ| ≥ e^{n/8}` and pairwise Hamming distance at least
`n/8`. -/
theorem exists_gilbertVarshamov (n : ℕ) :
    ∃ Θ : Finset (Fin n → Bool), Real.exp ((n : ℝ) / 8) ≤ Θ.card ∧
      ∀ θ ∈ Θ, ∀ θ' ∈ Θ, θ ≠ θ' → (n : ℝ) / 8 ≤ hammingDist θ θ' := by
  set r := n / 8 with hrdef
  obtain ⟨Θ, hsep, hcount⟩ := exists_separated_code n (r + 1) (by omega)
  refine ⟨Θ, ?_, ?_⟩
  · have hr8 : 8 * r ≤ n := by omega
    have hrn : r ≤ n := by omega
    have hV := sum_choose_le_seven_pow n r hrn
    have hcountR : (2 : ℝ) ^ n ≤ (Θ.card : ℝ) * ((∑ k ∈ range (r + 1), n.choose k : ℕ) : ℝ) := by
      exact_mod_cast hcount
    have hK : (2 : ℝ) ^ n ≤ (Θ.card : ℝ) * (7 ^ r * (8 / 7 : ℝ) ^ n) :=
      hcountR.trans (mul_le_mul_of_nonneg_left hV (Nat.cast_nonneg _))
    have h87 : (0 : ℝ) < (8 / 7 : ℝ) ^ n := by positivity
    have hK' : (7 / 4 : ℝ) ^ n ≤ (Θ.card : ℝ) * 7 ^ r := by
      have h2 : (2 : ℝ) ^ n = (7 / 4 : ℝ) ^ n * (8 / 7 : ℝ) ^ n := by
        rw [← mul_pow]; norm_num
      rw [h2, show (Θ.card : ℝ) * (7 ^ r * (8 / 7 : ℝ) ^ n) =
        ((Θ.card : ℝ) * 7 ^ r) * (8 / 7 : ℝ) ^ n by ring] at hK
      exact le_of_mul_le_mul_right hK h87
    have hK8 : ((7 / 4 : ℝ) ^ n) ^ 8 ≤ ((Θ.card : ℝ) * 7 ^ r) ^ 8 :=
      pow_le_pow_left₀ (by positivity) hK' 8
    have h7 : ((7 : ℝ) ^ r) ^ 8 ≤ (7 : ℝ) ^ n := by
      rw [← pow_mul]; exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hlhs : ((7 / 4 : ℝ) ^ n) ^ 8 = ((7 / 4 : ℝ) ^ 8) ^ n := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    have h21 : (3 : ℝ) ^ n * 7 ^ n ≤ ((7 / 4 : ℝ) ^ 8) ^ n := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
    have h3 : (3 : ℝ) ^ n * 7 ^ n ≤ (Θ.card : ℝ) ^ 8 * 7 ^ n := by
      calc (3 : ℝ) ^ n * 7 ^ n ≤ ((7 / 4 : ℝ) ^ 8) ^ n := h21
        _ = ((7 / 4 : ℝ) ^ n) ^ 8 := hlhs.symm
        _ ≤ ((Θ.card : ℝ) * 7 ^ r) ^ 8 := hK8
        _ = (Θ.card : ℝ) ^ 8 * ((7 : ℝ) ^ r) ^ 8 := by rw [mul_pow]
        _ ≤ (Θ.card : ℝ) ^ 8 * 7 ^ n :=
          mul_le_mul_of_nonneg_left h7 (by positivity)
    have h3' : (3 : ℝ) ^ n ≤ (Θ.card : ℝ) ^ 8 :=
      le_of_mul_le_mul_right h3 (by positivity)
    have he : Real.exp 1 ^ n ≤ (3 : ℝ) ^ n := by
      have := Real.exp_one_lt_d9
      exact pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith) n
    have hexp : Real.exp ((n : ℝ) / 8) ^ 8 = Real.exp 1 ^ n := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    have h8 : Real.exp ((n : ℝ) / 8) ^ 8 ≤ (Θ.card : ℝ) ^ 8 := by
      rw [hexp]; exact he.trans h3'
    exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le (Nat.cast_nonneg _) (by norm_num)).mp h8
  · intro θ hθ θ' hθ' hne
    have hd := hsep θ hθ θ' hθ' hne
    have hn : n ≤ 8 * (r + 1) := by omega
    have hnR : (n : ℝ) ≤ 8 * ((r : ℝ) + 1) := by exact_mod_cast hn
    have hdR : ((r : ℝ) + 1) ≤ (hammingDist θ θ' : ℝ) := by exact_mod_cast hd
    linarith

end StatisticalRL.Packing
