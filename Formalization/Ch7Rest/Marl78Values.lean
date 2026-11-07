import Formalization.Ch7Rest.Marl78Defs
import Mathlib.Algebra.Order.Ring.Pow

/-!
# Corrected Theorem 7.8: general value facts and the scalar chain recursion

* `deviate_sum`, `deviate_sum_coord`: expectations under the deviation `π'_i × π_{-i}`.
* `valueJ_le`, `gapJ_ge`: values are at most `k` when rewards are at most `1`; the gap dominates
  any single deviation gain at any state.
* `chainU`: the scalar recursion `u_h = 1 + (1 − ℓ_h) u_{h+1}` of a chain state (reward `1` per step,
  exit probability `ℓ_h` to an absorbing zero-reward sink), with the lower bounds used in the proof.
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl

open StatisticalRL

variable {m S H : ℕ} {A : Fin m → ℕ}

theorem deviate_sum (π : JointPolicy m S A) (i : Fin m) (π' : PlayerPolicy S (A i)) (h : ℕ)
    (s : Fin S) (g : ((j : Fin m) → Fin (A j)) → ℝ) :
    ∑ a, (deviate π i π' h s).prob a * g a =
      ∑ a', ∑ b, (π h s).prob a' * (π' h s).prob b * g (Function.update a' i b) := by
  simp only [deviate]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp_rw [mul_assoc, ← Finset.mul_sum]
  congr 1
  congr 1
  simp_rw [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Under `π'_i × π_{-i}` the action of player `i` has law `π'_i`. -/
theorem deviate_sum_coord (π : JointPolicy m S A) (i : Fin m) (π' : PlayerPolicy S (A i)) (h : ℕ)
    (s : Fin S) (f : Fin (A i) → ℝ) :
    ∑ a, (deviate π i π' h s).prob a * f (a i) = ∑ b, (π' h s).prob b * f b := by
  rw [deviate_sum]
  simp only [Function.update_self]
  simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, (π h s).sum_prob, one_mul]

theorem expectation_le_const {Ω : Type*} [Fintype Ω] (d : FiniteDistribution Ω) (f : Ω → ℝ)
    (c : ℝ) (hf : ∀ x, f x ≤ c) : d.expectation f ≤ c := by
  unfold FiniteDistribution.expectation
  calc ∑ x, d.prob x * f x ≤ ∑ x, d.prob x * c :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hf x) (d.prob_nonneg x)
    _ = c := by rw [← Finset.sum_mul, d.sum_prob, one_mul]

theorem valueJ_le (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m)
    (hR : ∀ h s a, G.reward i h s a ≤ 1) : ∀ k h s, valueJ G π i h k s ≤ k := by
  intro k
  induction k with
  | zero => intro h s; simp [valueJ]
  | succ k ih =>
    intro h s
    simp only [valueJ]
    calc ∑ a, (π h s).prob a * (G.reward i h s a + (G.transition h s a).expectation
          (valueJ G π i (h + 1) k)) ≤ ∑ a, (π h s).prob a * (1 + (k : ℝ)) :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
            (add_le_add (hR h s a) (expectation_le_const _ _ _ fun x => ih (h + 1) x))
            ((π h s).prob_nonneg a)
      _ = ((k + 1 : ℕ) : ℝ) := by rw [← Finset.sum_mul, (π h s).sum_prob]; push_cast; ring

/-- The gap dominates the gain of any single Markov deviation of any player at any state. -/
theorem gapJ_ge (G : MarkovGame m S H A) (π : JointPolicy m S A) (i : Fin m)
    (hR : ∀ h s a, G.reward i h s a ≤ 1) (π' : PlayerPolicy S (A i)) (s : Fin S) :
    valueJ G (deviate π i π') i 1 H s - valueJ G π i 1 H s ≤ gapJ G π := by
  have hbr : valueJ G (deviate π i π') i 1 H s ≤ bestResponseValueJ G π i s := by
    refine le_ciSup (f := fun π' : PlayerPolicy S (A i) => valueJ G (deviate π i π') i 1 H s)
      ⟨(H : ℝ), ?_⟩ π'
    rintro _ ⟨π'', rfl⟩
    exact valueJ_le G _ i hR H 1 s
  have h1 : bestResponseValueJ G π i s - valueJ G π i 1 H s ≤
      ⨆ j : Fin m, (bestResponseValueJ G π j s - valueJ G π j 1 H s) :=
    le_ciSup (f := fun j : Fin m => bestResponseValueJ G π j s - valueJ G π j 1 H s)
      (Set.finite_range _).bddAbove i
  have h2 : (⨆ j : Fin m, (bestResponseValueJ G π j s - valueJ G π j 1 H s)) ≤ gapJ G π :=
    le_ciSup (f := fun s : Fin S => ⨆ j : Fin m, (bestResponseValueJ G π j s - valueJ G π j 1 H s))
      (Set.finite_range _).bddAbove s
  linarith

/-! ### The scalar chain recursion -/

/-- `chainU ℓ h k`: value over `k` steps from step `h` of a chain state with reward `1` per step
and exit probability `ℓ_h` to an absorbing zero-reward sink. -/
noncomputable def chainU (ℓ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | _, 0 => 0
  | h, k + 1 => 1 + (1 - ℓ h) * chainU ℓ (h + 1) k

theorem chainU_zero (ℓ : ℕ → ℝ) (h : ℕ) : chainU ℓ h 0 = 0 := rfl

theorem chainU_succ (ℓ : ℕ → ℝ) (h k : ℕ) :
    chainU ℓ h (k + 1) = 1 + (1 - ℓ h) * chainU ℓ (h + 1) k := rfl

theorem chainU_nonneg (ℓ : ℕ → ℝ) (hℓ : ∀ h, ℓ h ≤ 1) : ∀ k h, 0 ≤ chainU ℓ h k := by
  intro k
  induction k with
  | zero => intro h; simp [chainU_zero]
  | succ k ih =>
    intro h
    rw [chainU_succ]
    have := ih (h + 1)
    have := hℓ h
    nlinarith

/-- `u_h(k) ≥ k − k² x / 2` when every exit probability is at most `x ∈ [0, 1]`. -/
theorem chainU_ge (ℓ : ℕ → ℝ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hℓ : ∀ h, ℓ h ≤ x) :
    ∀ (k : ℕ) (h : ℕ), (k : ℝ) - (k : ℝ) ^ 2 * x / 2 ≤ chainU ℓ h k := by
  have hℓ1 : ∀ h, ℓ h ≤ 1 := fun h => (hℓ h).trans hx1
  intro k
  induction k with
  | zero => intro h; simp [chainU_zero]
  | succ k ih =>
    intro h
    rw [chainU_succ]
    have hu := chainU_nonneg ℓ hℓ1 k (h + 1)
    have hk := ih (h + 1)
    have h1 : (1 - x) * chainU ℓ (h + 1) k ≤ (1 - ℓ h) * chainU ℓ (h + 1) k :=
      mul_le_mul_of_nonneg_right (by linarith [hℓ h]) hu
    have h2 : (1 - x) * ((k : ℝ) - (k : ℝ) ^ 2 * x / 2) ≤ (1 - x) * chainU ℓ (h + 1) k :=
      mul_le_mul_of_nonneg_left hk (by linarith)
    push_cast
    nlinarith [sq_nonneg ((k : ℝ) * x)]

/-- **Chain difference.** If `ℓ⋆_h ≤ ℓ_h ≤ x ≤ 1` for every `h`, then
`u⋆_h(k) − u_h(k) ≥ ∑_{j<k} (1 − x)^j (ℓ_{h+j} − ℓ⋆_{h+j}) u⋆_{h+j+1}(k − j − 1)`. -/
theorem chainU_diff (ℓ ℓs : ℕ → ℝ) (x : ℝ) (hx1 : x ≤ 1) (hle : ∀ h, ℓs h ≤ ℓ h)
    (hℓ : ∀ h, ℓ h ≤ x) :
    ∀ k h, ∑ j ∈ Finset.range k, (1 - x) ^ j * (ℓ (h + j) - ℓs (h + j)) *
        chainU ℓs (h + j + 1) (k - j - 1) ≤ chainU ℓs h k - chainU ℓ h k := by
  have hℓs1 : ∀ h, ℓs h ≤ 1 := fun h => ((hle h).trans (hℓ h)).trans hx1
  have hterm : ∀ h j n, 0 ≤ (1 - x) ^ j * (ℓ (h + j) - ℓs (h + j)) * chainU ℓs (h + j + 1) n :=
    fun h j n => mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _)
      (by linarith [hle (h + j)])) (chainU_nonneg ℓs hℓs1 _ _)
  intro k
  induction k with
  | zero => intro h; simp [chainU_zero]
  | succ k ih =>
    intro h
    rw [Finset.sum_range_succ', chainU_succ, chainU_succ]
    have hR := ih (h + 1)
    set R := ∑ j ∈ Finset.range k, (1 - x) ^ j * (ℓ (h + 1 + j) - ℓs (h + 1 + j)) *
        chainU ℓs (h + 1 + j + 1) (k - j - 1) with hRdef
    have hR0 : 0 ≤ R := Finset.sum_nonneg fun j _ => hterm (h + 1) j _
    have hshift : ∑ j ∈ Finset.range k, (1 - x) ^ (j + 1) * (ℓ (h + (j + 1)) - ℓs (h + (j + 1))) *
        chainU ℓs (h + (j + 1) + 1) (k + 1 - (j + 1) - 1) = (1 - x) * R := by
      rw [hRdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e1 : h + (j + 1) = h + 1 + j := by omega
      have e2 : k + 1 - (j + 1) - 1 = k - j - 1 := by omega
      rw [e1, e2, pow_succ]
      ring
    rw [hshift]
    simp only [add_zero, pow_zero, one_mul, Nat.add_sub_cancel, Nat.sub_zero]
    have hdiff : (1 - x) * R ≤ (1 - ℓ h) * (chainU ℓs (h + 1) k - chainU ℓ (h + 1) k) :=
      mul_le_mul (by linarith [hℓ h]) hR hR0 (by linarith [hℓ h])
    nlinarith

/-- **Chain gap over the first half.** For `H ≥ 2`, if `ℓ⋆_h ≤ ℓ_h ≤ 1/H` for every `h`, then
`u⋆_1(H) − u_1(H) ≥ ∑_{j < ⌊H/2⌋} (H/8) (ℓ_{1+j} − ℓ⋆_{1+j})`. -/
theorem chainU_gap_half (H : ℕ) (hH : 2 ≤ H) (ℓ ℓs : ℕ → ℝ)
    (hle : ∀ h, ℓs h ≤ ℓ h) (hℓ : ∀ h, ℓ h ≤ 1 / (H : ℝ)) :
    ∑ j ∈ Finset.range (H / 2), (H : ℝ) / 8 * (ℓ (1 + j) - ℓs (1 + j)) ≤
      chainU ℓs 1 H - chainU ℓ 1 H := by
  have hH' : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hHpos : (0 : ℝ) < H := by linarith
  set x : ℝ := 1 / (H : ℝ) with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [hxdef, div_le_one hHpos]; linarith
  have hℓs1 : ∀ h, ℓs h ≤ 1 := fun h => ((hle h).trans (hℓ h)).trans hx1
  have hmain := chainU_diff ℓ ℓs x hx1 hle hℓ H 1
  refine le_trans ?_ hmain
  have hsub : Finset.range (H / 2) ⊆ Finset.range H :=
    Finset.range_subset_range.mpr (Nat.div_le_self H 2)
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ =>
    mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (by linarith [hle (1 + j)]))
      (chainU_nonneg ℓs hℓs1 _ _))
  refine Finset.sum_le_sum fun j hj => ?_
  rw [Finset.mem_range] at hj
  have hj2 : 2 * (j + 1) ≤ H := by omega
  have hj2' : 2 * ((j : ℝ) + 1) ≤ H := by exact_mod_cast hj2
  have hδ : 0 ≤ ℓ (1 + j) - ℓs (1 + j) := by linarith [hle (1 + j)]
  -- survival weight
  have hpow : (1 : ℝ) / 2 ≤ (1 - x) ^ j := by
    have hb := one_add_mul_sub_le_pow (a := 1 - x) (by linarith) j
    have : (j : ℝ) * x ≤ 1 / 2 := by
      rw [hxdef, mul_one_div, div_le_iff₀ hHpos]; linarith
    linarith
  -- continuation value
  have hcast : ((H - j - 1 : ℕ) : ℝ) = (H : ℝ) - j - 1 := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
  have hu := chainU_ge ℓs x hx0 hx1 (fun h => (hle h).trans (hℓ h)) (H - j - 1) (1 + j + 1)
  rw [hcast] at hu
  have hk1 : (H : ℝ) / 2 ≤ (H : ℝ) - j - 1 := by linarith
  have hk2 : (H : ℝ) - j - 1 ≤ H := by linarith
  have hval : (H : ℝ) / 4 ≤ chainU ℓs (1 + j + 1) (H - j - 1) := by
    refine le_trans ?_ hu
    set k : ℝ := (H : ℝ) - j - 1
    have hkx : k ^ 2 * x / 2 = k * (k / H) / 2 := by rw [hxdef]; field_simp
    rw [hkx]
    have hkH : k / H ≤ 1 := by rw [div_le_one hHpos]; exact hk2
    have hk0 : 0 ≤ k := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hkH hk0]
  calc (H : ℝ) / 8 * (ℓ (1 + j) - ℓs (1 + j))
      = (1 / 2) * (ℓ (1 + j) - ℓs (1 + j)) * ((H : ℝ) / 4) := by ring
    _ ≤ (1 - x) ^ j * (ℓ (1 + j) - ℓs (1 + j)) * chainU ℓs (1 + j + 1) (H - j - 1) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right hpow hδ) hval (by positivity)
        exact mul_nonneg (pow_nonneg (by linarith) _) hδ

end StatisticalRL.Ch7Rest.Marl
