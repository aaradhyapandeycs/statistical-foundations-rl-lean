import Formalization.Ch7Rest.Marl78Values

/-!
# Corrected Theorem 7.8: product policies as joint policies

`toJoint π` is the joint policy of a product policy `π = π₁ × ⋯ × π_m` (probability `jointProb`).
`gapJ_toJoint`: the joint-policy gap `gapJ` of `toJoint π` is the product-policy gap `gap` of
`MarlPrinted78.lean`, so the corrected statement (joint outputs) covers product outputs with the
same gap.
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl

open StatisticalRL

variable {m S H : ℕ} {A : Fin m → ℕ}

/-- A product policy viewed as a joint policy. -/
noncomputable def toJoint (π : ProductPolicy m S A) : JointPolicy m S A := fun h s =>
  { prob := fun a => jointProb π h s a
    prob_nonneg := fun a => Finset.prod_nonneg fun i _ => (π i h s).prob_nonneg (a i)
    sum_prob := by
      unfold jointProb
      have hp := Finset.prod_univ_sum (fun i : Fin m => (Finset.univ : Finset (Fin (A i))))
        (fun i b => (π i h s).prob b)
      rw [Fintype.piFinset_univ] at hp
      rw [← hp]
      simp [(π _ h s).sum_prob] }

/-- Values depend on the policy only through its expectations. -/
theorem valueJ_congr (G : MarkovGame m S H A) (π₁ π₂ : JointPolicy m S A) (i : Fin m)
    (hπ : ∀ h s (g : ((j : Fin m) → Fin (A j)) → ℝ),
      ∑ a, (π₁ h s).prob a * g a = ∑ a, (π₂ h s).prob a * g a) :
    ∀ k h s, valueJ G π₁ i h k s = valueJ G π₂ i h k s := by
  intro k
  induction k with
  | zero => intro h s; rfl
  | succ k ih =>
    intro h s
    simp only [valueJ]
    have : valueJ G π₁ i (h + 1) k = valueJ G π₂ i (h + 1) k :=
      funext fun s' => ih (h + 1) s'
    rw [this]
    exact hπ h s _

theorem valueJ_toJoint (G : MarkovGame m S H A) (π : ProductPolicy m S A) (i : Fin m) :
    ∀ k h s, valueJ G (toJoint π) i h k s = value G π i h k s := by
  intro k
  induction k with
  | zero => intro h s; rfl
  | succ k ih =>
    intro h s
    simp only [valueJ, value]
    have : valueJ G (toJoint π) i (h + 1) k = value G π i (h + 1) k :=
      funext fun s' => ih (h + 1) s'
    rw [this]
    rfl

/-- Splitting a product expectation at coordinate `i`. -/
theorem jointProb_sum_split (π : ProductPolicy m S A) (h : ℕ) (s : Fin S) (i : Fin m)
    (g : ((j : Fin m) → Fin (A j)) → ℝ) :
    ∑ a, jointProb π h s a * g a =
      ∑ r : (j : {j : Fin m // j ≠ i}) → Fin (A j), (∏ j : {j : Fin m // j ≠ i}, (π j h s).prob (r j)) *
        ∑ c, (π i h s).prob c * g ((Equiv.piSplitAt i (fun j => Fin (A j))).symm (c, r)) := by
  set e := Equiv.piSplitAt i (fun j => Fin (A j))
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold jointProb
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  have h1 : e.symm (c, r) i = c := by simp [e, Equiv.piSplitAt]
  have h2 : ∀ j : {j : Fin m // j ≠ i}, e.symm (c, r) j.1 = r j := by
    intro j; simp [e, Equiv.piSplitAt, j.2]
  rw [h1]
  simp only [h2]
  ring

theorem update_piSplitAt_symm (i : Fin m) (c b : Fin (A i))
    (r : (j : {j : Fin m // j ≠ i}) → Fin (A j)) :
    Function.update ((Equiv.piSplitAt i (fun j => Fin (A j))).symm (c, r)) i b =
      (Equiv.piSplitAt i (fun j => Fin (A j))).symm (b, r) := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [Equiv.piSplitAt]
  · rw [Function.update_of_ne hj]; simp [Equiv.piSplitAt, hj]

/-- For a product policy, the deviation `π'_i × π_{-i}` is the product policy with `π_i`
replaced by `π'_i`. -/
theorem deviate_toJoint_sum (π : ProductPolicy m S A) (i : Fin m) (π' : PlayerPolicy S (A i))
    (h : ℕ) (s : Fin S) (g : ((j : Fin m) → Fin (A j)) → ℝ) :
    ∑ a, (deviate (toJoint π) i π' h s).prob a * g a =
      ∑ a, (toJoint (Function.update π i π') h s).prob a * g a := by
  rw [deviate_sum]
  have hL : ∑ a', ∑ b, (toJoint π h s).prob a' * (π' h s).prob b * g (Function.update a' i b) =
      ∑ a', jointProb π h s a' * ∑ b, (π' h s).prob b * g (Function.update a' i b) := by
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [toJoint]
    ring
  rw [hL, jointProb_sum_split π h s i]
  change _ = ∑ a, jointProb (Function.update π i π') h s a * g a
  rw [jointProb_sum_split (Function.update π i π') h s i]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hQ : ∏ j : {j : Fin m // j ≠ i}, (Function.update π i π' j h s).prob (r j) =
      ∏ j : {j : Fin m // j ≠ i}, (π j h s).prob (r j) := by
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [Function.update_of_ne j.2]
  rw [hQ, Function.update_self]
  congr 1
  simp only [update_piSplitAt_symm]
  rw [← Finset.sum_mul, (π i h s).sum_prob, one_mul]

/-- The joint-policy gap of a product policy is the product-policy gap. -/
theorem gapJ_toJoint (G : MarkovGame m S H A) (π : ProductPolicy m S A) :
    gapJ G (toJoint π) = gap G π := by
  unfold gapJ gap
  refine iSup_congr fun s => iSup_congr fun i => ?_
  rw [valueJ_toJoint]
  congr 1
  unfold bestResponseValueJ bestResponseValue
  refine iSup_congr fun π' => ?_
  rw [valueJ_congr G _ _ i (deviate_toJoint_sum π i π') H 1 s, valueJ_toJoint]

end StatisticalRL.Ch7Rest.Marl
