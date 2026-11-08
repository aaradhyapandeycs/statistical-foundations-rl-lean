import Formalization.Ch7Rest.Marl77Core

/-!
# Theorem 7.7: from a CCE to a Nash equilibrium in two-player zero-sum games

* `valueJ_shift`, `bestResponseValueJ_shift`, `gapJ_shift`: adding a constant to one player's reward
  does not change the gap.
* `margDist μ j`: the marginal of player `j`; `margProd π`: the product of the marginals of `π`.
* `gap_margProd_le`: for two players whose rewards sum to `0` on steps `1..H`,
  `gap(⊗_i π̂_i) ≤ 2·gapJ(π̂)` (`marl.tex:332–346`; the deviation `π'_i × π_{-i}` only sees the
  other player's marginal).
-/

open scoped BigOperators
open Finset

namespace StatisticalRL.Ch7Rest.Marl77

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.Ch7Rest.Marl76

variable {m S H : ℕ} {A : Fin m → ℕ}

/-! ### Reward shifts -/

theorem valueJ_shift (G G' : MarkovGame m S H A) (hP : G'.transition = G.transition) (i : Fin m)
    (c : ℝ) (hr : ∀ h s a, G'.reward i h s a = G.reward i h s a + c) (ρ : JointPolicy m S A) :
    ∀ k h s, valueJ G' ρ i h k s = valueJ G ρ i h k s + c * k := by
  intro k
  induction k with
  | zero => intro h s; simp [valueJ]
  | succ k ih =>
    intro h s
    simp only [valueJ, hP, hr]
    have : valueJ G' ρ i (h + 1) k = fun s' => valueJ G ρ i (h + 1) k s' + c * k :=
      funext fun s' => ih _ _
    rw [this]
    have e : ∀ a, (ρ h s).prob a * (G.reward i h s a + c + (G.transition h s a).expectation
        (fun s' => valueJ G ρ i (h + 1) k s' + c * k)) =
        (ρ h s).prob a * (G.reward i h s a + (G.transition h s a).expectation
          (valueJ G ρ i (h + 1) k)) + c * (k + 1) * (ρ h s).prob a := by
      intro a
      rw [FiniteDistribution.expectation_add, FiniteDistribution.expectation_const]; ring
    simp_rw [e]
    rw [sum_add_distrib, ← mul_sum, (ρ h s).sum_prob]
    push_cast; ring

theorem bestResponseValueJ_shift (G G' : MarkovGame m S H A) (hP : G'.transition = G.transition)
    (i : Fin m) (hAi : 0 < A i) (c : ℝ) (hr : ∀ h s a, G'.reward i h s a = G.reward i h s a + c)
    (π : JointPolicy m S A) (s : Fin S) :
    bestResponseValueJ G' π i s = bestResponseValueJ G π i s + c * H := by
  apply le_antisymm
  · rw [bestResponseValueJ_eq_brPolicy G' π i hAi s, valueJ_shift G G' hP i c hr]
    linarith [valueJ_deviate_le_bestResponseValueJ G π i (brPolicy G' π i hAi) s]
  · rw [bestResponseValueJ_eq_brPolicy G π i hAi s, ← valueJ_shift G G' hP i c hr]
    exact valueJ_deviate_le_bestResponseValueJ G' π i _ s

theorem gapJ_shift (G G' : MarkovGame m S H A) (hP : G'.transition = G.transition)
    (hA : ∀ i, 0 < A i) (c : Fin m → ℝ) (hr : ∀ i h s a, G'.reward i h s a = G.reward i h s a + c i)
    (π : JointPolicy m S A) : gapJ G' π = gapJ G π := by
  unfold gapJ
  refine iSup_congr fun s => iSup_congr fun i => ?_
  rw [bestResponseValueJ_shift G G' hP i (hA i) (c i) (hr i) π s,
    valueJ_shift G G' hP i (c i) (hr i) π H 1 s]
  ring

/-! ### Marginals -/

/-- The marginal law of player `j`'s action. -/
noncomputable def margDist (μ : FiniteDistribution (JointAction m A)) (j : Fin m) :
    FiniteDistribution (Fin (A j)) where
  prob c := ∑ a, μ.prob a * (if a j = c then 1 else 0)
  prob_nonneg c := sum_nonneg fun a _ => mul_nonneg (μ.prob_nonneg a) (by split_ifs <;> norm_num)
  sum_prob := by
    rw [sum_comm]
    simp_rw [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, if_true]
    exact μ.sum_prob

theorem margDist_sum (μ : FiniteDistribution (JointAction m A)) (j : Fin m) (F : Fin (A j) → ℝ) :
    ∑ c, (margDist μ j).prob c * F c = ∑ a, μ.prob a * F (a j) := by
  simp only [margDist]
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_eq_single (a j)]
  · simp
  · intro c _ hc; simp [Ne.symm hc]
  · simp

/-- The product of the marginals of a joint policy. -/
noncomputable def margProd (π : JointPolicy m S A) : ProductPolicy m S A :=
  fun j h s => margDist (π h s) j

/-- A function depending on the joint action only through coordinate `j` has the same expectation
under two laws with the same `j`-marginal. -/
theorem sum_eq_of_marg (μ ν : FiniteDistribution (JointAction m A)) (j : Fin m)
    (hμν : ∀ c, (margDist μ j).prob c = (margDist ν j).prob c) (F : JointAction m A → ℝ)
    (a₀ : JointAction m A) (hF : ∀ a, F a = F (Function.update a₀ j (a j))) :
    ∑ a, μ.prob a * F a = ∑ a, ν.prob a * F a := by
  rw [show (∑ a, μ.prob a * F a) = ∑ a, μ.prob a * F (Function.update a₀ j (a j)) from
      sum_congr rfl fun a _ => congrArg _ (hF a),
    show (∑ a, ν.prob a * F a) = ∑ a, ν.prob a * F (Function.update a₀ j (a j)) from
      sum_congr rfl fun a _ => congrArg _ (hF a)]
  rw [← margDist_sum μ j (fun c => F (Function.update a₀ j c)),
    ← margDist_sum ν j (fun c => F (Function.update a₀ j c))]
  simp_rw [hμν]

theorem margDist_toJoint (σ : ProductPolicy m S A) (h : ℕ) (s : Fin S) (j : Fin m) (c : Fin (A j)) :
    (margDist (toJoint σ h s) j).prob c = (σ j h s).prob c := by
  have hsplit := jointProb_sum_split σ h s j (fun a => if a j = c then (1 : ℝ) else 0)
  have hone := jointProb_sum_split σ h s j (fun _ => (1 : ℝ))
  simp only [mul_one] at hone
  rw [show ∑ a, jointProb σ h s a = 1 from (toJoint σ h s).sum_prob, (σ j h s).sum_prob] at hone
  simp only [mul_one] at hone
  have hj : ∀ (c' : Fin (A j)) (r : (k : {k : Fin m // k ≠ j}) → Fin (A k)),
      (Equiv.piSplitAt j (fun k => Fin (A k))).symm (c', r) j = c' := by
    intro c' r; simp [Equiv.piSplitAt]
  simp_rw [hj, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true] at hsplit
  simp only [margDist]
  rw [show ∑ a, (toJoint σ h s).prob a * (if a j = c then (1 : ℝ) else 0) =
    ∑ a, jointProb σ h s a * (if a j = c then (1 : ℝ) else 0) from rfl]
  simp only [mul_ite, mul_one, mul_zero]
  rw [hsplit, ← sum_mul, ← hone, one_mul]

/-! ### Two players -/

theorem fin2_other (i : Fin 2) : ∀ k : Fin 2, k ≠ i → k = (if i = 0 then 1 else 0) := by
  intro k hk
  fin_cases i <;> fin_cases k <;> simp_all

/-- For two players, the deviation `π'_i × π_{-i}` only depends on the other player's marginal. -/
theorem deviate_sum_two {S : ℕ} {A : Fin 2 → ℕ} (hA : ∀ k, 0 < A k) (π ν : JointPolicy 2 S A) (i : Fin 2)
    (π' : PlayerPolicy S (A i)) (h : ℕ) (s : Fin S)
    (hmarg : ∀ c, (margDist (π h s) (if i = 0 then 1 else 0)).prob c =
      (margDist (ν h s) (if i = 0 then 1 else 0)).prob c)
    (g : JointAction 2 A → ℝ) :
    ∑ a, (deviate π i π' h s).prob a * g a = ∑ a, (deviate ν i π' h s).prob a * g a := by
  rw [deviate_sum, deviate_sum]
  simp_rw [mul_assoc, ← mul_sum]
  let a₀ : JointAction 2 A := fun k => ⟨0, hA k⟩
  refine sum_eq_of_marg (π h s) (ν h s) _ hmarg
    (fun a' => ∑ b, (π' h s).prob b * g (Function.update a' i b)) a₀ fun a => ?_
  refine sum_congr rfl fun b _ => ?_
  congr 2
  funext k
  by_cases hk : k = i
  · subst hk; simp
  · rw [Function.update_of_ne hk, Function.update_of_ne hk]
    have := fin2_other i k hk
    subst this
    simp

end StatisticalRL.Ch7Rest.Marl77
