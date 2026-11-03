import Formalization.Generative.PolicyEvaluationSampleAssembly

/-! Combinatorial geometry of the source multi-hypothesis hard family. -/
namespace StatisticalRL.GenerativeLowerBound

/-- Baseline or one altered active-state/nondefault-action pair. -/
abbrev HardFamilyIndex (m n : ℕ) := Option (Fin m × Fin n)

/-- Baseline chooses zero everywhere; an alternative changes one coordinate. -/
def hardPolicySignature {m n : ℕ} (i : HardFamilyIndex m n) : Fin m → Fin (n + 1) :=
  fun s ↦ match i with
    | none => 0
    | some (j, k) => if s = j then k.succ else 0

/-- The parameterization has the exact source family cardinality. -/
theorem hardFamilyIndex_card (m n : ℕ) :
    Fintype.card (HardFamilyIndex m n) = 1 + m * n := by
  simp [HardFamilyIndex, Nat.add_comm]

/-- Different model indices give different active-state action signatures. -/
theorem hardPolicySignature_injective (m n : ℕ) :
    Function.Injective (@hardPolicySignature m n) := by
  intro i j h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some jk =>
      rcases jk with ⟨j, k⟩
      have h' := congrFun h j
      simp [hardPolicySignature] at h'
      exact False.elim (Fin.succ_ne_zero k h'.symm)
  | some ik =>
    rcases ik with ⟨i, k⟩
    cases j with
    | none =>
      have h' := congrFun h i
      simp [hardPolicySignature] at h'
    | some jl =>
      rcases jl with ⟨j, l⟩
      have hij : i = j := by
        by_contra hn
        have h' := congrFun h i
        simp [hardPolicySignature, hn] at h'
      subst j
      have h' := congrFun h i
      simp [hardPolicySignature] at h'
      exact congrArg some (Prod.ext rfl h')

/-- Decode an arbitrary policy; default to the baseline when it is outside
the finite hard family. -/
noncomputable def decodeHardPolicy {m n : ℕ} (π : Fin m → Fin (n + 1)) : HardFamilyIndex m n :=
  if h : ∃ i, hardPolicySignature i = π then Classical.choose h else none

/-- Decoding every hard-family signature returns exactly its model index. -/
theorem decodeHardPolicy_signature (m n : ℕ) (i : HardFamilyIndex m n) :
    decodeHardPolicy (hardPolicySignature i) = i := by
  unfold decodeHardPolicy
  split
  · rename_i h
    apply hardPolicySignature_injective m n
    exact Classical.choose_spec h
  · rename_i h
    exact False.elim (h ⟨i, rfl⟩)

/-- A decoder error implies the output policy differs from the true indexed
signature, including outputs outside the hard family. -/
theorem decodeHardPolicy_error_ne_signature (m n : ℕ) (π : Fin m → Fin (n + 1))
    (i : HardFamilyIndex m n) (h : decodeHardPolicy π ≠ i) :
    π ≠ hardPolicySignature i := by
  intro heq
  apply h
  rw [heq, decodeHardPolicy_signature]

/-- The source family size is at least SA/4 under the corrected nondegenerate
state/action conditions. -/
theorem hardFamilyIndex_card_lower (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) :
    (m + 1) * (n + 1) ≤ 4 * Fintype.card (HardFamilyIndex m n) := by
  rw [hardFamilyIndex_card]
  have h₁ : m ≤ m * n := by nlinarith [Nat.mul_le_mul_left m hn]
  have h₂ : n ≤ m * n := by nlinarith [Nat.mul_le_mul_right n hm]
  nlinarith

/-- In the source SA≥16 regime the corrected family has at least four models. -/
theorem hardFamilyIndex_card_ge_four (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hsize : 16 ≤ (m + 1) * (n + 1)) :
    4 ≤ Fintype.card (HardFamilyIndex m n) := by
  have h := hardFamilyIndex_card_lower m n hm hn
  omega

end StatisticalRL.GenerativeLowerBound
