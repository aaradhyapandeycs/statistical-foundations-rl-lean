import Formalization.Ch7Rest.MarlPrinted78

/-!
# Printed Theorem 7.8 is false when every `A_i = 1` (SOURCE-ISSUES C40)

`marl.tex:487–503` places no range on `A_i`. If every player has a single
action, every player has a single Markov policy, so the best-response value of
player `i` equals its value and the gap (`marl.tex:332–340`) is `0` for every
game and every policy. Hence `P_θ(gap > ε) = 0 < 1/4` for every estimator, at
sample size `N = 0`, which the printed bound admits for every `c₂ > 0`.

The witness is `m = 2`, `S = H = 1`, `A ≡ 1`, `ε = c₁`, `N = 0`, for every pair of
constants `c₁, c₂ > 0` and every admissibility predicate (in particular every
reading of "`m`-player zero-sum").

Scope: degenerate-domain refutation. It shows only that the printed domain
admits `A_i = 1` for all `i` (a hypothesis such as `max_i A_i ≥ 2` is missing);
it says nothing about the lower bound itself. The named zero-sum readings below
are refuted through the same `A ≡ 1` route; the `S = 1` / `H = 1` known-reward
degeneracies and the vanishing-rewards reading are not formalized here.
-/

open MeasureTheory

namespace StatisticalRL.Ch7Rest.Marl

instance finiteDistribution_fin_one_subsingleton :
    Subsingleton (FiniteDistribution (Fin 1)) := by
  constructor
  rintro ⟨p, hp, hsp⟩ ⟨q, hq, hsq⟩
  have hp0 : p 0 = 1 := by simpa using hsp
  have hq0 : q 0 = 1 := by simpa using hsq
  have : p = q := by
    funext x
    rw [Fin.fin_one_eq_zero x, hp0, hq0]
  subst this
  rfl

section SingleAction

variable {m S H : ℕ}

/-- With one action per player, the best-response value equals the value. -/
theorem bestResponseValue_eq_value_of_single (G : MarkovGame m S H fun _ ↦ 1)
    (π : ProductPolicy m S fun _ ↦ 1) (i : Fin m) (s : Fin S) :
    bestResponseValue G π i s = value G π i 1 H s := by
  unfold bestResponseValue
  have h : ∀ π' : PlayerPolicy S 1, Function.update π i π' = π := by
    intro π'
    rw [Subsingleton.elim π' (π i), Function.update_eq_self]
  simp_rw [h]
  haveI : Nonempty (PlayerPolicy S 1) := ⟨π i⟩
  exact ciSup_const

/-- With one action per player, the gap of every policy in every game is `0`. -/
theorem gap_eq_zero_of_single (G : MarkovGame m S H fun _ ↦ 1)
    (π : ProductPolicy m S fun _ ↦ 1) : gap G π = 0 := by
  unfold gap
  simp_rw [bestResponseValue_eq_value_of_single, sub_self]
  simp only [Real.iSup_const_zero]

end SingleAction

/-- **C40.** For every admissibility predicate and every pair of constants
`c₁, c₂ > 0`, the core of printed Theorem 7.8 fails at `m = 2`, `S = H = 1`,
`A ≡ 1` (witness `ε = c₁`, `N = 0`). -/
theorem not_thm7_8_core_single
    (Adm : (m S H : ℕ) → (A : Fin m → ℕ) → MarkovGame m S H A → Prop)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) :
    ¬ Thm7_8_core Adm c₁ c₂ 2 1 1 (fun _ ↦ 1) := by
  intro h
  have hsup : ((Finset.univ.sup (fun _ : Fin 2 ↦ (1 : ℕ)) : ℕ) : ℝ) = 1 := by
    rw [Finset.sup_const Finset.univ_nonempty]
    norm_num
  obtain ⟨Θ, G, -, Ω, _, law, hall⟩ := h c₁ hc₁ (by simp) 0
    (by rw [hsup]; push_cast; positivity)
  let π₀ : ProductPolicy 2 1 (fun _ ↦ 1) := fun _ _ _ ↦
    ⟨fun _ ↦ 1, fun _ ↦ zero_le_one, by simp⟩
  obtain ⟨θ, hθ⟩ := hall π₀ 0 (by norm_num)
  have hempty : {_ω : Ω | c₁ < gap (G θ) π₀} = ∅ := by
    rw [gap_eq_zero_of_single]
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
    exact hc₁.le
  rw [hempty, measureReal_empty] at hθ
  exact lt_irrefl _ hθ

/-- **C40.** Printed Theorem 7.8 is false for every reading of "`m`-player
zero-sum" (every admissibility predicate `Adm`). -/
theorem not_thm7_8_printed
    (Adm : (m S H : ℕ) → (A : Fin m → ℕ) → MarkovGame m S H A → Prop) :
    ¬ Thm7_8_printed Adm := by
  rintro ⟨c₁, c₂, hc₁, hc₂, h⟩
  exact not_thm7_8_core_single Adm c₁ c₂ hc₁ hc₂
    (h 2 1 1 (fun _ ↦ 1) le_rfl le_rfl le_rfl fun _ ↦ le_rfl)

/-- **C40.** Even with constants allowed to depend on `(m, S, H, A)`, the printed
Theorem 7.8 is false. -/
theorem not_thm7_8_printed_sizeDependentConstants
    (Adm : (m S H : ℕ) → (A : Fin m → ℕ) → MarkovGame m S H A → Prop) :
    ¬ Thm7_8_printed_sizeDependentConstants Adm := by
  intro h
  obtain ⟨c₁, c₂, hc₁, hc₂, hcore⟩ :=
    h 2 1 1 (fun _ ↦ 1) le_rfl le_rfl le_rfl fun _ ↦ le_rfl
  exact not_thm7_8_core_single Adm c₁ c₂ hc₁ hc₂ hcore

/-- The literal "`∑ᵢ rᵢ = 0`, `rᵢ ∈ [0,1]`" zero-sum reading is refuted. -/
theorem not_thm7_8_printed_sumZeroNormalized : ¬ Thm7_8_printed sumZeroNormalized :=
  not_thm7_8_printed _

/-- The "rewards sum to a per-step constant" zero-sum reading is refuted. -/
theorem not_thm7_8_printed_sumConstant : ¬ Thm7_8_printed sumConstant :=
  not_thm7_8_printed _

end StatisticalRL.Ch7Rest.Marl
