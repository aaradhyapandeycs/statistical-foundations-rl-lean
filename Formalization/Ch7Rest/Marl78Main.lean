import Formalization.Ch7Rest.Marl78Bayes
import Formalization.Ch7Rest.Marl78Statement

/-!
# Corrected Theorem 7.8: proof

Constants `c₁ = 1/2048`, `c₂ = 2⁻³²`, `λ = 1024 ε`.
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl

open StatisticalRL OnlineLowerBound AdaptiveKL

/-- The KL budget from the sample-size hypothesis (`λ = 1024 ε`, `c₂ = 2⁻³²`). -/
theorem budget_of_N {S H n N : ℕ} (hS : 2 ≤ S) (hH : 2 ≤ H) (hn : 2 ≤ n) {ε : ℝ} (hε : 0 < ε)
    (hN : (N : ℝ) < 1 / 2 ^ 32 * (H : ℝ) ^ 4 * S * (n : ℝ) / ε ^ 2) :
    64 * (4 * (1024 * ε) ^ 2 / (H : ℝ) ^ 3) * N ≤
      ((n : ℝ) - 1) * ((S : ℝ) - 1) * ((H / 2 : ℕ) : ℝ) := by
  have hS' : (2 : ℝ) ≤ S := by exact_mod_cast hS
  have hH' : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hH2 : (H : ℝ) / 4 ≤ ((H / 2 : ℕ) : ℝ) := by
    have h1 : H ≤ 4 * (H / 2) := by omega
    have h2 : (H : ℝ) ≤ 4 * ((H / 2 : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hHpos : (0 : ℝ) < H := by linarith
  have hN' : (N : ℝ) * ε ^ 2 ≤ (H : ℝ) ^ 4 * S * n / 2 ^ 32 := by
    rw [lt_div_iff₀ (by positivity)] at hN
    nlinarith
  have e : 64 * (4 * (1024 * ε) ^ 2 / (H : ℝ) ^ 3) * N =
      2 ^ 28 * ((N : ℝ) * ε ^ 2) / (H : ℝ) ^ 3 := by
    field_simp; ring
  rw [e, div_le_iff₀ (by positivity)]
  have h1 : 2 ^ 28 * ((N : ℝ) * ε ^ 2) ≤ (H : ℝ) ^ 4 * S * n / 16 := by
    have := mul_le_mul_of_nonneg_left hN' (by norm_num : (0 : ℝ) ≤ 2 ^ 28)
    linarith
  have h2 : (H : ℝ) * S * n / 16 ≤ ((n : ℝ) - 1) * ((S : ℝ) - 1) * ((H / 2 : ℕ) : ℝ) := by
    have ha : (n : ℝ) / 2 ≤ (n : ℝ) - 1 := by linarith
    have hs : (S : ℝ) / 2 ≤ (S : ℝ) - 1 := by linarith
    calc (H : ℝ) * S * n / 16 = ((n : ℝ) / 2) * ((S : ℝ) / 2) * ((H : ℝ) / 4) := by ring
      _ ≤ ((n : ℝ) - 1) * ((S : ℝ) - 1) * ((H / 2 : ℕ) : ℝ) := by
          apply mul_le_mul (mul_le_mul ha hs (by positivity) (by linarith)) hH2
            (by positivity) (by nlinarith)
  have h3 := mul_le_mul_of_nonneg_right h2 (by positivity : (0 : ℝ) ≤ (H : ℝ) ^ 3)
  calc 2 ^ 28 * ((N : ℝ) * ε ^ 2) ≤ (H : ℝ) ^ 4 * S * n / 16 := h1
    _ = (H : ℝ) * S * n / 16 * (H : ℝ) ^ 3 := by ring
    _ ≤ _ := h3

/-- Averaging a per-seed Bayes bound over a discrete seed law `μ` (any type, `μ ≥ 0`, total mass
`1`): some parameter has seed-averaged failure probability at least `1/4`. -/
theorem exists_param_of_seed_avg {Θ Ω : Type*} [Fintype Θ] (ρ : Θ → ℝ) (hρ0 : ∀ θ, 0 ≤ ρ θ)
    (hρ1 : ∑ θ, ρ θ = 1) (μ : Ω → ℝ) (hμ0 : ∀ ω, 0 ≤ μ ω) (hμ : HasSum μ 1)
    (F : Θ → Ω → ℝ) (hF0 : ∀ θ ω, 0 ≤ F θ ω) (hF1 : ∀ θ ω, F θ ω ≤ 1)
    (hB : ∀ ω, (1 : ℝ) / 4 ≤ ∑ θ, ρ θ * F θ ω) :
    ∃ θ, (1 : ℝ) / 4 ≤ ∑' ω, μ ω * F θ ω := by
  classical
  have hsum : ∀ θ, Summable (fun ω => μ ω * F θ ω) := fun θ =>
    Summable.of_nonneg_of_le (fun ω => mul_nonneg (hμ0 ω) (hF0 θ ω))
      (fun ω => by simpa using mul_le_mul_of_nonneg_left (hF1 θ ω) (hμ0 ω)) hμ.summable
  have hL : HasSum (fun ω => ∑ θ, ρ θ * (μ ω * F θ ω)) (∑ θ, ρ θ * ∑' ω, μ ω * F θ ω) :=
    hasSum_sum fun θ _ => (hsum θ).hasSum.mul_left (ρ θ)
  have hR : HasSum (fun ω => μ ω * (1 / 4)) (1 * (1 / 4)) := hμ.mul_right (1 / 4)
  have hle : (1 : ℝ) / 4 ≤ ∑ θ, ρ θ * ∑' ω, μ ω * F θ ω := by
    have := hasSum_le (fun ω => by
      have h := mul_le_mul_of_nonneg_left (hB ω) (hμ0 ω)
      rw [Finset.mul_sum] at h
      refine h.trans_eq (Finset.sum_congr rfl fun θ _ => by ring)) hR hL
    linarith
  by_contra hcon
  push_neg at hcon
  obtain ⟨θ0, hθ0⟩ : ∃ θ0, 0 < ρ θ0 := by
    by_contra hall
    push_neg at hall
    have : ∑ θ, ρ θ ≤ 0 := Finset.sum_nonpos fun θ _ => hall θ
    linarith
  have hlt : ∑ θ, ρ θ * ∑' ω, μ ω * F θ ω < ∑ θ, ρ θ * (1 / 4) :=
    Finset.sum_lt_sum (fun θ _ => mul_le_mul_of_nonneg_left (hcon θ).le (hρ0 θ))
      ⟨θ0, Finset.mem_univ _, mul_lt_mul_of_pos_left (hcon θ0) hθ0⟩
  rw [← Finset.sum_mul, hρ1, one_mul] at hlt
  linarith

/-- **The hard family defeats every learner** below the KL budget: for every learner with a
discrete seed law some `θ` has `P_θ(gap > ε) ≥ 1/4`. -/
theorem hard_family_lower {m S H : ℕ} {A : Fin m → ℕ} (hS : 2 ≤ S) (hH : 2 ≤ H) (istar : Fin m)
    (hn : 2 ≤ A istar) (z : Fin S) (lam : ℝ) (hl : 0 < lam) (hlH : lam ≤ (H : ℝ) / 2)
    (ε : ℝ) (hεl : ε < lam / 512) (cst : ℝ) (hcst0 : 0 ≤ cst)
    (rest : Fin m → ℕ → Fin S → ((i : Fin m) → Fin (A i)) → ℝ) (N : ℕ)
    (hbudget : 64 * (4 * lam ^ 2 / (H : ℝ) ^ 3) * N ≤
      ((A istar : ℝ) - 1) * ((S : ℝ) - 1) * ((H / 2 : ℕ) : ℝ))
    (Ω : Type) (μ : Ω → ℝ) (hμ0 : ∀ ω, 0 ≤ μ ω) (hμ : HasSum μ 1)
    (rule : Ω → (t : ℕ) → (Fin t → Query m S H A × Fin S) → FiniteDistribution (Query m S H A))
    (out : Ω → (Fin N → Query m S H A × Fin S) → JointPolicy m S A) :
    ∃ θ : Fin S × Fin H → Fin (A istar), (1 : ℝ) / 4 ≤ ∑' ω, μ ω *
      ∑ hist, (interactionLaw (rule ω) (genEnv (hardGame istar z hH lam hl hlH cst rest θ)) N).prob
        hist * (if ε < gapJ (hardGame istar z hH lam hl hlH cst rest θ) (out ω hist) then 1 else 0) := by
  classical
  set ref : Fin (A istar) := ⟨0, by omega⟩
  refine exists_param_of_seed_avg (prior ref) (prior_nonneg hn ref) (sum_prior hn ref) μ hμ0 hμ
    (fun θ ω => evProb (interactionLaw (rule ω) (genEnv (hardGame istar z hH lam hl hlH cst rest θ)) N)
      (fun hist => ε < gapJ (hardGame istar z hH lam hl hlH cst rest θ) (out ω hist)))
    (fun θ ω => evProb_nonneg _ _) (fun θ ω => ?_)
    (fun ω => hard_bayes cst hcst0 rest hS hn ref rfl ε hεl N hbudget (rule ω) (out ω))
  unfold evProb
  calc _ ≤ ∑ hist, (interactionLaw (rule ω) (genEnv (hardGame istar z hH lam hl hlH cst rest θ)) N).prob hist * 1 :=
        Finset.sum_le_sum fun hist _ => mul_le_mul_of_nonneg_left (by split_ifs <;> norm_num)
          ((interactionLaw _ _ N).prob_nonneg hist)
    _ = 1 := by simp_rw [mul_one]; exact (interactionLaw _ _ N).sum_prob

/-- **Theorem 7.8 corrected** (zero-sum convention). -/
theorem thm7_8_corrected : Thm7_8_corrected := by
  refine ⟨1 / 2048, 1 / 2 ^ 32, by norm_num, by norm_num, ?_⟩
  intro m S H A hm hS hH hA ε hε hεc
  classical
  obtain ⟨istar, -, hsup⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin m))
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ A
  have hn : 2 ≤ A istar := hsup ▸ hA
  -- a partner, which is player 1 whenever `istar` is not
  obtain ⟨p, hp, hp0⟩ : ∃ p : Fin m, p ≠ istar ∧ ((istar : ℕ) ≠ 0 → (p : ℕ) = 0) := by
    by_cases h0 : (istar : ℕ) = 0
    · refine ⟨⟨1, by omega⟩, fun h => ?_, fun h => absurd h0 h⟩
      have := congrArg Fin.val h
      simp only at this
      omega
    · exact ⟨⟨0, by omega⟩, fun h => h0 (by rw [← h]), fun _ => rfl⟩
  set z : Fin S := ⟨0, by omega⟩
  set lam : ℝ := 1024 * ε with hlam
  have hl : 0 < lam := by positivity
  have hlH : lam ≤ (H : ℝ) / 2 := by rw [hlam]; linarith
  set cst : ℝ := if (istar : ℕ) = 0 then 0 else 1 with hcst
  have hcst0 : 0 ≤ cst := by rw [hcst]; split_ifs <;> norm_num
  set rest : Fin m → ℕ → Fin S → ((i : Fin m) → Fin (A i)) → ℝ :=
    fun i _ s _ => if i = p then -((if s = z then 0 else 1) - cst) else 0 with hrest
  refine ⟨Fin S × Fin H → Fin (A istar), hardGame istar z hH lam hl hlH cst rest, ?_, ?_, ?_⟩
  · -- zero-sum admissibility
    intro θ
    have hrew : ∀ i h s a, (hardGame istar z hH lam hl hlH cst rest θ).reward i h s a =
        if i = istar then (if s = z then 0 else 1) - cst
        else if i = p then -((if s = z then 0 else 1) - cst) else 0 := by
      intro i h s a; simp [hardGame, hardReward, hrest]
    have hX : ∀ s : Fin S, -1 ≤ (if s = z then (0 : ℝ) else 1) - cst ∧
        (if s = z then (0 : ℝ) else 1) - cst ≤ 1 := by
      intro s; rw [hcst]; split_ifs <;> norm_num
    refine ⟨?_, ?_, ?_⟩
    · intro h s a
      simp_rw [hrew]
      rw [Fintype.sum_eq_add istar p (Ne.symm hp) (fun i hi => by simp [hi.1, hi.2])]
      simp [hp]
    · intro i h s a hi0
      rw [hrew]
      by_cases his : i = istar
      · have : (istar : ℕ) = 0 := his ▸ hi0
        simp only [his, if_true, hcst, this, if_true, sub_zero]
        split_ifs <;> norm_num
      · rw [if_neg his]
        by_cases hip : i = p
        · have hist0 : (istar : ℕ) ≠ 0 := by
            intro h0
            exact his (Fin.ext (hi0.trans h0.symm))
          simp only [hip, if_true, hcst, hist0, if_false]
          split_ifs <;> norm_num
        · rw [if_neg hip]; norm_num
    · intro i h s a
      have hc1 : cst ≤ 1 := by rw [hcst]; split_ifs <;> norm_num
      rw [hrew, abs_le]
      split_ifs <;> constructor <;> linarith
  · intro θ θ'; rfl
  · intro N hN Ω μ hμ0 hμ rule out
    rw [hsup] at hN
    exact hard_family_lower hS hH istar hn z lam hl hlH ε (by rw [hlam]; linarith) cst hcst0 rest N
      (budget_of_N hS hH hn hε hN) Ω μ hμ0 hμ rule out

/-- **Theorem 7.8 corrected, constant-sum normalised convention** (`Σᵢ rᵢ = 1`, all `rᵢ ∈ [0,1]`,
the footnote shift of `marl.tex:53`). -/
theorem thm7_8_corrected_constSum : Thm7_8_corrected_constSum := by
  refine ⟨1 / 2048, 1 / 2 ^ 32, by norm_num, by norm_num, ?_⟩
  intro m S H A hm hS hH hA ε hε hεc
  classical
  obtain ⟨istar, -, hsup⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin m))
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ A
  have hn : 2 ≤ A istar := hsup ▸ hA
  obtain ⟨p, hp⟩ : ∃ p : Fin m, p ≠ istar := by
    by_cases h0 : (istar : ℕ) = 0
    · refine ⟨⟨1, by omega⟩, fun h => ?_⟩
      have := congrArg Fin.val h
      simp only at this
      omega
    · exact ⟨⟨0, by omega⟩, fun h => h0 (by rw [← h])⟩
  set z : Fin S := ⟨0, by omega⟩
  set lam : ℝ := 1024 * ε with hlam
  have hl : 0 < lam := by positivity
  have hlH : lam ≤ (H : ℝ) / 2 := by rw [hlam]; linarith
  set rest : Fin m → ℕ → Fin S → ((i : Fin m) → Fin (A i)) → ℝ :=
    fun i _ s _ => if i = p then 1 - (if s = z then 0 else 1) else 0 with hrest
  refine ⟨Fin S × Fin H → Fin (A istar), hardGame istar z hH lam hl hlH 0 rest, ?_, ?_, ?_⟩
  · intro θ
    have hrew : ∀ i h s a, (hardGame istar z hH lam hl hlH 0 rest θ).reward i h s a =
        if i = istar then (if s = z then 0 else 1) - 0
        else if i = p then 1 - (if s = z then 0 else 1) else 0 := by
      intro i h s a; simp [hardGame, hardReward, hrest]
    refine ⟨?_, ?_⟩
    · intro h s a
      simp_rw [hrew]
      rw [Fintype.sum_eq_add istar p (Ne.symm hp) (fun i hi => by simp [hi.1, hi.2])]
      simp [hp]
    · intro i h s a
      rw [hrew]
      split_ifs <;> norm_num
  · intro θ θ'; rfl
  · intro N hN Ω μ hμ0 hμ rule out
    rw [hsup] at hN
    exact hard_family_lower hS hH istar hn z lam hl hlH ε (by rw [hlam]; linarith) 0 le_rfl rest N
      (budget_of_N hS hH hn hε hN) Ω μ hμ0 hμ rule out

end StatisticalRL.Ch7Rest.Marl
