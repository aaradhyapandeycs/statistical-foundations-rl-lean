import Formalization.Federated.Sync.Main

/-!
# Per-agent sample size read off from corrected Theorem 7.9 (`eq:sample-size-per-agent-fedQ`)

Source: `chapters/federated_RL.tex:118–129` ("Implications"): Theorem 7.9 implies that each
agent requires at most `Õ(SA/(K(1-γ)⁵ε²))` samples (`eq:sample-size-per-agent-fedQ`), each agent
drawing `SA` samples per iteration. SOURCE-ISSUES C41.

The corrected theorem (`fedSynQ_error_le_of_eta_le_one`, constants `c_η = 1/216`, `c_T = 10⁴`)
needs the prescribed step size `η = c_η K(1-γ)⁴ε²/log(SAKT/δ)` to be at most `1`, and its sample
condition (112–113) is implicit in `T`. This file proves:

* `exists_horizon_of_log_cube`: an explicit inversion of `T ≥ 10⁴ B log³(xT)`, namely
  `T = ⌈2.7·10⁸ · B (1 + log x)³⌉₊` works whenever `x ≥ 1` and `0 < B ≤ x³`;
* `fedSynQ_readOff_restricted`: the read-off in the `K`-range where the printed `η` at `T = 1` is at
  most `1`, i.e. `K(1-γ)⁴ε²/216 ≤ log(SAK/δ)`: there is a horizon `T ≥ 1` with
  `SA·T ≤ C·SA/(K(1-γ)⁵ε²)·(1 + log(SAK/(δε(1-γ)²)))³`, `C = 270000216`, such that FedSynQ run
  for `T` iterations with the printed `η` and any `τ ≥ 1` obeying (106) is `ε`-accurate with
  probability at least `1-δ`;
* `horizon_ge_exp_of_eta_le_one`: what is *not* implied. For any constant `c_η > 0`, whenever the
  prescribed `η` is at most `1` (as the corrected theorem requires), `T ≥ δ·exp(c_η K(1-γ)⁴ε²)/(SAK)`.
  So for `K ≫ log(SAKT/δ)/((1-γ)⁴ε²)` the corrected theorem only certifies horizons exponential in
  `K`, and the `Õ(1/K)` per-agent read-off (linear speedup for all `K`) does not follow from it.
  Whether the algorithm itself achieves it for such `K` is not decided here.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.FedSync

open StatisticalRL StatisticalRL.Ch7Rest.Fed StatisticalRL.Ch7Rest.FedGeneric

/-- Explicit inversion of the implicit horizon condition `T ≥ 10⁴ B log³(xT)`. -/
theorem exists_horizon_of_log_cube (x B : ℝ) (hx : 1 ≤ x) (hB0 : 0 < B) (hBx : B ≤ x ^ 3) :
    ∃ T : ℕ, 1 ≤ T ∧ (T : ℝ) ≤ 270000000 * B * (1 + Real.log x) ^ 3 + 1 ∧
      10000 * B * Real.log (x * T) ^ 3 ≤ T := by
  set L := Real.log x with hLdef
  have hL : 0 ≤ L := Real.log_nonneg hx
  set Tr : ℝ := 270000000 * B * (1 + L) ^ 3 with hTrdef
  have hTr : 0 < Tr := by positivity
  refine ⟨⌈Tr⌉₊, Nat.ceil_pos.mpr hTr, (Nat.ceil_lt_add_one hTr.le).le, ?_⟩
  set T : ℕ := ⌈Tr⌉₊
  have hTge : Tr ≤ (T : ℝ) := Nat.le_ceil Tr
  have hTlt : (T : ℝ) < Tr + 1 := Nat.ceil_lt_add_one hTr.le
  have hTpos : 0 < (T : ℝ) := hTr.trans_le hTge
  have hx0 : 0 < x := by linarith
  have h1L : 1 ≤ 1 + L := by linarith
  have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hx
  have hL3 : 1 ≤ (1 + L) ^ 3 := one_le_pow₀ h1L
  have hprod : 1 ≤ x ^ 3 * (1 + L) ^ 3 := one_le_mul_of_one_le_of_one_le hx3 hL3
  have hTub : (T : ℝ) ≤ 270000001 * (x ^ 3 * (1 + L) ^ 3) := by
    have : Tr ≤ 270000000 * (x ^ 3 * (1 + L) ^ 3) := by
      rw [hTrdef, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hBx (by positivity)) (by norm_num)
    linarith
  have hlogC : Real.log 270000001 ≤ 30 := by
    have h2 : (270000001 : ℝ) ≤ 2 ^ 30 := by norm_num
    calc Real.log 270000001 ≤ Real.log (2 ^ 30) := Real.log_le_log (by norm_num) h2
      _ = 30 * Real.log 2 := by rw [Real.log_pow]; norm_num
      _ ≤ 30 := by have := Real.log_two_lt_d9; linarith
  have hlog1L : Real.log (1 + L) ≤ L := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + L by linarith)
    linarith
  have hlogT : Real.log T ≤ 30 + 6 * L := by
    calc Real.log T ≤ Real.log (270000001 * (x ^ 3 * (1 + L) ^ 3)) :=
          Real.log_le_log hTpos hTub
      _ = Real.log 270000001 + (3 * L + 3 * Real.log (1 + L)) := by
          rw [Real.log_mul (by norm_num) (by positivity),
            Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
          push_cast; ring
      _ ≤ 30 + 6 * L := by linarith
  have hxT : Real.log (x * T) = L + Real.log T := Real.log_mul hx0.ne' hTpos.ne'
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast Nat.ceil_pos.mpr hTr
  have hlxT0 : 0 ≤ Real.log (x * T) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hx hT1)
  have hlxT : Real.log (x * T) ≤ 30 * (1 + L) := by rw [hxT]; linarith
  have hcube : Real.log (x * T) ^ 3 ≤ (30 * (1 + L)) ^ 3 := pow_le_pow_left₀ hlxT0 hlxT 3
  calc 10000 * B * Real.log (x * T) ^ 3 ≤ 10000 * B * (30 * (1 + L)) ^ 3 :=
        mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = Tr := by rw [hTrdef]; ring
    _ ≤ T := hTge

variable {State Action : Type} [Fintype State] [Fintype Action]

/-- **Restricted per-agent read-off** (`eq:sample-size-per-agent-fedQ`, `federated_RL.tex:118–129`;
SOURCE-ISSUES C41). In the range `K(1-γ)⁴ε²/216 ≤ log(SAK/δ)`, an explicit horizon `T` with
`SA·T ≤ 270000216·SA/(K(1-γ)⁵ε²)·(1 + log(SAK/(δε(1-γ)²)))³` makes the corrected Theorem 7.9 apply,
for every synchronization period `τ ≥ 1` obeying (106). -/
theorem fedSynQ_readOff_restricted (M : DiscountedMDP State Action) (K : ℕ) (δ ε : ℝ)
    (Q₀ : State → Action → ℝ) (hK : 1 ≤ K) (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε)
    (hεH : ε ≤ 1 / (1 - M.discount))
    (hQ₀ : ∀ s a, 0 ≤ Q₀ s a ∧ Q₀ s a ≤ 1 / (1 - M.discount))
    (hKr : 1 / 216 * K * (1 - M.discount) ^ 4 * ε ^ 2 ≤
      Real.log (Fintype.card State * Fintype.card Action * K / δ)) :
    ∃ T : ℕ, 1 ≤ T ∧
      (Fintype.card State * Fintype.card Action * T : ℝ) ≤
        270000216 * (Fintype.card State * Fintype.card Action) /
            (K * (1 - M.discount) ^ 5 * ε ^ 2) *
          (1 + Real.log (Fintype.card State * Fintype.card Action * K /
            (δ * ε * (1 - M.discount) ^ 2))) ^ 3 ∧
      ∀ (τ : ℕ) (η : ℝ), 1 ≤ τ →
        η = 1 / 216 * K * (1 - M.discount) ^ 4 * ε ^ 2 /
          Real.log (Fintype.card State * Fintype.card Action * K * T / δ) →
        (τ : ℝ) ≤ 1 + 1 / η * min ((1 - M.discount) / (8 * M.discount)) (1 / (K : ℝ)) →
        1 - δ ≤ (fedSamplingLaw M T K 1).real {data | ∀ s a,
          |fedOutput M η K τ Q₀ (fun t k s a ↦ fedSamplesExtend M T K 1 data t k s a 0) T s a -
            M.optimalityFixedPoint s a| ≤ ε} := by
  haveI := M.state_nonempty
  haveI := M.action_nonempty
  have hγ1 := M.discount_lt_one
  set g : ℝ := 1 - M.discount with hgdef
  have hg0 : 0 < g := by rw [hgdef]; linarith
  have hg1 : g ≤ 1 := by rw [hgdef]; linarith [M.discount_nonneg]
  set S : ℝ := (Fintype.card State : ℝ) with hSdef
  set A : ℝ := (Fintype.card Action : ℝ) with hAdef
  have hS : (1 : ℝ) ≤ S := by rw [hSdef]; exact_mod_cast Fintype.card_pos
  have hA : (1 : ℝ) ≤ A := by rw [hAdef]; exact_mod_cast Fintype.card_pos
  have hKr1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hSAK : 1 ≤ S * A * K :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hS hA) hKr1
  set Pd : ℝ := S * A * K / δ with hPddef
  have hPd1 : 1 ≤ Pd := by rw [hPddef, le_div_iff₀ hδ]; linarith
  have hεg : ε * g ≤ 1 := by rwa [le_div_iff₀ hg0] at hεH
  have hεg2 : ε * g ^ 2 ≤ 1 := by
    calc ε * g ^ 2 = (ε * g) * g := by ring
      _ ≤ 1 * 1 := mul_le_mul hεg hg1 hg0.le zero_le_one
      _ = 1 := by ring
  have hεg2pos : 0 < ε * g ^ 2 := by positivity
  set y : ℝ := 1 / (ε * g ^ 2) with hydef
  have hy1 : 1 ≤ y := by rw [hydef, le_div_iff₀ hεg2pos]; linarith
  set x : ℝ := S * A * K / (δ * ε * g ^ 2) with hxdef
  have hxPy : x = Pd * y := by
    rw [hxdef, hPddef, hydef]; field_simp
  have hyx : y ≤ x := by rw [hxPy]; exact le_mul_of_one_le_left (by linarith) hPd1
  have hx1 : 1 ≤ x := hy1.trans hyx
  set B : ℝ := 1 / (K * g ^ 5 * ε ^ 2) with hBdef
  have hB0 : 0 < B := by positivity
  have hBy : B ≤ y ^ 3 := by
    have hy3 : y ^ 3 = 1 / (ε * g ^ 2) ^ 3 := by rw [hydef, div_pow, one_pow]
    rw [hy3, hBdef]
    apply one_div_le_one_div_of_le (by positivity)
    calc (ε * g ^ 2) ^ 3 = (ε * g) * (ε ^ 2 * g ^ 5) := by ring
      _ ≤ 1 * (ε ^ 2 * g ^ 5) := mul_le_mul_of_nonneg_right hεg (by positivity)
      _ ≤ K * (ε ^ 2 * g ^ 5) := mul_le_mul_of_nonneg_right hKr1 (by positivity)
      _ = K * g ^ 5 * ε ^ 2 := by ring
  have hBx : B ≤ x ^ 3 := hBy.trans (pow_le_pow_left₀ (by linarith) hyx 3)
  obtain ⟨T, hT1, hTub, hTc⟩ := exists_horizon_of_log_cube x B hx1 hB0 hBx
  have hT1r : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  set L := Real.log x with hLdef
  have hL : 0 ≤ L := Real.log_nonneg hx1
  refine ⟨T, hT1, ?_, ?_⟩
  · -- the bound on the per-agent sample size
    have hPdx : Pd ≤ x := by
      rw [hxPy]; exact le_mul_of_one_le_right (by linarith) hy1
    have hlogPd : Real.log Pd ≤ L := Real.log_le_log (by linarith) hPdx
    have hL13 : L ≤ (1 + L) ^ 3 := by
      have : 1 + L ≤ (1 + L) ^ 3 := le_self_pow₀ (by linarith) (by norm_num)
      linarith
    have hKg : K * g ^ 4 * ε ^ 2 ≤ 216 * (1 + L) ^ 3 := by
      have : 1 / 216 * K * g ^ 4 * ε ^ 2 ≤ Real.log Pd := hKr
      linarith
    have hone : 1 ≤ 216 * B * (1 + L) ^ 3 := by
      have hBK : B * (K * g ^ 4 * ε ^ 2) = 1 / g := by
        rw [hBdef]; field_simp
      have hg' : 1 ≤ 1 / g := by rw [le_div_iff₀ hg0]; linarith
      calc (1 : ℝ) ≤ B * (K * g ^ 4 * ε ^ 2) := by rw [hBK]; exact hg'
        _ ≤ B * (216 * (1 + L) ^ 3) := mul_le_mul_of_nonneg_left hKg hB0.le
        _ = 216 * B * (1 + L) ^ 3 := by ring
    have hTB : (T : ℝ) ≤ 270000216 * B * (1 + L) ^ 3 := by linarith
    have hSA : 0 ≤ S * A := by positivity
    calc S * A * T ≤ S * A * (270000216 * B * (1 + L) ^ 3) :=
          mul_le_mul_of_nonneg_left hTB hSA
      _ = 270000216 * (S * A) / (K * g ^ 5 * ε ^ 2) * (1 + L) ^ 3 := by
          rw [hBdef]; ring
  · intro τ η hτ hη hτc
    refine fedSynQ_error_le_of_eta_le_one M K τ T δ ε Q₀ hK hτ hT1 hδ hδ1 hε hεH hQ₀ η hη
      ?_ hτc ?_
    · -- `η ≤ 1` from the `K`-restriction
      have hPd0 : 0 < Real.log Pd := Real.log_pos (by
        rw [hPddef, lt_div_iff₀ hδ]; linarith)
      have hmono : Real.log Pd ≤ Real.log (S * A * K * T / δ) := by
        apply Real.log_le_log (by linarith)
        rw [hPddef]
        apply div_le_div_of_nonneg_right _ hδ.le
        exact le_mul_of_one_le_right (by linarith) hT1r
      rw [hη, div_le_one (hPd0.trans_le hmono)]
      exact hKr.trans hmono
    · -- the implicit sample condition (112–113)
      have hxT : S * A * K * T / (δ * ε * g ^ 2) = x * T := by rw [hxdef]; ring
      have hcoef : 10000 / (K * g ^ 5 * ε ^ 2) = 10000 * B := by rw [hBdef]; ring
      rw [hxT, hcoef]
      exact hTc

/-- **What the corrected theorem does not give** (SOURCE-ISSUES C41). For any constant `c_η > 0`,
if the prescribed step size `η = c_η K(1-γ)⁴ε²/log(SAKT/δ)` is at most `1` (a hypothesis of the
corrected Theorem 7.9), then `T ≥ δ·exp(c_η K(1-γ)⁴ε²)/(SAK)`: the horizons the corrected theorem
can certify grow exponentially in `K`. -/
theorem horizon_ge_exp_of_eta_le_one (M : DiscountedMDP State Action) (K T : ℕ) (δ ε c_η η : ℝ)
    (hK : 1 ≤ K) (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hη : η = c_η * K * (1 - M.discount) ^ 4 * ε ^ 2 /
      Real.log (Fintype.card State * Fintype.card Action * K * T / δ))
    (hη1 : η ≤ 1) :
    δ * Real.exp (c_η * K * (1 - M.discount) ^ 4 * ε ^ 2) /
        (Fintype.card State * Fintype.card Action * K) ≤ T := by
  haveI := M.state_nonempty
  haveI := M.action_nonempty
  set S : ℝ := (Fintype.card State : ℝ) with hSdef
  set A : ℝ := (Fintype.card Action : ℝ) with hAdef
  have hS : (1 : ℝ) ≤ S := by rw [hSdef]; exact_mod_cast Fintype.card_pos
  have hA : (1 : ℝ) ≤ A := by rw [hAdef]; exact_mod_cast Fintype.card_pos
  have hKr1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hT1r : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hSAKT : 1 ≤ S * A * K * T :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hS hA) hKr1) hT1r
  have harg : 1 < S * A * K * T / δ := by rw [lt_div_iff₀ hδ]; linarith
  have hlog : 0 < Real.log (S * A * K * T / δ) := Real.log_pos harg
  rw [hη, div_le_one hlog] at hη1
  have hexp : Real.exp (c_η * K * (1 - M.discount) ^ 4 * ε ^ 2) ≤ S * A * K * T / δ := by
    calc Real.exp _ ≤ Real.exp (Real.log (S * A * K * T / δ)) := Real.exp_le_exp.mpr hη1
      _ = S * A * K * T / δ := Real.exp_log (by linarith)
  rw [le_div_iff₀ hδ] at hexp
  have hSAK : 0 < S * A * K := by positivity
  rw [div_le_iff₀ hSAK]
  calc δ * Real.exp (c_η * K * (1 - M.discount) ^ 4 * ε ^ 2)
      = Real.exp (c_η * K * (1 - M.discount) ^ 4 * ε ^ 2) * δ := by ring
    _ ≤ S * A * K * T := hexp
    _ = T * (S * A * K) := by ring

end StatisticalRL.Ch7Rest.FedSync
