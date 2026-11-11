import Formalization.MultiAgent.Hedge.PathwiseMain
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Theorem 7.7: the general-sum guarantee of the witness algorithm

`core_cce`: for `S ≥ 1`, `A_i ≥ 1`, `δ ∈ (0,1)`, `0 < ε ≤ H` and rewards in `[0,1]` on `1..H`,
the algorithm with `L = log(4HSΣA/δ)`, `T = ⌈2000H³L/ε²⌉ + 1`, `η = ε/(80H²)` makes
`N = H S T ΣA ≤ 2002 H⁴ S ΣA L / ε²` queries and, for every kernel `P`, outputs a joint policy
with `gapJ ≤ ε` with probability at least `1 − δ`.
-/

open scoped BigOperators
open Finset

namespace StatisticalRL.Ch7Rest.Marl77

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.Ch7Rest.Marl76
open StatisticalRL.Online.Hedge StatisticalRL.AdaptiveKL

/-- The final arithmetic. -/
theorem gap_arith {H ε L T : ℝ} (hH : 1 ≤ H) (hε : 0 < ε) (hεH : ε ≤ H) (hL : 0 ≤ L) (hT : 0 < T)
    (hTL : 2000 * H ^ 3 * L / ε ^ 2 ≤ T) :
    40 * (ε / (80 * H ^ 2)) * H ^ 2 + 16 * H ^ 2 * L / T + 3 * H * L / (ε / (80 * H ^ 2) * T) +
      ε / (80 * H ^ 2) * H ^ 3 * L / T ≤ ε := by
  have hH0 : 0 < H := by linarith
  set u := L / T with hu
  have hu0 : 0 ≤ u := div_nonneg hL hT.le
  have huB : u * (2000 * H ^ 3) ≤ ε ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hTL
    rw [hu, div_mul_eq_mul_div, div_le_iff₀ hT]
    nlinarith
  have e1 : 40 * (ε / (80 * H ^ 2)) * H ^ 2 = ε / 2 := by field_simp; norm_num
  have e2 : 16 * H ^ 2 * L / T = 16 * H ^ 2 * u := by rw [hu]; try ring
  have e3 : 3 * H * L / (ε / (80 * H ^ 2) * T) = 240 * H ^ 3 * u / ε := by
    rw [hu]; field_simp; try ring
  have e4 : ε / (80 * H ^ 2) * H ^ 3 * L / T = ε * H * u / 80 := by
    rw [hu]; field_simp; try ring
  rw [e1, e2, e3, e4]
  -- bounds
  have b2 : 16 * H ^ 2 * u ≤ 16 * ε / 2000 := by
    have : u * (2000 * H ^ 3) ≤ ε * H := by nlinarith
    have : u * H ^ 2 * 2000 ≤ ε := by
      have h' : u * H ^ 2 * 2000 * H ≤ ε * H := by nlinarith
      exact le_of_mul_le_mul_right h' hH0
    nlinarith
  have b3 : 240 * H ^ 3 * u / ε ≤ 240 * ε / 2000 := by
    rw [div_le_iff₀ hε]
    nlinarith
  have b4 : ε * H * u / 80 ≤ ε / 1000 := by
    have : u * H ≤ 1 / 2000 := by
      have h1 : u * (2000 * H ^ 3) ≤ H ^ 2 := le_trans huB (by nlinarith)
      have h2 : u * H * 2000 * H ^ 2 ≤ 1 * H ^ 2 := by nlinarith
      have := le_of_mul_le_mul_right h2 (by positivity)
      linarith
    have : ε * H * u ≤ ε / 2000 := by nlinarith
    linarith
  linarith

theorem log_ge_one_of {y : ℝ} (hy : 4 ≤ y) : 1 ≤ Real.log y := by
  have h4 : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  rw [← Real.log_exp 1]
  exact Real.log_le_log (Real.exp_pos 1) (by linarith)

variable {m S H : ℕ} {A : Fin m → ℕ}

/-- The algorithm with the theorem's tuning. -/
noncomputable def tunedAlg (hS : 1 ≤ S) (hA : ∀ i, 1 ≤ A i) (hH : 1 ≤ H) (δ ε : ℝ)
    (rew : Fin m → ℕ → Fin S → JointAction m A → ℝ) : Alg m S H A where
  rew := rew
  T := ⌈2000 * (H : ℝ) ^ 3 * Real.log (4 * H * S * (∑ i, (A i : ℝ)) / δ) / ε ^ 2⌉₊ + 1
  η := ε / (80 * (H : ℝ) ^ 2)
  hT := Nat.succ_pos _
  hA := fun i => hA i
  z₀ := ((⟨0, hH⟩, ⟨0, hS⟩, fun i => ⟨0, hA i⟩), ⟨0, hS⟩)

theorem sum_A_cases (hA : ∀ i, 1 ≤ A i) :
    (∑ i, (A i : ℝ)) = 0 ∧ m = 0 ∨ 1 ≤ ∑ i, (A i : ℝ) := by
  rcases Nat.eq_zero_or_pos m with h | h
  · left; subst h; simp
  · right
    calc (1 : ℝ) ≤ (A ⟨0, h⟩ : ℝ) := by exact_mod_cast hA _
      _ ≤ _ := single_le_sum (f := fun i => (A i : ℝ)) (fun i _ => by positivity) (mem_univ _)

theorem core_cce (hS : 1 ≤ S) (hA : ∀ i, 1 ≤ A i) (δ ε : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 < ε) (hεH : ε ≤ H) (rew : Fin m → ℕ → Fin S → JointAction m A → ℝ)
    (hrew : ∀ i h s a, 1 ≤ h → h ≤ H → 0 ≤ rew i h s a ∧ rew i h s a ≤ 1) :
    ∃ al : Alg m S H A, al.rew = rew ∧
      (al.N : ℝ) ≤ 2002 * (H : ℝ) ^ 4 * S * (∑ i, (A i : ℝ)) / ε ^ 2 *
          Real.log (4 * H * S * (∑ i, (A i : ℝ)) / δ) ∧
      ∀ P : ℕ → Fin S → JointAction m A → FiniteDistribution (Fin S),
        1 - δ ≤ ∑ hist, (interactionLaw al.rule (genEnv (⟨P, rew⟩ : MarkovGame m S H A)) al.N).prob hist *
          (if gapJ (⟨P, rew⟩ : MarkovGame m S H A) (al.out hist) ≤ ε then 1 else 0) := by
  have hHn : 1 ≤ H := by
    have : (0 : ℝ) < H := lt_of_lt_of_le hε hεH
    exact_mod_cast this
  have hHr : (1 : ℝ) ≤ H := by exact_mod_cast hHn
  have hSr : (1 : ℝ) ≤ S := by exact_mod_cast hS
  have hcases := sum_A_cases hA
  have hmM' : (m : ℝ) ≤ ∑ i, (A i : ℝ) := by
    calc (m : ℝ) = ∑ _i : Fin m, (1 : ℝ) := by simp
      _ ≤ _ := sum_le_sum fun i _ => by exact_mod_cast hA i
  have hAM' : ∀ i, (A i : ℝ) ≤ ∑ i, (A i : ℝ) := fun i =>
    single_le_sum (f := fun i => (A i : ℝ)) (fun i _ => by positivity) (mem_univ _)
  have hMn' : (numPairs A : ℝ) = ∑ i, (A i : ℝ) := by simp [numPairs]
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∑ i, (A i : ℝ) := ⟨_, rfl⟩
  rw [← hM] at hcases hmM' hMn' hAM' ⊢
  obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = Real.log (4 * H * S * M / δ) := ⟨_, rfl⟩
  rw [← hLdef]
  obtain ⟨al, hal⟩ : ∃ al, al = tunedAlg hS hA hHn δ ε rew := ⟨_, rfl⟩
  have hTdef : (al.T : ℝ) = (⌈2000 * (H : ℝ) ^ 3 * L / ε ^ 2⌉₊ : ℝ) + 1 := by
    rw [hal]; simp only [tunedAlg, ← hM, ← hLdef]; push_cast; ring
  have hηdef : al.η = ε / (80 * (H : ℝ) ^ 2) := by rw [hal]; rfl
  have hrewal : al.rew = rew := by rw [hal]; rfl
  have hη : 0 < al.η := by rw [hηdef]; positivity
  have hTr : (0 : ℝ) < al.T := by exact_mod_cast al.hT
  have hM0 : 0 ≤ M := by
    rcases hcases with h | h
    · linarith [h.1]
    · linarith
  have hbig : 1 ≤ M → 4 ≤ 4 * H * S * M := fun h1 => by
    have := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hHr hSr) h1
    linarith
  have hL0 : 0 ≤ L := by
    rcases hcases with h | h
    · rw [hLdef, h.1]; simp
    · rw [hLdef]; apply Real.log_nonneg
      rw [le_div_iff₀ hδ0]; linarith [hbig h]
  have hlog : ∀ i, Real.log (A i) ≤ L := by
    intro i
    have hAi : (1 : ℝ) ≤ A i := by exact_mod_cast hA i
    have hM1 : 1 ≤ M := le_trans hAi (hAM' i)
    rw [hLdef]
    apply Real.log_le_log (by linarith)
    rw [le_div_iff₀ hδ0]
    have h4 := hbig hM1
    have h4HS : (1 : ℝ) ≤ 4 * H * S := by nlinarith
    have hMle : M ≤ 4 * H * S * M := by nlinarith
    have hAδ : (A i : ℝ) * δ ≤ A i := mul_le_of_le_one_right (by linarith) hδ1.le
    linarith [hAM' i]
  have hηH : al.η * H ≤ 1 / 4 := by
    rw [hηdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hεH (by linarith : (0 : ℝ) ≤ H)]
  have hTL : 2000 * (H : ℝ) ^ 3 * L / ε ^ 2 ≤ al.T := by
    rw [hTdef]
    linarith [Nat.le_ceil (2000 * (H : ℝ) ^ 3 * L / ε ^ 2)]
  refine ⟨al, hrewal, ?_, ?_⟩
  · -- the sample count
    have hTle : (al.T : ℝ) ≤ 2000 * (H : ℝ) ^ 3 * L / ε ^ 2 + 2 := by
      rw [hTdef]
      have := Nat.ceil_lt_add_one (show 0 ≤ 2000 * (H : ℝ) ^ 3 * L / ε ^ 2 by positivity)
      linarith
    have hN : (al.N : ℝ) = H * S * al.T * M := by
      simp only [Alg.N]; push_cast; rw [hM]
    rw [hN]
    rcases hcases with h0 | hM1
    · rw [h0.1]; simp
    · have hL1 : 1 ≤ L := by
        rw [hLdef]; exact log_ge_one_of (by rw [le_div_iff₀ hδ0]; linarith [hbig hM1])
      have hx : 1 ≤ (H : ℝ) ^ 3 * L / ε ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        have h1 : ε ^ 2 ≤ (H : ℝ) ^ 2 := pow_le_pow_left₀ hε.le hεH 2
        have h2 : (H : ℝ) ^ 2 ≤ (H : ℝ) ^ 3 := pow_le_pow_right₀ hHr (by norm_num)
        have h3 : (H : ℝ) ^ 3 ≤ (H : ℝ) ^ 3 * L := le_mul_of_one_le_right (by positivity) hL1
        linarith
      have hT2 : (al.T : ℝ) ≤ 2002 * ((H : ℝ) ^ 3 * L / ε ^ 2) := by
        have : 2000 * (H : ℝ) ^ 3 * L / ε ^ 2 = 2000 * ((H : ℝ) ^ 3 * L / ε ^ 2) := by ring
        linarith
      have hHS : (0 : ℝ) ≤ H * S := by positivity
      have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT2 hHS) hM0
      refine h1.trans (le_of_eq ?_)
      ring
  · intro P
    have hrew' : al.RewOK := fun i h s a h1 h2 => hrewal ▸ hrew i h s a h1 h2
    have hgood := al.good_prob (G := (⟨P, rew⟩ : MarkovGame m S H A)) hrew' hη
      hη.le (by linarith) L
    -- the failure budget
    have hcard : (Fintype.card al.Ev : ℝ) * Real.exp (-L) ≤ δ := by
      have hc : (Fintype.card al.Ev : ℝ) = H * S * M + H * S * m * 3 := by
        simp only [Alg.Ev, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
        push_cast
        rw [hM]; ring
      rw [hc]
      rcases hcases with h0 | hM1
      · rw [h0.1, h0.2]; simp; linarith
      · have harg : 0 < 4 * H * S * M / δ := by positivity
        have hexp : Real.exp (-L) = δ / (4 * H * S * M) := by
          rw [Real.exp_neg, hLdef, Real.exp_log harg, inv_div]
        rw [hexp, mul_div_assoc', div_le_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ H * S * 3 * δ := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hmM' this]
    refine le_trans (by linarith) (le_trans hgood (sum_le_sum fun hist _ => ?_))
    refine mul_le_mul_of_nonneg_left ?_ ((interactionLaw al.rule _ al.N).prob_nonneg hist)
    by_cases hg : al.Good (⟨P, rew⟩ : MarkovGame m S H A) al.η L hist
    · rw [if_pos hg, if_pos]
      have hb := al.gapJ_le_of_good (⟨P, rew⟩ : MarkovGame m S H A) hrewal.symm hrew' hη hg
        hHn hηH hL0 hlog
      have ha := gap_arith hHr hε hεH hL0 hTr hTL
      rw [hηdef] at hb
      linarith
    · rw [if_neg hg]; split_ifs <;> norm_num

end StatisticalRL.Ch7Rest.Marl77
