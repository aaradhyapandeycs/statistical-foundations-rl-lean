import Formalization.Online.Bandit.UCBCountBound
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Theorem 5.1 (`thm:bandit-pure-ucb`): regret of UCB

`chapters/bandits.tex:258–277`, proof `:387–501`. Regret decomposition (`:79–82`), Step 3
(instance-dependent bound, `:455–467`) and Step 4 (worst-case bound, `:470–501`) on top of the
repaired per-arm bound `E N_T(a) ≤ 8L/Δ(a)² + 2` of `UCBCountBound`.
-/

open MeasureTheory ProbabilityTheory Finset

noncomputable section

namespace StatisticalRL.Bandit

variable {A : ℕ}

/-- Theorem 5.1 (`thm:bandit-pure-ucb`, `chapters/bandits.tex:258–277`): for the UCB algorithm
(Algorithm 5.1, with index `⊤` for unpulled arms and any round-dependent selection rule inside
the argmax) on the round-indexed `N(0,1)` noise table, with means in `[0,1]`, `0 < δ < 1` and
`2 ≤ A ≤ T`, the pseudo-regret `T r⋆ - Σ_t r(a_t)` is integrable and its expectation satisfies
(5.1a) `≤ 8 √(A T log(T²/δ))` and (5.1b) `≤ 10 log(T²/δ) Σ_{Δ(a)>0} 1/Δ(a)`. -/
theorem ucb_regret_bounds (A T : ℕ) (r : Fin A → ℝ) (δ : ℝ)
    (tie : ℕ → Finset (Fin A) → Fin A) (htie : ∀ t s, s.Nonempty → tie t s ∈ s)
    (hA : 2 ≤ A) (hAT : A ≤ T) (hr : ∀ a, r a ∈ Set.Icc (0 : ℝ) 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    let L := Real.log ((T : ℝ) ^ 2 / δ)
    let rstar := ⨆ a, r a
    let Δ := fun a => rstar - r a
    let regret := fun z : Fin T → Fin A → ℝ => (T : ℝ) * rstar - ∑ t, r (ucbAction tie L r z t)
    Integrable regret (gaussianNoiseTable T A) ∧
    ∫ z, regret z ∂gaussianNoiseTable T A ≤ 8 * Real.sqrt (A * T * L) ∧
    ∫ z, regret z ∂gaussianNoiseTable T A
      ≤ 10 * L * ∑ a ∈ univ.filter (fun a => 0 < Δ a), 1 / Δ a := by
  classical
  intro L rstar Δ regret
  haveI : NeZero A := ⟨by omega⟩
  set μ := gaussianNoiseTable T A
  have hT : 2 ≤ T := le_trans hA hAT
  have hTpos : (0 : ℝ) < T := by exact_mod_cast (show 0 < T by omega)
  have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
  have hATr : (A : ℝ) ≤ T := by exact_mod_cast hAT
  -- `L ≥ 1`
  have hL1 : 1 ≤ L := by
    have h4 : (4 : ℝ) ≤ (T : ℝ) ^ 2 / δ := by
      rw [le_div_iff₀ hδ0]
      have : (2 : ℝ) ≤ T := by exact_mod_cast hT
      nlinarith
    have hlog4 : 1 < Real.log 4 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      linarith
    exact le_trans hlog4.le (Real.log_le_log (by norm_num) h4)
  have hL0 : 0 ≤ L := by linarith
  -- optimal arm
  obtain ⟨astar, hastar⟩ := exists_eq_ciSup_of_finite (f := r)
  have hle : ∀ a, r a ≤ rstar := fun a => le_ciSup (Finite.bddAbove_range r) a
  have hΔ0 : ∀ a, 0 ≤ Δ a := fun a => sub_nonneg.mpr (hle a)
  have hΔ1 : ∀ a, Δ a ≤ 1 := by
    intro a
    have h1 := (hr astar).2; have h2 := (hr a).1
    simp only [Δ, rstar, ← hastar]; linarith
  -- counts
  let N : Fin A → (Fin T → Fin A → ℝ) → ℝ := fun a z =>
    (ucbCount tie L r (extendNoise z) T a : ℝ)
  have hNint : ∀ a, Integrable (N a) μ := fun a => integrable_count_real tie r L T a
  have hN0 : ∀ a, 0 ≤ ∫ z, N a z ∂μ := fun a => integral_nonneg (fun z => Nat.cast_nonneg _)
  have hNsum : ∑ a, ∫ z, N a z ∂μ = T := by
    rw [← integral_finset_sum _ (fun a _ => hNint a)]
    have : ∀ z, ∑ a, N a z = T := by
      intro z
      simp only [N]
      rw [← Nat.cast_sum, sum_ucbCount]
    simp_rw [this]
    simp
  have hNa : ∀ a, 0 < Δ a → ∫ z, N a z ∂μ ≤ 8 * L / Δ a ^ 2 + 2 := by
    intro a ha
    have hΔa : Δ a = r astar - r a := by simp only [Δ, rstar, ← hastar]
    rw [hΔa] at ha ⊢
    exact ucb_expected_count_le tie r htie (by omega) hδ0 hδ1.le a astar ha
  -- regret decomposition
  have hdecomp : ∀ z, regret z = ∑ a, Δ a * N a z := by
    intro z
    simp only [regret, Δ, N, ucbAction]
    simp_rw [ucbCount_eq_sum]
    push_cast
    simp_rw [mul_sum]
    rw [sum_comm]
    rw [Fin.sum_univ_eq_sum_range (fun s => r (ucbArm tie L r (extendNoise z) s)) T]
    have : ∀ s, ∑ a, (rstar - r a) * (if ucbArm tie L r (extendNoise z) s = a then (1 : ℝ) else 0)
        = rstar - r (ucbArm tie L r (extendNoise z) s) := by
      intro s
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [sum_ite_eq]; simp
    simp_rw [this]
    rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  have hregint : Integrable regret μ := by
    have : regret = fun z => ∑ a, Δ a * N a z := funext hdecomp
    rw [this]
    exact integrable_finset_sum _ (fun a _ => (hNint a).const_mul _)
  have hER : ∫ z, regret z ∂μ = ∑ a, Δ a * ∫ z, N a z ∂μ := by
    simp_rw [hdecomp]
    rw [integral_finset_sum _ (fun a _ => (hNint a).const_mul _)]
    simp_rw [integral_const_mul]
  refine ⟨hregint, ?_, ?_⟩
  · -- (5.1a), Step 4
    set s := Real.sqrt (A * T * L) with hs
    have hs2 : s ^ 2 = A * T * L := Real.sq_sqrt (by positivity)
    have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
    have hAs : (A : ℝ) ≤ s := by
      rw [hs]; apply Real.le_sqrt_of_sq_le
      have h1 := mul_le_mul_of_nonneg_left hATr hApos.le
      have h2 := mul_le_mul_of_nonneg_left hL1 (by positivity : (0 : ℝ) ≤ A * T)
      nlinarith
    set D := 2 * s / T with hD
    have hDpos : 0 < D := by positivity
    have hper : ∀ a, Δ a * ∫ z, N a z ∂μ ≤ 8 * L / D + 2 + D * ∫ z, N a z ∂μ := by
      intro a
      by_cases hbig : D ≤ Δ a
      · have ha : 0 < Δ a := lt_of_lt_of_le hDpos hbig
        have h1 := hNa a ha
        calc Δ a * ∫ z, N a z ∂μ ≤ Δ a * (8 * L / Δ a ^ 2 + 2) :=
              mul_le_mul_of_nonneg_left h1 ha.le
          _ = 8 * L / Δ a + 2 * Δ a := by field_simp
          _ ≤ 8 * L / D + 2 := by
              have : 8 * L / Δ a ≤ 8 * L / D := div_le_div_of_nonneg_left (by positivity) hDpos hbig
              linarith [hΔ1 a]
          _ ≤ 8 * L / D + 2 + D * ∫ z, N a z ∂μ := by
              have := mul_nonneg hDpos.le (hN0 a); linarith
      · have : Δ a * ∫ z, N a z ∂μ ≤ D * ∫ z, N a z ∂μ :=
          mul_le_mul_of_nonneg_right (le_of_not_ge hbig) (hN0 a)
        have : 0 ≤ 8 * L / D := by positivity
        linarith
    rw [hER]
    calc ∑ a, Δ a * ∫ z, N a z ∂μ ≤ ∑ a, (8 * L / D + 2 + D * ∫ z, N a z ∂μ) := sum_le_sum
          (fun a _ => hper a)
      _ = A * (8 * L / D) + 2 * A + D * T := by
          rw [sum_add_distrib, ← mul_sum, hNsum, sum_const, card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
      _ = 4 * s + 2 * A + 2 * s := by
          have hTne : (T : ℝ) ≠ 0 := hTpos.ne'
          rw [hD]
          field_simp
          nlinarith [hs2]
      _ ≤ 8 * s := by linarith
  · -- (5.1b), Step 3
    rw [hER]
    have hsplit : ∑ a, Δ a * ∫ z, N a z ∂μ
        = ∑ a ∈ univ.filter (fun a => 0 < Δ a), Δ a * ∫ z, N a z ∂μ := by
      rw [sum_filter_of_ne]
      intro a _ hne
      by_contra hneg
      have : Δ a = 0 := le_antisymm (le_of_not_gt hneg) (hΔ0 a)
      rw [this, zero_mul] at hne; exact hne rfl
    rw [hsplit, mul_sum]
    apply sum_le_sum
    intro a ha
    have ha' : 0 < Δ a := (mem_filter.mp ha).2
    have h1 := hNa a ha'
    calc Δ a * ∫ z, N a z ∂μ ≤ Δ a * (8 * L / Δ a ^ 2 + 2) :=
          mul_le_mul_of_nonneg_left h1 ha'.le
      _ = 8 * L / Δ a + 2 * Δ a := by field_simp
      _ ≤ 8 * L / Δ a + 2 * L / Δ a := by
          have : 2 * Δ a ≤ 2 * L / Δ a := by
            rw [le_div_iff₀ ha']
            nlinarith [hΔ1 a]
          linarith
      _ = 10 * L * (1 / Δ a) := by field_simp; ring

end StatisticalRL.Bandit
