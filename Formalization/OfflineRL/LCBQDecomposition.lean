import Formalization.OfflineRL.LCBQLemma612

/-!
# LCB-Q: the error decomposition of Theorem 6.8 (Steps 3–4)

`theorem:lcbq`, proof Steps 3–4, `chapters/offlineRL.tex:1938–2276`.

Deterministic results on the event where Lemma 6.9(a) holds and pessimism (Lemma 6.10) holds:

* `Δ_t(s) ≤ γ F_t(s,π⋆(s)) + min{β_{n_t(s,π⋆(s))}, 1/(1-γ)}` (`eq:first_step_rewrite`);
* the visit regrouping `eq:visit-regrouping-zeta0-offlineQ`–`eq:zeta0-visit-bound-offlineQ`,
  using `Σ_{m ≥ i} η_i^m = 1 + 1/H`;
* the one-step flow `Σ_s [ρᵀP^j](s) P_{s,π⋆(s)} f = ρᵀP^{j+1} f`;
* `α_j ≤ α_{j+1} + ξ_j + θ_j + ψ_j + φ_j` (`eq:alpha-recursion-offlineQ`) and its iteration
  `α_0 ≤ ξ + θ + ψ + φ` (`eq:alpha0-five-terms-offlineQ`, with `α = lim α_j = 0`);
* `V⋆(ρ) − V^{π̂}(ρ) ≤ α_0/T` (`eq:performance-to-alpha0`).
-/

open scoped BigOperators ENNReal
open Filter Topology MeasureTheory ProbabilityTheory

namespace StatisticalRL.OfflineRL.LCBQ

open StatisticalRL StatisticalRL.OnlineRL
open Classical

set_option linter.unusedSectionVars false

variable {S A : Type*} [Fintype S] [Fintype A]

section Regroup

/-- `Σ_{m<N} Σ_{i≤m} η_{i+1}^{m+1} x_i ≤ (1 + 1/H) Σ_{i<N} x_i` for `x ≥ 0`
(`eq:visit-regrouping-zeta0-offlineQ` with `Σ_{m≥i} η_i^m = 1 + 1/H`). -/
theorem triangle_rate_le {H : ℕ} (hH : 0 < H) (N : ℕ) (x : ℕ → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ m ∈ Finset.range N, ∑ i ∈ Finset.range (m + 1), onlineQRateWeight H (m + 1) (i + 1) * x i ≤
      (1 + 1 / (H : ℝ)) * ∑ i ∈ Finset.range N, x i := by
  rw [Finset.sum_comm' (t' := Finset.range N) (s' := fun i => Finset.Ico i N) (by
    intro m i
    simp only [Finset.mem_range, Finset.mem_Ico]
    omega)]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => ?_
  rw [← Finset.sum_mul, mul_comm, mul_comm (1 + 1 / (H : ℝ))]
  apply mul_le_mul_of_nonneg_left _ (hx i)
  obtain ⟨hsum, htsum⟩ := onlineQRateWeight_tail_sum H (i + 1) hH (by omega)
  rw [Finset.sum_Ico_eq_sum_range]
  calc ∑ k ∈ Finset.range (N - i), onlineQRateWeight H (i + k + 1) (i + 1)
      = ∑ k ∈ Finset.range (N - i), onlineQRateWeight H (i + 1 + k) (i + 1) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show i + k + 1 = i + 1 + k by omega]
    _ ≤ ∑' k : ℕ, onlineQRateWeight H (i + 1 + k) (i + 1) :=
        hsum.sum_le_tsum _ (fun k _ => onlineQRateWeight_nonneg hH _ _)
    _ = 1 + 1 / (H : ℝ) := htsum

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  {T : ℕ} (data : Fin T → (S × A) × S)

/-- Sum over samples regrouped by label. -/
theorem sum_by_label (g : S × A → Fin T → ℝ) :
    ∑ u : Fin T, g (data u).1 u = ∑ p : S × A, ∑ u : Fin T, (if (data u).1 = p then g p u else 0) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_ite_eq]
  simp

/-- The per-pair visit regrouping (`eq:zeta0-visit-bound-offlineQ`): under pessimism,
`Σ_{t : (s_t,a_t)=p} F_t(p) ≤ (1+1/H) Σ_{t : (s_t,a_t)=p} P_p Δ_{t-1}`. -/
theorem visit_regroup_pair (hcb : 0 ≤ cb) (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hpess : ∀ u, u ≤ T → ∀ s, (run M cb δ sel π₀ data u).V s ≤ optValue M s) (p : S × A) :
    ∑ u : Fin T, (if (data u).1 = p then
        visitDeltaSum M cb δ sel π₀ data (u.val + 1) p.1 p.2 else 0) ≤
      (1 + 1 / (horizon M.discount (iota S A T δ) : ℝ)) *
        ∑ u : Fin T, (if (data u).1 = p then
          (M.transition p.1 p.2).expectation (delta M cb δ sel π₀ data u.val) else 0) := by
  set H := horizon M.discount (iota S A T δ) with hHdef
  have hH := horizon_pos M hT hδ hδ1
  set N := Nat.count (visitPred data p) T with hN
  set x : ℕ → ℝ := fun i =>
    (M.transition p.1 p.2).expectation (delta M cb δ sel π₀ data (visitTime data p i)) with hx
  have hx0 : ∀ i, i < N → 0 ≤ x i := by
    intro i hi
    have hlt := visitTime_lt data hi
    apply FiniteDistribution.expectation_nonneg
    intro y
    have := hpess _ hlt.le y
    simp only [delta]; linarith
  -- the label of a visit has rank below `N`
  have hrank : ∀ u : Fin T, (data u).1 = p → Nat.count (visitPred data p) u.val < N := by
    intro u hu
    exact Nat.count_strict_mono ⟨u.isLt, hu⟩ u.isLt
  have hcnt : ∀ u : Fin T, (data u).1 = p →
      (run M cb δ sel π₀ data (u.val + 1)).count p.1 p.2 =
        Nat.count (visitPred data p) u.val + 1 := by
    intro u hu
    rw [run_count M cb δ sel π₀ data u.isLt, Nat.count_succ, if_pos ⟨u.isLt, hu⟩]
  set G : ℕ → ℝ := fun m => ∑ i ∈ Finset.range (m + 1),
    onlineQRateWeight H (m + 1) (i + 1) * x i with hG
  have hL : ∑ u : Fin T, (if (data u).1 = p then
        visitDeltaSum M cb δ sel π₀ data (u.val + 1) p.1 p.2 else 0) =
      ∑ u : Fin T, (if (data u).1 = p ∧ Nat.count (visitPred data p) u.val < N then
        G (Nat.count (visitPred data p) u.val) else 0) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : (data u).1 = p
    · rw [if_pos hu, if_pos ⟨hu, hrank u hu⟩]
      simp only [visitDeltaSum, hcnt u hu, hG, hx, ← hHdef]
    · rw [if_neg hu, if_neg (fun h => hu h.1)]
  have hR : ∑ u : Fin T, (if (data u).1 = p then
        (M.transition p.1 p.2).expectation (delta M cb δ sel π₀ data u.val) else 0) =
      ∑ u : Fin T, (if (data u).1 = p ∧ Nat.count (visitPred data p) u.val < N then
        (M.transition p.1 p.2).expectation (delta M cb δ sel π₀ data u.val) else 0) := by
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : (data u).1 = p
    · rw [if_pos hu, if_pos ⟨hu, hrank u hu⟩]
    · rw [if_neg hu, if_neg (fun h => hu h.1)]
  have h1 := sum_fin_visits_eq data p N le_rfl (fun m _ => G m)
  have h2 := sum_fin_visits_eq data p N le_rfl
    (fun _ u => (M.transition p.1 p.2).expectation (delta M cb δ sel π₀ data u.val))
  simp only at h1 h2
  rw [hL, hR, h1, h2]
  have hvt : ∀ i ∈ Finset.range N, visitTime data p i < T := fun i hi =>
    visitTime_lt data (Finset.mem_range.1 hi)
  have eL : ∀ i ∈ Finset.range N, (if _h : visitTime data p i < T then G i else 0) = G i :=
    fun i hi => dif_pos (hvt i hi)
  have eR : ∀ i ∈ Finset.range N, (if h : visitTime data p i < T then
      (M.transition p.1 p.2).expectation
        (delta M cb δ sel π₀ data (⟨visitTime data p i, h⟩ : Fin T).val) else 0) = x i :=
    fun i hi => by rw [dif_pos (hvt i hi)]
  rw [Finset.sum_congr rfl eL, Finset.sum_congr rfl eR]
  simp only [hG]
  -- extend `x` by zero beyond `N` to apply the triangle bound
  set x' : ℕ → ℝ := fun i => if i < N then x i else 0 with hx'
  have hx'0 : ∀ i, 0 ≤ x' i := fun i => by
    simp only [hx']; split_ifs with h
    · exact hx0 i h
    · exact le_rfl
  have htri := triangle_rate_le hH N x' hx'0
  have e1 : ∑ m ∈ Finset.range N, ∑ i ∈ Finset.range (m + 1),
      onlineQRateWeight H (m + 1) (i + 1) * x' i =
      ∑ m ∈ Finset.range N, ∑ i ∈ Finset.range (m + 1), onlineQRateWeight H (m + 1) (i + 1) * x i := by
    refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun i hi => ?_
    have : i < N := by
      have := Finset.mem_range.1 hm; have := Finset.mem_range.1 hi; omega
    simp only [hx', if_pos this]
  have e2 : ∑ i ∈ Finset.range N, x' i = ∑ i ∈ Finset.range N, x i :=
    Finset.sum_congr rfl fun i hi => by simp only [hx', if_pos (Finset.mem_range.1 hi)]
  rw [e1, e2] at htri
  exact htri

end Regroup

section Steps

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  {T : ℕ} (data : Fin T → (S × A) × S) (ρ : FiniteDistribution S) (πstar : S → A)
  (db : FiniteDistribution (S × A))

/-- One-step flow along `π⋆`: `Σ_s [ρᵀP^j](s) P_{s,π⋆(s)} f = Σ_{s'} [ρᵀP^{j+1}](s') f(s')`. -/
theorem occ_flow (j : ℕ) (f : S → ℝ) :
    ∑ s, M.occupancyStateAt (detPolicy πstar) ρ j s * (M.transition s (πstar s)).expectation f =
      ∑ s', M.occupancyStateAt (detPolicy πstar) ρ (j + 1) s' * f s' := by
  simp_rw [M.occupancyStateAt_succ, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold FiniteDistribution.expectation
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [M.policyTransition_prob]
  simp only [detPolicy, EnvironmentStage.expectation_pointMass]
  ring

/-- `Σ_{s,a} d_j(s,a) g(s,a) = Σ_s [ρᵀP^j](s) g(s,π⋆(s))`. -/
theorem sum_dWeight (j : ℕ) (g : S → A → ℝ) :
    ∑ s, ∑ a, dWeight M ρ πstar j s a * g s a =
      ∑ s, M.occupancyStateAt (detPolicy πstar) ρ j s * g s (πstar s) := by
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sum_action_collapse πstar (fun s a => dWeight M ρ πstar j s a * g s a)
    (fun s a ha => by
      show dWeight M ρ πstar j s a * g s a = 0
      rw [dWeight_of_ne M ρ πstar j s a ha, zero_mul]) s]
  simp [dWeight]

/-- `eq:first_step_rewrite`, pointwise: on the Lemma 6.9(a) event and under pessimism,
`Δ_t(s) ≤ γ F_t(s,π⋆(s)) + min{β_{n_t(s,π⋆(s))}, 1/(1-γ)}` for `1 ≤ t ≤ T`. -/
theorem delta_le_visit (hcb : 0 ≤ cb) (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hopt : ∀ s, letI : Nonempty A := M.action_nonempty
      M.optimalityFixedPoint s (πstar s) = actionMaximum (M.optimalityFixedPoint s))
    (hup : upperRecursion M cb δ sel π₀ data)
    (hpess : ∀ u, u ≤ T → ∀ s, (run M cb δ sel π₀ data u).V s ≤ optValue M s)
    {t : ℕ} (ht1 : 1 ≤ t) (htT : t ≤ T) (s : S) :
    delta M cb δ sel π₀ data t s ≤
      M.discount * visitDeltaSum M cb δ sel π₀ data t s (πstar s) +
        betaTrunc cb M.discount (iota S A T δ) (horizon M.discount (iota S A T δ))
          ((run M cb δ sel π₀ data t).count s (πstar s)) := by
  letI : Nonempty A := M.action_nonempty
  have hF := visitDeltaSum_bounds M cb δ sel π₀ data hcb hT hδ hδ1 htT
    (fun v hv s => hpess v (by omega) s) s (πstar s)
  have hγF : 0 ≤ M.discount * visitDeltaSum M cb δ sel π₀ data t s (πstar s) :=
    mul_nonneg M.discount_nonneg hF.1
  have hc := delta_le M cb δ sel π₀ data hcb t s
  have hstar : optValue M s = M.optimalityFixedPoint s (πstar s) := by
    unfold optValue; rw [optValue_eq, hopt s]
  have hV : (run M cb δ sel π₀ data t).Q s (πstar s) ≤ (run M cb δ sel π₀ data t).V s :=
    (le_actionMaximum _ _).trans (actionMaximum_le_run_V M cb δ sel π₀ data t s)
  unfold betaTrunc
  split_ifs with hn
  · linarith
  · have hpos : 0 < (run M cb δ sel π₀ data t).count s (πstar s) := Nat.pos_of_ne_zero hn
    have hu := hup t ht1 htT s (πstar s) hpos
    have hdef : visitDeltaSum M cb δ sel π₀ data t s (πstar s) =
        ∑ i ∈ Finset.range ((run M cb δ sel π₀ data t).count s (πstar s)),
          onlineQRateWeight (horizon M.discount (iota S A T δ))
            ((run M cb δ sel π₀ data t).count s (πstar s)) (i + 1) *
            (M.transition s (πstar s)).expectation (fun s' =>
              M.trajectoryExpectedValue M.optimalGreedyPolicy s' -
                (run M cb δ sel π₀ data (visitTime data (s, πstar s) i)).V s') := rfl
    rw [← hdef] at hu
    have hΔ : delta M cb δ sel π₀ data t s ≤
        M.optimalityFixedPoint s (πstar s) - (run M cb δ sel π₀ data t).Q s (πstar s) := by
      unfold delta; rw [hstar]; linarith
    rcases le_total (3 * cb * Real.sqrt (horizon M.discount (iota S A T δ) * iota S A T δ /
        ((run M cb δ sel π₀ data t).count s (πstar s) * (1 - M.discount) ^ 2)))
        (1 / (1 - M.discount)) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith

end Steps

section AlphaStep

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  {T : ℕ} (data : Fin T → (S × A) × S) (ρ : FiniteDistribution S) (πstar : S → A)
  (db : FiniteDistribution (S × A))

theorem sum_Icc_eq_sum_fin (g : ℕ → ℝ) : ∑ t ∈ Finset.Icc 1 T, g t = ∑ u : Fin T, g (u.val + 1) := by
  rw [sum_Icc_one_eq_sum_range, ← Fin.sum_univ_eq_sum_range (fun u => g (u + 1))]

set_option maxHeartbeats 2000000 in
/-- `α_j ≤ α_{j+1} + ξ_j + θ_j + ψ_j + φ_j` (`eq:alpha-recursion-offlineQ`). -/
theorem alpha_step (hcb : 0 ≤ cb) (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hopt : ∀ s, letI : Nonempty A := M.action_nonempty
      M.optimalityFixedPoint s (πstar s) = actionMaximum (M.optimalityFixedPoint s))
    (hup : upperRecursion M cb δ sel π₀ data)
    (hpess : ∀ u, u ≤ T → ∀ s, (run M cb δ sel π₀ data u).V s ≤ optValue M s) (j : ℕ) :
    alphaSeq M cb δ sel π₀ data ρ πstar j ≤
      alphaSeq M cb δ sel π₀ data ρ πstar (j + 1) + xiSeq M cb δ sel π₀ data ρ πstar j +
        thetaSeq M cb δ sel π₀ data ρ πstar j + psiSeq M cb δ sel π₀ data ρ πstar db j +
        phiSeq M cb δ sel π₀ data ρ πstar db j := by
  set H := horizon M.discount (iota S A T δ) with hHdef
  set κ := kappa M.discount H with hκ
  set c := 1 + 1 / (H : ℝ) with hc
  set γ := M.discount with hγ
  have hκ0 : 0 ≤ κ := kappa_nonneg M _
  have hγ0 : 0 ≤ γ := M.discount_nonneg
  have hHpos := horizon_pos M hT hδ hδ1
  have hc1 : 1 ≤ c := (one_le_c_le_two hHpos).1
  have hκc : κ = γ * c ^ 3 := rfl
  set w : S → ℝ := fun s => M.occupancyStateAt (detPolicy πstar) ρ j s with hw
  set w' : S → ℝ := fun s => M.occupancyStateAt (detPolicy πstar) ρ (j + 1) s with hw'
  have hw0 : ∀ s, 0 ≤ w s := fun s => M.occupancyStateAt_nonneg _ _ _ _
  have hw'0 : ∀ s, 0 ≤ w' s := fun s => M.occupancyStateAt_nonneg _ _ _ _
  set F : ℕ → S → A → ℝ := fun t s a => visitDeltaSum M cb δ sel π₀ data t s a with hF
  set Δ : ℕ → S → ℝ := fun t s => delta M cb δ sel π₀ data t s with hΔ
  set PD : ℕ → S → A → ℝ := fun u s a => (M.transition s a).expectation (Δ u) with hPD
  set W : ℕ → S → ℝ := fun t s => betaTrunc cb γ (iota S A T δ) H
    ((run M cb δ sel π₀ data t).count s (πstar s)) with hW
  set r : S × A → ℝ := fun p => dWeight M ρ πstar j p.1 p.2 / db.prob p with hr
  have hr0 : ∀ p, 0 ≤ r p := fun p => div_nonneg (dWeight_nonneg M ρ πstar j _ _) (db.prob_nonneg _)
  -- the five named sums
  set Z := ∑ u : Fin T, ∑ s, ∑ a, dWeight M ρ πstar j s a * F (u.val + 1) s a with hZ
  set X := ∑ u : Fin T, r (data u).1 * F (u.val + 1) (data u).1.1 (data u).1.2 with hX
  set Y := ∑ u : Fin T, r (data u).1 * PD u.val (data u).1.1 (data u).1.2 with hY
  set Q := ∑ u : Fin T, ∑ s', w' s' * Δ u.val s' with hQ
  -- (a) the first-step rewrite
  have hα : alphaSeq M cb δ sel π₀ data ρ πstar j ≤
      κ ^ j * γ * Z + thetaSeq M cb δ sel π₀ data ρ πstar j := by
    have hpt : ∀ u : Fin T, ∑ s, w s * Δ (u.val + 1) s ≤
        γ * ∑ s, ∑ a, dWeight M ρ πstar j s a * F (u.val + 1) s a + ∑ s, w s * W (u.val + 1) s := by
      intro u
      rw [sum_dWeight M ρ πstar j, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun s _ => ?_
      have := delta_le_visit M cb δ sel π₀ data πstar hcb hT hδ hδ1 hopt hup hpess
        (t := u.val + 1) (by omega) u.isLt s
      have h := mul_le_mul_of_nonneg_left this (hw0 s)
      simp only [hw, hF, hW, hΔ] at h ⊢
      linarith [h]
    have hθ : thetaSeq M cb δ sel π₀ data ρ πstar j = κ ^ j * ∑ u : Fin T, ∑ s, w s * W (u.val + 1) s := by
      simp only [thetaSeq]
      rw [sum_Icc_eq_sum_fin (fun t => ∑ s, M.occupancyStateAt (detPolicy πstar) ρ j s *
        betaTrunc cb M.discount (iota S A T δ) (horizon M.discount (iota S A T δ))
          ((run M cb δ sel π₀ data t).count s (πstar s)))]
    have hαd : alphaSeq M cb δ sel π₀ data ρ πstar j = κ ^ j * ∑ u : Fin T, ∑ s, w s * Δ (u.val + 1) s := by
      simp only [alphaSeq]
      rw [sum_Icc_eq_sum_fin (fun t => ∑ s, M.occupancyStateAt (detPolicy πstar) ρ j s *
        delta M cb δ sel π₀ data t s)]
    rw [hαd, hθ]
    have hs := Finset.sum_le_sum fun u (_ : u ∈ (Finset.univ : Finset (Fin T))) => hpt u
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
    have := mul_le_mul_of_nonneg_left hs (pow_nonneg hκ0 j)
    linarith
  -- (b) ψ_j
  have hψ : psiSeq M cb δ sel π₀ data ρ πstar db j = γ * κ ^ j * Z - γ * κ ^ j * c * X := by
    simp only [psiSeq]
    rw [← hHdef, ← hκ, ← hc, Finset.sum_sub_distrib, mul_sub]
    congr 1
    rw [mul_assoc, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [hr, hF]
    ring
  -- (c) regrouping
  have hXY : X ≤ c * Y := by
    have hX' : X = ∑ p : S × A, r p * ∑ u : Fin T, (if (data u).1 = p then
        F (u.val + 1) p.1 p.2 else 0) := by
      rw [hX, sum_by_label data (fun p u => r p * F (u.val + 1) p.1 p.2)]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      split_ifs <;> simp
    have hY' : Y = ∑ p : S × A, r p * ∑ u : Fin T, (if (data u).1 = p then
        PD u.val p.1 p.2 else 0) := by
      rw [hY, sum_by_label data (fun p u => r p * PD u.val p.1 p.2)]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      split_ifs <;> simp
    rw [hX', hY', Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    have h := visit_regroup_pair M cb δ sel π₀ data hcb hT hδ hδ1 hpess p
    have := mul_le_mul_of_nonneg_left h (hr0 p)
    simp only [hF, hPD, hΔ] at this ⊢
    linarith
  -- (d) φ_j and the flow
  have hφ : phiSeq M cb δ sel π₀ data ρ πstar db j = γ * κ ^ j * c ^ 2 * Y - κ ^ (j + 1) * Q := by
    simp only [phiSeq]
    rw [← hHdef, ← hκ, ← hc, Finset.sum_sub_distrib, mul_sub]
    congr 1
    rw [hQ, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hflow := occ_flow M ρ πstar j (Δ u.val)
    rw [← sum_dWeight M ρ πstar j (fun s a => PD u.val s a)] at hflow
    simp only [hPD, hΔ] at hflow
    simp only [hw']
    rw [← hflow, hκc, pow_succ]
    ring
  -- (e) the time shift
  have hQle : Q ≤ ∑ s', w' s' * Δ 0 s' + ∑ u : Fin T, ∑ s', w' s' * Δ (u.val + 1) s' := by
    have hT0 : 0 ≤ ∑ s', w' s' * Δ T s' := Finset.sum_nonneg fun s' _ => mul_nonneg (hw'0 s') (by
      have := hpess T le_rfl s'
      simp only [hΔ, delta]; linarith)
    have e1 : Q = ∑ u ∈ Finset.range T, ∑ s', w' s' * Δ u s' := by
      rw [hQ, Fin.sum_univ_eq_sum_range (fun u => ∑ s', w' s' * Δ u s')]
    have e2 : ∑ u : Fin T, ∑ s', w' s' * Δ (u.val + 1) s' =
        ∑ u ∈ Finset.range T, ∑ s', w' s' * Δ (u + 1) s' := by
      rw [Fin.sum_univ_eq_sum_range (fun u => ∑ s', w' s' * Δ (u + 1) s')]
    have e3 := Finset.sum_range_succ (fun u => ∑ s', w' s' * Δ u s') T
    have e4 := Finset.sum_range_succ' (fun u => ∑ s', w' s' * Δ u s') T
    rw [e1, e2]
    linarith
  have hξ : xiSeq M cb δ sel π₀ data ρ πstar j = κ ^ (j + 1) * ∑ s', w' s' * Δ 0 s' := rfl
  have hα1 : alphaSeq M cb δ sel π₀ data ρ πstar (j + 1) =
      κ ^ (j + 1) * ∑ u : Fin T, ∑ s', w' s' * Δ (u.val + 1) s' := by
    simp only [alphaSeq]
    rw [sum_Icc_eq_sum_fin (fun t => ∑ s, M.occupancyStateAt (detPolicy πstar) ρ (j + 1) s *
      delta M cb δ sel π₀ data t s)]
  -- assemble
  have hγκ : 0 ≤ γ * κ ^ j := mul_nonneg hγ0 (pow_nonneg hκ0 j)
  have h1 : γ * κ ^ j * c * X ≤ γ * κ ^ j * c ^ 2 * Y := by
    have := mul_le_mul_of_nonneg_left hXY (mul_nonneg hγκ (by linarith : (0 : ℝ) ≤ c))
    linarith
  have h2 := mul_le_mul_of_nonneg_left hQle (pow_nonneg hκ0 (j + 1))
  rw [hψ, hφ, hξ, hα1]
  linarith

end AlphaStep

section Iterate

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  {T : ℕ} (data : Fin T → (S × A) × S) (ρ : FiniteDistribution S) (πstar : S → A)
  (db : FiniteDistribution (S × A))

/-- `α_0 ≤ ξ + θ + ψ + φ` (`eq:alpha0-five-terms-offlineQ`, with `α = lim α_j = 0`). -/
theorem alpha0_le (hcb : 0 ≤ cb) (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hopt : ∀ s, letI : Nonempty A := M.action_nonempty
      M.optimalityFixedPoint s (πstar s) = actionMaximum (M.optimalityFixedPoint s))
    (hup : upperRecursion M cb δ sel π₀ data)
    (hpess : ∀ u, u ≤ T → ∀ s, (run M cb δ sel π₀ data u).V s ≤ optValue M s)
    (hα : Tendsto (alphaSeq M cb δ sel π₀ data ρ πstar) atTop (𝓝 0)) {ξ θ ψ φ : ℝ}
    (hξ : HasSum (xiSeq M cb δ sel π₀ data ρ πstar) ξ)
    (hθ : HasSum (thetaSeq M cb δ sel π₀ data ρ πstar) θ)
    (hψ : HasSum (psiSeq M cb δ sel π₀ data ρ πstar db) ψ)
    (hφ : HasSum (phiSeq M cb δ sel π₀ data ρ πstar db) φ) :
    alphaSeq M cb δ sel π₀ data ρ πstar 0 ≤ ξ + θ + ψ + φ := by
  set g : ℕ → ℝ := fun j => xiSeq M cb δ sel π₀ data ρ πstar j +
    thetaSeq M cb δ sel π₀ data ρ πstar j + psiSeq M cb δ sel π₀ data ρ πstar db j +
    phiSeq M cb δ sel π₀ data ρ πstar db j with hg
  have hgsum : HasSum g (ξ + θ + ψ + φ) := ((hξ.add hθ).add hψ).add hφ
  have hiter : ∀ N, alphaSeq M cb δ sel π₀ data ρ πstar 0 ≤
      alphaSeq M cb δ sel π₀ data ρ πstar N + ∑ j ∈ Finset.range N, g j := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      have := alpha_step M cb δ sel π₀ data ρ πstar db hcb hT hδ hδ1 hopt hup hpess N
      rw [Finset.sum_range_succ]
      simp only [hg]
      linarith
  have hlim : Tendsto (fun N => alphaSeq M cb δ sel π₀ data ρ πstar N + ∑ j ∈ Finset.range N, g j)
      atTop (𝓝 (0 + (ξ + θ + ψ + φ))) := hα.add hgsum.tendsto_sum_nat
  rw [zero_add] at hlim
  exact ge_of_tendsto' hlim hiter

/-- `V⋆(ρ) − V^{π_T}(ρ) ≤ α_0/T` (`eq:performance-to-alpha0`), under pessimism and
`V_T ≤ V^{π_T}` (Lemma 6.10). -/
theorem performance_le_alpha0 (hT : 1 ≤ T)
    (hpess : ∀ u, u ≤ T → ∀ s, (run M cb δ sel π₀ data u).V s ≤ optValue M s)
    (hVT : ∀ s, (run M cb δ sel π₀ data T).V s ≤
      M.trajectoryExpectedValue (detPolicy (run M cb δ sel π₀ data T).policy) s) :
    ρ.expectation (M.trajectoryExpectedValue M.optimalGreedyPolicy) -
        ρ.expectation (M.trajectoryExpectedValue (detPolicy (run M cb δ sel π₀ data T).policy)) ≤
      alphaSeq M cb δ sel π₀ data ρ πstar 0 / T := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  set D : S → ℝ := delta M cb δ sel π₀ data T with hD
  have h1 : ρ.expectation (M.trajectoryExpectedValue M.optimalGreedyPolicy) -
      ρ.expectation (M.trajectoryExpectedValue (detPolicy (run M cb δ sel π₀ data T).policy)) ≤
      ρ.expectation D := by
    rw [← FiniteDistribution.expectation_sub]
    apply ρ.expectation_mono
    intro s
    have := hVT s
    simp only [hD, delta, optValue]
    linarith
  have h2 : (T : ℝ) * ρ.expectation D ≤ alphaSeq M cb δ sel π₀ data ρ πstar 0 := by
    simp only [alphaSeq, pow_zero, one_mul]
    calc (T : ℝ) * ρ.expectation D = ∑ _t ∈ Finset.Icc 1 T, ρ.expectation D := by simp
      _ ≤ ∑ t ∈ Finset.Icc 1 T, ∑ s, M.occupancyStateAt (detPolicy πstar) ρ 0 s *
            delta M cb δ sel π₀ data t s := by
          refine Finset.sum_le_sum fun t ht => ?_
          rw [Finset.mem_Icc] at ht
          unfold FiniteDistribution.expectation
          refine Finset.sum_le_sum fun s _ => ?_
          rw [M.occupancyStateAt_zero]
          apply mul_le_mul_of_nonneg_left _ (ρ.prob_nonneg s)
          have := run_V_mono M cb δ sel π₀ data ht.2 s
          simp only [hD, delta]
          linarith
  rw [le_div_iff₀ hT']
  have h3 := mul_le_mul_of_nonneg_right h1 hT'.le
  linarith

end Iterate

section Strict

theorem inter_five_prob_strict {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ] {E₁ E₂ E₃ E₄ E₅ : Set Ω} {ε : ℝ}
    (h₁ : MeasurableSet E₁) (h₂ : MeasurableSet E₂) (h₃ : MeasurableSet E₃)
    (h₄ : MeasurableSet E₄) (h₅ : MeasurableSet E₅)
    (p₁ : 1 - ε < μ.real E₁) (p₂ : 1 - ε ≤ μ.real E₂) (p₃ : 1 - ε ≤ μ.real E₃)
    (p₄ : 1 - ε ≤ μ.real E₄) (p₅ : 1 - ε ≤ μ.real E₅) :
    1 - 5 * ε < μ.real (E₁ ∩ E₂ ∩ E₃ ∩ E₄ ∩ E₅) := by
  have hm : MeasurableSet (E₁ ∩ E₂ ∩ E₃ ∩ E₄ ∩ E₅) :=
    ((((h₁.inter h₂).inter h₃).inter h₄).inter h₅)
  have hc := MeasureTheory.probReal_compl_eq_one_sub (μ := μ) hm
  have hu : μ.real (E₁ ∩ E₂ ∩ E₃ ∩ E₄ ∩ E₅)ᶜ ≤
      μ.real E₁ᶜ + μ.real E₂ᶜ + μ.real E₃ᶜ + μ.real E₄ᶜ + μ.real E₅ᶜ := by
    simp only [Set.compl_inter]
    refine (MeasureTheory.measureReal_union_le _ _).trans ?_
    gcongr
    refine (MeasureTheory.measureReal_union_le _ _).trans ?_
    gcongr
    refine (MeasureTheory.measureReal_union_le _ _).trans ?_
    gcongr
    exact MeasureTheory.measureReal_union_le _ _
  rw [MeasureTheory.probReal_compl_eq_one_sub h₁, MeasureTheory.probReal_compl_eq_one_sub h₂,
    MeasureTheory.probReal_compl_eq_one_sub h₃, MeasureTheory.probReal_compl_eq_one_sub h₄,
    MeasureTheory.probReal_compl_eq_one_sub h₅] at hu
  linarith

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  (ρ : FiniteDistribution S) (πstar : S → A) (db : FiniteDistribution (S × A))

theorem upperRecursion_of_event_fifth {T : ℕ} (data : Fin T → (S × A) × S) (hcb : 4 ≤ cb)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hι : 1 ≤ iota S A T δ)
    (hE : martingaleEvent M cb δ sel π₀ data (δ / 5)) :
    upperRecursion M cb δ sel π₀ data := by
  have hcb0 : 0 ≤ cb := by linarith
  intro t ht1 htT s a hn
  have hT : 1 ≤ T := le_trans ht1 htT
  have hι0 := iota_pos M hT hδ hδ1
  have hH := horizon_pos M hT hδ hδ1
  have hid := error_identity M cb δ sel π₀ data hδ hδ1 htT s a hn
    (M.trajectoryExpectedValue M.optimalGreedyPolicy)
  rw [← optQ_eq_reward_add] at hid
  have hm := martSum_le_of_event_fifth M cb δ sel π₀ data hcb hδ hι hE htT s a hn
  have hp := (penalty_sum_bounds hcb0 M.discount_lt_one hι0.le hH hn).2
  have h3 : 3 * cb * Real.sqrt (horizon M.discount (iota S A T δ) * iota S A T δ /
      ((run M cb δ sel π₀ data t).count s a * (1 - M.discount) ^ 2)) =
      cb * Real.sqrt (horizon M.discount (iota S A T δ) * iota S A T δ /
        ((run M cb δ sel π₀ data t).count s a * (1 - M.discount) ^ 2)) +
      2 * (cb * Real.sqrt (horizon M.discount (iota S A T δ) * iota S A T δ /
        ((run M cb δ sel π₀ data t).count s a * (1 - M.discount) ^ 2))) := by ring
  have hm' := (abs_le.mp hm).1
  rw [hid, h3]
  linarith

set_option maxHeartbeats 1000000 in
theorem lemma612_events_strict (hcb : 4 ≤ cb) (T : ℕ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hι : 1 ≤ iota S A T δ) (hCs : concentrability M ρ πstar db ≠ ⊤) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] :
    letI : MeasurableSpace ((S × A) × S) := ⊤
    ∀ X : Ω → Fin T → (S × A) × S, Measurable X → iIndepFun (fun i ω => X ω i) μ →
      (∀ i, μ.map (fun ω => X ω i) = ∑ x : (S × A) × S,
        ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) • Measure.dirac x) →
      1 - δ < μ.real {ω | lemma612Conclusion M cb δ sel π₀ ρ πstar db (X ω) ∧
        upperRecursion M cb δ sel π₀ (X ω) ∧ lowerRecursion M cb δ sel π₀ (X ω)} := by
  letI : MeasurableSpace ((S × A) × S) := ⊤
  intro X hX hind hmarg
  have hcb0 : 0 ≤ cb := by linarith
  have hT : 1 ≤ T := by
    rcases Nat.eq_zero_or_pos T with h0 | h0
    · subst h0; simp [iota] at hι; linarith
    · exact h0
  have hpre : ∀ P : (Fin T → (S × A) × S) → Prop, MeasurableSet {ω | P (X ω)} :=
    fun P => hX (Set.toFinite {x | P x}).measurableSet
  have hlaw := iid_map_eq_pi M db μ X hX hind hmarg
  set jr := JointRow.jointRow db M.transition with hjr
  have hν : μ.map X = onlineStackProductLaw (fun _ : Fin T => jr) := hlaw
  have hlift : ∀ B : Set (Fin T → (S × A) × S),
      μ.real (X ⁻¹' B) = (onlineStackProductLaw (fun _ : Fin T => jr)).real B := by
    intro B
    rw [← hν, map_measureReal_apply hX (Set.toFinite B).measurableSet]
  obtain ⟨x₀⟩ : Nonempty ((S × A) × S) :=
    ⟨((M.state_nonempty.some, M.action_nonempty.some), M.state_nonempty.some)⟩
  -- the five events
  set E₁ := {ω | martingaleEvent M cb δ sel π₀ (X ω) (δ / 5)} with hE₁
  set E₂ := {ω | prefixCountEvent db (X ω) δ} with hE₂
  set E₃ := {ω | ∀ u : Fin T, δ / (5 * Fintype.card S * T) ≤ db.prob (X ω u).1 ∨
    (X ω u).1.2 ≠ πstar (X ω u).1.1} with hE₃
  have p₁ : 1 - δ / 5 < μ.real E₁ :=
    martingaleEvent_prob_conf M cb δ sel π₀ hcb0 db T hδ hδ1 (δ / 5) (by positivity)
      (by linarith) μ X hX hind hmarg
  have p₂ : 1 - δ / 5 ≤ μ.real E₂ := prefixCountEvent_prob M db hδ hδ1 hι μ X hX hlaw
  have p₃ : 1 - δ / 5 ≤ μ.real E₃ := icEvent_prob M db πstar hδ μ X hX hmarg
  have hψ := freedman_gated_prob M cb δ sel π₀ ρ πstar db hT hδ hδ1 hι hCs x₀
    (fun data u s a => visitDeltaSum M cb δ sel π₀ data u s a)
    (fun data data' u hu h => funext fun s => funext fun a =>
      visitDeltaSum_congr M cb δ sel π₀ hu.le h s a)
    (fun data u hu hg s a => visitDeltaSum_bounds M cb δ sel π₀ data hcb0 hT hδ hδ1 hu.le
      (fun v hv s => hg v hv.le s) s a)
    _ _ _ rfl rfl rfl
  have hφ := freedman_gated_prob M cb δ sel π₀ ρ πstar db hT hδ hδ1 hι hCs x₀
    (fun data u s a => (M.transition s a).expectation (delta M cb δ sel π₀ data u))
    (fun data data' u _ h => by
      funext s a
      simp only
      rw [delta_congr M cb δ sel π₀ h])
    (fun data u _ hg s a => ⟨FiniteDistribution.expectation_nonneg _ fun x => by
        have := hg u le_rfl x
        simp only [delta]; linarith,
      FiniteDistribution.expectation_le_const _ fun x => delta_le M cb δ sel π₀ data hcb0 u x⟩)
    _ _ _ rfl rfl rfl
  rw [← hlift] at hψ hφ
  have h₁ : MeasurableSet E₁ := hpre (fun x => martingaleEvent M cb δ sel π₀ x (δ / 5))
  have h₂ : MeasurableSet E₂ := hpre (fun x => prefixCountEvent db x δ)
  have h₃ : MeasurableSet E₃ := hpre (fun x => ∀ u : Fin T,
    δ / (5 * Fintype.card S * T) ≤ db.prob (x u).1 ∨ (x u).1.2 ≠ πstar (x u).1.1)
  have hall := inter_five_prob_strict μ h₁ h₂ h₃ (hX (Set.toFinite _).measurableSet)
    (hX (Set.toFinite _).measurableSet) p₁ p₂ p₃ hψ hφ
  refine lt_of_le_of_lt (by linarith) (hall.trans_le (measureReal_mono ?_))
  rintro ω ⟨⟨⟨⟨hω₁, hω₂⟩, hω₃⟩, hω₄⟩, hω₅⟩
  have hpess := pess_of_event_fifth M cb δ sel π₀ (X ω) hcb hδ hδ1 hι hω₁
  have hgate : ∀ u, u < T → gateProp M cb δ sel π₀ (X ω) u :=
    fun u hu v hv s => hpess v (by omega) s
  exact ⟨lemma612Conclusion_of_events M cb δ sel π₀ ρ πstar db hcb hT hδ hδ1 hι (X ω)
    (fun _ => ⟨hpess, hω₂, hω₃, hω₄ hgate, hω₅ hgate⟩),
    upperRecursion_of_event_fifth M cb δ sel π₀ (X ω) hcb hδ hδ1 hι hω₁,
    lowerRecursion_of_event_fifth M cb δ sel π₀ (X ω) hcb hδ hδ1 hι hω₁⟩

end Strict

section Final

set_option maxHeartbeats 2000000 in
/-- The closing arithmetic of Step 6 (`offlineRL.tex:2326–2353`) under the corrected (log²)
sample-size condition. -/
theorem final_scalar {gap α ξ θ Ψ C Cs S T ι L x ε : ℝ}
    (hx0 : 0 < x) (hx1 : x ≤ 1) (hε : 0 < ε) (hεx : x * ε ≤ 1) (hC : 1 ≤ C) (hCs : 1 ≤ Cs)
    (hS : 1 ≤ S) (hT : 0 < T) (hι : 1 ≤ ι) (hιL : ι ≤ L)
    (hcond : 16 * C ^ 2 * S * Cs * L ^ 2 / (x ^ 5 * ε ^ 2) ≤ T)
    (hgap : gap ≤ α / T) (hα : α ≤ ξ + θ + Ψ) (hξ : ξ ≤ C / x ^ 2)
    (hθ : θ ≤ C * Real.sqrt (Cs * S * T * ι ^ 2 / x ^ 5)) (hΨ : Ψ ≤ C * Cs * ι ^ 2 / x ^ 3) :
    gap ≤ ε := by
  have hL : 1 ≤ L := le_trans hι hιL
  set K := S * Cs * L ^ 2 with hK
  have hK1 : 1 ≤ K := by
    have h1 : 1 ≤ S * Cs := one_le_mul_of_one_le_of_one_le hS hCs
    have h2 : 1 ≤ L ^ 2 := one_le_pow₀ hL
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hx5 : 0 < x ^ 5 := by positivity
  have hcond' : 16 * C ^ 2 * K ≤ T * (x ^ 5 * ε ^ 2) := by
    rw [div_le_iff₀ (by positivity)] at hcond
    have : 16 * C ^ 2 * S * Cs * L ^ 2 = 16 * C ^ 2 * K := by rw [hK]; ring
    linarith
  have hC2 : C ≤ C ^ 2 := le_self_pow₀ hC two_ne_zero
  have hCK : C ^ 2 ≤ C ^ 2 * K := le_mul_of_one_le_right (sq_nonneg C) hK1
  -- (a) the θ term
  have hθT : C * Real.sqrt (Cs * S * T * ι ^ 2 / x ^ 5) ≤ T * ε / 4 := by
    have hR0 : 0 ≤ Real.sqrt (Cs * S * T * ι ^ 2 / x ^ 5) := Real.sqrt_nonneg _
    have hRsq : Real.sqrt (Cs * S * T * ι ^ 2 / x ^ 5) ^ 2 = Cs * S * T * ι ^ 2 / x ^ 5 :=
      Real.sq_sqrt (by positivity)
    by_contra hlt
    push_neg at hlt
    have hsq := pow_lt_pow_left₀ hlt (by positivity) (two_ne_zero)
    rw [mul_pow, hRsq] at hsq
    have hι2 : ι ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by linarith) hιL 2
    have h1 : C ^ 2 * (Cs * S * T * ι ^ 2 / x ^ 5) ≤ C ^ 2 * (K * T / x ^ 5) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg C)
      apply div_le_div_of_nonneg_right _ hx5.le
      rw [hK]
      have : 0 ≤ Cs * S * T := by positivity
      have := mul_le_mul_of_nonneg_left hι2 this
      linarith
    have h2 : C ^ 2 * (K * T / x ^ 5) ≤ (T * ε / 4) ^ 2 := by
      rw [show C ^ 2 * (K * T / x ^ 5) = (16 * C ^ 2 * K) * T / (16 * x ^ 5) by field_simp,
        div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_right hcond' hT.le
      linarith
    linarith
  -- (b) the ξ term
  have hξT : C / x ^ 2 ≤ T * ε / 16 := by
    have hx3 : x ^ 3 * ε ≤ 1 := by
      have : x ^ 3 * ε = x ^ 2 * (x * ε) := by ring
      rw [this]
      have : x ^ 2 ≤ 1 := pow_le_one₀ hx0.le hx1
      exact mul_le_one₀ this (by positivity) hεx
    have h1 : 16 * C ≤ T * (x ^ 5 * ε ^ 2) := by linarith
    have h2 : T * (x ^ 5 * ε ^ 2) ≤ T * (x ^ 2 * ε) := by
      apply mul_le_mul_of_nonneg_left _ hT.le
      have : x ^ 5 * ε ^ 2 = (x ^ 2 * ε) * (x ^ 3 * ε) := by ring
      rw [this]
      exact mul_le_of_le_one_right (by positivity) hx3
    rw [div_le_iff₀ (by positivity),
      show T * ε / 16 * x ^ 2 = T * (x ^ 2 * ε) / 16 by ring]
    linarith
  -- (c) the ψ + φ term
  have hΨT : C * Cs * ι ^ 2 / x ^ 3 ≤ T * ε / 16 := by
    have hx2 : x ^ 2 * ε ≤ 1 := by
      have : x ^ 2 * ε = x * (x * ε) := by ring
      rw [this]; exact mul_le_one₀ hx1 (by positivity) hεx
    have hι2 : ι ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by linarith) hιL 2
    have h1 : 16 * C * Cs * ι ^ 2 ≤ 16 * C ^ 2 * K := by
      rw [hK]
      have : C * Cs * ι ^ 2 ≤ C ^ 2 * (S * Cs * L ^ 2) := by
        have a1 : C * Cs * ι ^ 2 ≤ C * Cs * L ^ 2 :=
          mul_le_mul_of_nonneg_left hι2 (by positivity)
        have a2 : C * Cs * L ^ 2 ≤ C ^ 2 * (S * Cs * L ^ 2) := by
          have : C * (Cs * L ^ 2) ≤ C ^ 2 * (S * (Cs * L ^ 2)) := by
            apply mul_le_mul hC2 (le_mul_of_one_le_left (by positivity) hS) (by positivity)
              (by positivity)
          linarith
        linarith
      linarith
    have h2 : T * (x ^ 5 * ε ^ 2) ≤ T * (x ^ 3 * ε) := by
      apply mul_le_mul_of_nonneg_left _ hT.le
      have : x ^ 5 * ε ^ 2 = (x ^ 3 * ε) * (x ^ 2 * ε) := by ring
      rw [this]
      exact mul_le_of_le_one_right (by positivity) hx2
    rw [div_le_iff₀ (by positivity),
      show T * ε / 16 * x ^ 3 = T * (x ^ 3 * ε) / 16 by ring]
    linarith
  rw [le_div_iff₀ hT] at hgap
  have : α ≤ T * ε / 4 + T * ε / 16 + T * ε / 16 := by linarith
  have hTε : 0 ≤ T * ε := by positivity
  have hfin : gap * T ≤ ε * T := by linarith
  exact le_of_mul_le_mul_right hfin hT

end Final

section Theorem68

/-- The constant `c₂` of `Thm6_8_corrected`: `16 C²` with `C` the constant of Lemma 6.12. -/
noncomputable def thm68Const (cb : ℝ) : ℝ := 16 * lemma612Const cb ^ 2

theorem one_le_lemma612Const {cb : ℝ} (hcb : 0 ≤ cb) : 1 ≤ lemma612Const cb := by
  unfold lemma612Const; linarith

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  (ρ : FiniteDistribution S) (πstar : S → A) (db : FiniteDistribution (S × A))

/-- The C22 corner `log(SAT/δ) < 1` (`docs/SOURCE-ISSUES.md#C22`, `#C24`): under the corrected
sample-size condition (with any `c₂ ≥ 16`), it forces `|A| = 1`. -/
theorem corner_subsingleton {T : ℕ} (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hι : iota S A T δ < 1) {c₂ Cs ε : ℝ} (hc₂ : 16 ≤ c₂) (hCs : 1 ≤ Cs) (hε : 0 < ε)
    (hεx : (1 - M.discount) * ε ≤ 1)
    (hcond : c₂ * Fintype.card S * Cs *
        Real.log ((Fintype.card S : ℝ) * Fintype.card A * T / ((1 - M.discount) * δ)) ^ 2 /
        ((1 - M.discount) ^ 5 * ε ^ 2) ≤ T) :
    Subsingleton A := by
  haveI := M.state_nonempty
  haveI := M.action_nonempty
  have hx0 : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hx1 : 1 - M.discount ≤ 1 := by linarith [M.discount_nonneg]
  set n : ℕ := Fintype.card S * Fintype.card A * T with hn
  have hncast : (n : ℝ) = (Fintype.card S : ℝ) * Fintype.card A * T := by rw [hn]; push_cast; ring
  have hn1 : 1 ≤ n := by
    have := card_SAT_ge_one M hT
    exact_mod_cast (show (1 : ℝ) ≤ n by rw [hncast]; exact this)
  have hlt3 : n < 3 := by
    have hpos : 0 < (n : ℝ) / δ := by positivity
    have h := (Real.log_lt_iff_lt_exp hpos).1 (by rw [hncast]; exact hι)
    have he := Real.exp_one_lt_d9
    have : (n : ℝ) < 3 * δ := by
      rw [div_lt_iff₀ hδ] at h
      have h3 : Real.exp 1 * δ < 3 * δ := mul_lt_mul_of_pos_right (by linarith) hδ
      linarith
    have : (n : ℝ) < 3 := by linarith
    exact_mod_cast this
  have hn_one : n = 1 := by
    by_contra hne
    have hn2 : n = 2 := by omega
    -- `L > log 2` and the condition give `T > 2`
    set L := Real.log ((Fintype.card S : ℝ) * Fintype.card A * T / ((1 - M.discount) * δ)) with hL
    have hL2 : Real.log 2 < L := by
      rw [hL]
      apply Real.log_lt_log (by norm_num)
      rw [← hncast, hn2, lt_div_iff₀ (by positivity)]
      push_cast
      have hh : (1 - M.discount) * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right hx1 hδ.le
      linarith
    have hlog2 := Real.log_two_gt_d9
    have hS : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
    have hden : (1 - M.discount) ^ 5 * ε ^ 2 ≤ 1 := by
      have h1 : ((1 - M.discount) * ε) ^ 2 ≤ 1 := by
        have : 0 ≤ (1 - M.discount) * ε := by positivity
        exact pow_le_one₀ this hεx
      have h2 : (1 - M.discount) ^ 3 ≤ 1 := pow_le_one₀ hx0.le hx1
      have : (1 - M.discount) ^ 5 * ε ^ 2 = (1 - M.discount) ^ 3 * ((1 - M.discount) * ε) ^ 2 := by
        ring
      rw [this]
      exact mul_le_one₀ h2 (sq_nonneg _) h1
    have hL0 : 0 < L := by linarith
    have hnum : 16 * L ^ 2 ≤ c₂ * Fintype.card S * Cs * L ^ 2 := by
      have : 16 ≤ c₂ * Fintype.card S * Cs := by
        have := mul_le_mul hc₂ hS (by norm_num) (by linarith)
        have := mul_le_mul this hCs (by norm_num) (by positivity)
        linarith
      exact mul_le_mul_of_nonneg_right this (sq_nonneg L)
    have hge : c₂ * Fintype.card S * Cs * L ^ 2 ≤
        c₂ * Fintype.card S * Cs * L ^ 2 / ((1 - M.discount) ^ 5 * ε ^ 2) :=
      le_div_self (by positivity) (by positivity) hden
    have hTle : (T : ℝ) ≤ 2 := by
      have : T ≤ n := by
        rw [hn]
        have : 1 ≤ Fintype.card S * Fintype.card A :=
          Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero Fintype.card_ne_zero Fintype.card_ne_zero)
        exact Nat.le_mul_of_pos_left T this
      exact_mod_cast (show T ≤ 2 by omega)
    have hL69 : (0.69 : ℝ) < L := by linarith
    have hL2sq : (0.69 : ℝ) ^ 2 < L ^ 2 := pow_lt_pow_left₀ hL69 (by norm_num) two_ne_zero
    have hDen0 : 0 < (1 - M.discount) ^ 5 * ε ^ 2 := by positivity
    linarith
  have h0 : Fintype.card S * Fintype.card A * T = 1 := by rw [← hn]; exact hn_one
  have h1 : Fintype.card S * Fintype.card A = 1 := Nat.eq_one_of_mul_eq_one_right h0
  have h2 : Fintype.card A = 1 := Nat.eq_one_of_mul_eq_one_left h1
  exact Fintype.card_le_one_iff_subsingleton.mp h2.le

set_option maxHeartbeats 2000000 in
/-- **Theorem 6.8, corrected (library form)** (`theorem:lcbq`, `offlineRL.tex:1754–1772`, with
the sample-size condition squared in the logarithm, `docs/SOURCE-ISSUES.md#C24`). For `c_b ≥ 4`
and `c₂ = thm68Const c_b`: if `1 ≤ T`, `C⋆ < ∞`, `0 < ε ≤ 1/(1-γ)` and
`T ≥ c₂ S C⋆ log²(SAT/((1-γ)δ))/((1-γ)⁵ε²)`, then with probability exceeding `1 − δ` the output
policy `π̂ = π_T` satisfies `V⋆(ρ) − V^{π̂}(ρ) ≤ ε`. -/
theorem thm68_corrected_prob (hcb : 4 ≤ cb) (hsel : ∀ (f : A → ℝ) (a : A), f a ≤ f (sel f))
    (hopt : ∀ s, letI : Nonempty A := M.action_nonempty
      M.optimalityFixedPoint s (πstar s) = actionMaximum (M.optimalityFixedPoint s))
    (T : ℕ) (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hCs : concentrability M ρ πstar db ≠ ⊤) (ε : ℝ) (hε : 0 < ε)
    (hεx : ε ≤ 1 / (1 - M.discount))
    (hcond : thm68Const cb * Fintype.card S * (concentrability M ρ πstar db).toReal *
        Real.log ((Fintype.card S : ℝ) * Fintype.card A * T / ((1 - M.discount) * δ)) ^ 2 /
        ((1 - M.discount) ^ 5 * ε ^ 2) ≤ T)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    letI : MeasurableSpace ((S × A) × S) := ⊤
    ∀ X : Ω → Fin T → (S × A) × S, Measurable X → iIndepFun (fun i ω => X ω i) μ →
      (∀ i, μ.map (fun ω => X ω i) = ∑ x : (S × A) × S,
        ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) • Measure.dirac x) →
      1 - δ < μ.real {ω | ρ.expectation (M.trajectoryExpectedValue M.optimalGreedyPolicy) -
        ρ.expectation (M.trajectoryExpectedValue
          (detPolicy (run M cb δ sel π₀ (X ω) T).policy)) ≤ ε} := by
  letI : MeasurableSpace ((S × A) × S) := ⊤
  intro X hX hind hmarg
  have hcb0 : 0 ≤ cb := by linarith
  have hx0 : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hx1 : 1 - M.discount ≤ 1 := by linarith [M.discount_nonneg]
  have hεx' : (1 - M.discount) * ε ≤ 1 := by
    rw [le_div_iff₀ hx0] at hεx; linarith
  have hCs1 := one_le_concentrability M ρ πstar db hCs
  set C := lemma612Const cb with hCdef
  have hC1 : 1 ≤ C := one_le_lemma612Const hcb0
  by_cases hι : 1 ≤ iota S A T δ
  · refine lt_of_lt_of_le (lemma612_events_strict M cb δ sel π₀ ρ πstar db hcb T hδ hδ1 hι hCs μ
      X hX hind hmarg) (measureReal_mono ?_)
    rintro ω ⟨hcon, hup, hlow⟩
    have hpessAll := (run_le_opt_of_lowerRecursion M cb δ sel π₀ (X ω) hδ hδ1 hlow).1
    have hVT : ∀ s, (run M cb δ sel π₀ (X ω) T).V s ≤
        M.trajectoryExpectedValue (detPolicy (run M cb δ sel π₀ (X ω) T).policy) s :=
      fun s => ((pessimism_of_lowerRecursion M cb δ sel π₀ (X ω) hsel hδ hδ1 hlow T hT le_rfl).2 s).1
    simp only [lemma612Conclusion] at hcon
    obtain ⟨hαt, ⟨ξ, hξ, hξle⟩, ⟨θ, hθ, hθle⟩, ⟨ψ, φ, hψ, hφ, hψφ⟩⟩ := hcon
    have hgap := performance_le_alpha0 M cb δ sel π₀ (X ω) ρ πstar hT hpessAll hVT
    have hα0 := alpha0_le M cb δ sel π₀ (X ω) ρ πstar db hcb0 hT hδ hδ1 hopt hup hpessAll hαt
      hξ hθ hψ hφ
    have hιL : iota S A T δ ≤
        Real.log ((Fintype.card S : ℝ) * Fintype.card A * T / ((1 - M.discount) * δ)) := by
      unfold iota
      have hX0 := card_SAT_ge_one M hT
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ hδ (by positivity)]
      have : 0 ≤ (Fintype.card S : ℝ) * Fintype.card A * T := by positivity
      have := mul_nonneg (mul_nonneg this hδ.le) M.discount_nonneg
      linarith
    haveI := M.state_nonempty
    have hS : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
    have hT' : (0 : ℝ) < T := by exact_mod_cast hT
    have hcond' : 16 * C ^ 2 * Fintype.card S * (concentrability M ρ πstar db).toReal *
        Real.log ((Fintype.card S : ℝ) * Fintype.card A * T / ((1 - M.discount) * δ)) ^ 2 /
        ((1 - M.discount) ^ 5 * ε ^ 2) ≤ T := hcond
    exact final_scalar hx0 hx1 hε hεx' hC1 hCs1 hS hT' hι hιL hcond' hgap
      (by linarith) hξle (hθle hCs) (hψφ hCs)
  · push_neg at hι
    have hc₂ : 16 ≤ thm68Const cb := by
      unfold thm68Const
      have h := one_le_pow₀ (n := 2) hC1
      linarith
    haveI hsub := corner_subsingleton M δ hT hδ hδ1 hι hc₂ hCs1 hε hεx' hcond
    have huniv : {ω | ρ.expectation (M.trajectoryExpectedValue M.optimalGreedyPolicy) -
        ρ.expectation (M.trajectoryExpectedValue
          (detPolicy (run M cb δ sel π₀ (X ω) T).policy)) ≤ ε} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      have hpol : detPolicy (run M cb δ sel π₀ (X ω) T).policy = M.optimalGreedyPolicy := by
        funext s
        simp only [detPolicy, DiscountedMDP.optimalGreedyPolicy]
        rw [Subsingleton.elim ((run M cb δ sel π₀ (X ω) T).policy s) (M.optimalGreedyAction s)]
      rw [hpol, sub_self]
      exact hε.le
    rw [huniv, probReal_univ]
    linarith

end Theorem68

end StatisticalRL.OfflineRL.LCBQ
