import Formalization.OfflineRL.LCBQRecursion
import Formalization.OfflineRL.LCBQUsefulSeries
import Formalization.Online.QLearning.ReciprocalSqrt

/-!
# LCB-Q, Lemma 6.12: scalar facts, concentrability, and the terms `α`, `ξ`, `θ`

`lem:lcbq-alpha-xi-psi-phi-bound`, `chapters/offlineRL.tex:2309–2324`; proof `:4786–4972`.
Everything here is deterministic (pathwise) and assumes `log(SAT/δ) ≥ 1`, the premise of
`Lemma6_11_restricted` (see `docs/SOURCE-ISSUES.md#C22`, `#C24`).

* `κ = γ(1+1/H)³ ≤ 1 − (1−γ)/4 < 1` and `H ≤ 5ι/(1−γ)`;
* `C⋆ ≥ 1` and `d⋆(s,a) ≤ C⋆ d^b(s,a)` when `C⋆ < ∞`;
* `α_j → 0` (`eq:alpha-bound-offlineQ`);
* `ξ = Σ_j ξ_j ≤ 168/(1−γ)²` (`eq:xi-bound-offlineQ`);
* `θ = Σ_j θ_j ≲ √(C⋆STι²/(1−γ)⁵)` on the prefix-count event (`eq:theta-bound-offlineQ`).
-/

open scoped BigOperators ENNReal
open Filter Topology

namespace StatisticalRL.OfflineRL.LCBQ

open StatisticalRL StatisticalRL.OnlineRL
open Classical

set_option linter.unusedSectionVars false

variable {S A : Type*} [Fintype S] [Fintype A]

section Scalars

variable (M : DiscountedMDP S A) {T : ℕ} {δ : ℝ}

include M in
theorem card_SAT_ge_one (hT : 1 ≤ T) :
    (1 : ℝ) ≤ (Fintype.card S : ℝ) * Fintype.card A * T := by
  haveI := M.state_nonempty
  haveI := M.action_nonempty
  have hS : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hA : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have h1 : (1 : ℝ) ≤ (Fintype.card S : ℝ) * Fintype.card A := by nlinarith
  nlinarith

/-- `1/H ≤ (1-γ)/4` once `ι ≥ 1`. -/
theorem inv_horizon_le (hι : 1 ≤ iota S A T δ) :
    1 / (horizon M.discount (iota S A T δ) : ℝ) ≤ (1 - M.discount) / 4 := by
  have hx0 : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hH : 4 / (1 - M.discount) * iota S A T δ ≤ horizon M.discount (iota S A T δ) :=
    Nat.le_ceil _
  have h4 : 4 / (1 - M.discount) ≤ 4 / (1 - M.discount) * iota S A T δ := by
    have : 0 < 4 / (1 - M.discount) := by positivity
    nlinarith
  have hHpos : (0 : ℝ) < horizon M.discount (iota S A T δ) := by
    have : 0 < 4 / (1 - M.discount) := by positivity
    linarith
  rw [div_le_div_iff₀ hHpos (by norm_num)]
  have := (div_le_iff₀ hx0).mp (h4.trans hH)
  linarith

theorem horizon_le (hι : 1 ≤ iota S A T δ) :
    (horizon M.discount (iota S A T δ) : ℝ) ≤ 5 * iota S A T δ / (1 - M.discount) := by
  have hx0 : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hx1 : 1 - M.discount ≤ 1 := by linarith [M.discount_nonneg]
  have hc := Nat.ceil_lt_add_one (show 0 ≤ 4 / (1 - M.discount) * iota S A T δ by positivity)
  have h1 : 1 ≤ iota S A T δ / (1 - M.discount) := by
    rw [le_div_iff₀ hx0]; nlinarith
  calc (horizon M.discount (iota S A T δ) : ℝ) ≤ 4 / (1 - M.discount) * iota S A T δ + 1 :=
        hc.le
    _ ≤ 4 * (iota S A T δ / (1 - M.discount)) + iota S A T δ / (1 - M.discount) := by
        rw [div_mul_eq_mul_div, mul_div_assoc]; linarith
    _ = 5 * iota S A T δ / (1 - M.discount) := by ring

theorem kappa_nonneg (H : ℕ) : 0 ≤ kappa M.discount H := by
  unfold kappa; have := M.discount_nonneg; positivity

/-- `κ ≤ 1 − (1−γ)/4` (as in `lcbq_useful`). -/
theorem kappa_le (hι : 1 ≤ iota S A T δ) :
    kappa M.discount (horizon M.discount (iota S A T δ)) ≤ 1 - (1 - M.discount) / 4 := by
  set x := 1 - M.discount with hx
  have hγ0 := M.discount_nonneg
  have hx0 : 0 < x := by rw [hx]; linarith [M.discount_lt_one]
  have hinv := inv_horizon_le M hι
  have hpow : (1 + 1 / (horizon M.discount (iota S A T δ) : ℝ)) ^ 3 ≤ (1 + x / 4) ^ 3 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 3
  have hγx : M.discount = 1 - x := by rw [hx]; ring
  unfold kappa
  calc M.discount * (1 + 1 / (horizon M.discount (iota S A T δ) : ℝ)) ^ 3
      ≤ M.discount * (1 + x / 4) ^ 3 := mul_le_mul_of_nonneg_left hpow hγ0
    _ = 1 - x / 4 - (9 / 16 * x ^ 2 + 11 / 64 * x ^ 3 + 1 / 64 * x ^ 4) := by rw [hγx]; ring
    _ ≤ 1 - x / 4 := by
        have : 0 ≤ 9 / 16 * x ^ 2 + 11 / 64 * x ^ 3 + 1 / 64 * x ^ 4 := by positivity
        linarith

theorem kappa_lt_one (hι : 1 ≤ iota S A T δ) :
    kappa M.discount (horizon M.discount (iota S A T δ)) < 1 := by
  have := kappa_le M hι
  have : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  linarith

/-- Every `κ^j`-weighted occupancy series of a bounded function is summable. -/
theorem summable_kappa_occ {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (π : StationaryPolicy S A)
    (ρ : FiniteDistribution S) (W : S → ℝ) (k : ℕ) :
    Summable (fun j => κ ^ (j + k) * ∑ s, M.occupancyStateAt π ρ (j + k) s * W s) := by
  apply Summable.of_norm_bounded (g := fun j => κ ^ j * ∑ s, |W s|)
  · exact (summable_geometric_of_lt_one hκ0 hκ1).mul_right _
  · intro j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hκ0 _)]
    apply mul_le_mul (pow_le_pow_of_le_one hκ0 hκ1.le (by omega)) _ (abs_nonneg _)
      (pow_nonneg hκ0 _)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [abs_mul, abs_of_nonneg (M.occupancyStateAt_nonneg _ _ _ _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (M.occupancyStateAt_le_one _ _ _ _)

end Scalars

section Concentrability

variable (M : DiscountedMDP S A) (ρ : FiniteDistribution S) (πstar : S → A)
  (db : FiniteDistribution (S × A))

/-- `d⋆(s,a) ≤ C⋆ d^b(s,a)` when `C⋆ < ∞`. -/
theorem dstar_le (hC : concentrability M ρ πstar db ≠ ⊤) (s : S) (a : A) :
    M.discountedJointOccupancy (detPolicy πstar) ρ s a ≤
      (concentrability M ρ πstar db).toReal * db.prob (s, a) := by
  set x := M.discountedJointOccupancy (detPolicy πstar) ρ s a
  set y := db.prob (s, a)
  have hx0 : 0 ≤ x := M.discountedJointOccupancy_nonneg _ _ _ _
  have hy0 : 0 ≤ y := db.prob_nonneg _
  have hle : ENNReal.ofReal x / ENNReal.ofReal y ≤ concentrability M ρ πstar db :=
    le_iSup (fun p : S × A => ENNReal.ofReal (M.discountedJointOccupancy (detPolicy πstar) ρ p.1
      p.2) / ENNReal.ofReal (db.prob p)) (s, a)
  rcases hy0.eq_or_lt with hy | hy
  · -- `d^b = 0` forces `d⋆ = 0`
    rw [← hy] at hle ⊢
    rcases hx0.eq_or_lt with hx | hx
    · rw [← hx]; simp
    · exfalso
      rw [ENNReal.ofReal_zero, ENNReal.div_zero (ENNReal.ofReal_pos.2 hx).ne', top_le_iff] at hle
      exact hC hle
  · have h := ENNReal.toReal_mono hC hle
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hx0, ENNReal.toReal_ofReal hy0,
      div_le_iff₀ hy] at h
    exact h

/-- `C⋆ ≥ 1` (`offlineRL.tex:141–149`). -/
theorem one_le_concentrability (hC : concentrability M ρ πstar db ≠ ⊤) :
    1 ≤ (concentrability M ρ πstar db).toReal := by
  by_contra hlt
  push_neg at hlt
  have h1 : ∑ s, ∑ a, M.discountedJointOccupancy (detPolicy πstar) ρ s a = 1 :=
    M.discountedJointOccupancy_sum _ ρ
  have h2 : ∑ s, ∑ a, M.discountedJointOccupancy (detPolicy πstar) ρ s a ≤
      (concentrability M ρ πstar db).toReal * ∑ s, ∑ a, db.prob (s, a) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => dstar_le M ρ πstar db hC s a
  have h3 : ∑ s, ∑ a, db.prob (s, a) = 1 := by
    rw [← Fintype.sum_prod_type' (fun s a => db.prob (s, a))]
    exact db.sum_prob
  rw [h3, mul_one, h1] at h2
  linarith

/-- `d⋆(s) = d⋆(s, π⋆(s)) ≤ C⋆ d^b(s, π⋆(s))`. -/
theorem dstarState_le (hC : concentrability M ρ πstar db ≠ ⊤) (s : S) :
    M.discountedStateOccupancy (detPolicy πstar) ρ s ≤
      (concentrability M ρ πstar db).toReal * db.prob (s, πstar s) := by
  have h := dstar_le M ρ πstar db hC s (πstar s)
  rw [show detPolicy πstar = fun x => EnvironmentStage.pointMass (πstar x) from rfl,
    M.discountedJointOccupancy_deterministic, if_pos rfl, mul_one] at h
  exact h

end Concentrability

section Values

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  {T : ℕ} (data : Fin T → (S × A) × S)

theorem optValue_bounds (s : S) : 0 ≤ optValue M s ∧ optValue M s ≤ 1 / (1 - M.discount) := by
  letI : Nonempty A := M.action_nonempty
  unfold optValue
  rw [optValue_eq]
  constructor
  · exact (M.optimalityFixedPoint_bounds s (Classical.arbitrary A)).1.trans (le_actionMaximum _ _)
  · exact Finset.sup'_le _ _ (fun a _ => (M.optimalityFixedPoint_bounds s a).2)

theorem abs_delta_le (hcb : 0 ≤ cb) (t : ℕ) (s : S) :
    |delta M cb δ sel π₀ data t s| ≤ 1 / (1 - M.discount) := by
  have h1 := optValue_bounds M s
  have h2 := (run_bounds M cb δ sel π₀ data hcb t).2 s
  unfold delta
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem delta_le (hcb : 0 ≤ cb) (t : ℕ) (s : S) :
    delta M cb δ sel π₀ data t s ≤ 1 / (1 - M.discount) :=
  (abs_le.mp (abs_delta_le M cb δ sel π₀ data hcb t s)).2

end Values

section Alpha

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  {T : ℕ} (data : Fin T → (S × A) × S) (ρ : FiniteDistribution S) (πstar : S → A)

/-- `α = lim_j α_j = 0` (`eq:alpha-bound-offlineQ`): `|α_j| ≤ κ^j T/(1-γ)`. -/
theorem alphaSeq_tendsto_zero (hcb : 0 ≤ cb) (hι : 1 ≤ iota S A T δ) :
    Tendsto (alphaSeq M cb δ sel π₀ data ρ πstar) atTop (𝓝 0) := by
  set κ := kappa M.discount (horizon M.discount (iota S A T δ))
  have hκ0 : 0 ≤ κ := kappa_nonneg M _
  have hκ1 : κ < 1 := kappa_lt_one M hι
  set c := 1 / (1 - M.discount)
  have hbound : ∀ j, |alphaSeq M cb δ sel π₀ data ρ πstar j| ≤ κ ^ j * ((T : ℝ) * c) := by
    intro j
    unfold alphaSeq
    rw [abs_mul, abs_of_nonneg (pow_nonneg hκ0 j)]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hκ0 j)
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ t ∈ Finset.Icc 1 T, |∑ s, M.occupancyStateAt (detPolicy πstar) ρ j s *
          delta M cb δ sel π₀ data t s|
        ≤ ∑ t ∈ Finset.Icc 1 T, c := by
          refine Finset.sum_le_sum fun t _ => ?_
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ s, |M.occupancyStateAt (detPolicy πstar) ρ j s * delta M cb δ sel π₀ data t s|
              ≤ ∑ s, M.occupancyStateAt (detPolicy πstar) ρ j s * c := by
                refine Finset.sum_le_sum fun s _ => ?_
                rw [abs_mul, abs_of_nonneg (M.occupancyStateAt_nonneg _ _ _ _)]
                exact mul_le_mul_of_nonneg_left (abs_delta_le M cb δ sel π₀ data hcb t s)
                  (M.occupancyStateAt_nonneg _ _ _ _)
            _ = c := by rw [← Finset.sum_mul, occupancyStateAt_sum, one_mul]
      _ = (T : ℝ) * c := by simp
  have hlim : Tendsto (fun j => κ ^ j * ((T : ℝ) * c)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hκ0 hκ1).mul_const ((T : ℝ) * c)
  exact squeeze_zero_norm hbound hlim

end Alpha

section Xi

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  {T : ℕ} (data : Fin T → (S × A) × S) (ρ : FiniteDistribution S) (πstar : S → A)

theorem delta_zero (s : S) : delta M cb δ sel π₀ data 0 s = optValue M s := by
  simp [delta, run_zero, init]

/-- `ξ = Σ_j ξ_j ≤ 168/(1−γ)²` (`eq:xi-bound-offlineQ`). -/
theorem xiSeq_hasSum_le (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1) (hι : 1 ≤ iota S A T δ) :
    ∃ ξ, HasSum (xiSeq M cb δ sel π₀ data ρ πstar) ξ ∧ ξ ≤ 168 / (1 - M.discount) ^ 2 := by
  set κ := kappa M.discount (horizon M.discount (iota S A T δ)) with hκdef
  have hκ0 : 0 ≤ κ := kappa_nonneg M _
  have hκ1 : κ < 1 := kappa_lt_one M hι
  have hx0 : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  set W : S → ℝ := optValue M
  have hW0 : ∀ s, 0 ≤ W s := fun s => (optValue_bounds M s).1
  have hxi : xiSeq M cb δ sel π₀ data ρ πstar =
      fun j => κ ^ (j + 1) * ∑ s, M.occupancyStateAt (detPolicy πstar) ρ (j + 1) s * W s := by
    funext j
    simp only [xiSeq, delta_zero, hκdef, W]
  have hsum := summable_kappa_occ M hκ0 hκ1 (detPolicy πstar) ρ W 1
  have hsum0 := summable_kappa_occ M hκ0 hκ1 (detPolicy πstar) ρ W 0
  simp only [add_zero] at hsum0
  refine ⟨∑' j, κ ^ (j + 1) * ∑ s, M.occupancyStateAt (detPolicy πstar) ρ (j + 1) s * W s,
    by rw [hxi]; exact hsum.hasSum, ?_⟩
  have hshift := hsum0.tsum_eq_zero_add
  have h0 : 0 ≤ κ ^ 0 * ∑ s, M.occupancyStateAt (detPolicy πstar) ρ 0 s * W s :=
    mul_nonneg (pow_nonneg hκ0 0) (Finset.sum_nonneg fun s _ =>
      mul_nonneg (M.occupancyStateAt_nonneg _ _ _ _) (hW0 s))
  have hU : ∑' j : ℕ, κ ^ j * ∑ s, M.occupancyStateAt (detPolicy πstar) ρ j s * W s ≤
      84 * ((∑ s, M.discountedStateOccupancy (detPolicy πstar) ρ s * W s) / (1 - M.discount) +
        δ * ‖W‖ / ((Fintype.card S : ℝ) * (T : ℝ) ^ 4 * (1 - M.discount))) :=
    lcbq_useful M (detPolicy πstar) ρ δ T W hδ hδ1 hT hι hW0
  set c := 1 / (1 - M.discount) with hc
  have hWc : ∀ s, W s ≤ c := fun s => (optValue_bounds M s).2
  have hdW : ∑ s, M.discountedStateOccupancy (detPolicy πstar) ρ s * W s ≤ c := by
    calc ∑ s, M.discountedStateOccupancy (detPolicy πstar) ρ s * W s
        ≤ ∑ s, M.discountedStateOccupancy (detPolicy πstar) ρ s * c :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hWc s)
            (M.discountedStateOccupancy_nonneg _ _ _)
      _ = c := by rw [← Finset.sum_mul, M.discountedStateOccupancy_sum, one_mul]
  have hnorm : ‖W‖ ≤ c := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun s => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hW0 s)]
    exact hWc s
  have hST : (1 : ℝ) ≤ (Fintype.card S : ℝ) * (T : ℝ) ^ 4 := by
    haveI := M.state_nonempty
    have hS : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
    have hT' : (1 : ℝ) ≤ (T : ℝ) ^ 4 := one_le_pow₀ (by exact_mod_cast hT)
    nlinarith
  have hsec : δ * ‖W‖ / ((Fintype.card S : ℝ) * (T : ℝ) ^ 4 * (1 - M.discount)) ≤ c / (1 - M.discount) := by
    rw [div_le_div_iff₀ (by positivity) hx0]
    have h0 : δ * ‖W‖ ≤ c := by nlinarith [norm_nonneg W]
    have hc0 : 0 ≤ c := by positivity
    have h1 : δ * ‖W‖ * (1 - M.discount) ≤ c * (1 - M.discount) :=
      mul_le_mul_of_nonneg_right h0 hx0.le
    have h2 : c * (1 - M.discount) ≤
        c * ((Fintype.card S : ℝ) * (T : ℝ) ^ 4 * (1 - M.discount)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hx0.le hST) hc0
    linarith
  have hfirst : (∑ s, M.discountedStateOccupancy (detPolicy πstar) ρ s * W s) / (1 - M.discount) ≤
      c / (1 - M.discount) := div_le_div_of_nonneg_right hdW hx0.le
  calc ∑' j, κ ^ (j + 1) * ∑ s, M.occupancyStateAt (detPolicy πstar) ρ (j + 1) s * W s
      ≤ ∑' j : ℕ, κ ^ j * ∑ s, M.occupancyStateAt (detPolicy πstar) ρ j s * W s := by
        rw [hshift]; linarith
    _ ≤ 84 * (c / (1 - M.discount) + c / (1 - M.discount)) := hU.trans (by gcongr)
    _ = 168 / (1 - M.discount) ^ 2 := by rw [hc]; field_simp; ring

end Xi

section Theta

/-- The prefix-count event `eq:prefix-count-lower-bound-lcbq` (`offlineRL.tex:4880–4887`), with
the constant `3ι` in place of the printed `(4/3)ι` (the extra room absorbs the confidence split). -/
def prefixCountEvent (db : FiniteDistribution (S × A)) {T : ℕ} (data : Fin T → (S × A) × S)
    (δ : ℝ) : Prop :=
  ∀ t, 1 ≤ t → t ≤ T → ∀ sa : S × A,
    (t : ℝ) * db.prob sa / 12 ≤ max (Nat.count (visitPred data sa) t : ℝ) (3 * iota S A T δ)

/-- `W_t(s) = min{β_n, 1/(1-γ)} ≤ (6 + 11c_b) √(Hι/(x(1-γ)²))` whenever `max{n, 3ι} ≥ x/12`
(`eq:prefix-count-beta-bound-lcbq`). -/
theorem betaTrunc_le {cb γ ι : ℝ} (hcb : 0 ≤ cb) (hγ : γ < 1) (hι : 0 ≤ ι) {H n : ℕ}
    (hH : 1 ≤ H) {x : ℝ} (hx : 0 < x) (h : x / 12 ≤ max (n : ℝ) (3 * ι)) :
    betaTrunc cb γ ι H n ≤ (6 + 11 * cb) * Real.sqrt (H * ι / (x * (1 - γ) ^ 2)) := by
  have hx1 : 0 < 1 - γ := by linarith
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  set z := (H : ℝ) * ι / (x * (1 - γ) ^ 2) with hz
  have hz0 : 0 ≤ z := by positivity
  have hsz := Real.sqrt_nonneg z
  have hle_c : betaTrunc cb γ ι H n ≤ 1 / (1 - γ) := by
    unfold betaTrunc; split_ifs
    · exact le_rfl
    · exact min_le_right _ _
  rcases le_or_gt x (36 * ι) with hsmall | hbig
  · -- clipping
    have hc : 1 / (1 - γ) ≤ 6 * Real.sqrt z := by
      have h36 : (1 / (1 - γ)) ^ 2 ≤ 36 * z := by
        rw [hz, div_pow, one_pow, show 36 * ((H : ℝ) * ι / (x * (1 - γ) ^ 2)) =
          (36 * H * ι / x) * (1 / (1 - γ) ^ 2) by field_simp]
        apply le_mul_of_one_le_left (by positivity)
        rw [le_div_iff₀ hx]
        nlinarith
      have : 1 / (1 - γ) ≤ Real.sqrt (36 * z) :=
        Real.le_sqrt_of_sq_le h36
      rwa [Real.sqrt_mul (by norm_num), show Real.sqrt 36 = 6 by
        rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
    nlinarith
  · -- enough visits
    have hn : x / 12 ≤ (n : ℝ) := by
      rcases le_max_iff.mp h with h' | h'
      · exact h'
      · exfalso; linarith
    have hnpos : (0 : ℝ) < n := by linarith [div_pos hx (by norm_num : (0 : ℝ) < 12)]
    have hn0 : n ≠ 0 := by intro h0; rw [h0] at hnpos; simp at hnpos
    have hβ : betaTrunc cb γ ι H n ≤ 3 * cb * Real.sqrt (H * ι / (n * (1 - γ) ^ 2)) := by
      unfold betaTrunc; rw [if_neg hn0]; exact min_le_left _ _
    have hsq : Real.sqrt (H * ι / (n * (1 - γ) ^ 2)) ≤ Real.sqrt 12 * Real.sqrt z := by
      rw [← Real.sqrt_mul (by norm_num)]
      apply Real.sqrt_le_sqrt
      rw [hz, div_le_iff₀ (by positivity)]
      rw [show 12 * ((H : ℝ) * ι / (x * (1 - γ) ^ 2)) * ((n : ℝ) * (1 - γ) ^ 2) =
        (H * ι) * (12 * n / x) by field_simp]
      have : 1 ≤ 12 * (n : ℝ) / x := by rw [le_div_iff₀ hx]; linarith
      have : 0 ≤ (H : ℝ) * ι := by positivity
      nlinarith
    have h12 : Real.sqrt 12 ≤ 11 / 3 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    calc betaTrunc cb γ ι H n ≤ 3 * cb * (Real.sqrt 12 * Real.sqrt z) :=
          hβ.trans (mul_le_mul_of_nonneg_left hsq (by positivity))
      _ ≤ 3 * cb * (11 / 3 * Real.sqrt z) := by gcongr
      _ ≤ (6 + 11 * cb) * Real.sqrt z := by nlinarith

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  {T : ℕ} (data : Fin T → (S × A) × S) (ρ : FiniteDistribution S) (πstar : S → A)
  (db : FiniteDistribution (S × A))

theorem betaTrunc_nonneg {cb γ ι : ℝ} (hcb : 0 ≤ cb) (hγ : γ < 1) (H n : ℕ) :
    0 ≤ betaTrunc cb γ ι H n := by
  have : 0 < 1 - γ := by linarith
  unfold betaTrunc; split_ifs
  · positivity
  · exact le_min (by positivity) (by positivity)

/-- The per-time, per-state step of `eq:theta-bound-offlineQ`:
`d⋆(s) W_t(s) ≤ (6+11c_b) √(Hι)/((1-γ)√t) √(C⋆ d⋆(s))`. -/
theorem dstar_mul_W_le (hcb : 0 ≤ cb) (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hι : 1 ≤ iota S A T δ) (hC : concentrability M ρ πstar db ≠ ⊤)
    (hcount : prefixCountEvent db data δ) {t : ℕ} (ht1 : 1 ≤ t) (htT : t ≤ T) (s : S) :
    M.discountedStateOccupancy (detPolicy πstar) ρ s *
        betaTrunc cb M.discount (iota S A T δ) (horizon M.discount (iota S A T δ))
          ((run M cb δ sel π₀ data t).count s (πstar s)) ≤
      (6 + 11 * cb) * (Real.sqrt (horizon M.discount (iota S A T δ) * iota S A T δ) /
        (1 - M.discount) / Real.sqrt t) *
        Real.sqrt ((concentrability M ρ πstar db).toReal *
          M.discountedStateOccupancy (detPolicy πstar) ρ s) := by
  set ι := iota S A T δ
  set H := horizon M.discount ι
  set Cs := (concentrability M ρ πstar db).toReal
  set d := M.discountedStateOccupancy (detPolicy πstar) ρ s
  set b := db.prob (s, πstar s)
  have hx1 : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hd0 : 0 ≤ d := M.discountedStateOccupancy_nonneg _ _ _
  have hdle : d ≤ Cs * b := dstarState_le M ρ πstar db hC s
  have hCs : 1 ≤ Cs := one_le_concentrability M ρ πstar db hC
  have hH : 1 ≤ H := horizon_pos M hT hδ hδ1
  have ht : (0 : ℝ) < t := by exact_mod_cast ht1
  have hRHS0 : 0 ≤ (6 + 11 * cb) * (Real.sqrt (H * ι) / (1 - M.discount) / Real.sqrt t) *
      Real.sqrt (Cs * d) := by positivity
  rcases (show 0 ≤ b from db.prob_nonneg _).eq_or_lt with hb | hb
  · have : d = 0 := le_antisymm (by rw [← hb] at hdle; simpa using hdle) hd0
    exact (le_of_eq (by rw [this, zero_mul])).trans hRHS0
  · have hcnt := hcount t ht1 htT (s, πstar s)
    rw [← run_count M cb δ sel π₀ data htT] at hcnt
    have hW := betaTrunc_le hcb M.discount_lt_one (by linarith : (0 : ℝ) ≤ ι) hH
      (mul_pos ht hb) (by simpa [mul_div_assoc] using hcnt)
    rw [sqrt_ratio_eq M.discount_lt_one _ (by positivity) _ (by positivity),
      Real.sqrt_mul ht.le] at hW
    have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 hb
    have hkey : d / Real.sqrt b ≤ Real.sqrt (Cs * d) := by
      rw [div_le_iff₀ hsb, ← Real.sqrt_mul (by positivity)]
      calc d = Real.sqrt (d * d) := (Real.sqrt_mul_self hd0).symm
        _ ≤ Real.sqrt (Cs * d * b) := Real.sqrt_le_sqrt (by nlinarith)
    have hst : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
    calc d * betaTrunc cb M.discount ι H ((run M cb δ sel π₀ data t).count s (πstar s))
        ≤ d * ((6 + 11 * cb) * (Real.sqrt (H * ι) / (1 - M.discount) /
            (Real.sqrt t * Real.sqrt b))) := mul_le_mul_of_nonneg_left hW hd0
      _ = (6 + 11 * cb) * (Real.sqrt (H * ι) / (1 - M.discount) / Real.sqrt t) *
            (d / Real.sqrt b) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hkey (by positivity)

set_option maxHeartbeats 1000000 in
/-- **θ bound** (`eq:theta-bound-offlineQ`): on the prefix-count event and for `C⋆ < ∞`,
`θ = Σ_j θ_j ≤ (3200 + 5600 c_b) √(C⋆ S T ι²/(1-γ)⁵)`. -/
theorem thetaSeq_hasSum_le (hcb : 0 ≤ cb) (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hι : 1 ≤ iota S A T δ) (hC : concentrability M ρ πstar db ≠ ⊤)
    (hcount : prefixCountEvent db data δ) :
    ∃ θ, HasSum (thetaSeq M cb δ sel π₀ data ρ πstar) θ ∧
      θ ≤ (3200 + 5600 * cb) * Real.sqrt ((concentrability M ρ πstar db).toReal *
        Fintype.card S * T * iota S A T δ ^ 2 / (1 - M.discount) ^ 5) := by
  set ι := iota S A T δ with hιdef
  set H := horizon M.discount ι with hHdef
  set γ := M.discount with hγdef
  set Cs := (concentrability M ρ πstar db).toReal with hCsdef
  set κ := kappa γ H with hκdef
  have hκ0 : 0 ≤ κ := kappa_nonneg M _
  have hκ1 : κ < 1 := kappa_lt_one M hι
  have hx0 : 0 < 1 - γ := by linarith [M.discount_lt_one]
  have hx1 : 1 - γ ≤ 1 := by linarith [M.discount_nonneg]
  have hCs : 1 ≤ Cs := one_le_concentrability M ρ πstar db hC
  haveI := M.state_nonempty
  have hS : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  set c := 1 / (1 - γ) with hc
  set W : ℕ → S → ℝ := fun t s =>
    betaTrunc cb γ ι H ((run M cb δ sel π₀ data t).count s (πstar s)) with hWdef
  have hW0 : ∀ t s, 0 ≤ W t s := fun t s => betaTrunc_nonneg hcb M.discount_lt_one _ _
  have hWc : ∀ t s, W t s ≤ c := by
    intro t s
    simp only [hWdef, betaTrunc]
    split_ifs
    · exact le_rfl
    · exact min_le_right _ _
  set f : ℕ → ℕ → ℝ := fun t j => κ ^ j * ∑ s, M.occupancyStateAt (detPolicy πstar) ρ j s * W t s
    with hfdef
  have hθ : thetaSeq M cb δ sel π₀ data ρ πstar = fun j => ∑ t ∈ Finset.Icc 1 T, f t j := by
    funext j
    simp only [thetaSeq, hfdef, hWdef, Finset.mul_sum]
    rfl
  have hsum : ∀ t, Summable (f t) := by
    intro t
    simpa using summable_kappa_occ M hκ0 hκ1 (detPolicy πstar) ρ (W t) 0
  refine ⟨∑ t ∈ Finset.Icc 1 T, ∑' j, f t j, by
    rw [hθ]; exact hasSum_sum fun t _ => (hsum t).hasSum, ?_⟩
  set Y := Real.sqrt (H * ι) / (1 - γ) with hY
  set K1 := 6 + 11 * cb with hK1
  have hK10 : 0 ≤ K1 := by positivity
  -- the Cauchy–Schwarz factor
  have hCS : ∑ s, Real.sqrt (Cs * M.discountedStateOccupancy (detPolicy πstar) ρ s) ≤
      Real.sqrt (Cs * Fintype.card S) := by
    have h := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset S)
      (f := fun s => Cs * M.discountedStateOccupancy (detPolicy πstar) ρ s) (g := fun _ => 1)
      (fun s => mul_nonneg (by linarith) (M.discountedStateOccupancy_nonneg _ _ _))
      (fun _ => zero_le_one)
    simp only [Real.sqrt_one, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
    rw [← Finset.mul_sum, M.discountedStateOccupancy_sum, mul_one, ← Real.sqrt_mul (by linarith)]
      at h
    exact h
  have hper : ∀ t ∈ Finset.Icc 1 T, ∑' j, f t j ≤
      84 * (K1 * Y * Real.sqrt (Cs * Fintype.card S) / (1 - γ)) * (1 / Real.sqrt t) +
        84 * (c / (1 - γ)) / T := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    have hU : ∑' j : ℕ, f t j ≤
        84 * ((∑ s, M.discountedStateOccupancy (detPolicy πstar) ρ s * W t s) / (1 - γ) +
          δ * ‖W t‖ / ((Fintype.card S : ℝ) * (T : ℝ) ^ 4 * (1 - γ))) :=
      lcbq_useful M (detPolicy πstar) ρ δ T (W t) hδ hδ1 hT hι (hW0 t)
    have hd : ∑ s, M.discountedStateOccupancy (detPolicy πstar) ρ s * W t s ≤
        K1 * (Y / Real.sqrt t) * Real.sqrt (Cs * Fintype.card S) := by
      calc ∑ s, M.discountedStateOccupancy (detPolicy πstar) ρ s * W t s
          ≤ ∑ s, K1 * (Y / Real.sqrt t) *
              Real.sqrt (Cs * M.discountedStateOccupancy (detPolicy πstar) ρ s) :=
            Finset.sum_le_sum fun s _ =>
              dstar_mul_W_le M cb δ sel π₀ data ρ πstar db hcb hT hδ hδ1 hι hC hcount ht.1 ht.2 s
        _ = K1 * (Y / Real.sqrt t) *
              ∑ s, Real.sqrt (Cs * M.discountedStateOccupancy (detPolicy πstar) ρ s) := by
            rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left hCS (by positivity)
    have hnorm : ‖W t‖ ≤ c := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun s => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hW0 t s)]
      exact hWc t s
    have hST : (T : ℝ) ≤ (Fintype.card S : ℝ) * (T : ℝ) ^ 4 := by
      have : (T : ℝ) ≤ (T : ℝ) ^ 4 := by
        calc (T : ℝ) = (T : ℝ) ^ 1 := (pow_one _).symm
          _ ≤ (T : ℝ) ^ 4 := pow_le_pow_right₀ hT' (by norm_num)
      nlinarith
    have hsec : δ * ‖W t‖ / ((Fintype.card S : ℝ) * (T : ℝ) ^ 4 * (1 - γ)) ≤ c / (1 - γ) / T := by
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have h0 : δ * ‖W t‖ ≤ c := by nlinarith [norm_nonneg (W t)]
      have hc0 : 0 ≤ c := by positivity
      have h1 : δ * ‖W t‖ * ((1 - γ) * T) ≤ c * ((1 - γ) * T) :=
        mul_le_mul_of_nonneg_right h0 (by positivity)
      have h2 : c * ((1 - γ) * T) ≤ c * ((Fintype.card S : ℝ) * (T : ℝ) ^ 4 * (1 - γ)) := by
        apply mul_le_mul_of_nonneg_left _ hc0; nlinarith
      linarith
    calc ∑' j, f t j ≤ _ := hU
      _ ≤ 84 * (K1 * (Y / Real.sqrt t) * Real.sqrt (Cs * Fintype.card S) / (1 - γ) +
            c / (1 - γ) / T) := by gcongr
      _ = _ := by ring
  have hsqrt : ∑ t ∈ Finset.Icc 1 T, 1 / Real.sqrt (t : ℝ) ≤ 2 * Real.sqrt T :=
    qLearning_sum_reciprocalSqrt_le T
  set R := Real.sqrt (Cs * Fintype.card S * T * ι ^ 2 / (1 - γ) ^ 5) with hR
  have hmain : Y * Real.sqrt (Cs * Fintype.card S) / (1 - γ) * Real.sqrt T ≤
      Real.sqrt 5 * R := by
    rw [hR, ← Real.sqrt_mul (by norm_num)]
    apply Real.le_sqrt_of_sq_le
    have hHle : (H : ℝ) ≤ 5 * ι / (1 - γ) := horizon_le M hι
    have hH0 : (0 : ℝ) ≤ H := Nat.cast_nonneg _
    have e1 : (Y * Real.sqrt (Cs * Fintype.card S) / (1 - γ) * Real.sqrt T) ^ 2 =
        Real.sqrt (H * ι) ^ 2 * Real.sqrt (Cs * Fintype.card S) ^ 2 * Real.sqrt T ^ 2 /
          (1 - γ) ^ 4 := by rw [hY]; field_simp
    rw [e1, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    have hk : 0 ≤ ι * (Cs * Fintype.card S) * T := by positivity
    have hHx : (H : ℝ) * (1 - γ) ≤ 5 * ι := by rwa [le_div_iff₀ hx0] at hHle
    have e2 : (H : ℝ) * ι * (Cs * Fintype.card S) * T / (1 - γ) ^ 4 =
        ((H : ℝ) * (1 - γ)) * (ι * (Cs * Fintype.card S) * T) / (1 - γ) ^ 5 := by
      field_simp
    have e3 : 5 * (Cs * Fintype.card S * T * ι ^ 2 / (1 - γ) ^ 5) =
        (5 * ι) * (ι * (Cs * Fintype.card S) * T) / (1 - γ) ^ 5 := by ring
    rw [e2, e3]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hHx hk) (by positivity)
  have hRc : c / (1 - γ) ≤ R := by
    rw [hR]
    apply Real.le_sqrt_of_sq_le
    rw [hc, div_div, div_pow, one_pow, ← pow_two]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hι2 : 1 ≤ ι ^ 2 := one_le_pow₀ hι
    have h1 : 1 ≤ Cs * Fintype.card S * T * ι ^ 2 := by
      have := mul_le_mul hCs hS zero_le_one (by linarith)
      have := mul_le_mul this hT' zero_le_one (by positivity)
      have := mul_le_mul this hι2 zero_le_one (by positivity)
      simpa using this
    have h5 : (1 - γ) ^ 5 ≤ ((1 - γ) ^ 2) ^ 2 := by
      rw [← pow_mul]; exact pow_le_pow_of_le_one hx0.le hx1 (by norm_num)
    nlinarith [pow_pos hx0 5]
  have hs5 : Real.sqrt 5 ≤ 9 / 4 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  calc ∑ t ∈ Finset.Icc 1 T, ∑' j, f t j
      ≤ ∑ t ∈ Finset.Icc 1 T, (84 * (K1 * Y * Real.sqrt (Cs * Fintype.card S) / (1 - γ)) *
          (1 / Real.sqrt t) + 84 * (c / (1 - γ)) / T) := Finset.sum_le_sum hper
    _ = 84 * (K1 * Y * Real.sqrt (Cs * Fintype.card S) / (1 - γ)) *
          ∑ t ∈ Finset.Icc 1 T, 1 / Real.sqrt (t : ℝ) + 84 * (c / (1 - γ)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Nat.card_Icc,
          Nat.add_sub_cancel, nsmul_eq_mul]
        field_simp
    _ ≤ 84 * (K1 * Y * Real.sqrt (Cs * Fintype.card S) / (1 - γ)) * (2 * Real.sqrt T) +
          84 * R := by
        have h1 := mul_le_mul_of_nonneg_left hsqrt
          (by positivity : (0 : ℝ) ≤ 84 * (K1 * Y * Real.sqrt (Cs * Fintype.card S) / (1 - γ)))
        have h2 : 84 * (c / (1 - γ)) ≤ 84 * R := by linarith
        linarith
    _ = 168 * K1 * (Y * Real.sqrt (Cs * Fintype.card S) / (1 - γ) * Real.sqrt T) + 84 * R := by
        ring
    _ ≤ 168 * K1 * (Real.sqrt 5 * R) + 84 * R := by
        have := mul_le_mul_of_nonneg_left hmain (by positivity : (0 : ℝ) ≤ 168 * K1)
        linarith
    _ ≤ 168 * K1 * (9 / 4 * R) + 84 * R := by
        have h1 := mul_le_mul_of_nonneg_right hs5 hR0
        have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 168 * K1)
        linarith
    _ ≤ (3200 + 5600 * cb) * R := by
        have h1 := mul_nonneg hcb hR0
        have e : (3200 + 5600 * cb) * R - (168 * K1 * (9 / 4 * R) + 84 * R) =
            848 * R + 1442 * (cb * R) := by rw [hK1]; ring
        linarith

end Theta

end StatisticalRL.OfflineRL.LCBQ
