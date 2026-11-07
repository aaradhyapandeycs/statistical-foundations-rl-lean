import Formalization.OfflineRL.LCBQSeriesBasic
import Formalization.Probability.Variance

/-!
# LCB-Q, Lemma 6.12: the terms `ψ` and `φ` (deterministic part)

`lem:lcbq-alpha-xi-psi-phi-bound`, `chapters/offlineRL.tex:2309–2324`; proof of the `ψ, φ`
bounds `:4974–5496`.

* `d̃(s,a) = γ Σ_j κ^j d_j(s,a)` (`eq:dtilde-offlineQ`) and the series identities
  `ψ = Σ_j ψ_j`, `φ = Σ_j φ_j` (`eq:psi-ft-rewrite-offlineQ`, `eq:phi-gt-rewrite-offlineQ`);
* the envelope of `d̃/d^b` on well-covered pairs (`eq:dtilde-bound-offlineQ`,
  `eq:fg-envelope-offlineQ-B-defn`), from `lcbq_useful`;
* the decomposition `ψ ≤ κ₁ + κ₂` with `κ₃ ≤ 0` (`eq:psi-kappa-decomposition-offlineQ`,
  `eq:kappa3-bound-offlineQ`), using an indexing that makes the `E f_1` term unnecessary;
* the AM–GM absorption of the Freedman bounds (`eq:kappa1-well-covered-bound-offlineQ`).
-/

open scoped BigOperators ENNReal
open Filter Topology

namespace StatisticalRL.OfflineRL.LCBQ

open StatisticalRL StatisticalRL.OnlineRL
open Classical

set_option linter.unusedSectionVars false

variable {S A : Type*} [Fintype S] [Fintype A]

/-- `d̃(s,a) = γ Σ_j κ^j d_j(s,a)` (`eq:dtilde-offlineQ`, `offlineRL.tex:4979–4983`). -/
noncomputable def dTilde (M : DiscountedMDP S A) (ρ : FiniteDistribution S) (πstar : S → A)
    (κ : ℝ) (s : S) (a : A) : ℝ :=
  M.discount * ∑' j : ℕ, κ ^ j * dWeight M ρ πstar j s a

section DTilde

variable (M : DiscountedMDP S A) (ρ : FiniteDistribution S) (πstar : S → A)

theorem dWeight_nonneg (j : ℕ) (s : S) (a : A) : 0 ≤ dWeight M ρ πstar j s a := by
  unfold dWeight
  exact mul_nonneg (M.occupancyStateAt_nonneg _ _ _ _) (by split_ifs <;> norm_num)

theorem dWeight_le_one (j : ℕ) (s : S) (a : A) : dWeight M ρ πstar j s a ≤ 1 := by
  unfold dWeight
  split_ifs
  · rw [mul_one]; exact M.occupancyStateAt_le_one _ _ _ _
  · rw [mul_zero]; exact zero_le_one

theorem dWeight_of_ne (j : ℕ) (s : S) (a : A) (ha : a ≠ πstar s) : dWeight M ρ πstar j s a = 0 := by
  unfold dWeight; rw [if_neg ha, mul_zero]

theorem summable_dWeight {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (s : S) (a : A) :
    Summable (fun j : ℕ => κ ^ j * dWeight M ρ πstar j s a) := by
  apply Summable.of_norm_bounded (g := fun j => κ ^ j)
    (summable_geometric_of_lt_one hκ0 hκ1)
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hκ0 j) (dWeight_nonneg M ρ πstar j s a))]
  exact mul_le_of_le_one_right (pow_nonneg hκ0 j) (dWeight_le_one M ρ πstar j s a)

theorem hasSum_dTilde {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (s : S) (a : A) :
    HasSum (fun j : ℕ => M.discount * κ ^ j * dWeight M ρ πstar j s a) (dTilde M ρ πstar κ s a) := by
  have h := ((summable_dWeight M ρ πstar hκ0 hκ1 s a).hasSum).mul_left M.discount
  unfold dTilde
  convert h using 1
  funext j; ring

theorem dTilde_nonneg {κ : ℝ} (hκ0 : 0 ≤ κ) (s : S) (a : A) : 0 ≤ dTilde M ρ πstar κ s a := by
  unfold dTilde
  exact mul_nonneg M.discount_nonneg (tsum_nonneg fun j =>
    mul_nonneg (pow_nonneg hκ0 j) (dWeight_nonneg M ρ πstar j s a))

theorem dTilde_of_ne (κ : ℝ) (s : S) (a : A) (ha : a ≠ πstar s) : dTilde M ρ πstar κ s a = 0 := by
  unfold dTilde
  simp [dWeight_of_ne M ρ πstar _ s a ha]

/-- `d̃(s,π⋆(s)) ≤ 84 (d⋆(s)/(1-γ) + δ/(ST⁴(1-γ)))` (`eq:dtilde-bound-offlineQ`). -/
theorem dTilde_le {T : ℕ} {δ : ℝ} (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hι : 1 ≤ iota S A T δ) (s : S) (a : A) :
    dTilde M ρ πstar (kappa M.discount (horizon M.discount (iota S A T δ))) s a ≤
      84 * (M.discountedStateOccupancy (detPolicy πstar) ρ s / (1 - M.discount) +
        δ / ((Fintype.card S : ℝ) * (T : ℝ) ^ 4 * (1 - M.discount))) := by
  set κ := kappa M.discount (horizon M.discount (iota S A T δ))
  have hκ0 : 0 ≤ κ := kappa_nonneg M _
  have hκ1 : κ < 1 := kappa_lt_one M hι
  have hx0 : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hRHS : 0 ≤ 84 * (M.discountedStateOccupancy (detPolicy πstar) ρ s / (1 - M.discount) +
      δ / ((Fintype.card S : ℝ) * (T : ℝ) ^ 4 * (1 - M.discount))) := by
    have := M.discountedStateOccupancy_nonneg (detPolicy πstar) ρ s
    have : (0 : ℝ) < T := by exact_mod_cast hT
    positivity
  by_cases ha : a = πstar s
  · subst ha
    set W : S → ℝ := fun x => if x = s then 1 else 0 with hW
    have hW0 : ∀ x, 0 ≤ W x := fun x => by simp only [hW]; split_ifs <;> norm_num
    have hU : ∑' j : ℕ, κ ^ j * ∑ x, M.occupancyStateAt (detPolicy πstar) ρ j x * W x ≤
        84 * ((∑ x, M.discountedStateOccupancy (detPolicy πstar) ρ x * W x) / (1 - M.discount) +
          δ * ‖W‖ / ((Fintype.card S : ℝ) * (T : ℝ) ^ 4 * (1 - M.discount))) :=
      lcbq_useful M (detPolicy πstar) ρ δ T W hδ hδ1 hT hι hW0
    have h1 : ∀ j, ∑ x, M.occupancyStateAt (detPolicy πstar) ρ j x * W x =
        dWeight M ρ πstar j s (πstar s) := by
      intro j
      simp [hW, dWeight]
    have h2 : ∑ x, M.discountedStateOccupancy (detPolicy πstar) ρ x * W x =
        M.discountedStateOccupancy (detPolicy πstar) ρ s := by simp [hW]
    have h3 : ‖W‖ ≤ 1 := by
      refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hW0 x)]
      simp only [hW]; split_ifs <;> norm_num
    simp_rw [h1] at hU
    rw [h2] at hU
    have hle : dTilde M ρ πstar κ s (πstar s) ≤ ∑' j : ℕ, κ ^ j * dWeight M ρ πstar j s (πstar s) := by
      unfold dTilde
      exact mul_le_of_le_one_left (tsum_nonneg fun j =>
        mul_nonneg (pow_nonneg hκ0 j) (dWeight_nonneg M ρ πstar j s _)) M.discount_lt_one.le
    refine hle.trans (hU.trans ?_)
    gcongr
    calc δ * ‖W‖ ≤ δ * 1 := mul_le_mul_of_nonneg_left h3 hδ.le
      _ = δ := mul_one δ
  · rw [dTilde_of_ne M ρ πstar _ s a ha]
    exact hRHS

end DTilde

section Absorb

/-- AM–GM absorption of a Freedman bound with variance proxy `≤ C·A`
(`eq:kappa1-well-covered-bound-offlineQ`): `|Z| ≤ A/(2H) + C(4HL + 1 + 10L)`. -/
theorem freedman_absorb {Z A V C H L Tr : ℝ} (hA : 0 ≤ A) (hC : 0 ≤ C) (hH : 0 < H)
    (hL : 0 ≤ L) (hV : V ≤ C * A) (hTr1 : Tr ≤ 1)
    (hZ : |Z| ≤ Real.sqrt (8 * max V (Tr * C ^ 2) * L) + 4 / 3 * C * L) :
    |Z| ≤ A / (2 * H) + C * (4 * H * L + 1 + 10 * L) := by
  have hmax : max V (Tr * C ^ 2) ≤ C * A + C ^ 2 := by
    apply max_le
    · nlinarith [sq_nonneg C]
    · nlinarith [sq_nonneg C]
  have hs1 : Real.sqrt (8 * max V (Tr * C ^ 2) * L) ≤
      Real.sqrt (8 * C * A * L) + Real.sqrt (8 * C ^ 2 * L) := by
    calc Real.sqrt (8 * max V (Tr * C ^ 2) * L)
        ≤ Real.sqrt (8 * C * A * L + 8 * C ^ 2 * L) := by
          apply Real.sqrt_le_sqrt; nlinarith
      _ ≤ _ := by
          rw [Real.sqrt_le_iff]
          refine ⟨by positivity, ?_⟩
          have h1 := Real.sq_sqrt (show 0 ≤ 8 * C * A * L by positivity)
          have h2 := Real.sq_sqrt (show 0 ≤ 8 * C ^ 2 * L by positivity)
          nlinarith [mul_nonneg (Real.sqrt_nonneg (8 * C * A * L))
            (Real.sqrt_nonneg (8 * C ^ 2 * L))]
  have hs2 : Real.sqrt (8 * C * A * L) ≤ A / (2 * H) + 4 * C * H * L := by
    -- `√(xy) ≤ (x+y)/2` with `x = A/H`, `y = 8CHL`
    have hx : 0 ≤ A / H := div_nonneg hA hH.le
    have hy : 0 ≤ 8 * C * H * L := by positivity
    have hxy : 8 * C * A * L = (A / H) * (8 * C * H * L) := by field_simp
    rw [hxy, Real.sqrt_mul hx]
    nlinarith [sq_nonneg (Real.sqrt (A / H) - Real.sqrt (8 * C * H * L)), Real.sq_sqrt hx,
      Real.sq_sqrt hy, show A / (2 * H) = A / H / 2 by field_simp]
  have hs3 : Real.sqrt (8 * C ^ 2 * L) ≤ C * (1 + 8 * L) := by
    have h8L : Real.sqrt (8 * L) ≤ 1 + 8 * L := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith
    rw [show 8 * C ^ 2 * L = C ^ 2 * (8 * L) by ring, Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]
    exact mul_le_mul_of_nonneg_left h8L hC
  have : 4 / 3 * C * L ≤ 2 * C * L := by nlinarith [mul_nonneg hC hL]
  nlinarith

end Absorb

section Variance

variable {α : Type*} [Fintype α]

theorem variance_le_mul_expectation (d : FiniteDistribution α) (h : α → ℝ) {C : ℝ}
    (hh : ∀ x, 0 ≤ h x ∧ h x ≤ C) : d.variance h ≤ C * d.expectation h := by
  refine (d.variance_le_expectation_sq h).trans ?_
  rw [← FiniteDistribution.expectation_mul]
  exact d.expectation_mono fun x => by nlinarith [hh x]

end Variance

section Series

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  {T : ℕ} (data : Fin T → (S × A) × S) (ρ : FiniteDistribution S) (πstar : S → A)
  (db : FiniteDistribution (S × A))

/-- `ψ = Σ_t {E_{d^b} f_t − (1+1/H) f_t(X_t)}` (`eq:psi-ft-rewrite-offlineQ`), written with
`E_{d^b} f_t = Σ_{s,a} d̃(s,a) F_t(s,a)`; sample `u` is iteration `t = u+1`. -/
noncomputable def psiTotal : ℝ :=
  let κ := kappa M.discount (horizon M.discount (iota S A T δ))
  let c := 1 + 1 / (horizon M.discount (iota S A T δ) : ℝ)
  ∑ u : Fin T,
    ((∑ s, ∑ a, dTilde M ρ πstar κ s a * visitDeltaSum M cb δ sel π₀ data (u.val + 1) s a) -
      c * (dTilde M ρ πstar κ (data u).1.1 (data u).1.2 / db.prob (data u).1) *
        visitDeltaSum M cb δ sel π₀ data (u.val + 1) (data u).1.1 (data u).1.2)

/-- `φ = (1+1/H)² Σ_t {g_t(X_t) − (1+1/H) E_{d^b} g_t}` (`eq:phi-gt-rewrite-offlineQ`). -/
noncomputable def phiTotal : ℝ :=
  let κ := kappa M.discount (horizon M.discount (iota S A T δ))
  let c := 1 + 1 / (horizon M.discount (iota S A T δ) : ℝ)
  c ^ 2 * ∑ u : Fin T,
    ((dTilde M ρ πstar κ (data u).1.1 (data u).1.2 / db.prob (data u).1) *
        (M.transition (data u).1.1 (data u).1.2).expectation (delta M cb δ sel π₀ data u.val) -
      c * ∑ s, ∑ a, dTilde M ρ πstar κ s a *
        (M.transition s a).expectation (delta M cb δ sel π₀ data u.val))

theorem psiSeq_hasSum (hι : 1 ≤ iota S A T δ) :
    HasSum (psiSeq M cb δ sel π₀ data ρ πstar db) (psiTotal M cb δ sel π₀ data ρ πstar db) := by
  set κ := kappa M.discount (horizon M.discount (iota S A T δ)) with hκ
  set c := 1 + 1 / (horizon M.discount (iota S A T δ) : ℝ) with hc
  have hκ0 : 0 ≤ κ := kappa_nonneg M _
  have hκ1 : κ < 1 := kappa_lt_one M hι
  set F := fun (u : Fin T) (s : S) (a : A) => visitDeltaSum M cb δ sel π₀ data (u.val + 1) s a
  set e := fun (j : ℕ) (s : S) (a : A) => M.discount * κ ^ j * dWeight M ρ πstar j s a
  have he : ∀ s a, HasSum (fun j => e j s a) (dTilde M ρ πstar κ s a) :=
    fun s a => hasSum_dTilde M ρ πstar hκ0 hκ1 s a
  have heq : psiSeq M cb δ sel π₀ data ρ πstar db = fun j => ∑ u : Fin T,
      ((∑ s, ∑ a, e j s a * F u s a) -
        (c * F u (data u).1.1 (data u).1.2 / db.prob (data u).1) * e j (data u).1.1 (data u).1.2) := by
    funext j
    simp only [psiSeq, Finset.mul_sum, e, F, ← hκ, ← hc]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_sub, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
    · ring
  rw [heq]
  have h := hasSum_sum (s := (Finset.univ : Finset (Fin T))) fun u _ =>
    (hasSum_sum (s := (Finset.univ : Finset S)) fun s _ =>
      hasSum_sum (s := (Finset.univ : Finset A)) fun a _ => (he s a).mul_right (F u s a)).sub
      ((he (data u).1.1 (data u).1.2).mul_left (c * F u (data u).1.1 (data u).1.2 / db.prob (data u).1))
  convert h using 1
  unfold psiTotal
  simp only [← hκ, ← hc]
  refine Finset.sum_congr rfl fun u _ => ?_
  congr 1
  ring

theorem phiSeq_hasSum (hι : 1 ≤ iota S A T δ) :
    HasSum (phiSeq M cb δ sel π₀ data ρ πstar db) (phiTotal M cb δ sel π₀ data ρ πstar db) := by
  set κ := kappa M.discount (horizon M.discount (iota S A T δ)) with hκ
  set c := 1 + 1 / (horizon M.discount (iota S A T δ) : ℝ) with hc
  have hκ0 : 0 ≤ κ := kappa_nonneg M _
  have hκ1 : κ < 1 := kappa_lt_one M hι
  set G := fun (u : Fin T) (s : S) (a : A) =>
    (M.transition s a).expectation (delta M cb δ sel π₀ data u.val)
  set e := fun (j : ℕ) (s : S) (a : A) => M.discount * κ ^ j * dWeight M ρ πstar j s a
  have he : ∀ s a, HasSum (fun j => e j s a) (dTilde M ρ πstar κ s a) :=
    fun s a => hasSum_dTilde M ρ πstar hκ0 hκ1 s a
  have heq : phiSeq M cb δ sel π₀ data ρ πstar db = fun j => c ^ 2 * ∑ u : Fin T,
      ((G u (data u).1.1 (data u).1.2 / db.prob (data u).1) * e j (data u).1.1 (data u).1.2 -
        c * ∑ s, ∑ a, e j s a * G u s a) := by
    funext j
    simp only [phiSeq, e, G, ← hκ, ← hc]
    rw [show ∀ X : ℝ, M.discount * κ ^ j * c ^ 2 * X = c ^ 2 * (M.discount * κ ^ j * X) from
      fun X => by ring, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [mul_sub]
    congr 1
    · ring
    · rw [show ∀ X : ℝ, M.discount * κ ^ j * (c * X) = c * (M.discount * κ ^ j * X) from
        fun X => by ring, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      ring
  rw [heq]
  have h := (hasSum_sum (s := (Finset.univ : Finset (Fin T))) fun u _ =>
    ((he (data u).1.1 (data u).1.2).mul_left (G u (data u).1.1 (data u).1.2 / db.prob (data u).1)).sub
      ((hasSum_sum (s := (Finset.univ : Finset S)) fun s _ =>
      hasSum_sum (s := (Finset.univ : Finset A)) fun a _ => (he s a).mul_right (G u s a)).mul_left c)).mul_left
      (c ^ 2)
  convert h using 1
  unfold phiTotal
  simp only [← hκ, ← hc]
  congr 1
  refine Finset.sum_congr rfl fun u _ => ?_
  congr 1
  ring

end Series

section Decomposition

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  {T : ℕ} (data : Fin T → (S × A) × S) (ρ : FiniteDistribution S) (πstar : S → A)
  (db : FiniteDistribution (S × A))

/-- `d̃(p)/d^b(p)` restricted to the well-covered set `I = {p : d^b(p) ≥ thr}`
(`eq:defn-I-set-kapp1-lcbq`). -/
noncomputable def ratioI (κ thr : ℝ) (p : S × A) : ℝ :=
  if thr ≤ db.prob p then dTilde M ρ πstar κ p.1 p.2 / db.prob p else 0

theorem visitDeltaSum_zero (s : S) (a : A) : visitDeltaSum M cb δ sel π₀ data 0 s a = 0 := by
  simp [visitDeltaSum, run_zero, init]

theorem visitDeltaSum_succ_of_ne {u : ℕ} (hu : u < T) (s : S) (a : A)
    (hne : (s, a) ≠ (data ⟨u, hu⟩).1) :
    visitDeltaSum M cb δ sel π₀ data (u + 1) s a = visitDeltaSum M cb δ sel π₀ data u s a := by
  have hc : (run M cb δ sel π₀ data (u + 1)).count s a = (run M cb δ sel π₀ data u).count s a := by
    rw [run_succ_of_lt M cb δ sel π₀ data hu, step_count, if_neg]
    rintro ⟨h1, h2⟩
    exact hne (Prod.ext h1 h2)
  simp only [visitDeltaSum, hc]

/-- `0 ≤ Σ_i η_i^n P_{s,a}Δ_{k_i−1} ≤ 1/(1-γ)` under pessimism before time `u`. -/
theorem visitDeltaSum_bounds (hcb : 0 ≤ cb) (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1) {u : ℕ}
    (hu : u ≤ T) (hpess : ∀ v, v < u → ∀ s, (run M cb δ sel π₀ data v).V s ≤ optValue M s)
    (s : S) (a : A) :
    0 ≤ visitDeltaSum M cb δ sel π₀ data u s a ∧
      visitDeltaSum M cb δ sel π₀ data u s a ≤ 1 / (1 - M.discount) := by
  have hH := horizon_pos M hT hδ hδ1
  set n := (run M cb δ sel π₀ data u).count s a with hn
  have hcnt : n = Nat.count (visitPred data (s, a)) u := run_count M cb δ sel π₀ data hu s a
  have hterm : ∀ i ∈ Finset.range n, 0 ≤ (M.transition s a).expectation
      (delta M cb δ sel π₀ data (visitTime data (s, a) i)) ∧
      (M.transition s a).expectation (delta M cb δ sel π₀ data (visitTime data (s, a) i)) ≤
        1 / (1 - M.discount) := by
    intro i hi
    rw [Finset.mem_range, hcnt] at hi
    have hlt := visitTime_lt data hi
    constructor
    · apply FiniteDistribution.expectation_nonneg
      intro x
      have := hpess _ hlt x
      unfold delta; linarith
    · exact FiniteDistribution.expectation_le_const _ fun x => delta_le M cb δ sel π₀ data hcb _ x
  simp only [visitDeltaSum, ← hn]
  constructor
  · exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (onlineQRateWeight_nonneg hH _ _) (hterm i hi).1
  · rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, Finset.range_zero, Finset.sum_empty]
      exact div_nonneg zero_le_one (by linarith [M.discount_lt_one])
    · calc ∑ i ∈ Finset.range n, onlineQRateWeight (horizon M.discount (iota S A T δ)) n (i + 1) *
            (M.transition s a).expectation (delta M cb δ sel π₀ data (visitTime data (s, a) i))
          ≤ ∑ i ∈ Finset.range n, onlineQRateWeight (horizon M.discount (iota S A T δ)) n (i + 1) *
              (1 / (1 - M.discount)) :=
            Finset.sum_le_sum fun i hi =>
              mul_le_mul_of_nonneg_left (hterm i hi).2 (onlineQRateWeight_nonneg hH _ _)
        _ = 1 / (1 - M.discount) := by
            rw [← Finset.sum_mul, sum_rateWeight_range_eq_one hH hpos, one_mul]

theorem sum_action_collapse (f : S → A → ℝ) (hf : ∀ s a, a ≠ πstar s → f s a = 0) (s : S) :
    ∑ a, f s a = f s (πstar s) :=
  Finset.sum_eq_single (πstar s) (fun a _ ha => hf s a ha) (fun h => absurd (Finset.mem_univ _) h)

/-- `Σ_s d̃(s,π⋆(s)) ≤ 168/(1-γ)` and the poorly-covered part `≤ 168 C⋆/(T(1-γ))`
(`eq:E-Ic-f-ub-123`, `eq:kappa2-bound-offlineQ`). -/
theorem sum_dTilde_le (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1) (hι : 1 ≤ iota S A T δ)
    (hC : concentrability M ρ πstar db ≠ ⊤) :
    let κ := kappa M.discount (horizon M.discount (iota S A T δ))
    let thr := δ / (5 * Fintype.card S * T)
    (∑ s, dTilde M ρ πstar κ s (πstar s) ≤ 168 / (1 - M.discount)) ∧
      ∑ s, (if db.prob (s, πstar s) < thr then dTilde M ρ πstar κ s (πstar s) else 0) ≤
        168 * (concentrability M ρ πstar db).toReal / (T * (1 - M.discount)) := by
  intro κ thr
  haveI := M.state_nonempty
  have hS : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hT' : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hx0 : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  have hCs := one_le_concentrability M ρ πstar db hC
  have hT4 : (T : ℝ) ≤ (T : ℝ) ^ 4 := by
    calc (T : ℝ) = (T : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (T : ℝ) ^ 4 := pow_le_pow_right₀ hT' (by norm_num)
  have hsmall : δ / ((Fintype.card S : ℝ) * (T : ℝ) ^ 4 * (1 - M.discount)) ≤
      1 / (Fintype.card S * T * (1 - M.discount)) := by
    apply div_le_div₀ zero_le_one hδ1.le (by positivity)
    have : (Fintype.card S : ℝ) * T ≤ (Fintype.card S : ℝ) * (T : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_left hT4 (by positivity)
    nlinarith
  constructor
  · calc ∑ s, dTilde M ρ πstar κ s (πstar s)
        ≤ ∑ s, 84 * (M.discountedStateOccupancy (detPolicy πstar) ρ s / (1 - M.discount) +
            1 / (Fintype.card S * T * (1 - M.discount))) :=
          Finset.sum_le_sum fun s _ =>
            (dTilde_le M ρ πstar hT hδ hδ1 hι s _).trans (by gcongr)
      _ = 84 * (1 / (1 - M.discount) + 1 / (T * (1 - M.discount))) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div,
            M.discountedStateOccupancy_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          field_simp
      _ ≤ 84 * (1 / (1 - M.discount) + 1 / (1 - M.discount)) := by
          gcongr
          exact le_mul_of_one_le_left hx0.le hT'
      _ = 168 / (1 - M.discount) := by ring
  · have hper : ∀ s, (if db.prob (s, πstar s) < thr then dTilde M ρ πstar κ s (πstar s) else 0) ≤
        84 * ((concentrability M ρ πstar db).toReal * thr / (1 - M.discount) +
          1 / (Fintype.card S * T * (1 - M.discount))) := by
      intro s
      have hR : 0 ≤ 84 * ((concentrability M ρ πstar db).toReal * thr / (1 - M.discount) +
          1 / (Fintype.card S * T * (1 - M.discount))) := by
        have : 0 ≤ thr := by positivity
        positivity
      split_ifs with hlt
      · refine (dTilde_le M ρ πstar hT hδ hδ1 hι s _).trans ?_
        have hd := dstarState_le M ρ πstar db hC s
        have : M.discountedStateOccupancy (detPolicy πstar) ρ s ≤
            (concentrability M ρ πstar db).toReal * thr :=
          hd.trans (mul_le_mul_of_nonneg_left hlt.le (by linarith))
        gcongr
      · exact hR
    calc ∑ s, (if db.prob (s, πstar s) < thr then dTilde M ρ πstar κ s (πstar s) else 0)
        ≤ ∑ _s : S, 84 * ((concentrability M ρ πstar db).toReal * thr / (1 - M.discount) +
          1 / (Fintype.card S * T * (1 - M.discount))) := Finset.sum_le_sum fun s _ => hper s
      _ = 84 * ((concentrability M ρ πstar db).toReal * δ / (5 * T * (1 - M.discount)) +
          1 / (T * (1 - M.discount))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          simp only [thr]
          field_simp
      _ ≤ 84 * ((concentrability M ρ πstar db).toReal / (T * (1 - M.discount)) +
          (concentrability M ρ πstar db).toReal / (T * (1 - M.discount))) := by
          have hP : 0 < (T : ℝ) * (1 - M.discount) := by positivity
          have h1 : (concentrability M ρ πstar db).toReal * δ / (5 * T * (1 - M.discount)) ≤
              (concentrability M ρ πstar db).toReal / (T * (1 - M.discount)) := by
            rw [div_le_div_iff₀ (by positivity) hP]
            have hCP := mul_pos (by linarith : (0 : ℝ) < (concentrability M ρ πstar db).toReal) hP
            nlinarith
          have h2 : 1 / (T * (1 - M.discount)) ≤
              (concentrability M ρ πstar db).toReal / (T * (1 - M.discount)) :=
            div_le_div_of_nonneg_right hCs hP.le
          linarith
      _ = _ := by ring

end Decomposition

section Bounds

variable (M : DiscountedMDP S A) (cb δ : ℝ) (sel : (A → ℝ) → A) (π₀ : S → A)
  {T : ℕ} (data : Fin T → (S × A) × S) (ρ : FiniteDistribution S) (πstar : S → A)
  (db : FiniteDistribution (S × A))

/-- `E_{d^b}[1_I·(d̃/d^b)·G] = Σ_{(s,a) ∈ I} d̃(s,a) G(s,a)` (well-covered part). -/
noncomputable def edI (κ thr : ℝ) (G : S → A → ℝ) : ℝ :=
  ∑ s, ∑ a, (if thr ≤ db.prob (s, a) then dTilde M ρ πstar κ s a * G s a else 0)

theorem edI_nonneg {κ thr : ℝ} (hκ0 : 0 ≤ κ) (G : S → A → ℝ) (hG : ∀ s a, 0 ≤ G s a) :
    0 ≤ edI M ρ πstar db κ thr G :=
  Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun a _ => by
    split_ifs
    · exact mul_nonneg (dTilde_nonneg M ρ πstar hκ0 s a) (hG s a)
    · exact le_rfl

/-- `ratioI·G ≤ (d̃/d^b)·G`, with equality on `I`. -/
theorem ratioI_mul_le {κ thr : ℝ} (hκ0 : 0 ≤ κ) (p : S × A) (g : ℝ) (hg : 0 ≤ g) :
    ratioI M ρ πstar db κ thr p * g ≤ dTilde M ρ πstar κ p.1 p.2 / db.prob p * g := by
  unfold ratioI
  split_ifs
  · exact le_rfl
  · rw [zero_mul]
    exact mul_nonneg (div_nonneg (dTilde_nonneg M ρ πstar hκ0 _ _) (db.prob_nonneg _)) hg

theorem one_le_c_le_two {H : ℕ} (hH : 0 < H) :
    1 ≤ 1 + 1 / (H : ℝ) ∧ 1 + 1 / (H : ℝ) ≤ 2 := by
  have hH1 : (1 : ℝ) ≤ H := by exact_mod_cast hH
  have h0 : 0 ≤ 1 / (H : ℝ) := by positivity
  have h1 : 1 / (H : ℝ) ≤ 1 := by rw [div_le_one (by positivity)]; exact hH1
  constructor <;> linarith

set_option maxHeartbeats 1000000 in
/-- **ψ bound, deterministic part** (`eq:psi-kappa-decomposition-offlineQ` through
`eq:psi-bound-offlineQ`): under pessimism up to time `T` and the absorbed Freedman bound for the
well-covered martingale, `ψ ≤ 2K₀ + 168 C⋆/(1-γ)² + 168/(1-γ)²`. -/
theorem psiTotal_le (hcb : 0 ≤ cb) (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hι : 1 ≤ iota S A T δ) (hC : concentrability M ρ πstar db ≠ ⊤)
    (hpess : ∀ u, u ≤ T → ∀ s, (run M cb δ sel π₀ data u).V s ≤ optValue M s)
    (K₀ : ℝ) (hK₀ : 0 ≤ K₀)
    (hZ : |∑ u : Fin T,
        (ratioI M ρ πstar db (kappa M.discount (horizon M.discount (iota S A T δ)))
            (δ / (5 * Fintype.card S * T)) (data u).1 *
          visitDeltaSum M cb δ sel π₀ data u.val (data u).1.1 (data u).1.2 -
        edI M ρ πstar db (kappa M.discount (horizon M.discount (iota S A T δ)))
          (δ / (5 * Fintype.card S * T)) (visitDeltaSum M cb δ sel π₀ data u.val))| ≤
      (∑ u : Fin T, edI M ρ πstar db (kappa M.discount (horizon M.discount (iota S A T δ)))
          (δ / (5 * Fintype.card S * T)) (visitDeltaSum M cb δ sel π₀ data u.val)) /
        (2 * horizon M.discount (iota S A T δ)) + K₀) :
    psiTotal M cb δ sel π₀ data ρ πstar db ≤
      2 * K₀ + 168 * (concentrability M ρ πstar db).toReal / (1 - M.discount) ^ 2 +
        168 / (1 - M.discount) ^ 2 := by
  set H := horizon M.discount (iota S A T δ) with hHdef
  set κ := kappa M.discount H with hκ
  set thr := δ / (5 * Fintype.card S * T) with hthr
  set c := 1 + 1 / (H : ℝ) with hc
  set Cs := (concentrability M ρ πstar db).toReal with hCs
  have hHpos : 0 < H := horizon_pos M hT hδ hδ1
  have hHr : (0 : ℝ) < H := by exact_mod_cast hHpos
  obtain ⟨hc1, hc2⟩ := one_le_c_le_two hHpos
  have hκ0 : 0 ≤ κ := kappa_nonneg M _
  have hx0 : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  set c0 := 1 / (1 - M.discount) with hc0
  have hc00 : 0 ≤ c0 := by positivity
  set F : ℕ → S → A → ℝ := fun u s a => visitDeltaSum M cb δ sel π₀ data u s a with hF
  have hFb : ∀ u, u ≤ T → ∀ s a, 0 ≤ F u s a ∧ F u s a ≤ c0 := fun u hu s a =>
    visitDeltaSum_bounds M cb δ sel π₀ data hcb hT hδ hδ1 hu
      (fun v hv s => hpess v (by omega) s) s a
  set r : S × A → ℝ := fun p => dTilde M ρ πstar κ p.1 p.2 / db.prob p with hr
  have hr0 : ∀ p, 0 ≤ r p := fun p => div_nonneg (dTilde_nonneg M ρ πstar hκ0 _ _) (db.prob_nonneg _)
  set f : ℕ → S × A → ℝ := fun u p => r p * F u p.1 p.2 with hf
  set Ed : ℕ → ℝ := fun u => ∑ s, ∑ a, dTilde M ρ πstar κ s a * F u s a with hEd
  set EdI : ℕ → ℝ := fun u => edI M ρ πstar db κ thr (F u) with hEdI
  set EdIc : ℕ → ℝ := fun u => ∑ s, ∑ a,
    (if thr ≤ db.prob (s, a) then 0 else dTilde M ρ πstar κ s a * F u s a) with hEdIc
  set ℓ : Fin T → S × A := fun u => (data u).1 with hℓ
  set fI : Fin T → ℝ := fun u => ratioI M ρ πstar db κ thr (ℓ u) * F u.val (ℓ u).1 (ℓ u).2
    with hfI
  -- (1) the source expression
  have h1 : psiTotal M cb δ sel π₀ data ρ πstar db =
      ∑ u : Fin T, (Ed (u.val + 1) - c * f (u.val + 1) (ℓ u)) := by
    simp only [psiTotal]
    rw [← hHdef, ← hκ, ← hc]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [hEd, hf, hr, hF, hℓ]
    ring
  -- (2) telescoping of `Ed`
  have hEd0 : Ed 0 = 0 := by simp [hEd, hF, visitDeltaSum_zero]
  have h2 : ∑ u : Fin T, (Ed (u.val + 1) - Ed u.val) = Ed T := by
    rw [Fin.sum_univ_eq_sum_range (fun u => Ed (u + 1) - Ed u) T, Finset.sum_range_sub, hEd0,
      sub_zero]
  -- (3) `κ₃ ≤ 0`
  have h3 : ∑ u : Fin T, (f u.val (ℓ u) - f (u.val + 1) (ℓ u)) ≤ 0 := by
    have heq : ∑ u : Fin T, (f u.val (ℓ u) - f (u.val + 1) (ℓ u)) =
        ∑ p : S × A, (f 0 p - f T p) := by
      calc ∑ u : Fin T, (f u.val (ℓ u) - f (u.val + 1) (ℓ u))
          = ∑ u : Fin T, ∑ p : S × A, (f u.val p - f (u.val + 1) p) := by
            refine Finset.sum_congr rfl fun u _ => ?_
            refine (Finset.sum_eq_single (f := fun p => f u.val p - f (u.val + 1) p) (ℓ u)
              (fun p _ hp => by
                have := visitDeltaSum_succ_of_ne M cb δ sel π₀ data u.isLt p.1 p.2 hp
                show f u.val p - f (u.val + 1) p = 0
                simp only [hf, hF, this, sub_self])
              (fun h => absurd (Finset.mem_univ _) h)).symm
        _ = ∑ p : S × A, ∑ u : Fin T, (f u.val p - f (u.val + 1) p) := Finset.sum_comm
        _ = ∑ p : S × A, (f 0 p - f T p) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [Fin.sum_univ_eq_sum_range (fun u => f u p - f (u + 1) p) T,
              Finset.sum_range_sub']
    rw [heq]
    refine Finset.sum_nonpos fun p _ => ?_
    have h0 : f 0 p = 0 := by simp [hf, hF, visitDeltaSum_zero]
    have hT0 : 0 ≤ f T p := mul_nonneg (hr0 p) (hFb T le_rfl p.1 p.2).1
    linarith
  -- (4) the well-covered split, termwise
  have hEdsplit : ∀ u, Ed u = EdI u + EdIc u := by
    intro u
    simp only [hEd, hEdI, hEdIc, edI, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> ring
  have h4 : ∀ u : Fin T, Ed u.val - c * f u.val (ℓ u) ≤
      c * (EdI u.val - fI u) - 1 / (H : ℝ) * EdI u.val + EdIc u.val := by
    intro u
    have hfI : fI u ≤ f u.val (ℓ u) := ratioI_mul_le M ρ πstar db hκ0 _ _
      (hFb u.val u.isLt.le _ _).1
    have := hEdsplit u.val
    have hcf : c * fI u ≤ c * f u.val (ℓ u) := mul_le_mul_of_nonneg_left hfI (by linarith)
    have hcH : c - 1 = 1 / (H : ℝ) := by rw [hc]; ring
    nlinarith
  -- (5) Freedman, absorbed
  set Atot := ∑ u : Fin T, EdI u.val with hAtot
  have hA0 : 0 ≤ Atot := Finset.sum_nonneg fun u _ =>
    edI_nonneg M ρ πstar db hκ0 _ fun s a => (hFb u.val u.isLt.le s a).1
  have hZ' : |∑ u : Fin T, (fI u - EdI u.val)| ≤ Atot / (2 * H) + K₀ := hZ
  have h5 : ∑ u : Fin T, (Ed u.val - c * f u.val (ℓ u)) ≤ 2 * K₀ + ∑ u : Fin T, EdIc u.val := by
    calc ∑ u : Fin T, (Ed u.val - c * f u.val (ℓ u))
        ≤ ∑ u : Fin T, (c * (EdI u.val - fI u) - 1 / (H : ℝ) * EdI u.val + EdIc u.val) :=
          Finset.sum_le_sum fun u _ => h4 u
      _ = -(c * ∑ u : Fin T, (fI u - EdI u.val)) - 1 / (H : ℝ) * Atot +
            ∑ u : Fin T, EdIc u.val := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            hAtot, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
          ring
      _ ≤ c * (Atot / (2 * H) + K₀) - 1 / (H : ℝ) * Atot + ∑ u : Fin T, EdIc u.val := by
          have := neg_abs_le (∑ u : Fin T, (fI u - EdI u.val))
          have hm := mul_le_mul_of_nonneg_left hZ' (by linarith : (0 : ℝ) ≤ c)
          nlinarith [abs_nonneg (∑ u : Fin T, (fI u - EdI u.val))]
      _ ≤ 2 * K₀ + ∑ u : Fin T, EdIc u.val := by
          have e : c * (Atot / (2 * H)) - 1 / (H : ℝ) * Atot = (c / 2 - 1) * (Atot / H) := by
            field_simp
          have hAH : 0 ≤ Atot / H := div_nonneg hA0 hHr.le
          have : c * (Atot / (2 * H) + K₀) - 1 / (H : ℝ) * Atot =
              (c / 2 - 1) * (Atot / H) + c * K₀ := by rw [mul_add, ← e]; ring
          nlinarith
  -- (6) the deterministic pieces
  obtain ⟨hsumd, hsumIc⟩ := sum_dTilde_le M δ ρ πstar db hT hδ hδ1 hι hC
  have hcollapse : ∀ (G : S → A → ℝ) (P : S → A → Prop) [∀ s a, Decidable (P s a)] (s : S),
      ∑ a, (if P s a then 0 else dTilde M ρ πstar κ s a * G s a) =
        (if P s (πstar s) then 0 else dTilde M ρ πstar κ s (πstar s) * G s (πstar s)) := by
    intro G P _ s
    exact sum_action_collapse πstar
      (fun s a => if P s a then 0 else dTilde M ρ πstar κ s a * G s a) (fun s a ha => by
        show (if P s a then 0 else dTilde M ρ πstar κ s a * G s a) = 0
        rw [dTilde_of_ne M ρ πstar κ s a ha]; split_ifs <;> simp) s
  have h6a : ∀ u, u ≤ T → EdIc u ≤ c0 * (168 * Cs / (T * (1 - M.discount))) := by
    intro u hu
    calc EdIc u = ∑ s, (if thr ≤ db.prob (s, πstar s) then 0 else
          dTilde M ρ πstar κ s (πstar s) * F u s (πstar s)) := by
          simp only [hEdIc]
          exact Finset.sum_congr rfl fun s _ => hcollapse (F u) (fun s a => thr ≤ db.prob (s, a)) s
      _ ≤ ∑ s, c0 * (if db.prob (s, πstar s) < thr then dTilde M ρ πstar κ s (πstar s) else 0) := by
          refine Finset.sum_le_sum fun s _ => ?_
          split_ifs with h1 h2 h2
          · exact mul_nonneg hc00 (dTilde_nonneg M ρ πstar hκ0 s (πstar s))
          · simp
          · have := (hFb u hu s (πstar s)).2
            have := dTilde_nonneg M ρ πstar hκ0 s (πstar s)
            nlinarith
          · exact absurd (lt_of_not_ge h1) h2
      _ = c0 * ∑ s, (if db.prob (s, πstar s) < thr then dTilde M ρ πstar κ s (πstar s) else 0) := by
          rw [Finset.mul_sum]
      _ ≤ c0 * (168 * Cs / (T * (1 - M.discount))) := mul_le_mul_of_nonneg_left hsumIc hc00
  have h6b : Ed T ≤ c0 * (168 / (1 - M.discount)) := by
    calc Ed T = ∑ s, dTilde M ρ πstar κ s (πstar s) * F T s (πstar s) := by
          simp only [hEd]
          exact Finset.sum_congr rfl fun s _ => sum_action_collapse πstar
            (fun s a => dTilde M ρ πstar κ s a * F T s a)
            (fun s a ha => by
              show dTilde M ρ πstar κ s a * F T s a = 0
              rw [dTilde_of_ne M ρ πstar κ s a ha, zero_mul]) s
      _ ≤ ∑ s, dTilde M ρ πstar κ s (πstar s) * c0 :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hFb T le_rfl s _).2
            (dTilde_nonneg M ρ πstar hκ0 _ _)
      _ = c0 * ∑ s, dTilde M ρ πstar κ s (πstar s) := by rw [← Finset.sum_mul, mul_comm]
      _ ≤ c0 * (168 / (1 - M.discount)) := mul_le_mul_of_nonneg_left hsumd hc00
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have h6c : ∑ u : Fin T, EdIc u.val ≤ 168 * Cs / (1 - M.discount) ^ 2 := by
    calc ∑ u : Fin T, EdIc u.val ≤ ∑ _u : Fin T, c0 * (168 * Cs / (T * (1 - M.discount))) :=
          Finset.sum_le_sum fun u _ => h6a u.val u.isLt.le
      _ = 168 * Cs / (1 - M.discount) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc0]
          field_simp
  have h6d : Ed T ≤ 168 / (1 - M.discount) ^ 2 := by
    refine h6b.trans (le_of_eq ?_)
    rw [hc0]; field_simp
  -- assemble
  rw [h1]
  calc ∑ u : Fin T, (Ed (u.val + 1) - c * f (u.val + 1) (ℓ u))
      = ∑ u : Fin T, (Ed u.val - c * f u.val (ℓ u)) + ∑ u : Fin T, (Ed (u.val + 1) - Ed u.val) +
          c * ∑ u : Fin T, (f u.val (ℓ u) - f (u.val + 1) (ℓ u)) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun u _ => ?_
        ring
    _ ≤ (2 * K₀ + ∑ u : Fin T, EdIc u.val) + Ed T + c * 0 := by
        rw [h2]
        have := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ c)
        linarith
    _ ≤ _ := by linarith

set_option maxHeartbeats 1000000 in
/-- **φ bound, deterministic part** (the omitted "analogous" argument, `offlineRL.tex:5483–5485`):
on the event that no sample hits a poorly covered pair `(s,π⋆(s))`, under pessimism and the
absorbed Freedman bound, `φ ≤ 4K₀`. -/
theorem phiTotal_le (hT : 1 ≤ T) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hpess : ∀ u, u ≤ T → ∀ s, (run M cb δ sel π₀ data u).V s ≤ optValue M s)
    (hIc : ∀ u : Fin T, δ / (5 * Fintype.card S * T) ≤ db.prob (data u).1 ∨
      (data u).1.2 ≠ πstar (data u).1.1)
    (K₀ : ℝ) (hK₀ : 0 ≤ K₀)
    (hZ : |∑ u : Fin T,
        (ratioI M ρ πstar db (kappa M.discount (horizon M.discount (iota S A T δ)))
            (δ / (5 * Fintype.card S * T)) (data u).1 *
          (M.transition (data u).1.1 (data u).1.2).expectation (delta M cb δ sel π₀ data u.val) -
        edI M ρ πstar db (kappa M.discount (horizon M.discount (iota S A T δ)))
          (δ / (5 * Fintype.card S * T))
          (fun s a => (M.transition s a).expectation (delta M cb δ sel π₀ data u.val)))| ≤
      (∑ u : Fin T, edI M ρ πstar db (kappa M.discount (horizon M.discount (iota S A T δ)))
          (δ / (5 * Fintype.card S * T))
          (fun s a => (M.transition s a).expectation (delta M cb δ sel π₀ data u.val))) /
        (2 * horizon M.discount (iota S A T δ)) + K₀) :
    phiTotal M cb δ sel π₀ data ρ πstar db ≤ 4 * K₀ := by
  set H := horizon M.discount (iota S A T δ) with hHdef
  set κ := kappa M.discount H with hκ
  set thr := δ / (5 * Fintype.card S * T) with hthr
  set c := 1 + 1 / (H : ℝ) with hc
  have hHpos : 0 < H := horizon_pos M hT hδ hδ1
  have hHr : (0 : ℝ) < H := by exact_mod_cast hHpos
  obtain ⟨hc1, hc2⟩ := one_le_c_le_two hHpos
  have hκ0 : 0 ≤ κ := kappa_nonneg M _
  set G : ℕ → S → A → ℝ := fun u s a =>
    (M.transition s a).expectation (delta M cb δ sel π₀ data u) with hG
  have hG0 : ∀ u, u ≤ T → ∀ s a, 0 ≤ G u s a := by
    intro u hu s a
    apply FiniteDistribution.expectation_nonneg
    intro x
    have := hpess u hu x
    simp only [delta]; linarith
  set ℓ : Fin T → S × A := fun u => (data u).1 with hℓ
  set gI : Fin T → ℝ := fun u => ratioI M ρ πstar db κ thr (ℓ u) * G u.val (ℓ u).1 (ℓ u).2
    with hgI
  set EdP : ℕ → ℝ := fun u => ∑ s, ∑ a, dTilde M ρ πstar κ s a * G u s a with hEdP
  set EdPI : ℕ → ℝ := fun u => edI M ρ πstar db κ thr (G u) with hEdPI
  have h1 : phiTotal M cb δ sel π₀ data ρ πstar db =
      c ^ 2 * ∑ u : Fin T, (dTilde M ρ πstar κ (ℓ u).1 (ℓ u).2 / db.prob (ℓ u) *
        G u.val (ℓ u).1 (ℓ u).2 - c * EdP u.val) := by
    simp only [phiTotal]
    rw [← hHdef, ← hκ, ← hc]
  -- on the event, the sampled ratio equals its well-covered restriction
  have hsample : ∀ u : Fin T, dTilde M ρ πstar κ (ℓ u).1 (ℓ u).2 / db.prob (ℓ u) *
      G u.val (ℓ u).1 (ℓ u).2 = gI u := by
    intro u
    simp only [hgI, ratioI]
    split_ifs with h
    · rfl
    · rcases hIc u with h' | h'
      · exact absurd h' h
      · rw [dTilde_of_ne M ρ πstar κ _ _ h', zero_div, zero_mul]
  have hEdP : ∀ u : Fin T, EdPI u.val ≤ EdP u.val := by
    intro u
    simp only [hEdP, hEdPI, edI]
    refine Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun a _ => ?_
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (dTilde_nonneg M ρ πstar hκ0 s a) (hG0 u.val u.isLt.le s a)
  set Atot := ∑ u : Fin T, EdPI u.val with hAtot
  have hA0 : 0 ≤ Atot := Finset.sum_nonneg fun u _ =>
    edI_nonneg M ρ πstar db hκ0 _ fun s a => hG0 u.val u.isLt.le s a
  have hZ' : |∑ u : Fin T, (gI u - EdPI u.val)| ≤ Atot / (2 * H) + K₀ := hZ
  have hinner : ∑ u : Fin T, (dTilde M ρ πstar κ (ℓ u).1 (ℓ u).2 / db.prob (ℓ u) *
      G u.val (ℓ u).1 (ℓ u).2 - c * EdP u.val) ≤ K₀ := by
    calc ∑ u : Fin T, (dTilde M ρ πstar κ (ℓ u).1 (ℓ u).2 / db.prob (ℓ u) *
          G u.val (ℓ u).1 (ℓ u).2 - c * EdP u.val)
        ≤ ∑ u : Fin T, ((gI u - EdPI u.val) - 1 / (H : ℝ) * EdPI u.val) := by
          refine Finset.sum_le_sum fun u _ => ?_
          rw [hsample u]
          have := hEdP u
          have hEI0 : 0 ≤ EdPI u.val :=
            edI_nonneg M ρ πstar db hκ0 _ fun s a => hG0 u.val u.isLt.le s a
          have hcH : c = 1 + 1 / (H : ℝ) := hc
          nlinarith
      _ = ∑ u : Fin T, (gI u - EdPI u.val) - 1 / (H : ℝ) * Atot := by
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ ≤ (Atot / (2 * H) + K₀) - 1 / (H : ℝ) * Atot := by
          have := le_abs_self (∑ u : Fin T, (gI u - EdPI u.val))
          linarith
      _ ≤ K₀ := by
          have e : Atot / (2 * H) - 1 / (H : ℝ) * Atot = -(Atot / (2 * H)) := by field_simp; ring
          have : 0 ≤ Atot / (2 * H) := by positivity
          linarith
  rw [h1]
  have hc2' : c ^ 2 ≤ 4 := by nlinarith
  have hc20 : 0 ≤ c ^ 2 := sq_nonneg c
  calc c ^ 2 * _ ≤ c ^ 2 * K₀ := mul_le_mul_of_nonneg_left hinner hc20
    _ ≤ 4 * K₀ := mul_le_mul_of_nonneg_right hc2' hK₀

end Bounds

end StatisticalRL.OfflineRL.LCBQ
