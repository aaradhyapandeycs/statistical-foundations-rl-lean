import Formalization.Probability.Variance
import Formalization.OfflineRL.VILCBDefinitions
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Corrected offline VI-LCB Lemma 6.2 for `γ ≥ 1/2`

Source: `lem:monotone-contraction`, `chapters/offlineRL.tex:872–890`, proof
`:3205–3484`. The printed lemma omits `γ ≥ 1/2`, while its proof uses it at
`:3343`. A counterexample to the unrestricted statement is recorded in
`docs/SOURCE-ISSUES.md#C10`; this module proves only the restricted variant.

The proof uses bounded-vector monotonicity of the source penalty, contraction on
the source value box, and the fixed-point characterization. Empirical rows and
counts are arbitrary inputs, so the formalized model includes the dataset-built
rows as a special case.
-/

open scoped BigOperators NNReal

namespace StatisticalRL.OfflineVILCB

open StatisticalRL

variable {S A : Type*} [Fintype S] [Fintype A]
/-! ## Scalar and distribution lemmas -/

theorem min_sub_min_le (x y C : ℝ) : min x C - min y C ≤ max (x - y) 0 := by
  have hx : x ≤ y + max (x - y) 0 := by linarith [le_max_left (x - y) 0]
  have hC : C ≤ C + max (x - y) 0 := by linarith [le_max_right (x - y) 0]
  have h1 : min x C ≤ min y C + max (x - y) 0 := by
    calc min x C ≤ min (y + max (x - y) 0) (C + max (x - y) 0) := min_le_min hx hC
      _ = min y C + max (x - y) 0 := min_add_add_right y C _
  linarith

theorem max_sqrt_sub_le {κ β x y : ℝ} (hκ : 0 ≤ κ) (hβ : 0 < β) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    max (Real.sqrt (κ * x)) β - max (Real.sqrt (κ * y)) β ≤ κ * max (x - y) 0 / (2 * β) := by
  set a := max (Real.sqrt (κ * x)) β with ha_def
  set c := max (Real.sqrt (κ * y)) β with hc_def
  have hm0 : 0 ≤ max (x - y) 0 := le_max_right _ _
  have hRHS : 0 ≤ κ * max (x - y) 0 / (2 * β) := by positivity
  by_cases hac : a ≤ c
  · linarith
  push_neg at hac
  have hcβ : β ≤ c := le_max_right _ _
  have haβ : β < a := lt_of_le_of_lt hcβ hac
  have ha : a = Real.sqrt (κ * x) := by
    rcases max_choice (Real.sqrt (κ * x)) β with h | h
    · rw [ha_def, h]
    · exfalso
      rw [ha_def, h] at haβ
      exact lt_irrefl _ haβ
  have ha2 : a ^ 2 = κ * x := by rw [ha, Real.sq_sqrt (mul_nonneg hκ hx)]
  have hc2 : κ * y ≤ c ^ 2 := by
    have hs : Real.sqrt (κ * y) ≤ c := le_max_left _ _
    have h0 : 0 ≤ Real.sqrt (κ * y) := Real.sqrt_nonneg _
    calc κ * y = Real.sqrt (κ * y) ^ 2 := (Real.sq_sqrt (mul_nonneg hκ hy)).symm
      _ ≤ c ^ 2 := pow_le_pow_left₀ h0 hs 2
  have hc0 : 0 < c := lt_of_lt_of_le hβ hcβ
  have hnum : a ^ 2 - c ^ 2 ≤ κ * max (x - y) 0 := by
    have : κ * (x - y) ≤ κ * max (x - y) 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hκ
    nlinarith
  have hpos : 0 ≤ a ^ 2 - c ^ 2 := by nlinarith
  have hdiff : a - c = (a ^ 2 - c ^ 2) / (a + c) := by
    rw [eq_div_iff (by linarith : a + c ≠ 0)]
    ring
  rw [hdiff, div_le_div_iff₀ (by linarith) (by positivity)]
  calc (a ^ 2 - c ^ 2) * (2 * β) ≤ κ * max (x - y) 0 * (2 * β) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
    _ ≤ κ * max (x - y) 0 * (a + c) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem expectation_const_sub (d : FiniteDistribution S) (c : ℝ) (f : S → ℝ) :
    d.expectation (fun t => c - f t) = c - d.expectation f := by
  have h := d.expectation_sub (fun _ => c) f
  simpa using h

theorem expectation_add_const (d : FiniteDistribution S) (f : S → ℝ) (c : ℝ) :
    d.expectation (fun t => f t + c) = d.expectation f + c := by
  have h := d.expectation_add f (fun _ => c)
  simpa using h

theorem variance_add_const (d : FiniteDistribution S) (f : S → ℝ) (c : ℝ) :
    d.variance (fun t => f t + c) = d.variance f := by
  rw [FiniteDistribution.variance_eq_expectation_centered_sq,
    FiniteDistribution.variance_eq_expectation_centered_sq, expectation_add_const]
  congr 1
  funext t
  ring

/-- Variance increase along a pointwise increase, for range-bounded vectors. -/
theorem variance_sub_le (d : FiniteDistribution S) (V W : S → ℝ) (R : ℝ)
    (hVW : ∀ s, V s ≤ W s) (hV : ∀ s t, V s - V t ≤ R) (hW : ∀ s t, W s - W t ≤ R) :
    d.variance W - d.variance V ≤ 2 * R * d.expectation (fun s => W s - V s) := by
  have hWE : ∀ s, W s - d.expectation W ≤ R := by
    intro s
    rw [← expectation_const_sub]
    exact d.expectation_le_const (fun t => hW s t)
  have hVE : ∀ s, V s - d.expectation V ≤ R := by
    intro s
    rw [← expectation_const_sub]
    exact d.expectation_le_const (fun t => hV s t)
  set EW := d.expectation W with hEW
  set EV := d.expectation V with hEV
  have hterm : ∀ s, (W s - V s) * (W s + V s - EW - EV) ≤ 2 * R * (W s - V s) := by
    intro s
    have h0 : 0 ≤ W s - V s := sub_nonneg.mpr (hVW s)
    have : W s + V s - EW - EV ≤ 2 * R := by linarith [hWE s, hVE s]
    nlinarith
  have hkey := d.expectation_mono hterm
  have hid : d.expectation (fun s => (W s - V s) * (W s + V s - EW - EV)) =
      d.variance W - d.variance V := by
    unfold FiniteDistribution.variance
    rw [hEW, hEV]
    unfold FiniteDistribution.expectation
    have : ∀ s, d.prob s * ((W s - V s) * (W s + V s - (∑ x, d.prob x * W x) -
        (∑ x, d.prob x * V x))) =
        d.prob s * W s ^ 2 - d.prob s * V s ^ 2 -
          ((∑ x, d.prob x * W x) + (∑ x, d.prob x * V x)) * (d.prob s * W s) +
          ((∑ x, d.prob x * W x) + (∑ x, d.prob x * V x)) * (d.prob s * V s) := by
      intro s; ring
    simp_rw [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hid] at hkey
  have hmul := d.expectation_mul (2 * R) (fun s => W s - V s)
  linarith

namespace Input

variable (M : Input S A)

theorem one_sub_γ_pos : 0 < 1 - M.γ := sub_pos.mpr M.γ_lt_one

theorem logTerm_pos : 0 < M.logTerm := by
  unfold logTerm
  apply Real.log_pos
  have h1 : (1 - M.γ) * M.δ < 1 := by
    have := M.one_sub_γ_pos
    nlinarith [M.γ_nonneg, M.δ_pos, M.δ_lt_one]
  have hN : (1 : ℝ) ≤ M.N := by exact_mod_cast M.N_pos
  rw [lt_div_iff₀ (mul_pos M.one_sub_γ_pos M.δ_pos)]
  linarith

theorem bonus_nonneg (s : S) (a : A) (V : S → ℝ) : 0 ≤ M.bonus s a V := by
  have hN : (0 : ℝ) < M.N := by exact_mod_cast M.N_pos
  have hR : 0 < 1 / (1 - M.γ) := by have := M.one_sub_γ_pos; positivity
  unfold bonus
  split_ifs
  · positivity
  · have h1 : 0 ≤ max (Real.sqrt (M.cb * M.logTerm / M.count s a * (M.Phat s a).variance V))
        (2 * M.cb * M.logTerm / ((1 - M.γ) * M.count s a)) :=
      le_trans (Real.sqrt_nonneg _) (le_max_left _ _)
    have h2 : 0 ≤ min (max (Real.sqrt (M.cb * M.logTerm / M.count s a *
        (M.Phat s a).variance V)) (2 * M.cb * M.logTerm / ((1 - M.γ) * M.count s a)))
        (1 / (1 - M.γ)) := le_min h1 hR.le
    positivity

/-- Path-free penalty increase bound: `b(W) − b(V) ≤ ½ P̂(W − V)`. -/
theorem bonus_sub_le (s : S) (a : A) (V W : S → ℝ) (hVW : ∀ t, V t ≤ W t)
    (hV : ∀ t u, V t - V u ≤ 1 / (1 - M.γ)) (hW : ∀ t u, W t - W u ≤ 1 / (1 - M.γ)) :
    M.bonus s a W - M.bonus s a V ≤
      (1 / 2) * (M.Phat s a).expectation (fun t => W t - V t) := by
  have hD : 0 ≤ (M.Phat s a).expectation (fun t => W t - V t) :=
    (M.Phat s a).expectation_nonneg (fun t => sub_nonneg.mpr (hVW t))
  unfold bonus
  split_ifs with h0
  · linarith
  · set n : ℝ := (M.count s a : ℝ) with hn
    have hnpos : 0 < n := by
      have : 0 < M.count s a := Nat.pos_of_ne_zero h0
      rw [hn]; exact_mod_cast this
    have hγ1 := M.one_sub_γ_pos
    have hL := M.logTerm_pos
    set κ := M.cb * M.logTerm / n with hκ
    set β := 2 * M.cb * M.logTerm / ((1 - M.γ) * n) with hβ
    have hκ0 : 0 ≤ κ := by have := M.cb_pos; positivity
    have hβ0 : 0 < β := by have := M.cb_pos; positivity
    have hvar := variance_sub_le (M.Phat s a) V W (1 / (1 - M.γ)) hVW hV hW
    have hsq := max_sqrt_sub_le hκ0 hβ0 ((M.Phat s a).variance_nonneg W)
      ((M.Phat s a).variance_nonneg V)
    have hmin := min_sub_min_le (max (Real.sqrt (κ * (M.Phat s a).variance W)) β)
      (max (Real.sqrt (κ * (M.Phat s a).variance V)) β) (1 / (1 - M.γ))
    have hmaxvar : max ((M.Phat s a).variance W - (M.Phat s a).variance V) 0 ≤
        2 * (1 / (1 - M.γ)) * (M.Phat s a).expectation (fun t => W t - V t) :=
      max_le hvar (by positivity)
    have hratio : κ * (2 * (1 / (1 - M.γ)) * (M.Phat s a).expectation (fun t => W t - V t)) /
        (2 * β) = (1 / 2) * (M.Phat s a).expectation (fun t => W t - V t) := by
      rw [hκ, hβ]
      have h1 := M.cb_pos.ne'
      have h2 := hL.ne'
      have h3 := hnpos.ne'
      have h4 := hγ1.ne'
      field_simp
    have hstep : κ * max ((M.Phat s a).variance W - (M.Phat s a).variance V) 0 / (2 * β) ≤
        (1 / 2) * (M.Phat s a).expectation (fun t => W t - V t) := by
      rw [← hratio]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hmaxvar hκ0
    have hmax2 : max (max (Real.sqrt (κ * (M.Phat s a).variance W)) β -
        max (Real.sqrt (κ * (M.Phat s a).variance V)) β) 0 ≤
        (1 / 2) * (M.Phat s a).expectation (fun t => W t - V t) :=
      max_le (hsq.trans hstep) (by positivity)
    linarith

variable [Nonempty A]

theorem tilde_mono (hγ : 1 / 2 ≤ M.γ) (s : S) (a : A) (V W : S → ℝ) (hVW : ∀ t, V t ≤ W t)
    (hV : ∀ t u, V t - V u ≤ 1 / (1 - M.γ)) (hW : ∀ t u, W t - W u ≤ 1 / (1 - M.γ)) :
    M.tilde s a V ≤ M.tilde s a W := by
  have hb := M.bonus_sub_le s a V W hVW hV hW
  have hD : 0 ≤ (M.Phat s a).expectation (fun t => W t - V t) :=
    (M.Phat s a).expectation_nonneg (fun t => sub_nonneg.mpr (hVW t))
  have hE := (M.Phat s a).expectation_sub W V
  unfold tilde
  nlinarith

theorem tilde_add_const (s : S) (a : A) (V : S → ℝ) (c : ℝ) :
    M.tilde s a (fun t => V t + c) = M.tilde s a V + M.γ * c := by
  have hb : M.bonus s a (fun t => V t + c) = M.bonus s a V := by
    unfold bonus
    rw [variance_add_const]
  unfold tilde
  rw [hb, expectation_add_const]
  ring

/-! ## The value map -/

theorem le_value (Q : S → A → ℝ) (s : S) (a : A) : Q s a ≤ value Q s :=
  Finset.le_sup' (Q s) (Finset.mem_univ a)

theorem value_le (Q : S → A → ℝ) (s : S) (x : ℝ) (h : ∀ a, Q s a ≤ x) : value Q s ≤ x :=
  Finset.sup'_le _ _ (fun a _ => h a)

/-- The box `[0, 1/(1-γ)]^{S×A}`. -/
def box : Set (S → A → ℝ) :=
  ⋂ s, ⋂ a, ({Q | 0 ≤ Q s a} ∩ {Q | Q s a ≤ 1 / (1 - M.γ)})

theorem mem_box (Q : S → A → ℝ) :
    Q ∈ M.box ↔ ∀ s a, 0 ≤ Q s a ∧ Q s a ≤ 1 / (1 - M.γ) := by
  simp [box, Set.mem_iInter]

theorem isClosed_box : IsClosed M.box := by
  apply isClosed_iInter; intro s
  apply isClosed_iInter; intro a
  have hc : Continuous fun Q : S → A → ℝ => Q s a := by fun_prop
  exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)

theorem value_range (Q : S → A → ℝ) (hQ : Q ∈ M.box) (s t : S) :
    value Q s - value Q t ≤ 1 / (1 - M.γ) := by
  rw [mem_box] at hQ
  have h1 : value Q s ≤ 1 / (1 - M.γ) := value_le Q s _ (fun a => (hQ s a).2)
  obtain ⟨a⟩ := ‹Nonempty A›
  have h2 : 0 ≤ value Q t := le_trans (hQ t a).1 (le_value Q t a)
  linarith

theorem value_nonneg (Q : S → A → ℝ) (hQ : Q ∈ M.box) (s : S) : 0 ≤ value Q s := by
  rw [mem_box] at hQ
  obtain ⟨a⟩ := ‹Nonempty A›
  exact le_trans (hQ s a).1 (le_value Q s a)

theorem value_le_bound (Q : S → A → ℝ) (hQ : Q ∈ M.box) (s : S) :
    value Q s ≤ 1 / (1 - M.γ) := by
  rw [mem_box] at hQ
  exact value_le Q s _ (fun a => (hQ s a).2)

theorem pess_mem_box (Q : S → A → ℝ) (hQ : Q ∈ M.box) : M.pess Q ∈ M.box := by
  rw [mem_box]
  intro s a
  refine ⟨le_max_right _ _, max_le ?_ (by have := M.one_sub_γ_pos; positivity)⟩
  have hE : (M.Phat s a).expectation (value Q) ≤ 1 / (1 - M.γ) :=
    (M.Phat s a).expectation_le_const (fun t => M.value_le_bound Q hQ t)
  have hb := M.bonus_nonneg s a (value Q)
  have hr := M.r_le_one s a
  have hγ0 := M.γ_nonneg
  have hγ1 := M.one_sub_γ_pos
  have heq : 1 + M.γ * (1 / (1 - M.γ)) = 1 / (1 - M.γ) := by field_simp; ring
  unfold tilde
  nlinarith [mul_le_mul_of_nonneg_left hE hγ0]

theorem abs_le_dist (Q₁ Q₂ : S → A → ℝ) (s : S) (a : A) :
    |Q₁ s a - Q₂ s a| ≤ dist Q₁ Q₂ :=
  calc |Q₁ s a - Q₂ s a| = dist (Q₁ s a) (Q₂ s a) := (Real.dist_eq _ _).symm
    _ ≤ dist (Q₁ s) (Q₂ s) := dist_le_pi_dist _ _ a
    _ ≤ dist Q₁ Q₂ := dist_le_pi_dist _ _ s

theorem dist_le_of_abs (Q₁ Q₂ : S → A → ℝ) {k : ℝ} (hk : 0 ≤ k)
    (h : ∀ s a, |Q₁ s a - Q₂ s a| ≤ k) : dist Q₁ Q₂ ≤ k :=
  (dist_pi_le_iff hk).2 fun s => (dist_pi_le_iff hk).2 fun a => by
    rw [Real.dist_eq]; exact h s a

/-- `T_pess` is a `γ`-contraction on the box (for `γ ≥ 1/2`). -/
theorem pess_contract (hγ : 1 / 2 ≤ M.γ) (Q₁ Q₂ : S → A → ℝ) (h₁ : Q₁ ∈ M.box)
    (h₂ : Q₂ ∈ M.box) (c : ℝ) (hc : ∀ s a, |Q₁ s a - Q₂ s a| ≤ c) (s : S) (a : A) :
    |M.pess Q₁ s a - M.pess Q₂ s a| ≤ M.γ * c := by
  have hc0 : 0 ≤ c := le_trans (abs_nonneg _) (hc s a)
  have hgc : 0 ≤ M.γ * c := mul_nonneg M.γ_nonneg hc0
  -- One-sided bound from monotonicity plus shift-equivariance.
  have side : ∀ (P₁ P₂ : S → A → ℝ), P₁ ∈ M.box → P₂ ∈ M.box →
      (∀ s a, |P₁ s a - P₂ s a| ≤ c) → M.pess P₁ s a ≤ M.pess P₂ s a + M.γ * c := by
    intro P₁ P₂ hP₁ hP₂ hcP
    have hle : ∀ t, value P₁ t ≤ value P₂ t + c := by
      intro t
      apply value_le
      intro b
      have h := hcP t b
      rw [abs_le] at h
      linarith [le_value P₂ t b]
    have hmono := M.tilde_mono hγ s a (value P₁) (fun t => value P₂ t + c) hle
      (M.value_range P₁ hP₁) (fun t u => by
        have := M.value_range P₂ hP₂ t u
        linarith)
    rw [M.tilde_add_const s a (value P₂) c] at hmono
    unfold pess
    exact max_le (by linarith [le_max_left (M.tilde s a (value P₂)) 0])
      (by linarith [le_max_right (M.tilde s a (value P₂)) 0])
  rw [abs_sub_le_iff]
  constructor
  · linarith [side Q₁ Q₂ h₁ h₂ hc]
  · linarith [side Q₂ Q₁ h₂ h₁ (fun s a => by rw [abs_sub_comm]; exact hc s a)]

/-- `T_pess` restricted to the box. -/
noncomputable def boxMap : M.box → M.box := fun Q => ⟨M.pess Q.1, M.pess_mem_box Q.1 Q.2⟩

theorem boxMap_contracting (hγ : 1 / 2 ≤ M.γ) :
    ContractingWith ⟨M.γ, M.γ_nonneg⟩ M.boxMap := by
  constructor
  · rw [← NNReal.coe_lt_coe]
    simpa using M.γ_lt_one
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [Subtype.dist_eq, Subtype.dist_eq]
    simp only [NNReal.coe_mk]
    apply dist_le_of_abs _ _ (mul_nonneg M.γ_nonneg dist_nonneg)
    intro s a
    exact M.pess_contract hγ x.1 y.1 x.2 y.2 _ (abs_le_dist x.1 y.1) s a

theorem zero_mem_box : (0 : S → A → ℝ) ∈ M.box := by
  rw [mem_box]
  intro s a
  exact ⟨le_rfl, by have := M.one_sub_γ_pos; simp only [Pi.zero_apply]; positivity⟩

/-- Every fixed point of `T_pess` (anywhere in `ℝ^{SA}`) lies in the box. -/
theorem fixed_mem_box (Q : S → A → ℝ) (hQ : M.pess Q = Q) : Q ∈ M.box := by
  have hnn : ∀ s a, 0 ≤ Q s a := fun s a => by
    rw [← hQ]; exact le_max_right _ _
  set m := ‖Q‖ with hm
  have hm0 : 0 ≤ m := norm_nonneg _
  have hent : ∀ s a, Q s a ≤ m := fun s a =>
    calc Q s a ≤ ‖Q s a‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
      _ ≤ ‖Q s‖ := norm_le_pi_norm (Q s) a
      _ ≤ ‖Q‖ := norm_le_pi_norm Q s
  have hval : ∀ t, value Q t ≤ m := fun t => value_le Q t m (fun b => hent t b)
  have hγ0 := M.γ_nonneg
  have hup : ∀ s a, Q s a ≤ 1 + M.γ * m := by
    intro s a
    have hE : (M.Phat s a).expectation (value Q) ≤ m :=
      (M.Phat s a).expectation_le_const hval
    have hb := M.bonus_nonneg s a (value Q)
    have hr := M.r_le_one s a
    rw [← hQ]
    unfold pess tilde
    refine max_le ?_ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hE hγ0]
  have hmle : m ≤ 1 + M.γ * m := by
    have hpos : 0 ≤ 1 + M.γ * m := by positivity
    rw [hm]
    refine (pi_norm_le_iff_of_nonneg hpos).2 fun s => (pi_norm_le_iff_of_nonneg hpos).2 fun a => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn s a)]
    exact hup s a
  have hγ1 := M.one_sub_γ_pos
  have hmR : m ≤ 1 / (1 - M.γ) := by
    rw [le_div_iff₀ hγ1]
    nlinarith
  rw [mem_box]
  exact fun s a => ⟨hnn s a, (hent s a).trans hmR⟩

theorem iter_succ (τ : ℕ) : M.iter (τ + 1) = M.pess (M.iter τ) := by
  unfold iter
  rw [Function.iterate_succ_apply']

theorem iter_mem_box (τ : ℕ) : M.iter τ ∈ M.box := by
  induction τ with
  | zero => exact M.zero_mem_box
  | succ τ ih => rw [iter_succ]; exact M.pess_mem_box _ ih

/-- **Corrected `lem:monotone-contraction`** (`offlineRL.tex:872–890`) under the
added hypothesis `1/2 ≤ γ`. Starting from `Q̂_0 = 0`:
- `T_pess` has a unique fixed point `Q̂⋆_pe` in all of `ℝ^{SA}`;
- for every `τ`, `Q̂_τ ≤ Q̂⋆_pe` and `‖Q̂_τ − Q̂⋆_pe‖_∞ ≤ γ^τ/(1−γ)`;
- `τ ≥ log(N/(1−γ))/log(1/γ)` gives `‖Q̂_τ − Q̂⋆_pe‖_∞ ≤ 1/N`. -/
theorem lem_monotone_contraction_corrected (hγ : 1 / 2 ≤ M.γ) :
    ∃ Qstar : S → A → ℝ, M.pess Qstar = Qstar ∧
      (∀ Q, M.pess Q = Q → Q = Qstar) ∧
      (∀ τ : ℕ, M.iter τ ≤ Qstar ∧ ‖M.iter τ - Qstar‖ ≤ M.γ ^ τ / (1 - M.γ)) ∧
      (∀ τ : ℕ, Real.log (M.N / (1 - M.γ)) / Real.log (1 / M.γ) ≤ τ →
        ‖M.iter τ - Qstar‖ ≤ 1 / M.N) := by
  haveI : CompleteSpace M.box := M.isClosed_box.completeSpace_coe
  haveI : Nonempty M.box := ⟨⟨0, M.zero_mem_box⟩⟩
  have hF := M.boxMap_contracting hγ
  set P := ContractingWith.fixedPoint M.boxMap hF with hPdef
  have hP : M.boxMap P = P := hF.fixedPoint_isFixedPt
  have hPfix : M.pess P.1 = P.1 := congrArg Subtype.val hP
  have hPbox : P.1 ∈ M.box := P.2
  have hγ1 := M.one_sub_γ_pos
  have hγ0 := M.γ_nonneg
  -- Iterates stay below the fixed point.
  have hle : ∀ τ : ℕ, M.iter τ ≤ P.1 := by
    intro τ
    induction τ with
    | zero =>
      intro s a
      exact ((M.mem_box P.1).1 hPbox s a).1
    | succ τ ih =>
      intro s a
      rw [iter_succ, ← hPfix]
      unfold pess
      apply max_le_max _ le_rfl
      apply M.tilde_mono hγ s a
      · intro t
        apply value_le
        intro b
        exact le_trans (ih t b) (le_value P.1 t b)
      · exact M.value_range _ (M.iter_mem_box τ)
      · exact M.value_range _ hPbox
  -- Geometric convergence.
  have hdist : ∀ τ : ℕ, dist (M.iter τ) P.1 ≤ M.γ ^ τ * (1 / (1 - M.γ)) := by
    intro τ
    induction τ with
    | zero =>
      simp only [pow_zero, one_mul]
      apply dist_le_of_abs _ _ (by positivity)
      intro s a
      have h := (M.mem_box P.1).1 hPbox s a
      simp only [iter, Function.iterate_zero, id_eq, Pi.zero_apply, zero_sub, abs_neg,
        abs_of_nonneg h.1]
      exact h.2
    | succ τ ih =>
      rw [iter_succ, ← hPfix]
      calc dist (M.pess (M.iter τ)) (M.pess P.1)
          ≤ M.γ * dist (M.iter τ) P.1 :=
            dist_le_of_abs _ _ (mul_nonneg hγ0 dist_nonneg) fun s a =>
              M.pess_contract hγ _ _ (M.iter_mem_box τ) hPbox _ (abs_le_dist _ _) s a
        _ ≤ M.γ * (M.γ ^ τ * (1 / (1 - M.γ))) := mul_le_mul_of_nonneg_left ih hγ0
        _ = M.γ ^ (τ + 1) * (1 / (1 - M.γ)) := by ring
  have hnorm : ∀ τ : ℕ, ‖M.iter τ - P.1‖ ≤ M.γ ^ τ / (1 - M.γ) := by
    intro τ
    rw [← dist_eq_norm, div_eq_mul_one_div]
    exact hdist τ
  refine ⟨P.1, hPfix, ?_, fun τ => ⟨hle τ, hnorm τ⟩, ?_⟩
  · intro Q hQ
    have hb := M.fixed_mem_box Q hQ
    have hfix : M.boxMap ⟨Q, hb⟩ = ⟨Q, hb⟩ := Subtype.ext hQ
    exact congrArg Subtype.val (hF.fixedPoint_unique hfix)
  · intro τ hτ
    have hγpos : 0 < M.γ := by linarith
    have hNpos : (0 : ℝ) < M.N := by exact_mod_cast M.N_pos
    have hlogpos : 0 < Real.log (1 / M.γ) :=
      Real.log_pos (by rw [lt_div_iff₀ hγpos]; linarith [M.γ_lt_one])
    have h1 : Real.log (M.N / (1 - M.γ)) ≤ τ * Real.log (1 / M.γ) := (div_le_iff₀ hlogpos).1 hτ
    have e1 : Real.log (1 / M.γ) = - Real.log M.γ := by rw [one_div, Real.log_inv]
    have e2 : Real.log ((1 - M.γ) / M.N) = - Real.log (M.N / (1 - M.γ)) := by
      rw [← Real.log_inv, inv_div]
    have hpow : M.γ ^ τ ≤ (1 - M.γ) / M.N := by
      rw [← Real.log_le_log_iff (pow_pos hγpos τ) (by positivity), Real.log_pow, e2]
      rw [e1] at h1
      linarith
    calc ‖M.iter τ - P.1‖ ≤ M.γ ^ τ / (1 - M.γ) := hnorm τ
      _ ≤ ((1 - M.γ) / M.N) / (1 - M.γ) := div_le_div_of_nonneg_right hpow hγ1.le
      _ = 1 / M.N := by field_simp

end Input
end StatisticalRL.OfflineVILCB
