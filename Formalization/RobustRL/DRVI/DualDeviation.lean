import Formalization.RobustRL.DRVI.VarianceTransfer
import Formalization.RobustRL.TVSourceMaximum
import Formalization.RobustRL.ChiSquaredSourceMaximum

/-!
# Dual representation and row-deviation bounds (milestone 3, module D; plan §3.4)

Lemma 7.1 (`robust_RL.tex:302–324`, library exports `tvPrimalInf_eq_source_max` and
`chiSquared_source_maximum`) writes the exact row infimum as a maximum of a clipped objective
over the global interval `I = [min V, max V]`, the same interval for every nominal row. Hence
for two rows `p, p'` the deviation `|g_{p'}(W) − g_p(W)|` is at most the uniform deviation of the
objectives on `I`, which is controlled on the net `α_j = j·step`, `j ≤ N`:

* (T) TV: `|g_{p'}(W) − g_p(W)| ≤ max_j |⟨p'−p, [W]_{α_j}⟩| + 2·step`;
* (X) χ²: `|g_{p'}(W) − g_p(W)| ≤ max_j (|⟨p'−p, f_j⟩| + √σ |std_{p'} f_j − std_p f_j|)
  + (2 + 2√σ)·step`, `f_j = [W]_{α_j}`.
-/

open scoped BigOperators

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7

variable {State : Type*} [Fintype State]

/-- `g` is the maximum of `φ` over `I`, attained. -/
def IsIntervalMax (I : Set ℝ) (φ : ℝ → ℝ) (g : ℝ) : Prop :=
  ∃ α ∈ I, g = φ α ∧ ∀ β ∈ I, φ β ≤ φ α

theorem abs_sub_le_of_isIntervalMax {I : Set ℝ} {φ ψ : ℝ → ℝ} {g h c : ℝ}
    (hg : IsIntervalMax I φ g) (hh : IsIntervalMax I ψ h) (hc : ∀ α ∈ I, |ψ α - φ α| ≤ c) :
    |h - g| ≤ c := by
  obtain ⟨α, hα, rfl, hmaxφ⟩ := hg
  obtain ⟨α', hα', rfl, hmaxψ⟩ := hh
  have h1 := (abs_le.mp (hc α' hα')).2
  have h2 := (abs_le.mp (hc α hα)).1
  have h3 := hmaxφ α' hα'
  have h4 := hmaxψ α hα
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Net point: every `α ∈ [0, N·step]` is within `step` of some `j·step`, `j ≤ N`. -/
theorem exists_net_point {α step : ℝ} {N : ℕ} (hstep : 0 < step) (h0 : 0 ≤ α)
    (h1 : α ≤ N * step) : ∃ j : ℕ, j ≤ N ∧ |α - j * step| ≤ step := by
  refine ⟨⌊α / step⌋₊, ?_, ?_⟩
  · have : α / step ≤ N := by rw [div_le_iff₀ hstep]; exact h1
    exact Nat.floor_le_of_le this
  · have hfl := Nat.floor_le (div_nonneg h0 hstep.le)
    have hlt := Nat.lt_floor_add_one (α / step)
    have e1 : (⌊α / step⌋₊ : ℝ) * step ≤ α := by
      calc (⌊α / step⌋₊ : ℝ) * step ≤ α / step * step := mul_le_mul_of_nonneg_right hfl hstep.le
        _ = α := div_mul_cancel₀ α hstep.ne'
    have e2 : α < (⌊α / step⌋₊ : ℝ) * step + step := by
      have := mul_lt_mul_of_pos_right hlt hstep
      rw [div_mul_cancel₀ α hstep.ne', add_mul, one_mul] at this
      exact this
    rw [abs_le]; constructor <;> linarith

/-- Clipping is 1-Lipschitz in the level. -/
theorem norm_clip_sub_le (W : State → ℝ) (α β : ℝ) :
    ‖(fun x ↦ min (W x) α) - (fun x ↦ min (W x) β)‖ ≤ |α - β| := by
  apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2
  intro x
  rw [Pi.sub_apply, Real.norm_eq_abs, min_comm (W x) α, min_comm (W x) β]
  exact abs_min_sub_min_le α β (W x)

section Dual

variable [Nonempty State]

/-- `min V` over the finite state space. -/
noncomputable def vmin (V : State → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty V

/-- `max V` over the finite state space. -/
noncomputable def vmax (V : State → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty V

theorem vmin_nonneg {V : State → ℝ} (hV : ∀ s, 0 ≤ V s) : 0 ≤ vmin V :=
  Finset.le_inf' _ _ (fun s _ ↦ hV s)

theorem vmax_le {V : State → ℝ} {c : ℝ} (hV : ∀ s, V s ≤ c) : vmax V ≤ c :=
  Finset.sup'_le _ _ (fun s _ ↦ hV s)

/-- TV branch of Lemma 7.1 in `rowInf` form. -/
theorem tv_rowInf_isIntervalMax (p : FiniteDistribution State) (V : State → ℝ)
    (hV : ∀ s, 0 ≤ V s) {σ : ℝ} (hσ : 0 < σ) :
    IsIntervalMax (Set.Icc (vmin V) (vmax V)) (fun α ↦ tvDualObjective p V σ α)
      (rowInf (tvBall p σ) V) := by
  classical
  have hfeas : ∀ q : FiniteDistribution State, tvFeasibleRow p σ q ↔ q ∈ tvBall p σ := by
    intro q
    unfold tvFeasibleRow
    rw [eventTV_eq_finiteTotalVariation p.prob q.prob p.prob_nonneg q.prob_nonneg p.sum_prob
      q.sum_prob]
    rfl
  have hInf : tvPrimalInf p V σ = rowInf (tvBall p σ) V := by
    unfold tvPrimalInf rowInf
    show sInf (Set.range fun q : tvFeasibleRows p σ ↦ q.1.expectation V) = _
    congr 1
    ext z
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.1, (hfeas q.1).1 q.2, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, (hfeas q).2 hq⟩, rfl⟩
  obtain ⟨α, hα, heq, hmax⟩ := TVProof.SourceMaximum.tvPrimalInf_eq_source_max p V σ hσ hV
  exact ⟨α, hα, by rw [← hInf, heq], hmax⟩

theorem valueMin_eq_vmin (p : FiniteDistribution State) (V : State → ℝ) :
    ChiSquaredPrimalDualWeakBridge.valueMin p V = vmin V := by
  classical
  apply le_antisymm
  · apply Finset.le_inf'
    intro s _
    exact ChiSquaredPrimalDualWeakBridge.valueMin_le p V s
  · unfold ChiSquaredPrimalDualWeakBridge.valueMin ChiSquaredPrimalDualWeakBridge.valueImage
    apply Finset.le_min'
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.inf'_le (s := Finset.univ) (f := V) hs

theorem valueMax_eq_vmax (p : FiniteDistribution State) (V : State → ℝ) :
    ChiSquaredPrimalDualWeakBridge.valueMax p V = vmax V := by
  classical
  apply le_antisymm
  · have hmem : ChiSquaredPrimalDualWeakBridge.valueMax p V ∈ Finset.univ.image V := by
      unfold ChiSquaredPrimalDualWeakBridge.valueMax ChiSquaredPrimalDualWeakBridge.valueImage
      exact Finset.max'_mem _ _
    obtain ⟨s, hs, hvalue⟩ := Finset.mem_image.mp hmem
    rw [← hvalue]
    exact Finset.le_sup' (s := Finset.univ) (f := V) hs
  · apply Finset.sup'_le
    intro s _
    exact ChiSquaredPrimalDualWeakBridge.le_valueMax p V s

/-- χ² branch of Lemma 7.1 in `rowInf` form (support-aware ball, global interval). -/
theorem chi_rowInf_isIntervalMax (p : FiniteDistribution State) (V : State → ℝ)
    (hV : ∀ s, 0 ≤ V s) {σ : ℝ} (hσ : 0 < σ) :
    IsIntervalMax (Set.Icc (vmin V) (vmax V))
      (fun α ↦ ChiSquaredPrimalDualWeakBridge.dualObjective p V σ α)
      (rowInf (chiBall p σ) V) := by
  obtain ⟨_, α, _, hα, _, hinf, hmax⟩ :=
    ChiSquaredSourceMaximum.chiSquared_source_maximum p V σ hσ hV
  have hset : rowInf (chiBall p σ) V = sInf (QLearning.qRobustExpectations p σ V) := by
    unfold rowInf
    congr 1
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩; exact ⟨q, hq, rfl⟩
  rw [valueMin_eq_vmin, valueMax_eq_vmax] at hα hmax
  exact ⟨α, hα, by rw [hset, hinf], hmax⟩

/-- (T): TV row deviation through the α-net. -/
theorem tv_rowInf_deviation (p p' : FiniteDistribution State) {W : State → ℝ}
    (hW0 : ∀ s, 0 ≤ W s) {σ step c : ℝ} {N : ℕ} (hσ : 0 < σ) (hstep : 0 < step)
    (hWB : ∀ s, W s ≤ N * step)
    (hc : ∀ j : ℕ, j ≤ N → |p'.expectation (fun x ↦ min (W x) (j * step)) -
      p.expectation (fun x ↦ min (W x) (j * step))| ≤ c) :
    |rowInf (tvBall p' σ) W - rowInf (tvBall p σ) W| ≤ c + 2 * step := by
  apply abs_sub_le_of_isIntervalMax (tv_rowInf_isIntervalMax p W hW0 hσ)
    (tv_rowInf_isIntervalMax p' W hW0 hσ)
  intro α hα
  have hα0 : 0 ≤ α := (vmin_nonneg hW0).trans hα.1
  have hα1 : α ≤ N * step := hα.2.trans (vmax_le hWB)
  obtain ⟨j, hj, hjα⟩ := exists_net_point hstep hα0 hα1
  have hdiff : tvDualObjective p' W σ α - tvDualObjective p W σ α =
      p'.expectation (fun x ↦ min (W x) α) - p.expectation (fun x ↦ min (W x) α) := by
    unfold tvDualObjective
    ring_nf
    rfl
  rw [hdiff]
  have hlip := FiniteDistribution.residual_sub_le_two_norm p p' (fun x ↦ min (W x) α)
    (fun x ↦ min (W x) (j * step))
  have hn := norm_clip_sub_le W α (j * step)
  have := hc j hj
  have h2 := (abs_le.mp hlip)
  rw [abs_le] at this ⊢
  constructor <;> nlinarith [h2.1, h2.2, this.1, this.2]

/-- (X): χ² row deviation through the α-net. -/
theorem chi_rowInf_deviation (p p' : FiniteDistribution State) {W : State → ℝ}
    (hW0 : ∀ s, 0 ≤ W s) {σ step c : ℝ} {N : ℕ} (hσ : 0 < σ) (hstep : 0 < step)
    (hWB : ∀ s, W s ≤ N * step)
    (hc : ∀ j : ℕ, j ≤ N →
      |p'.expectation (fun x ↦ min (W x) (j * step)) -
          p.expectation (fun x ↦ min (W x) (j * step))| +
        Real.sqrt σ * |Real.sqrt (p'.variance (fun x ↦ min (W x) (j * step))) -
          Real.sqrt (p.variance (fun x ↦ min (W x) (j * step)))| ≤ c) :
    |rowInf (chiBall p' σ) W - rowInf (chiBall p σ) W| ≤
      c + (2 + 2 * Real.sqrt σ) * step := by
  apply abs_sub_le_of_isIntervalMax (chi_rowInf_isIntervalMax p W hW0 hσ)
    (chi_rowInf_isIntervalMax p' W hW0 hσ)
  intro α hα
  have hα0 : 0 ≤ α := (vmin_nonneg hW0).trans hα.1
  have hα1 : α ≤ N * step := hα.2.trans (vmax_le hWB)
  obtain ⟨j, hj, hjα⟩ := exists_net_point hstep hα0 hα1
  set fα : State → ℝ := fun x ↦ min (W x) α
  set fj : State → ℝ := fun x ↦ min (W x) (j * step)
  have hsσ : 0 ≤ Real.sqrt σ := Real.sqrt_nonneg σ
  have hdiff : ChiSquaredPrimalDualWeakBridge.dualObjective p' W σ α -
      ChiSquaredPrimalDualWeakBridge.dualObjective p W σ α =
      (p'.expectation fα - p.expectation fα) -
        Real.sqrt σ * (Real.sqrt (p'.variance fα) - Real.sqrt (p.variance fα)) := by
    unfold ChiSquaredPrimalDualWeakBridge.dualObjective
    rw [Real.sqrt_mul hσ.le, Real.sqrt_mul hσ.le]
    ring
  rw [hdiff]
  have hn : ‖fα - fj‖ ≤ step := (norm_clip_sub_le W α (j * step)).trans hjα
  have hmean := FiniteDistribution.residual_sub_le_two_norm p p' fα fj
  have hs1 := FiniteDistribution.abs_sqrt_variance_sub_le_norm p' fα fj
  have hs2 := FiniteDistribution.abs_sqrt_variance_sub_le_norm p fα fj
  have hcj := hc j hj
  set Δm := p'.expectation fα - p.expectation fα
  set Δmj := p'.expectation fj - p.expectation fj
  set Δs := Real.sqrt (p'.variance fα) - Real.sqrt (p.variance fα)
  set Δsj := Real.sqrt (p'.variance fj) - Real.sqrt (p.variance fj)
  have hΔm : |Δm| ≤ |Δmj| + 2 * step := by
    have : |Δm - Δmj| ≤ 2 * step := hmean.trans (by linarith)
    have := abs_sub_abs_le_abs_sub Δm Δmj
    linarith
  have hΔs : |Δs| ≤ |Δsj| + 2 * step := by
    have h1 : |Δs - Δsj| ≤ 2 * step := by
      have : Δs - Δsj = (Real.sqrt (p'.variance fα) - Real.sqrt (p'.variance fj)) -
          (Real.sqrt (p.variance fα) - Real.sqrt (p.variance fj)) := by
        simp only [Δs, Δsj]; ring
      rw [this]
      calc _ ≤ |Real.sqrt (p'.variance fα) - Real.sqrt (p'.variance fj)| +
            |Real.sqrt (p.variance fα) - Real.sqrt (p.variance fj)| := abs_sub _ _
        _ ≤ step + step := add_le_add (hs1.trans hn) (hs2.trans hn)
        _ = 2 * step := by ring
    have := abs_sub_abs_le_abs_sub Δs Δsj
    linarith
  calc |Δm - Real.sqrt σ * Δs| ≤ |Δm| + Real.sqrt σ * |Δs| := by
        calc |Δm - Real.sqrt σ * Δs| ≤ |Δm| + |Real.sqrt σ * Δs| := abs_sub _ _
          _ = |Δm| + Real.sqrt σ * |Δs| := by rw [abs_mul, abs_of_nonneg hsσ]
    _ ≤ (|Δmj| + 2 * step) + Real.sqrt σ * (|Δsj| + 2 * step) :=
        add_le_add hΔm (mul_le_mul_of_nonneg_left hΔs hsσ)
    _ = (|Δmj| + Real.sqrt σ * |Δsj|) + (2 + 2 * Real.sqrt σ) * step := by ring
    _ ≤ c + (2 + 2 * Real.sqrt σ) * step := by linarith

end Dual

end StatisticalRL.RobustRL.DRVI
