import Formalization.ModelFree.FiniteQ.IterateBounds
import Formalization.ModelFree.QLearningChiComparison

/-! # Finite-horizon robust comparison functions

Finite-horizon analogue of the comparison functions of `sec:sharp-analysis-Q-generative`
(`chapters/generative_model_model_free.tex:1376–1525`), defined by backward induction (no fixed
point): with the source χ² uncertainty ball `U_ρ(p)` (`qChiBall`, support-restricted),
`Q⁺_h = r_h + b + sup_{q ∈ U_ρ(P_h(·|s,a))} q V⁺_{h+1}`, `Q⁻_h = r_h - b + inf_q q V⁻_{h+1}`,
`V^±_h = max_a Q^±_h`, `V^±_{H+1} = 0`. These are deterministic (they do not depend on data). -/

open StatisticalRL.QLearning

namespace StatisticalRL.FiniteQLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]

open EnvironmentStage

/-- Upper comparison value `V⁺` of a list of stages. -/
noncomputable def plusV (ρ b : ℝ) : List (EnvironmentStage State Action) → State → ℝ
  | [] => fun _ ↦ 0
  | e :: es => fun s ↦
    letI : Nonempty Action := e.action_nonempty
    actionMaximum fun a ↦ e.reward s a + b +
      sSup (qRobustExpectations (e.transition s a) ρ (plusV ρ b es))

/-- Upper comparison function `Q⁺` of the first stage of a list of stages. -/
noncomputable def plusQ (ρ b : ℝ) : List (EnvironmentStage State Action) → State → Action → ℝ
  | [] => fun _ _ ↦ 0
  | e :: es => fun s a ↦
    e.reward s a + b + sSup (qRobustExpectations (e.transition s a) ρ (plusV ρ b es))

/-- Lower comparison value `V⁻` of a list of stages. -/
noncomputable def minusV (ρ b : ℝ) : List (EnvironmentStage State Action) → State → ℝ
  | [] => fun _ ↦ 0
  | e :: es => fun s ↦
    letI : Nonempty Action := e.action_nonempty
    actionMaximum fun a ↦ e.reward s a - b +
      sInf (qRobustExpectations (e.transition s a) ρ (minusV ρ b es))

/-- Lower comparison function `Q⁻` of the first stage of a list of stages. -/
noncomputable def minusQ (ρ b : ℝ) : List (EnvironmentStage State Action) → State → Action → ℝ
  | [] => fun _ _ ↦ 0
  | e :: es => fun s a ↦
    e.reward s a - b + sInf (qRobustExpectations (e.transition s a) ρ (minusV ρ b es))

section NonemptyAction

variable [Nonempty Action]

theorem actionMaximum_const' (c : ℝ) : actionMaximum (fun _ : Action ↦ c) = c :=
  le_antisymm (actionMaximum_le_of_forall fun _ ↦ le_rfl) (le_actionMaximum (fun _ : Action ↦ c) (Classical.arbitrary _))

theorem actionMaximum_sub_le (f g : Action → ℝ) :
    actionMaximum f - actionMaximum g ≤ actionMaximum (fun a ↦ f a - g a) := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
  have h1 : actionMaximum f = f a := ha
  have h2 := le_actionMaximum g a
  have h3 := le_actionMaximum (fun a ↦ f a - g a) a
  simp only at h3
  linarith

theorem plusV_eq (ρ b : ℝ) (es : List (EnvironmentStage State Action)) (s : State) :
    plusV ρ b es s = actionMaximum (plusQ ρ b es s) := by
  cases es with
  | nil => simp [plusV, plusQ, actionMaximum_const']
  | cons e es => rfl

theorem minusV_eq (ρ b : ℝ) (es : List (EnvironmentStage State Action)) (s : State) :
    minusV ρ b es s = actionMaximum (minusQ ρ b es s) := by
  cases es with
  | nil => simp [minusV, minusQ, actionMaximum_const']
  | cons e es => rfl

theorem optimalValue_eq (es : List (EnvironmentStage State Action)) (s : State) :
    optimalValue es s = actionMaximum (optimalQ es s) := by
  cases es with
  | nil => simp [optimalValue, optimalQ, actionMaximum_const']
  | cons e es => rfl

end NonemptyAction

/-! ## Range of the true optimal values -/

theorem optimalQ_mem_range (es : List (EnvironmentStage State Action)) (s : State) (a : Action) :
    0 ≤ optimalQ es s a ∧ optimalQ es s a ≤ es.length := by
  induction es generalizing s a with
  | nil => simp [optimalQ]
  | cons e es ih =>
    letI : Nonempty Action := e.action_nonempty
    have hv : ∀ x, 0 ≤ optimalValue es x ∧ optimalValue es x ≤ es.length := fun x ↦ by
      rw [optimalValue_eq]
      exact ⟨le_actionMaximum_of_forall fun a ↦ (ih x a).1,
        actionMaximum_le_of_forall fun a ↦ (ih x a).2⟩
    have h0 := (e.transition s a).expectation_nonneg fun x ↦ (hv x).1
    have h1 := (e.transition s a).expectation_le_const fun x ↦ (hv x).2
    have hr0 := e.reward_nonneg s a
    have hr1 := e.reward_le_one s a
    simp only [optimalQ, qBackup, List.length_cons, Nat.cast_add, Nat.cast_one]
    constructor <;> linarith

theorem optimalValue_mem_range [Nonempty Action] (es : List (EnvironmentStage State Action))
    (s : State) : 0 ≤ optimalValue es s ∧ optimalValue es s ≤ es.length := by
  rw [optimalValue_eq]
  exact ⟨le_actionMaximum_of_forall fun a ↦ (optimalQ_mem_range es s a).1,
    actionMaximum_le_of_forall fun a ↦ (optimalQ_mem_range es s a).2⟩

theorem optimalQ_le_optimalValue [Nonempty Action] (es : List (EnvironmentStage State Action))
    (s : State) (a : Action) : optimalQ es s a ≤ optimalValue es s := by
  rw [optimalValue_eq]
  exact le_actionMaximum _ a

/-! ## Robust support values of a bounded vector -/

theorem sSup_robust_mem (p : FiniteDistribution State) {ρ : ℝ} (hρ : 0 ≤ ρ) (v : State → ℝ)
    {m M : ℝ} (hv : ∀ x, m ≤ v x ∧ v x ≤ M) :
    m ≤ sSup (qRobustExpectations p ρ v) ∧ sSup (qRobustExpectations p ρ v) ≤ M := by
  have hne := qRobustExpectations_nonempty p ρ hρ v
  have hb := (qChi_expectation_image_bounded p ρ v).1
  constructor
  · have hm : m ≤ p.expectation v := by
      have := p.expectation_mono (f := fun _ ↦ m) (g := v) fun x ↦ (hv x).1
      simpa using this
    exact hm.trans (le_csSup hb ⟨p, qChiBall_self p ρ hρ, rfl⟩)
  · apply csSup_le hne
    rintro z ⟨q, _, rfl⟩
    exact q.expectation_le_const fun x ↦ (hv x).2

theorem sInf_robust_mem (p : FiniteDistribution State) {ρ : ℝ} (hρ : 0 ≤ ρ) (v : State → ℝ)
    {m M : ℝ} (hv : ∀ x, m ≤ v x ∧ v x ≤ M) :
    m ≤ sInf (qRobustExpectations p ρ v) ∧ sInf (qRobustExpectations p ρ v) ≤ M := by
  have hne := qRobustExpectations_nonempty p ρ hρ v
  have hb := (qChi_expectation_image_bounded p ρ v).2
  constructor
  · apply le_csInf hne
    rintro z ⟨q, _, rfl⟩
    have := q.expectation_mono (f := fun _ ↦ m) (g := v) fun x ↦ (hv x).1
    simpa using this
  · have hM : p.expectation v ≤ M := p.expectation_le_const fun x ↦ (hv x).2
    exact (csInf_le hb ⟨p, qChiBall_self p ρ hρ, rfl⟩).trans hM

theorem expectation_le_sSup_robust (p : FiniteDistribution State) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (v : State → ℝ) : p.expectation v ≤ sSup (qRobustExpectations p ρ v) :=
  le_csSup (qChi_expectation_image_bounded p ρ v).1 ⟨p, qChiBall_self p ρ hρ, rfl⟩

theorem sInf_robust_le_expectation (p : FiniteDistribution State) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (v : State → ℝ) : sInf (qRobustExpectations p ρ v) ≤ p.expectation v :=
  csInf_le (qChi_expectation_image_bounded p ρ v).2 ⟨p, qChiBall_self p ρ hρ, rfl⟩

theorem expectation_sub_sInf_le (p : FiniteDistribution State) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (v : State → ℝ) :
    p.expectation v - sInf (qRobustExpectations p ρ v) ≤ Real.sqrt (ρ * p.variance v) := by
  have : p.expectation v - Real.sqrt (ρ * p.variance v) ≤ sInf (qRobustExpectations p ρ v) := by
    apply le_csInf (qRobustExpectations_nonempty p ρ hρ v)
    rintro z ⟨q, hq, rfl⟩
    have := (abs_le.mp (qChiBall_abs_expectation_sub_le p q ρ v hq)).1
    linarith
  linarith

/-! ## Range of the comparison functions

`Q⁺` of a list of length `n` lies in `[n b, n b + n]` and `Q⁻` in `[-n b, n - n b]`; in particular
the next-stage values have span at most `n - 1 ≤ H`. -/

theorem plus_mem_range [Nonempty Action] {ρ b : ℝ} (hρ : 0 ≤ ρ)
    (es : List (EnvironmentStage State Action)) :
    (∀ s a, es.length * b ≤ plusQ ρ b es s a ∧ plusQ ρ b es s a ≤ es.length * b + es.length) ∧
    (∀ s, es.length * b ≤ plusV ρ b es s ∧ plusV ρ b es s ≤ es.length * b + es.length) := by
  induction es with
  | nil => simp [plusQ, plusV]
  | cons e es ih =>
    have hQ : ∀ s a, ((e :: es).length : ℝ) * b ≤ plusQ ρ b (e :: es) s a ∧
        plusQ ρ b (e :: es) s a ≤ (e :: es).length * b + (e :: es).length := by
      intro s a
      have hs := sSup_robust_mem (e.transition s a) hρ (plusV ρ b es) ih.2
      have hr0 := e.reward_nonneg s a
      have hr1 := e.reward_le_one s a
      simp only [plusQ, List.length_cons, Nat.cast_add, Nat.cast_one]
      constructor <;> nlinarith
    refine ⟨hQ, fun s ↦ ?_⟩
    rw [plusV_eq]
    exact ⟨le_actionMaximum_of_forall fun a ↦ (hQ s a).1,
      actionMaximum_le_of_forall fun a ↦ (hQ s a).2⟩

theorem minus_mem_range [Nonempty Action] {ρ b : ℝ} (hρ : 0 ≤ ρ)
    (es : List (EnvironmentStage State Action)) :
    (∀ s a, -(es.length * b) ≤ minusQ ρ b es s a ∧
      minusQ ρ b es s a ≤ es.length - es.length * b) ∧
    (∀ s, -(es.length * b) ≤ minusV ρ b es s ∧ minusV ρ b es s ≤ es.length - es.length * b) := by
  induction es with
  | nil => simp [minusQ, minusV]
  | cons e es ih =>
    have hQ : ∀ s a, -(((e :: es).length : ℝ) * b) ≤ minusQ ρ b (e :: es) s a ∧
        minusQ ρ b (e :: es) s a ≤ (e :: es).length - (e :: es).length * b := by
      intro s a
      have hs := sInf_robust_mem (e.transition s a) hρ (minusV ρ b es) ih.2
      have hr0 := e.reward_nonneg s a
      have hr1 := e.reward_le_one s a
      simp only [minusQ, List.length_cons, Nat.cast_add, Nat.cast_one]
      constructor <;> nlinarith
    refine ⟨hQ, fun s ↦ ?_⟩
    rw [minusV_eq]
    exact ⟨le_actionMaximum_of_forall fun a ↦ (hQ s a).1,
      actionMaximum_le_of_forall fun a ↦ (hQ s a).2⟩

/-- Centered deviation of the next-stage upper value: `|V⁺(x) - p V⁺| ≤ n`. -/
theorem plusV_centered_le [Nonempty Action] {ρ b : ℝ} (hρ : 0 ≤ ρ)
    (es : List (EnvironmentStage State Action)) (p : FiniteDistribution State) (x : State) :
    |plusV ρ b es x - p.expectation (plusV ρ b es)| ≤ es.length := by
  have hr := (plus_mem_range (b := b) hρ es).2
  have hpair : ∀ x y, |plusV ρ b es x - plusV ρ b es y| ≤ es.length := fun x y ↦ by
    have := hr x; have := hr y
    rw [abs_le]; constructor <;> linarith
  exact qChi_abs_centered_le_of_pairwise p _ _ hpair x

theorem minusV_centered_le [Nonempty Action] {ρ b : ℝ} (hρ : 0 ≤ ρ)
    (es : List (EnvironmentStage State Action)) (p : FiniteDistribution State) (x : State) :
    |minusV ρ b es x - p.expectation (minusV ρ b es)| ≤ es.length := by
  have hr := (minus_mem_range (b := b) hρ es).2
  have hpair : ∀ x y, |minusV ρ b es x - minusV ρ b es y| ≤ es.length := fun x y ↦ by
    have := hr x; have := hr y
    rw [abs_le]; constructor <;> linarith
  exact qChi_abs_centered_le_of_pairwise p _ _ hpair x

/-! ## Residual lower bounds (absorption of the fluctuation, finite-horizon `B.3.3`)

With `b = 2ρK` and the next list of length at most `K`, the residuals
`Q⁺ - r - P V⁺` and `r + P V⁻ - Q⁻` are at least `√(ρ Var_P V^±) + ρ K`. -/

theorem plus_residual_ge [Nonempty Action] {ρ K : ℝ} (hρ : 0 ≤ ρ) (hK : 0 < K)
    (e : EnvironmentStage State Action) (es : List (EnvironmentStage State Action))
    (hlen : (es.length : ℝ) ≤ K) (s : State) (a : Action) :
    Real.sqrt (ρ * (e.transition s a).variance (plusV ρ (2 * ρ * K) es)) + ρ * K ≤
      plusQ ρ (2 * ρ * K) (e :: es) s a - e.reward s a -
        (e.transition s a).expectation (plusV ρ (2 * ρ * K) es) := by
  letI : Nonempty State := e.state_nonempty
  have hr := (plus_mem_range (b := 2 * ρ * K) hρ es).2
  have hspan : qChiValueSpan (plusV ρ (2 * ρ * K) es) ≤ K := by
    unfold qChiValueSpan
    have h1 := actionMaximum_le_of_forall fun x ↦ (hr x).2
    have h2 := actionMaximum_le_of_forall (f := fun x ↦ -plusV ρ (2 * ρ * K) es x)
      fun x ↦ neg_le_neg (hr x).1
    linarith
  have hc := ((qChi_support_comparison (e.transition s a) ρ K hρ hK _ hspan).1).1
  simp only [plusQ]
  nlinarith

theorem minus_residual_ge [Nonempty Action] {ρ K : ℝ} (hρ : 0 ≤ ρ) (hK : 0 < K)
    (e : EnvironmentStage State Action) (es : List (EnvironmentStage State Action))
    (hlen : (es.length : ℝ) ≤ K) (s : State) (a : Action) :
    Real.sqrt (ρ * (e.transition s a).variance (minusV ρ (2 * ρ * K) es)) + ρ * K ≤
      e.reward s a + (e.transition s a).expectation (minusV ρ (2 * ρ * K) es) -
        minusQ ρ (2 * ρ * K) (e :: es) s a := by
  letI : Nonempty State := e.state_nonempty
  have hr := (minus_mem_range (b := 2 * ρ * K) hρ es).2
  have hspan : qChiValueSpan (minusV ρ (2 * ρ * K) es) ≤ K := by
    unfold qChiValueSpan
    have h1 := actionMaximum_le_of_forall fun x ↦ (hr x).2
    have h2 := actionMaximum_le_of_forall (f := fun x ↦ -minusV ρ (2 * ρ * K) es x)
      fun x ↦ neg_le_neg (hr x).1
    nlinarith
  have hc := ((qChi_support_comparison (e.transition s a) ρ K hρ hK _ hspan).2).1
  simp only [minusQ]
  nlinarith

end StatisticalRL.FiniteQLearning
