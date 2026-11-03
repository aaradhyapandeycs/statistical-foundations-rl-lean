import Formalization.Generative.FiniteHorizonAuxiliaryVariance

/-! Finite true-kernel variance budgets underlying Li et al., Lemma 12.
The forcing and values are the actual auxiliary recursion, not new premises. -/
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]

noncomputable def auxiliaryVarianceBudget : List (EnvironmentStage State Action) →
    (ℕ → State → Action) → ℕ → State → ℝ
  | [], _, _ => fun _ ↦ 0
  | E :: es, f, l => fun s ↦
      (E.transition s (f 0 s)).variance (trueAuxiliaryValue es (fun k ↦ f (k + 1)) l) +
      (E.transition s (f 0 s)).expectation (auxiliaryVarianceBudget es (fun k ↦ f (k + 1)) l)

theorem auxiliaryVarianceBudget_nonneg (es : List (EnvironmentStage State Action))
    (f : ℕ → State → Action) (l : ℕ) (s : State) : 0 ≤ auxiliaryVarianceBudget es f l s := by
  induction es generalizing f s with
  | nil => exact le_rfl
  | cons E es ih =>
    exact add_nonneg ((E.transition s (f 0 s)).variance_nonneg _)
      ((E.transition s (f 0 s)).expectation_nonneg (fun t ↦ ih (fun k ↦ f (k + 1)) t))

/-- A telescoping potential bound for the actual cumulative conditional variances.
The uniform lower-level estimate is an input to this helper only; the final
level-growth theorem discharges it by induction from normalized rewards. -/
theorem auxiliaryVarianceBudget_le_potential (H l : ℕ) (M : ℝ)
    (hb : ∀ (es : List (EnvironmentStage State Action)) (f : ℕ → State → Action) (s : State),
      es.length ≤ H → trueAuxiliaryValue es f l s ≤ M)
    (es : List (EnvironmentStage State Action)) (f : ℕ → State → Action)
    (hlen : es.length ≤ H) (s : State) :
    auxiliaryVarianceBudget es f l s ≤
      2 * M * trueAuxiliaryValue es f l s - (trueAuxiliaryValue es f l s) ^ 2 := by
  induction es generalizing f s with
  | nil => simp [auxiliaryVarianceBudget, trueAuxiliaryValue]
  | cons E es ih =>
    have ht : es.length ≤ H := by simp only [List.length_cons] at hlen; omega
    let d := E.transition s (f 0 s)
    let V := trueAuxiliaryValue es (fun k ↦ f (k + 1)) l
    let r := auxiliaryPolicyReward (E :: es) f l s
    have hI := d.expectation_mono (fun t ↦ ih (fun k ↦ f (k + 1)) ht t)
    have hlin : d.expectation (fun t ↦ 2 * M * V t - V t ^ 2) =
        2 * M * d.expectation V - d.expectation (fun t ↦ V t ^ 2) := by
      rw [d.expectation_sub, d.expectation_mul]
    change d.expectation (auxiliaryVarianceBudget es (fun k ↦ f (k + 1)) l) ≤
      d.expectation (fun t ↦ 2 * M * V t - V t ^ 2) at hI
    rw [hlin] at hI
    have hr : 0 ≤ r := auxiliaryPolicyReward_nonneg _ _ _ _
    have hv : trueAuxiliaryValue (E :: es) f l s = r + d.expectation V :=
      trueAuxiliaryValue_bellman _ _ _ _ _
    have hupper := hb (E :: es) f s hlen
    have hm : d.expectation V ≤ trueAuxiliaryValue (E :: es) f l s := by rw [hv]; linarith
    have hp : 0 ≤ r * (2 * M - trueAuxiliaryValue (E :: es) f l s - d.expectation V) :=
      mul_nonneg hr (by linarith)
    change d.variance V + d.expectation (auxiliaryVarianceBudget es (fun k ↦ f (k + 1)) l) ≤ _
    unfold FiniteDistribution.variance
    nlinarith

/-- The potential is at most the square of the uniform value envelope. -/
theorem auxiliaryVarianceBudget_le_sq (H l : ℕ) (M : ℝ)
    (hb : ∀ (es : List (EnvironmentStage State Action)) (f : ℕ → State → Action) (s : State),
      es.length ≤ H → trueAuxiliaryValue es f l s ≤ M)
    (es : List (EnvironmentStage State Action)) (f : ℕ → State → Action)
    (hlen : es.length ≤ H) (s : State) : auxiliaryVarianceBudget es f l s ≤ M ^ 2 := by
  have hp := auxiliaryVarianceBudget_le_potential H l M hb es f hlen s
  nlinarith [sq_nonneg (M - trueAuxiliaryValue es f l s)]

/-- Two-term weighted Cauchy--Schwarz, including zero weights. -/
theorem auxiliary_add_sq_le {a b v w n : ℝ} (ha : 0 ≤ a)
    (hv : 0 ≤ v) (hw : 0 ≤ w) (hn : 0 ≤ n)
    (ha2 : a ^ 2 = v) (hb2 : b ^ 2 ≤ n * w) :
    (a + b) ^ 2 ≤ (n + 1) * (v + w) := by
  have hs := sq_nonneg (Real.sqrt n * a - Real.sqrt w)
  have hns := Real.sq_sqrt hn
  have hws := Real.sq_sqrt hw
  have hbn : b ≤ Real.sqrt n * Real.sqrt w := by
    have hnw : 0 ≤ Real.sqrt n * Real.sqrt w := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have he : (Real.sqrt n * Real.sqrt w) ^ 2 = n * w := by rw [mul_pow, hns, hws]
    nlinarith
  have hprod : a * b ≤ a * (Real.sqrt n * Real.sqrt w) := mul_le_mul_of_nonneg_left hbn ha
  nlinarith [sq_nonneg a]

/-- Jensen and finite-time Cauchy--Schwarz for the accumulated standard deviations. -/
theorem trueAuxiliaryValue_succ_sq_le (es : List (EnvironmentStage State Action))
    (f : ℕ → State → Action) (l : ℕ) (s : State) :
    (trueAuxiliaryValue es f (l + 1) s) ^ 2 ≤ es.length * auxiliaryVarianceBudget es f l s := by
  induction es generalizing f s with
  | nil => simp [trueAuxiliaryValue, auxiliaryVarianceBudget]
  | cons E es ih =>
    let d := E.transition s (f 0 s)
    let W := auxiliaryVarianceBudget es (fun k ↦ f (k + 1)) l
    let U := trueAuxiliaryValue es (fun k ↦ f (k + 1)) (l + 1)
    let v := d.variance (trueAuxiliaryValue es (fun k ↦ f (k + 1)) l)
    have hv : 0 ≤ v := d.variance_nonneg _
    have hw : 0 ≤ d.expectation W := d.expectation_nonneg (fun t ↦ auxiliaryVarianceBudget_nonneg _ _ _ _)
    have hj : (d.expectation U) ^ 2 ≤ d.expectation (fun t ↦ U t ^ 2) := by
      have h := d.variance_nonneg U
      unfold FiniteDistribution.variance at h
      linarith
    have hi := d.expectation_mono (fun t ↦ ih (fun k ↦ f (k + 1)) t)
    change d.expectation (fun t ↦ U t ^ 2) ≤ d.expectation (fun t ↦ (es.length : ℝ) * W t) at hi
    rw [d.expectation_mul] at hi
    have hh := auxiliary_add_sq_le (Real.sqrt_nonneg v)
      hv hw
      (Nat.cast_nonneg es.length) (Real.sq_sqrt hv) (hj.trans hi)
    simpa only [trueAuxiliaryValue, auxiliaryVarianceBudget, List.length_cons, Nat.cast_add,
      Nat.cast_one] using hh

/-- Normalized source rewards bound the actual level-zero value. -/
theorem trueAuxiliaryValue_zero_le_length (es : List (EnvironmentStage State Action))
    (f : ℕ → State → Action) (s : State) : trueAuxiliaryValue es f 0 s ≤ es.length := by
  induction es generalizing f s with
  | nil => simp [trueAuxiliaryValue]
  | cons E es ih =>
    have h := (E.transition s (f 0 s)).expectation_le_const
      (fun t ↦ ih (fun k ↦ f (k + 1)) t)
    have hr := E.reward_le_one s (f 0 s)
    simp only [trueAuxiliaryValue, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith

/-- Li et al. Lemma 12, with the exact displayed constant and no growth premise.
The bound holds for every fixed deterministic policy and every finite model. -/
theorem trueAuxiliaryValue_le_source_growth (H l : ℕ)
    (es : List (EnvironmentStage State Action)) (f : ℕ → State → Action)
    (hlen : es.length ≤ H) (s : State) :
    trueAuxiliaryValue es f l s ≤ (H : ℝ) * Real.sqrt (3 * (H : ℝ)) ^ l := by
  induction l generalizing es f s with
  | zero =>
    simpa only [pow_zero, mul_one] using (trueAuxiliaryValue_zero_le_length es f s).trans
      (Nat.cast_le.mpr hlen)
  | succ l ih =>
    let M : ℝ := (H : ℝ) * Real.sqrt (3 * (H : ℝ)) ^ l
    have hM : 0 ≤ M := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _)
    have hb : ∀ (xs : List (EnvironmentStage State Action)) (g : ℕ → State → Action) (t : State),
        xs.length ≤ H → trueAuxiliaryValue xs g l t ≤ M :=
      fun xs g t hx ↦ ih xs g hx t
    have hw := auxiliaryVarianceBudget_le_sq H l M hb es f hlen s
    have hs := trueAuxiliaryValue_succ_sq_le es f l s
    have hlenR : (es.length : ℝ) ≤ H := Nat.cast_le.mpr hlen
    have hprod : (es.length : ℝ) * auxiliaryVarianceBudget es f l s ≤ (H : ℝ) * M ^ 2 :=
      (mul_le_mul_of_nonneg_left hw (Nat.cast_nonneg _)).trans
        (mul_le_mul_of_nonneg_right hlenR (sq_nonneg M))
    have hH : 0 ≤ (H : ℝ) := Nat.cast_nonneg _
    have hr : Real.sqrt (3 * (H : ℝ)) ^ 2 = 3 * (H : ℝ) := Real.sq_sqrt (by positivity)
    have htarget : 0 ≤ Real.sqrt (3 * (H : ℝ)) * M := mul_nonneg (Real.sqrt_nonneg _) hM
    have htSq : (Real.sqrt (3 * (H : ℝ)) * M) ^ 2 = 3 * (H : ℝ) * M ^ 2 := by
      rw [mul_pow, hr]
    have hbound : trueAuxiliaryValue es f (l + 1) s ≤ Real.sqrt (3 * (H : ℝ)) * M := by
      have hnonneg := trueAuxiliaryValue_nonneg es f (l + 1) s
      have haux : 0 ≤ (H : ℝ) * M ^ 2 := mul_nonneg hH (sq_nonneg M)
      nlinarith
    calc
      trueAuxiliaryValue es f (l + 1) s ≤ Real.sqrt (3 * (H : ℝ)) * M := hbound
      _ = (H : ℝ) * Real.sqrt (3 * (H : ℝ)) ^ (l + 1) := by dsimp [M]; ring

/-- The source bound at every stage, including the terminal suffix. -/
theorem trueAuxiliaryValueAt_le_source_growth (es : List (EnvironmentStage State Action))
    (f : ℕ → State → Action) (l h : ℕ) (s : State) :
    trueAuxiliaryValueAt es f l h s ≤
      (es.length : ℝ) * Real.sqrt (3 * (es.length : ℝ)) ^ l := by
  exact trueAuxiliaryValue_le_source_growth es.length l (es.drop h) (fun k ↦ f (h + k))
    (by simp only [List.length_drop]; omega) s

/-- The complete supremum-norm statement of source Lemma 12. -/
theorem norm_trueAuxiliaryValueAt_le_source_growth (es : List (EnvironmentStage State Action))
    (f : ℕ → State → Action) (l h : ℕ) :
    ‖trueAuxiliaryValueAt es f l h‖ ≤
      (es.length : ℝ) * Real.sqrt (3 * (es.length : ℝ)) ^ l := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg _)
    (pow_nonneg (Real.sqrt_nonneg _) _))).2
  intro s
  rw [Real.norm_eq_abs]
  have hn : 0 ≤ trueAuxiliaryValueAt es f l h s := trueAuxiliaryValue_nonneg _ _ _ _
  rw [abs_of_nonneg hn]
  exact trueAuxiliaryValueAt_le_source_growth es f l h s

end StatisticalRL.FiniteHorizonGenerative
