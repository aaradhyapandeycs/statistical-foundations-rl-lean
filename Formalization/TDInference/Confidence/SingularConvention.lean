import Formalization.TDInference.PluginCovariance.Singular
import Formalization.TDInference.PluginCovariance.Coverage

/-!
# The convention on the singular event does not matter (SOURCE-ISSUES C47(4))

Source: `chapters/inference.tex:156–196`: the plug-in estimators `Ā_T`, `Γ̂_T` (:165–172), the
plug-in covariance `Λ̂_T = Ā_T⁻¹Γ̂_TĀ_T⁻ᵀ` (`eq:defn-hat-Lambda`, display :180–182) and the
confidence rule `eq:convex.Cdelta` (:187–196). SOURCE-ISSUES C47(4): `Ā_T` is singular exactly
when some state is unsampled (`aBar_det_ne_zero_iff`), so the printed `Λ̂_T`, and with it the
printed procedure, is undefined on that event, whose probability is positive for every `T` when
two distinct states have positive `μ`-mass (`pathProb_aBar_singular_pos`).

This file defines nothing new about the printed procedure and does not repair the source gap
(C47(4) stays recorded). It shows that the choice of a convention on the singular event does not
matter asymptotically, and quantifies it at finite `T`:

* `abs_pathProb_sub_le_of_eq_on_nonsingular`: two events of the sample path that agree on the
  event `{det Ā_T ≠ 0}` have probabilities differing by at most `P(Ā_T singular)`, hence by at
  most `∑_s (1 − μ(s))^T` (`pathProb_aBar_singular_le`).
* `abs_coverage_sub_le_of_eq_on_nonsingular`: the same for the coverage probabilities
  `P(V ∈ C₁(ω))`, `P(V ∈ C₂(ω))` of two confidence procedures `C₁ C₂ : data → Set (State → ℝ)`
  that agree whenever `Ā_T` is invertible (a statement about arbitrary set-valued procedures;
  the Gaussian-mass condition of `eq:convex.Cdelta` itself is not formalized here) (for example the procedure built with Lean's
  `Matrix.inv = 0` convention and the one built with any other value on the singular event).
* `exists_rate_abs_coverage_sub_le`: under full support the bound is `S ρ^T` with
  `ρ = max_s (1 − μ(s)) ∈ [0, 1)`, a geometric rate; `tendsto_abs_coverage_sub`: the difference
  tends to `0`.
* `tendsto_coverage_twoSided_plugin_anyConvention` (representative corollary of
  `plugin_coverage_tendsto`, D2): for every covariance estimate `L` that equals `lambdaHat`
  whenever `Ā_T` is invertible (an arbitrary convention on the singular event), the two-sided
  interval `|uᵀ(V̄_T − V^π)| ≤ z√(uᵀL u/T)` has coverage `→ 2Φ(z) − 1`.
-/

open Filter Topology Finset ProbabilityTheory
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

/-- **C47(4), finite `T`.** Two events of the sample path that agree on the event where `Ā_T` is
invertible have probabilities differing by at most `∑_s (1 − μ(s))^T`. -/
theorem abs_pathProb_sub_le_of_eq_on_nonsingular (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (T : ℕ)
    (E F : Set (Fin T → Tuple State Action))
    (hEF : ∀ ω, (aBar M ω).det ≠ 0 → (ω ∈ E ↔ ω ∈ F)) :
    |pathProb M π μ T E - pathProb M π μ T F| ≤
      pathProb M π μ T {ω | (aBar M ω).det = 0} ∧
    |pathProb M π μ T E - pathProb M π μ T F| ≤ ∑ s, (1 - μ.prob s) ^ T := by
  have h1 : |pathProb M π μ T E - pathProb M π μ T F| ≤
      pathProb M π μ T {ω | (aBar M ω).det = 0} := by
    simp only [pathProb]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ω _ ↦ ?_)
    rw [← mul_sub, abs_mul, abs_of_nonneg (pathWeight_nonneg M π μ ω)]
    refine mul_le_mul_of_nonneg_left ?_ (pathWeight_nonneg M π μ ω)
    by_cases hω : (aBar M ω).det = 0
    · rw [Set.indicator_of_mem (show ω ∈ {ω | (aBar M ω).det = 0} from hω)]
      by_cases hE : ω ∈ E <;> by_cases hF : ω ∈ F <;> simp [hE, hF]
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | (aBar M ω).det = 0} from hω)]
      by_cases hE : ω ∈ E
      · simp [hE, (hEF ω hω).1 hE]
      · have hF : ω ∉ F := fun h ↦ hE ((hEF ω hω).2 h)
        simp [hE, hF]
  exact ⟨h1, h1.trans (pathProb_aBar_singular_le M π μ T)⟩

/-- **C47(4), confidence procedures.** If two confidence procedures (maps from the data to sets
of value functions) agree whenever `Ā_T` is invertible, then for every target `V` their coverage
probabilities differ by at most `P(Ā_T singular) ≤ ∑_s (1 − μ(s))^T`. -/
theorem abs_coverage_sub_le_of_eq_on_nonsingular (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (T : ℕ)
    (C₁ C₂ : (Fin T → Tuple State Action) → Set (State → ℝ))
    (hC : ∀ ω, (aBar M ω).det ≠ 0 → C₁ ω = C₂ ω) (V : State → ℝ) :
    |pathProb M π μ T {ω | V ∈ C₁ ω} - pathProb M π μ T {ω | V ∈ C₂ ω}| ≤
      pathProb M π μ T {ω | (aBar M ω).det = 0} ∧
    |pathProb M π μ T {ω | V ∈ C₁ ω} - pathProb M π μ T {ω | V ∈ C₂ ω}| ≤
      ∑ s, (1 - μ.prob s) ^ T :=
  abs_pathProb_sub_le_of_eq_on_nonsingular M π μ T _ _ fun ω hω ↦ by
    simp only [Set.mem_setOf_eq, hC ω hω]

omit [DecidableEq State] in
/-- Under full support, `∑_s (1 − μ(s))^T ≤ S ρ^T` with `0 ≤ ρ < 1` (`ρ = max_s (1 − μ(s))`). -/
theorem exists_rate_sum_one_sub_prob_pow (μ : FiniteDistribution State)
    (hμ : ∀ s, 0 < μ.prob s) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ T : ℕ,
      ∑ s, (1 - μ.prob s) ^ T ≤ (Fintype.card State : ℝ) * ρ ^ T := by
  have hle : ∀ s, μ.prob s ≤ 1 := fun s ↦ by
    rw [← μ.sum_prob]
    exact Finset.single_le_sum (fun s _ ↦ μ.prob_nonneg s) (Finset.mem_univ s)
  rcases isEmpty_or_nonempty State with hS | hS
  · exact ⟨0, le_rfl, zero_lt_one, fun T ↦ by simp⟩
  · obtain ⟨s₀, hs₀⟩ := Finite.exists_max (fun s ↦ 1 - μ.prob s)
    refine ⟨1 - μ.prob s₀, by linarith [hle s₀], by linarith [hμ s₀], fun T ↦ ?_⟩
    calc ∑ s, (1 - μ.prob s) ^ T ≤ ∑ _s : State, (1 - μ.prob s₀) ^ T :=
          Finset.sum_le_sum fun s _ ↦ pow_le_pow_left₀ (by linarith [hle s]) (hs₀ s) T
      _ = (Fintype.card State : ℝ) * (1 - μ.prob s₀) ^ T := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

omit [DecidableEq State] in
/-- Under full support, `∑_s (1 − μ(s))^T → 0`. -/
theorem tendsto_sum_one_sub_prob_pow (μ : FiniteDistribution State) (hμ : ∀ s, 0 < μ.prob s) :
    Tendsto (fun T : ℕ ↦ ∑ s, (1 - μ.prob s) ^ T) atTop (𝓝 0) := by
  have hle : ∀ s, μ.prob s ≤ 1 := fun s ↦ by
    rw [← μ.sum_prob]
    exact Finset.single_le_sum (fun s _ ↦ μ.prob_nonneg s) (Finset.mem_univ s)
  have h := tendsto_finset_sum (Finset.univ : Finset State) fun s _ ↦
    tendsto_pow_atTop_nhds_zero_of_lt_one (r := 1 - μ.prob s) (by linarith [hle s])
      (by linarith [hμ s])
  simpa using h

/-- **C47(4), geometric rate.** Under full support there is `0 ≤ ρ < 1` (namely
`max_s (1 − μ(s))`) such that for every `T` and any two confidence procedures agreeing whenever
`Ā_T` is invertible, the coverage probabilities of every target `V` differ by at most `S ρ^T`. -/
theorem exists_rate_abs_coverage_sub_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State)
    (hμ : ∀ s, 0 < μ.prob s) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∀ (T : ℕ) (C₁ C₂ : (Fin T → Tuple State Action) → Set (State → ℝ)),
      (∀ ω, (aBar M ω).det ≠ 0 → C₁ ω = C₂ ω) → ∀ V : State → ℝ,
        |pathProb M π μ T {ω | V ∈ C₁ ω} - pathProb M π μ T {ω | V ∈ C₂ ω}| ≤
          (Fintype.card State : ℝ) * ρ ^ T := by
  obtain ⟨ρ, hρ0, hρ1, hρ⟩ := exists_rate_sum_one_sub_prob_pow μ hμ
  exact ⟨ρ, hρ0, hρ1, fun T C₁ C₂ hC V ↦
    (abs_coverage_sub_le_of_eq_on_nonsingular M π μ T C₁ C₂ hC V).2.trans (hρ T)⟩

/-- **C47(4), asymptotic.** Under full support, for families of confidence procedures
`C₁ T, C₂ T` agreeing whenever `Ā_T` is invertible, the difference of coverage probabilities of
every target `V` tends to `0`. -/
theorem tendsto_abs_coverage_sub (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State)
    (hμ : ∀ s, 0 < μ.prob s)
    (C₁ C₂ : ∀ T : ℕ, (Fin T → Tuple State Action) → Set (State → ℝ))
    (hC : ∀ T (ω : Fin T → Tuple State Action), (aBar M ω).det ≠ 0 → C₁ T ω = C₂ T ω)
    (V : State → ℝ) :
    Tendsto (fun T : ℕ ↦
      |pathProb M π μ T {ω | V ∈ C₁ T ω} - pathProb M π μ T {ω | V ∈ C₂ T ω}|) atTop (𝓝 0) :=
  squeeze_zero (fun _ ↦ abs_nonneg _)
    (fun T ↦ (abs_coverage_sub_le_of_eq_on_nonsingular M π μ T (C₁ T) (C₂ T) (hC T) V).2)
    (tendsto_sum_one_sub_prob_pow μ hμ)

/-- Transfer of a coverage limit to every convention on the singular event: if events `E T`,
`F T` agree whenever `Ā_T` is invertible and `P(F T) → ℓ`, then `P(E T) → ℓ`. -/
theorem tendsto_pathProb_of_eq_on_nonsingular (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State)
    (hμ : ∀ s, 0 < μ.prob s) (E F : ∀ T : ℕ, Set (Fin T → Tuple State Action))
    (hEF : ∀ T (ω : Fin T → Tuple State Action), (aBar M ω).det ≠ 0 → (ω ∈ E T ↔ ω ∈ F T))
    {ℓ : ℝ} (hF : Tendsto (fun T ↦ pathProb M π μ T (F T)) atTop (𝓝 ℓ)) :
    Tendsto (fun T ↦ pathProb M π μ T (E T)) atTop (𝓝 ℓ) := by
  have hd : Tendsto (fun T ↦ pathProb M π μ T (E T) - pathProb M π μ T (F T)) atTop (𝓝 0) :=
    squeeze_zero_norm
      (fun T ↦ (abs_pathProb_sub_le_of_eq_on_nonsingular M π μ T (E T) (F T) (hEF T)).2)
      (tendsto_sum_one_sub_prob_pow μ hμ)
  simpa using hd.add hF

/-- **Plug-in two-sided coverage under any convention (C47(4), representative corollary of
`plugin_coverage_tendsto`, D2).** Let `L` be any covariance estimate that equals the plug-in
`Λ̂_T = lambdaHat` whenever `Ā_T` is invertible; its values on the singular event (where the
printed `Λ̂_T` is undefined) are arbitrary. Under full-support `μ`, `Γ_true ≻ 0`, `0 < η₀ ≤ 1`
and every `V₀`, for `u ≠ 0` and `z ≥ 0` the two-sided interval built from `L` has coverage
`P(|uᵀ(V̄_T − V^π)| ≤ z√(uᵀL u/T)) → 2Φ(z) − 1`. -/
theorem tendsto_coverage_twoSided_plugin_anyConvention [Nonempty State] [Nonempty Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {η₀ : ℝ} (h0 : 0 < η₀) (h1 : η₀ ≤ 1) (V₀ : State → ℝ)
    (hμ : ∀ s, 0 < μ.prob s) (hΓ : ∀ s, 0 < trueGamma M π μ s)
    (L : ∀ T : ℕ, (Fin T → Tuple State Action) → Matrix State State ℝ)
    (hL : ∀ T (ω : Fin T → Tuple State Action), (aBar M ω).det ≠ 0 →
      L T ω = lambdaHat M η₀ V₀ ω)
    {u : State → ℝ} (hu : u ≠ 0) {z : ℝ} (hz : 0 ≤ z) :
    Tendsto (fun T : ℕ ↦ pathProb M π μ T
        {ω : Fin T → Tuple State Action |
          |∑ s, u s * (prAverage M η₀ V₀ ω s - M.valueFixedPoint π s)| ≤
            z * Real.sqrt ((∑ s, ∑ s', u s * u s' * L T ω s s') / T)}) atTop
      (𝓝 (2 * (gaussianReal 0 1).real (Set.Iic z) - 1)) := by
  refine tendsto_pathProb_of_eq_on_nonsingular M π μ hμ _
    (fun T ↦ {ω : Fin T → Tuple State Action |
      |∑ s, u s * (prAverage M η₀ V₀ ω s - M.valueFixedPoint π s)| ≤
        z * Real.sqrt ((∑ s, ∑ s', u s * u s' * lambdaHat M η₀ V₀ ω s s') / T)})
    (fun T ω hω ↦ by simp only [Set.mem_setOf_eq, hL T ω hω]) ?_
  exact (plugin_coverage_tendsto M π μ h0 h1 V₀ hμ hΓ).2.1 u hu z hz

end StatisticalRL.Ch7Rest.TDInference
