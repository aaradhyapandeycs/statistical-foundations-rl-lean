import Formalization.MDP.DiscountedFiniteTrajectory
import Formalization.ModelFree.TDIterateBounds
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Theorem 7.11 (`thm:Berry-Esseen-linear`): definitions

Source: `chapters/inference.tex`. Setting and i.i.d. sampling :47–66, TD update
`eqn:td-learning-inference-2` :70–74, Polyak–Ruppert average `eq:TD-averaging-inference`
:80–83, error `eq:defn-bar-deltat` :86–89, `Λ⋆ = A⁻¹ΓA⁻ᵀ`, `A`, `Γ` :99–117, convex distance
`eqn:convex-distance` :124–127, theorem :132–141. `P_π` and `r_π` are `prelim.tex:405–419`.

Objects (all concrete; no measurability is needed on the data side):
* `tupleProb M π μ (s,a,s')` is the i.i.d. per-step weight `μ(s) π(a|s) P(s'|s,a)` (:56–61);
  the reward is the deterministic `r_t = r(s_t,a_t)` (:61).
* `stepSize η₀ t = η₀ t^{-2/3}` is the printed rate `η_t`, used only at `t ≥ 1`.
* `tdIter` is the asynchronous update (:72): only coordinate `s_t` changes. The update producing
  `V_{t+1}` uses the sample `ω t` (the `(t+1)`-st tuple) and the step size `stepSize η₀ (t+1)`,
  i.e. `η_t = η₀ t^{-2/3}` for `t ≥ 1` (never Lean's junk `0 ^ (-2/3) = 0`).
* `prAverage` is `V̄_T = T⁻¹ ∑_{t=1}^T V_t`, `scaledError` is `√T (V̄_T − V^π)`.
* `lawProb … T C` is the probability that `√T Δ̄_T ∈ C` under the i.i.d. law, a finite
  weighted sum; `lawProb_univ` proves the data law has total mass `1`.
* `tdA = diag(μ)(I − γ P_π)`; `printedGamma` is the printed diagonal `Γ_ss` with `r(s)` read as
  `r_π(s)` (`prelim.tex:418`, the only definition of a state-indexed reward), and `trueGamma` is
  the per-sample TD-noise covariance (the C43 correction; the covariance of the corrected CLT
  limit and of the plug-in target `trueLambda`).
* `gaussCov A Γ = N(0, A⁻¹ diag(Γ) A⁻ᵀ)` is the law of `A⁻¹ (√Γ ⊙ Z)` with `Z` standard
  Gaussian on `State → ℝ`; `gaussCov_isProbabilityMeasure` and `measurable_gaussMap` show it
  is a genuine probability measure, not the junk `Measure.map` value `0`.
* Plug-in covariance estimator (`eq:defn-hat-Lambda`, :156–185; lemmas in
  `TDInference/PluginCovariance/Basic.lean`): `pathProb` (probability of a path event), `sampleAMat` (`A_t`, :166),
  `sampleB` (`b_t`, :168), `aBar` (`Ā_T`, :166), `pluginWeight` (`w_{t,T}`, :175–177),
  `pluginResidual`, `gammaHatAt`, `gammaHat` (`Γ̂_T`, :168), `lambdaHat` (`Λ̂_T`, :180–182; Lean's
  `Matrix.inv` gives the junk value `0` on a singular `Ā_T`, C47(4)), `printedLambda` (printed `Λ⋆`)
  and `trueLambda` (`A⁻¹ diag(Γ_true) A⁻ᵀ`, C43).
* `printedRate` is the printed `T^{-1/3}` coefficient. `Γ` is diagonal (:111–117), so
  `‖Γ⁻¹‖ = 1 / min_s Γ_ss` and `κ(Γ) = max_s Γ_ss / min_s Γ_ss`; these are only *defined*
  (finite) when `Γ ≻ 0`, which the statement modules therefore assume (a definedness condition:
  with `Γ` singular the printed right-hand side is `+∞`).
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace StatisticalRL.Ch7Rest.TDInference

open StatisticalRL.TemporalDifference (policyReward)

variable {State Action : Type} [Fintype State] [Fintype Action]

/-- A sample tuple `(s_t, a_t, s'_t)`; the reward `r_t = r(s_t,a_t)` is deterministic
(`inference.tex:61`). -/
abbrev Tuple (State Action : Type) := State × Action × State

/-- The i.i.d. per-step weight `μ(s) π(a|s) P(s'|s,a)` (`inference.tex:56–61`). -/
def tupleProb (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (x : Tuple State Action) : ℝ :=
  μ.prob x.1 * (π x.1).prob x.2.1 * (M.transition x.1 x.2.1).prob x.2.2

/-- The printed learning rate `η_t = η₀ t^{-2/3}` (`inference.tex:134`), meaningful for `t ≥ 1`. -/
noncomputable def stepSize (η₀ : ℝ) (t : ℕ) : ℝ := η₀ * (t : ℝ) ^ (-(2 / 3 : ℝ))

/-- One asynchronous TD update (`eqn:td-learning-inference-2`, `inference.tex:72`): only the
coordinate `s` of the tuple `(s,a,s')` changes, to `(1-η)V(s) + η(r(s,a) + γV(s'))`. -/
def tdStep [DecidableEq State] (M : DiscountedMDP State Action) (η : ℝ) (V : State → ℝ)
    (x : Tuple State Action) : State → ℝ :=
  Function.update V x.1 ((1 - η) * V x.1 + η * (M.reward x.1 x.2.1 + M.discount * V x.2.2))

/-- The TD iterates `V_0 = V₀, V_1, …, V_T` driven by the sample path `ω : Fin T → Tuple`.
The update producing `V_{t+1}` uses the tuple `ω t` and the step size
`stepSize η₀ (t+1) = η₀ (t+1)^{-2/3}` (so `η_t = η₀ t^{-2/3}` for `t ≥ 1`). Indices `t ≥ T`
are never used by `prAverage`; there the iterate is frozen. -/
noncomputable def tdIter [DecidableEq State] (M : DiscountedMDP State Action) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (ω : Fin T → Tuple State Action) : ℕ → State → ℝ
  | 0 => V₀
  | t + 1 =>
      if h : t < T then tdStep M (stepSize η₀ (t + 1)) (tdIter M η₀ V₀ ω t) (ω ⟨t, h⟩)
      else tdIter M η₀ V₀ ω t

/-- Polyak–Ruppert average `V̄_T = T⁻¹ ∑_{t=1}^T V_t` (`eq:TD-averaging-inference`, :82). -/
noncomputable def prAverage [DecidableEq State] (M : DiscountedMDP State Action) (η₀ : ℝ)
    (V₀ : State → ℝ) {T : ℕ} (ω : Fin T → Tuple State Action) : State → ℝ :=
  (T : ℝ)⁻¹ • ∑ t ∈ Finset.range T, tdIter M η₀ V₀ ω (t + 1)

/-- The scaled averaged error `√T Δ̄_T = √T (V̄_T − V^π)` (`eq:defn-bar-deltat`, :88). -/
noncomputable def scaledError [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ}
    (ω : Fin T → Tuple State Action) : State → ℝ :=
  Real.sqrt T • (prAverage M η₀ V₀ ω - M.valueFixedPoint π)

/-- The i.i.d. weight of a whole sample path, `∏_t μ(s_t)π(a_t|s_t)P(s'_t|s_t,a_t)`. -/
def pathWeight (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {T : ℕ} (ω : Fin T → Tuple State Action) : ℝ :=
  ∏ t, tupleProb M π μ (ω t)

/-- `P(√T Δ̄_T ∈ C)` under the i.i.d. sampling law (`inference.tex:54–61`), for any set `C`. -/
noncomputable def lawProb [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (T : ℕ) (C : Set (State → ℝ)) : ℝ :=
  ∑ ω : Fin T → Tuple State Action,
    pathWeight M π μ ω * C.indicator (fun _ ↦ (1 : ℝ)) (scaledError M π η₀ V₀ ω)

/-- The matrix `P_π` (`eqn:ppivq`, `prelim.tex:407–411`), `P_π(s,s') = ∑_a π(a|s)P(s'|s,a)`. -/
def policyMatrix (M : DiscountedMDP State Action) (π : StationaryPolicy State Action) :
    Matrix State State ℝ :=
  Matrix.of fun s s' ↦ (M.policyTransition π s).prob s'

/-- `A = diag(μ)(I − γ P_π)` (`inference.tex:110`). -/
def tdA [DecidableEq State] (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) : Matrix State State ℝ :=
  Matrix.diagonal μ.prob * (1 - M.discount • policyMatrix M π)

/-- The printed diagonal `Γ_ss = μ(s) E_{s'∼P_π(·|s)}[(V^π(s) − (r(s) + γV^π(s')))²]`
(`inference.tex:111`), with `r(s) := r_π(s) = E_{a∼π(·|s)} r(s,a)` (`prelim.tex:414–419`). -/
noncomputable def printedGamma (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (s : State) : ℝ :=
  μ.prob s * (M.policyTransition π s).expectation fun s' ↦
    (M.valueFixedPoint π s - (policyReward M π s + M.discount * M.valueFixedPoint π s')) ^ 2

/-- The per-sample TD-noise covariance (diagonal),
`μ(s) E_{a∼π(·|s), s'∼P(·|s,a)}[(V^π(s) − r(s,a) − γV^π(s'))²]` (the C43 correction). It is the
covariance of the corrected CLT limit `N(0, A⁻¹ diag(Γ_true) A⁻ᵀ)` (`TDInference/ClassicCLT.lean`), the
target of the plug-in `Γ̂_T` (`trueLambda` below), and equals `printedGamma` when `r(s,·)` is
constant on the support of `π(·|s)`. -/
noncomputable def trueGamma (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (s : State) : ℝ :=
  μ.prob s * (π s).expectation fun a ↦ (M.transition s a).expectation fun s' ↦
    (M.valueFixedPoint π s - M.reward s a - M.discount * M.valueFixedPoint π s') ^ 2

/-- The map `z ↦ A⁻¹ (√Γ ⊙ z)`. -/
noncomputable def gaussMap [DecidableEq State] (A : Matrix State State ℝ) (Γ : State → ℝ)
    (z : State → ℝ) : State → ℝ :=
  Matrix.mulVec A⁻¹ fun s ↦ Real.sqrt (Γ s) * z s

/-- `N(0, A⁻¹ diag(Γ) A⁻ᵀ)`, as the law of `A⁻¹(√Γ ⊙ Z)` with `Z` standard Gaussian on
`State → ℝ` (its covariance is `A⁻¹ diag(√Γ) I diag(√Γ) A⁻ᵀ = A⁻¹ diag(Γ) A⁻ᵀ`). -/
noncomputable def gaussCov [DecidableEq State] (A : Matrix State State ℝ) (Γ : State → ℝ) :
    Measure (State → ℝ) :=
  (Measure.pi fun _ : State ↦ gaussianReal 0 1).map (gaussMap A Γ)

/-- `min_s f(s)`. -/
noncomputable def diagMin [Nonempty State] (f : State → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty f

/-- `max_s f(s)`. -/
noncomputable def diagMax [Nonempty State] (f : State → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

/-- The printed `T^{-1/3}` coefficient (`inference.tex:138`) for a diagonal `Γ`:
`√(η₀/((1−γ)λ₀)) Tr(Γ)‖Γ⁻¹‖ + √(S κ(Γ))/((1−γ)λ₀η₀)`, with `λ₀ = min_s μ(s)`,
`‖Γ⁻¹‖ = 1/min_s Γ_ss`, `κ(Γ) = max_s Γ_ss / min_s Γ_ss`, `S = |State|`. -/
noncomputable def printedRate [Nonempty State] (M : DiscountedMDP State Action)
    (μ : FiniteDistribution State) (Γ : State → ℝ) (η₀ : ℝ) : ℝ :=
  Real.sqrt (η₀ / ((1 - M.discount) * diagMin μ.prob)) * (∑ s, Γ s) * (1 / diagMin Γ) +
    Real.sqrt (Fintype.card State * (diagMax Γ / diagMin Γ)) /
      ((1 - M.discount) * diagMin μ.prob * η₀)

/-! ## The plug-in covariance estimator `Λ̂_T` (`eq:defn-hat-Lambda`): definitions

Moved here from `TDInference/PluginCovariance/Basic.lean` (same names) so that the statement index can state
`eq:defn-hat-Lambda` from definition modules only; lemmas stay in `TDInference/PluginCovariance/Basic.lean`. -/

section Plugin

open scoped Matrix

/-- The probability of an event `E` of the sample path under the i.i.d. law (`inference.tex:54–61`). -/
noncomputable def pathProb (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (T : ℕ) (E : Set (Fin T → Tuple State Action)) : ℝ :=
  ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω * E.indicator (fun _ ↦ (1 : ℝ)) ω

variable [DecidableEq State]

/-- `A_t = e_{s_t}(e_{s_t} − γ e_{s'_t})ᵀ` (`inference.tex:166`), as a matrix (the operator form
`v ↦ A_t v` is `sampleA` in `TDInference/Operator.lean`). -/
noncomputable def sampleAMat (M : DiscountedMDP State Action) (x : Tuple State Action) :
    Matrix State State ℝ :=
  Matrix.vecMulVec (Pi.single x.1 1 : State → ℝ)
    ((Pi.single x.1 1 : State → ℝ) - M.discount • (Pi.single x.2.2 1 : State → ℝ))

/-- `b_t = r_t e_{s_t}` with `r_t = r(s_t,a_t)` (`inference.tex:168`). -/
noncomputable def sampleB (M : DiscountedMDP State Action) (x : Tuple State Action) : State → ℝ :=
  M.reward x.1 x.2.1 • (Pi.single x.1 (1 : ℝ) : State → ℝ)

/-- `Ā_T = T⁻¹ ∑_{t=1}^T A_t` (`inference.tex:166`). At `T = 0` it is `0`. -/
noncomputable def aBar (M : DiscountedMDP State Action) {T : ℕ} (ω : Fin T → Tuple State Action) :
    Matrix State State ℝ :=
  (T : ℝ)⁻¹ • ∑ t, sampleAMat M (ω t)

/-- The printed weight `w_{t,T} = t / ∑_{t=1}^T t` (`inference.tex:175–177`), indexed 0-based:
`pluginWeight T t` is the weight of the sample `ω t`, i.e. `w_{t+1,T}`. -/
noncomputable def pluginWeight (T : ℕ) (t : Fin T) : ℝ :=
  ((t : ℝ) + 1) / ∑ u : Fin T, ((u : ℝ) + 1)

/-- The residual `A_t V − b_t`. -/
noncomputable def pluginResidual (M : DiscountedMDP State Action) (V : State → ℝ)
    (x : Tuple State Action) : State → ℝ :=
  (sampleAMat M x).mulVec V - sampleB M x

/-- The `Γ̂` formula with residuals at an arbitrary `V`: `∑_t w_{t,T} (A_t V − b_t)(A_t V − b_t)ᵀ`. -/
noncomputable def gammaHatAt (M : DiscountedMDP State Action) (V : State → ℝ) {T : ℕ}
    (ω : Fin T → Tuple State Action) : Matrix State State ℝ :=
  ∑ t, pluginWeight T t • Matrix.vecMulVec (pluginResidual M V (ω t)) (pluginResidual M V (ω t))

/-- `Γ̂_T = ∑_t w_{t,T} (A_t V̄_T − b_t)(A_t V̄_T − b_t)ᵀ` (`inference.tex:168`). -/
noncomputable def gammaHat (M : DiscountedMDP State Action) (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ}
    (ω : Fin T → Tuple State Action) : Matrix State State ℝ :=
  ∑ t, pluginWeight T t •
    Matrix.vecMulVec (pluginResidual M (prAverage M η₀ V₀ ω) (ω t))
      (pluginResidual M (prAverage M η₀ V₀ ω) (ω t))

/-- `Λ̂_T = Ā_T⁻¹ Γ̂_T (Ā_T⁻¹)ᵀ` (`eq:defn-hat-Lambda`, `inference.tex:180–182`). Lean's
`Matrix.inv` is `0` on a singular `Ā_T` (C47(4)); then `lambdaHat = 0`. -/
noncomputable def lambdaHat (M : DiscountedMDP State Action) (η₀ : ℝ) (V₀ : State → ℝ) {T : ℕ}
    (ω : Fin T → Tuple State Action) : Matrix State State ℝ :=
  (aBar M ω)⁻¹ * gammaHat M η₀ V₀ ω * ((aBar M ω)⁻¹)ᵀ

/-- The printed `Λ⋆ = A⁻¹ΓA⁻ᵀ` (`inference.tex:99–117`) with `r(s) = r_π(s)`. -/
noncomputable def printedLambda (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) : Matrix State State ℝ :=
  (tdA M π μ)⁻¹ * Matrix.diagonal (printedGamma M π μ) * ((tdA M π μ)⁻¹)ᵀ

/-- The corrected `Λ = A⁻¹ Γ_true A⁻ᵀ` (SOURCE-ISSUES C43). -/
noncomputable def trueLambda (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) : Matrix State State ℝ :=
  (tdA M π μ)⁻¹ * Matrix.diagonal (trueGamma M π μ) * ((tdA M π μ)⁻¹)ᵀ

end Plugin

/-! ## Basic facts: the data law and the Gaussian are genuine probability laws -/

theorem tupleProb_nonneg (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (x : Tuple State Action) : 0 ≤ tupleProb M π μ x :=
  mul_nonneg (mul_nonneg (μ.prob_nonneg _) ((π _).prob_nonneg _)) ((M.transition _ _).prob_nonneg _)

theorem sum_tupleProb (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) : ∑ x : Tuple State Action, tupleProb M π μ x = 1 := by
  simp only [tupleProb, Fintype.sum_prod_type]
  have h : ∀ s : State, ∑ a : Action, ∑ s' : State,
      μ.prob s * (π s).prob a * (M.transition s a).prob s' = μ.prob s := by
    intro s
    simp_rw [← Finset.mul_sum, (M.transition _ _).sum_prob, mul_one, ← Finset.mul_sum,
      (π s).sum_prob, mul_one]
  simp_rw [h, μ.sum_prob]

theorem pathWeight_nonneg (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) {T : ℕ} (ω : Fin T → Tuple State Action) :
    0 ≤ pathWeight M π μ ω :=
  Finset.prod_nonneg fun _ _ ↦ tupleProb_nonneg M π μ _

theorem sum_pathWeight (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (T : ℕ) :
    ∑ ω : Fin T → Tuple State Action, pathWeight M π μ ω = 1 := by
  have h := Finset.prod_univ_sum (fun _ : Fin T ↦ (Finset.univ : Finset (Tuple State Action)))
    (fun _ x ↦ tupleProb M π μ x)
  rw [Fintype.piFinset_univ] at h
  simp only [pathWeight, ← h, sum_tupleProb, Finset.prod_const_one]

/-- The i.i.d. data law has total mass one (check-file fix F2). -/
theorem lawProb_univ [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (T : ℕ) : lawProb M π μ η₀ V₀ T Set.univ = 1 := by
  simp only [lawProb, Set.indicator_univ, mul_one]
  exact sum_pathWeight M π μ T

theorem lawProb_nonneg [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (T : ℕ) (C : Set (State → ℝ)) : 0 ≤ lawProb M π μ η₀ V₀ T C :=
  Finset.sum_nonneg fun ω _ ↦ mul_nonneg (pathWeight_nonneg M π μ ω)
    (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)

theorem lawProb_le_one [DecidableEq State] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ)
    (V₀ : State → ℝ) (T : ℕ) (C : Set (State → ℝ)) : lawProb M π μ η₀ V₀ T C ≤ 1 := by
  rw [← lawProb_univ M π μ η₀ V₀ T]
  refine Finset.sum_le_sum fun ω _ ↦ mul_le_mul_of_nonneg_left ?_ (pathWeight_nonneg M π μ ω)
  simp only [Set.indicator_univ]
  exact Set.indicator_le_self' (fun _ _ ↦ zero_le_one) _

theorem continuous_gaussMap [DecidableEq State] (A : Matrix State State ℝ) (Γ : State → ℝ) :
    Continuous (gaussMap A Γ) := by
  unfold gaussMap
  exact Continuous.matrix_mulVec (A := fun _ ↦ A⁻¹) continuous_const
    (continuous_pi fun s ↦ continuous_const.mul (continuous_apply s))

/-- The defining map of `gaussCov` is measurable (check-file fix F2). -/
theorem measurable_gaussMap [DecidableEq State] (A : Matrix State State ℝ) (Γ : State → ℝ) :
    Measurable (gaussMap A Γ) :=
  (continuous_gaussMap A Γ).measurable

/-- `gaussCov A Γ` is a probability measure, not the junk zero measure (check-file fix F2). -/
instance gaussCov_isProbabilityMeasure [DecidableEq State] (A : Matrix State State ℝ)
    (Γ : State → ℝ) : IsProbabilityMeasure (gaussCov A Γ) :=
  Measure.isProbabilityMeasure_map (measurable_gaussMap A Γ).aemeasurable

end StatisticalRL.Ch7Rest.TDInference
