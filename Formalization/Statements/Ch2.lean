import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic
import Formalization.Probability.FiniteSampleDefinitions
import Formalization.Probability.RandomFamilyBorel
import Formalization.Probability.EmpiricalHoeffdingRandomFamily
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Formalization.Probability.Fano.TestRiskDefinitions
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Formalization.Probability.BernoulliTailDefinitions
import Formalization.MDP.OptimalityOperatorDefinitions
import Formalization.MDP.PointMassDefinitions
import Formalization.MDP.FixedPointDefinitions
import Formalization.MDP.PolicyMatrixDefinitions
import Formalization.MDP.CoreDefinitions
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Source-facing statement index for Chapter 2. -/

open MeasureTheory
open scoped BigOperators Matrix

namespace StatisticalRL.Statements
universe u v

/-- `lem:variance-perturbation-var-P-V`, `chapters/prelim.tex:458–467`. -/
def Lemma2_2 : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (V Vhat : State → ℝ),
    (∀ s, 0 ≤ V s ∧ V s ≤ 1 / (1 - M.discount)) →
    (∀ s, 0 ≤ Vhat s ∧ Vhat s ≤ 1 / (1 - M.discount)) →
    ‖(fun s a ↦ (M.transition s a).expectation (fun x ↦ Vhat x ^ 2) -
        ((M.transition s a).expectation Vhat) ^ 2) -
      (fun s a ↦ (M.transition s a).expectation (fun x ↦ V x ^ 2) -
        ((M.transition s a).expectation V) ^ 2)‖ ≤
      (4 / (1 - M.discount)) * ‖Vhat - V‖

/-- `lem:Freedman-prelim`, `chapters/prelim.tex:1056–1075`. The increments
are indexed from zero, corresponding to the source's indexing from one. -/
def Lemma2_9 : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ),
    (∀ n, Measurable (X n)) →
    ∀ (B σ : ℝ),
    (∀ n ω, |X n ω| ≤ B) →
    (∀ n, μ[X n | ⨆ k, ⨆ (_ : k < n), MeasurableSpace.comap (X k) (borel ℝ)]
      =ᵐ[μ] fun _ ↦ 0) →
    ∀ (n K : ℕ), 0 < K →
    (∀ ω, (∑ k ∈ Finset.range n,
      μ[fun ω' ↦ X k ω' ^ 2 |
        ⨆ j, ⨆ (_ : j < k), MeasurableSpace.comap (X j) (borel ℝ)] ω) ≤ σ ^ 2) →
    ∀ (δ : ℝ), 0 < δ → δ < 1 →
    1 - δ ≤ μ.real {ω | |∑ k ∈ Finset.range n, X k ω| ≤
      Real.sqrt (8 * max (∑ k ∈ Finset.range n,
        μ[fun ω' ↦ X k ω' ^ 2 |
          ⨆ j, ⨆ (_ : j < k), MeasurableSpace.comap (X j) (borel ℝ)] ω)
        (σ ^ 2 / (2 : ℝ) ^ K) * Real.log (2 * K / δ)) +
        (4 / 3) * B * Real.log (2 * K / δ)}

/-- Azuma–Hoeffding Lemma 2.8, `lem:azuma-hoeffding`,
`chapters/prelim.tex:1038–1052`. The increments and deterministic bounds
are indexed from zero, corresponding to the printed indexing from one.
Each conditional mean is taken given exactly the preceding increments,
and is an almost-everywhere identity. No finite-space or standard-Borel
assumption, positive-time assumption or positive variance proxy is imposed.
-/
def Lemma2_8 : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (B : ℕ → ℝ),
    (∀ k, Measurable (X k)) →
    (∀ k ω, |X k ω| ≤ B k) →
    (∀ k, μ[X k | ⨆ j, ⨆ (_ : j < k), MeasurableSpace.comap (X j) (borel ℝ)]
      =ᵐ[μ] fun _ ↦ 0) →
    ∀ (n : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
    1 - δ < μ.real {ω | |∑ k ∈ Finset.range n, X k ω| ≤
      Real.sqrt (2 * (∑ k ∈ Finset.range n, (B k)^2) * Real.log (2/δ))}

/-- Lemma 2.3, `lem:basic-property-matrix-notation-inf`,
`chapters/prelim.tex:544–574`, for both policy transition matrices.
The matrix norm follows the book's explicit definition at
`chapters/intro.tex:204–209`: the maximum row-wise absolute sum. The Pi norm
below takes that maximum of the nonnegative row sums. Policies include all
stationary randomized policies, as defined at prelim.tex:66; discount zero is included.
-/
noncomputable def Lemma2_3 : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action),
    letI := Classical.decEq State
    letI := Classical.decEq Action
    let P : Matrix State State ℝ := fun s t =>
      ∑ a, (π s).prob a * (M.transition s a).prob t
    let Q : Matrix (State × Action) (State × Action) ℝ := fun sa tb =>
      (M.transition sa.1 sa.2).prob tb.1 * (π tb.1).prob tb.2
    let γ := M.discount
    ((1 - γ • P)⁻¹ = 1 + ∑' n : ℕ, (γ • P)^(n + 1) ∧
      (1 - γ • P)⁻¹ *ᵥ (fun _ => 1) = (fun _ => 1 / (1 - γ)) ∧
      ‖fun s => ∑ t, |((1 - γ • P)⁻¹) s t|‖ = 1 / (1 - γ) ∧
      ∀ s t, 0 ≤ ((1 - γ • P)⁻¹) s t) ∧
    ((1 - γ • Q)⁻¹ = 1 + ∑' n : ℕ, (γ • Q)^(n + 1) ∧
      (1 - γ • Q)⁻¹ *ᵥ (fun _ => 1) = (fun _ => 1 / (1 - γ)) ∧
      ‖fun sa => ∑ tb, |((1 - γ • Q)⁻¹) sa tb|‖ = 1 / (1 - γ) ∧
      ∀ sa tb, 0 ≤ ((1 - γ • Q)⁻¹) sa tb)

/-- Linear convergence of value iteration and policy iteration,
`chapters/prelim.tex:319–343`, equations `eq:value_iteration` and
`eq:policy_iteration`. Fixed points denote actual trajectory values by the separately proved
trajectory identification and optimality theorems;
policy iteration permits arbitrary maximizing tie choices at each update. -/
def Lemma2_1 : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action),
    (∀ (Q₀ : State → Action → ℝ) (k : ℕ), 1 ≤ k →
      ‖M.qOptimality^[k] Q₀ - M.optimalityFixedPoint‖ ≤
        M.discount ^ k * ‖Q₀ - M.optimalityFixedPoint‖) ∧
    (∀ (π : ℕ → StationaryPolicy State Action) (f : ℕ → State → Action),
      (∀ n, π (n + 1) = fun s ↦ EnvironmentStage.pointMass (f n s)) →
      (letI : Nonempty Action := M.action_nonempty
       ∀ n s, M.policyFixedPoint (π n) s (f n s) =
         actionMaximum (M.policyFixedPoint (π n) s)) →
      ∀ (k : ℕ), 1 ≤ k →
        ‖M.policyFixedPoint (π k) - M.optimalityFixedPoint‖ ≤
          M.discount ^ k *
            ‖M.policyFixedPoint (π 0) - M.optimalityFixedPoint‖)

/-- Lemma 2.7, `lem:tail-bound-sum-Bernoulli`, `chapters/prelim.tex:1001–1015`.
`Z_1,…,Z_n` are independent real random variables on an arbitrary probability space,
each with the Bernoulli(`p`) law on `{0,1}` (`0 < p ≤ 1`). Lower tail: for every `a > 0`,
`P(∑ (Z_i - E Z_i) < -a n) ≤ exp(-a² n / (2p))`; upper tail: for every `τ ≥ 2pn`,
`P(∑ Z_i > τ) ≤ 2 exp(-0.19 τ)`. -/
def Lemma2_7 : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1),
    ∀ (n : ℕ) (Z : Fin n → Ω → ℝ),
      (∀ i, Measurable (Z i)) → ProbabilityTheory.iIndepFun Z μ →
      (∀ i, ProbabilityTheory.HasLaw (Z i)
        (StatisticalRL.Probability.bernoulliRealLaw p hp.le hp1) μ) →
      (∀ a : ℝ, 0 < a →
        μ.real {ω | (∑ i : Fin n,
          (Z i ω - ∫ ω', Z i ω' ∂μ)) <
            -(a * (n : ℝ))} ≤ Real.exp (-(a ^ 2 * (n : ℝ) / (2 * p))) ) ∧
      (∀ τ : ℝ, 2 * p * (n : ℝ) ≤ τ →
        μ.real {ω | (∑ i : Fin n, Z i ω) > τ} ≤
          2 * Real.exp (-(0.19 : ℝ) * τ))

/-- Lemma 2.13, `lem:KL-quadratic-lower-bound`, `chapters/prelim.tex:1335–1346`, with the
Bernoulli KL divergence of `eq:defn-KL-bern` written out:
`KL(p ‖ q) = p log(p/q) + (1-p) log((1-p)/(1-q))`. For all `0 < p, q < 1`,
`KL(p ‖ q) ≤ (p-q)²/(q(1-q))`; and if `1/2 ≤ q < p < 1`, then
`KL(p ‖ q) ≤ KL(q ‖ p) ≤ (p-q)²/(p(1-p))`. -/
def Lemma2_13 : Prop :=
  (∀ p q : ℝ, 0 < p → p < 1 → 0 < q → q < 1 →
    p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) ≤
      (p - q) ^ 2 / (q * (1 - q))) ∧
  (∀ p q : ℝ, (1 : ℝ) / 2 ≤ q → q < p → p < 1 →
    (p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) ≤
      q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p))) ∧
    (q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p)) ≤
      (p - q) ^ 2 / (p * (1 - p))))

/-- Lemma 2.11, `lem:reverse-Fano-bound`, `chapters/prelim.tex:1209–1229`
(error definitions 1113–1128). For any probability laws `P 0, …, P M` on an
arbitrary measurable space, the minimax error infimum dominates the average
error infimum over the same measurable tests, and
`p̄_e ≥ 1 − 1/(M+1) − √(M/(2(M+1)²) · ∑_{j=1}^M KL(P₀‖P_j))`, written in
`ℝ≥0∞` by moving the square-root term to the right; an infinite KL sum makes the
bound trivially true rather than being truncated by `toReal`. All `M`, including
`M = 0`, are covered. -/
def Lemma2_11 : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω]
    (M : ℕ) (P : Fin (M+1) → Measure Ω) [∀ j, IsProbabilityMeasure (P j)],
    StatisticalRL.PrelimFano.averageErrorInfimum P ≤
        StatisticalRL.PrelimFano.minimaxErrorInfimum P ∧
      ENNReal.ofReal (1 - 1 / ((M : ℝ)+1)) ≤
        ENNReal.ofReal (StatisticalRL.PrelimFano.averageErrorInfimum P) +
          (ENNReal.ofReal ((M : ℝ) / (2 * ((M : ℝ)+1)^2)) *
            ∑ j : Fin M, InformationTheory.klDiv (P 0) (P j.succ)) ^ (1/2 : ℝ)

open StatisticalRL.FiniteDistribution ProbabilityTheory in
/-- Empirical Bernstein inequality, `empirical bernstein`,
`chapters/prelim.tex:916–927,985–997`. The unordered finite random family is
measurable in the finite-enumeration quotient-Borel structure and independent
of the empirical row. The family may be empty and its vectors may have zero
norm or empirical variance. -/
noncomputable def Lemma2_6 : Prop :=
  ∀ (State : Type u) [Fintype State] (Ω : Type v) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : FiniteDistribution State)
    (N : ℕ) (hN2 : 2 ≤ N) (δ : ℝ), 0 < δ → δ < 1 →
    letI : MeasurableSpace State := ⊤
    let hN : 0 < N := Nat.lt_of_lt_of_le (by decide : 0 < 2) hN2
    ∀ (draw : Ω → Fin N → State), Measurable draw → μ.map draw = d.sampleMeasure N →
    ∀ (family : Ω → Finset (State → ℝ)),
      (letI : MeasurableSpace (Finset (State → ℝ)) := finiteFamilyBorel
       Measurable family) →
      (letI : MeasurableSpace (Finset (State → ℝ)) := finiteFamilyBorel
       letI : MeasurableSpace (FiniteDistribution State) := rowVectorSpace
       IndepFun family (fun ω ↦ empiricalRow N hN (draw ω)) μ) →
      (∀ ω V, V ∈ family ω → ∀ s, 0 ≤ V s) →
      1 - δ < μ.real {ω | ∀ V ∈ family ω,
        |(empiricalRow N hN (draw ω)).expectation V - d.expectation V| ≤
          Real.sqrt (2 * Real.log (4 * (family ω).card / δ) / ((N : ℝ) - 1)) *
            Real.sqrt ((empiricalRow N hN (draw ω)).expectation (fun s ↦ V s ^ 2) -
              ((empiricalRow N hN (draw ω)).expectation V)^2) +
          7 * ‖V‖ * Real.log (4 * (family ω).card / δ) / (3 * ((N : ℝ) - 1))}

end StatisticalRL.Statements
