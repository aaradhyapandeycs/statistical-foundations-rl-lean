import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Basic
import Formalization.Probability.FiniteSampleDefinitions
import Formalization.Probability.RandomFamilyBorel
import Formalization.Probability.EmpiricalHoeffdingRandomFamily
import Formalization.Probability.BernsteinMatrixMarginals
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
import Formalization.MDP.InfiniteReturn
import Formalization.MDP.ForcedActionReturn
import Formalization.MDP.TrajectoryDefinitions
import Formalization.MDP.ActionTrajectoryDefinitions
import Formalization.MDP.PolicyEnvironmentDefinitions
import Formalization.MDP.FiniteOccupancy

/-! Source-facing statement index for Chapter 2. -/

open MeasureTheory
open scoped BigOperators Matrix

namespace StatisticalRL.Statements.Ch2
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
are indexed from zero, corresponding to the source's indexing from one.
The printed "`W_n ≤ σ²` holds deterministically" is assumed almost surely:
conditional expectations are defined only up to null sets, and the a.s.
hypothesis implies every pointwise reading for a fixed representative. -/
def Lemma2_9 : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ),
    (∀ n, Measurable (X n)) →
    ∀ (B σ : ℝ),
    (∀ n ω, |X n ω| ≤ B) →
    (∀ n, μ[X n | ⨆ k, ⨆ (_ : k < n), MeasurableSpace.comap (X k) (borel ℝ)]
      =ᵐ[μ] fun _ ↦ 0) →
    ∀ (n K : ℕ), 0 < K →
    (∀ᵐ ω ∂μ, (∑ k ∈ Finset.range n,
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

/-- `eq:Qpi-Vpi-matrix-notation-inf`, equations (2.24a–d), `chapters/prelim.tex:496–531`,
with the intermediate display `Q^π = r + γ P^π Q^π` of `chapters/prelim.tex:524–526`.
`Q^π` is the policy Bellman solution `M.policyFixedPoint π`, viewed as a
vector indexed by `State × Action`; the final two conjuncts record that `Q` is the expected
infinite-trajectory Q-value `trajectoryExpectedQ π` and `V` the trajectory value
`trajectoryExpectedValue π` (`eq:defn-Qpi-inf-horizon`, `eq:defn-Vpi-inf`), so the displayed
identities hold for the actual `Q^π`, `V^π`; `V^π = Π^π Q^π`, i.e. `V^π(s) = E_{a∼π(s)} Q^π(s,a)`
(`eq:Vpi-a-function-of-Qpi-inf`); `r` is the reward vector on `State × Action`,
`r_π(s) = E_{a∼π(s)} r(s,a)`; `P` is the `(S·A) × S` transition matrix; `P_π` and `P^π` are
the policy matrices exactly as in `Lemma2_3`; all stationary randomized policies are included.
The conjuncts, in order: (2.24a) `Q^π = r + γPV^π`; (2.24b) `V^π = r_π + γP_πV^π`;
(2.24c) `V^π = (I − γP_π)⁻¹ r_π`; the intermediate `Q^π = r + γP^πQ^π`; (2.24d)
`Q^π = (I − γP^π)⁻¹ r`; and the identifications `Q = trajectoryExpectedQ π`,
`V = trajectoryExpectedValue π`. The inverses are Mathlib's `Matrix` inverses; `I − γP_π` and
`I − γP^π` are invertible (`Lemma2_3`), so they are not junk values. -/
noncomputable def Eq_Qpi_Vpi_matrix_notation_inf : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action),
    letI := Classical.decEq State
    letI := Classical.decEq Action
    let Q : State × Action → ℝ := fun sa ↦ M.policyFixedPoint π sa.1 sa.2
    let V : State → ℝ := fun s ↦ ∑ a, (π s).prob a * M.policyFixedPoint π s a
    let r : State × Action → ℝ := fun sa ↦ M.reward sa.1 sa.2
    let rπ : State → ℝ := fun s ↦ ∑ a, (π s).prob a * M.reward s a
    let P : Matrix (State × Action) State ℝ := fun sa t ↦ (M.transition sa.1 sa.2).prob t
    let Pπ : Matrix State State ℝ := fun s t ↦ ∑ a, (π s).prob a * (M.transition s a).prob t
    let Ppi : Matrix (State × Action) (State × Action) ℝ := fun sa tb ↦
      (M.transition sa.1 sa.2).prob tb.1 * (π tb.1).prob tb.2
    let γ := M.discount
    Q = r + γ • (P *ᵥ V) ∧
    V = rπ + γ • (Pπ *ᵥ V) ∧
    V = (1 - γ • Pπ)⁻¹ *ᵥ rπ ∧
    Q = r + γ • (Ppi *ᵥ Q) ∧
    Q = (1 - γ • Ppi)⁻¹ *ᵥ r ∧
    Q = (fun sa ↦ M.trajectoryExpectedQ π sa.1 sa.2) ∧
    V = M.trajectoryExpectedValue π

/-- Linear convergence of value iteration and policy iteration,
`chapters/prelim.tex:317–343`, equations `eq:value_iteration` (`chapters/prelim.tex:317–319`) and
`eq:policy_iteration` (`chapters/prelim.tex:328–330`). The iterates are compared with the Bellman fixed points
`policyFixedPoint` and `optimalityFixedPoint`; the first two conjuncts identify them with the
actual trajectory objects: `Q^π = trajectoryExpectedQ π` for every stationary randomized policy
and `Q⋆ = max_π Q^π` (the supremum over all stationary randomized policies of the trajectory
Q-values). Policy iteration permits arbitrary maximizing tie choices at each update. -/
def Lemma2_1 : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action),
    (∀ π : StationaryPolicy State Action, M.trajectoryExpectedQ π = M.policyFixedPoint π) ∧
    (fun s a ↦ ⨆ π : StationaryPolicy State Action, M.trajectoryExpectedQ π s a) =
      M.optimalityFixedPoint ∧
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

/-- Iteration count stated after Lemma 2.1, `chapters/prelim.tex:357–360` (lemma
`chapters/prelim.tex:339–343`, algorithms `eq:value_iteration` and `eq:policy_iteration`,
`chapters/prelim.tex:315–333`): to reach `‖Q_k − Q⋆‖∞ ≤ ε` it takes no more than
`(1/(1−γ)) log(‖Q₀ − Q⋆‖∞/ε)` iterations, for value iteration and for policy iteration
(`Q_k = Q^{π_k}`, `Q₀ = Q^{π₀}`). Read as: for every `ε > 0` and every iteration count
`k ≥ log(‖Q₀ − Q⋆‖∞/ε)/(1−γ)`, `‖Q_k − Q⋆‖∞ ≤ ε`. Objects and binders are those of `Lemma2_1`
(policy iteration with arbitrary maximizing tie choices), including the leading identifications of
the fixed points with the trajectory objects. When `Q₀ = Q⋆` the printed `log 0`
is undefined; Lean's `log 0 = 0` turns the condition into `k ≥ 0`, and the conclusion holds
there since then every iterate equals `Q⋆`. -/
def Lemma2_1_iterationCount : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (ε : ℝ), 0 < ε →
    (∀ π : StationaryPolicy State Action, M.trajectoryExpectedQ π = M.policyFixedPoint π) ∧
    (fun s a ↦ ⨆ π : StationaryPolicy State Action, M.trajectoryExpectedQ π s a) =
      M.optimalityFixedPoint ∧
    (∀ (Q₀ : State → Action → ℝ) (k : ℕ),
      Real.log (‖Q₀ - M.optimalityFixedPoint‖ / ε) / (1 - M.discount) ≤ k →
      ‖M.qOptimality^[k] Q₀ - M.optimalityFixedPoint‖ ≤ ε) ∧
    (∀ (π : ℕ → StationaryPolicy State Action) (f : ℕ → State → Action),
      (∀ n, π (n + 1) = fun s ↦ EnvironmentStage.pointMass (f n s)) →
      (letI : Nonempty Action := M.action_nonempty
       ∀ n s, M.policyFixedPoint (π n) s (f n s) =
         actionMaximum (M.policyFixedPoint (π n) s)) →
      ∀ k : ℕ,
        Real.log (‖M.policyFixedPoint (π 0) - M.optimalityFixedPoint‖ / ε) /
          (1 - M.discount) ≤ k →
        ‖M.policyFixedPoint (π k) - M.optimalityFixedPoint‖ ≤ ε)

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
Bernoulli KL divergence of `eq:defn-KL-bern` (`chapters/prelim.tex:1326–1329`) written out:
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

open StatisticalRL.FiniteDistribution ProbabilityTheory in
/-- Lemma 2.4 (Hoeffding inequality), `lem:Hoeffding-prelim`, `chapters/prelim.tex:939–950`.
`N > 0` i.i.d. draws from the row `d = P_{s,a}` (their joint law is `d.sampleMeasure N`) form the
empirical row `P̂_{s,a}`; the finite family `𝒱` of nonnegative vectors is random, measurable in the
finite-enumeration quotient-Borel structure and independent of `P̂_{s,a}` (it may be empty).
With probability greater than `1-δ`, every `V ∈ 𝒱` satisfies the printed bound. -/
def Lemma2_4 : Prop :=
  ∀ (State : Type u) [Fintype State] (Ω : Type v) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : FiniteDistribution State)
    (N : ℕ) (hN : 0 < N) (δ : ℝ), 0 < δ → δ < 1 →
    letI : MeasurableSpace State := ⊤
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
          Real.sqrt (‖V‖ ^ 2 * Real.log (2 * (family ω).card / δ) / (2 * N))}

open StatisticalRL.FiniteDistribution ProbabilityTheory in
/-- Lemma 2.5 (Bernstein inequality), `lem:Bernstein-prelim`, `chapters/prelim.tex:956–978`, both
displays, in the setting of Lemma 2.4. First display: one row `d = P_{s,a}`. Second display: the
whole empirical matrix, rows indexed by `(s,a) ∈ 𝒮 × 𝒜`, each row of `N` draws with the correct
i.i.d. law `P_{s,a}` (any dependence across rows is allowed, which includes the independent
generative model), the family independent of the whole empirical matrix; the bound then holds
simultaneously for all rows with `4SA|𝒱|/δ` inside the logarithm. `Var_{P_{s,a}}(V)` is the
row variance (`prelim.tex:428–437`); the sampling setting is `prelim.tex:916–934`. The second
display assumes nonempty state and action types; the excluded cases are vacuous. -/
def Lemma2_5 : Prop :=
  (∀ (State : Type u) [Fintype State] (Ω : Type v) [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (d : FiniteDistribution State)
    (N : ℕ) (hN : 0 < N) (δ : ℝ), 0 < δ → δ < 1 →
    letI : MeasurableSpace State := ⊤
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
          Real.sqrt (2 * Real.log (4 * (family ω).card / δ) / N) * Real.sqrt (d.variance V) +
          2 * ‖V‖ * Real.log (4 * (family ω).card / δ) / (3 * N)}) ∧
  (∀ (State : Type u) (Action : Type u) [Fintype State] [Fintype Action] [Nonempty State]
    [Nonempty Action] (Ω : Type v) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : State × Action → FiniteDistribution State) (N : ℕ) (hN : 0 < N) (δ : ℝ),
    0 < δ → δ < 1 →
    letI : MeasurableSpace State := ⊤
    ∀ (draw : Ω → State × Action → Fin N → State), Measurable draw →
    (∀ i, μ.map (fun ω ↦ draw ω i) = (d i).sampleMeasure N) →
    ∀ (family : Ω → Finset (State → ℝ)),
      (letI : MeasurableSpace (Finset (State → ℝ)) := finiteFamilyBorel
       Measurable family) →
      (letI : MeasurableSpace (Finset (State → ℝ)) := finiteFamilyBorel
       letI : MeasurableSpace (State × Action → FiniteDistribution State) :=
         marginalMatrixVectorSpace
       IndepFun family (fun ω ↦ fun i ↦ empiricalRow N hN (draw ω i)) μ) →
      (∀ ω V, V ∈ family ω → ∀ s, 0 ≤ V s) →
      1 - δ < μ.real {ω | ∀ i : State × Action, ∀ V ∈ family ω,
        |(empiricalRow N hN (draw ω i)).expectation V - (d i).expectation V| ≤
          Real.sqrt (2 * Real.log (4 * Fintype.card State * Fintype.card Action *
            (family ω).card / δ) / N) * Real.sqrt ((d i).variance V) +
          2 * ‖V‖ * Real.log (4 * Fintype.card State * Fintype.card Action *
            (family ω).card / δ) / (3 * N)})

/-- Lemma 2.12, `lem:KL-tensorize`, `chapters/prelim.tex:1313–1319`. For finitely many probability
measures `P_i, Q_i` on arbitrary measurable spaces, the KL divergence of the product measures is
the sum of the coordinate divergences, in `ℝ≥0∞` (both sides are `∞` exactly when some
coordinate divergence is). The book defines KL (`eq:defn-KL`, `chapters/intro.tex:229–232`) only
when `P ≪ Q`; Mathlib's `klDiv` agrees there, including the value `∞`, and is `∞` otherwise, a
convention the book does not print. -/
def Lemma2_12 : Prop :=
  ∀ (ι : Type u) [Fintype ι] (α : ι → Type v)
    [∀ i, MeasurableSpace (α i)]
    (P Q : ∀ i, Measure (α i))
    [∀ i, IsProbabilityMeasure (P i)] [∀ i, IsProbabilityMeasure (Q i)],
    InformationTheory.klDiv (Measure.pi P) (Measure.pi Q) =
      ∑ i, InformationTheory.klDiv (P i) (Q i)

/-- Lemma 2.10 (Fano's lemma), `lem:fano`, `chapters/prelim.tex:1141–1168` (`\begin{lemma}` at
1140; part (iii), 1170–1199, is commented out in the source and is not part of the printed
lemma). Setting, `chapters/prelim.tex:1106–1132`: probability laws `P_0, …, P_M` on a common
measurable space; a test is a map `ψ` into `{0, …, M}` (carrying the discrete σ-algebra), taken
measurable so that `P_i(ψ ≠ i)` is defined; `p_e = inf_ψ max_i P_i(ψ ≠ i)`
(`eq:defn-minimax-prob-error-prelim`, line 1117) is `minimaxErrorInfimum P` and
`p̄_e = inf_ψ (1/(M+1)) ∑_{i=0}^M P_i(ψ ≠ i)` (`eq:defn-avg-prob-error-prelim`, line 1124) is
`averageErrorInfimum P`, both infima over all measurable tests. KL is Mathlib's `klDiv` (natural
logarithm; `⊤` unless the first law is absolutely continuous with respect to the second with
integrable log-likelihood ratio), which agrees with `eq:defn-KL` (`chapters/intro.tex:229–235`)
wherever the book defines it.
(i) (`eq:fano-binary`, lines 1145–1152) `M = 1`, two laws `P 0, P 1` indexed by `Fin 2`: if
`KL(P₁‖P₀) ≤ β < ∞`, written as "`klDiv (P 1) (P 0)` is finite and its real value is at most the
real number `β`", then `p_e ≥ p̄_e ≥ max{exp(−β)/4, (1 − √(β/2))/2}`.
(ii) (`eq:fano-multi`, lines 1154–1168) `M ≥ 2`, laws indexed by `Fin (M+1)`: if
`(1/(M+1)) ∑_{j=1}^M KL(P_j‖P₀) ≤ β log M` (the KL sum in `ℝ≥0∞`, `j.succ` running over
`1, …, M`) for some `0 < β < 1`, then `p_e ≥ p̄_e ≥ (log(M+1) − log 2)/log M − β`. -/
def Lemma2_10 : Prop :=
  (∀ {Ω : Type u} [MeasurableSpace Ω]
      (P : Fin 2 → Measure Ω) [∀ j, IsProbabilityMeasure (P j)] (β : ℝ),
      InformationTheory.klDiv (P 1) (P 0) ≠ ⊤ →
      (InformationTheory.klDiv (P 1) (P 0)).toReal ≤ β →
      StatisticalRL.PrelimFano.averageErrorInfimum P ≤
          StatisticalRL.PrelimFano.minimaxErrorInfimum P ∧
        max (1 / 4 * Real.exp (-β)) ((1 - Real.sqrt (β / 2)) / 2) ≤
          StatisticalRL.PrelimFano.averageErrorInfimum P) ∧
  (∀ {Ω : Type u} [MeasurableSpace Ω]
      (M : ℕ) (P : Fin (M+1) → Measure Ω) [∀ j, IsProbabilityMeasure (P j)] (β : ℝ),
      2 ≤ M → 0 < β → β < 1 →
      ENNReal.ofReal (1 / ((M : ℝ) + 1)) *
          ∑ j : Fin M, InformationTheory.klDiv (P j.succ) (P 0) ≤
        ENNReal.ofReal (β * Real.log (M : ℝ)) →
      StatisticalRL.PrelimFano.averageErrorInfimum P ≤
          StatisticalRL.PrelimFano.minimaxErrorInfimum P ∧
        (Real.log ((M : ℝ) + 1) - Real.log 2) / Real.log (M : ℝ) - β ≤
          StatisticalRL.PrelimFano.averageErrorInfimum P)

/-- eq. (2.27), `eq:QV-pi-perturbabtion-r-inf` (label typo as in the source), with
`eq:Q-pi-perturbabtion-r-inf` and `eq:V-pi-perturbabtion-r-inf`,
`chapters/prelim.tex:613–631`. Two discounted MDPs `M = (S,A,P,r,γ)` and
`M' = (S,A,P,r̃,γ)` with the same transition kernel and discount, differing only in the
reward. For every stationary randomized policy `π` (the policy class of `prelim.tex:66`),
`‖Q^π − Q̃^π‖∞ ≤ ‖r − r̃‖∞/(1−γ)` and `‖V^π − Ṽ^π‖∞ ≤ ‖r − r̃‖∞/(1−γ)`.
As in `Lemma2_1`, `Q^π` is written as the policy Bellman solution `M.policyFixedPoint π`, and
`V^π(s) = E_{a∼π(s)} Q^π(s,a)`; the leading conjunct identifies these, for both models, with the
actual trajectory objects `trajectoryExpectedQ π` and `trajectoryExpectedValue π`. The norms are
the finite sup norms (`‖·‖` on `State → Action → ℝ` and `State → ℝ` is the max of `|·|`). The
printed intermediate resolvent identities (`(I−γP^π)⁻¹ r` and `‖(I−γP^π)⁻¹‖₁ = 1/(1−γ)`) are
proof steps and are not restated here; the matrix facts are `Lemma2_3`. -/
def Eq_QV_pi_perturbation_r_inf : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M M' : DiscountedMDP State Action),
    M'.transition = M.transition → M'.discount = M.discount →
    ∀ π : StationaryPolicy State Action,
      (M.trajectoryExpectedQ π = M.policyFixedPoint π ∧
        M'.trajectoryExpectedQ π = M'.policyFixedPoint π ∧
        M.trajectoryExpectedValue π = (fun s ↦ (π s).expectation (M.policyFixedPoint π s)) ∧
        M'.trajectoryExpectedValue π = (fun s ↦ (π s).expectation (M'.policyFixedPoint π s))) ∧
      ‖M.policyFixedPoint π - M'.policyFixedPoint π‖ ≤
          ‖M.reward - M'.reward‖ / (1 - M.discount) ∧
      ‖(fun s ↦ (π s).expectation (M.policyFixedPoint π s)) -
          (fun s ↦ (π s).expectation (M'.policyFixedPoint π s))‖ ≤
          ‖M.reward - M'.reward‖ / (1 - M.discount)

/-- eq. (2.28), `eq:QV-star-perturbabtion-r-inf` (label typo as in the source), with
`eq:V-star-perturbabtion-r-inf`, `chapters/prelim.tex:633–653`. Same setting as
`Eq_QV_pi_perturbation_r_inf`. The printed chain
`‖Q⋆ − Q̃⋆‖∞ = ‖max_π Q^π − max_π Q̃^π‖∞ ≤ max_π ‖Q^π − Q̃^π‖∞ ≤ ‖r − r̃‖∞/(1−γ)` and
`‖V⋆ − Ṽ⋆‖∞ ≤ ‖r − r̃‖∞/(1−γ)` is stated with `max_π` as the supremum `⨆ π` over stationary
randomized policies of the policy Bellman solutions (`Q^π = M.policyFixedPoint π`,
`V^π(s) = E_{a∼π(s)} Q^π(s,a)`); the leading conjunct identifies these, for both models, with the
actual trajectory objects `trajectoryExpectedQ π` and `trajectoryExpectedValue π`, so the suprema
are over the true `Q^π`, `V^π`. The second conjunct records that these suprema are the optimal
Bellman solution `optimalityFixedPoint` (the `Q⋆` of `Lemma2_1`) of each model, so the Q-suprema
are attained (by `optimalGreedyPolicy`); the V-suprema are bounded above by `1/(1−γ)` and the
norm-supremum by `‖r − r̃‖∞/(1−γ)`, so no `⨆` here is a junk value. -/
def Eq_QV_star_perturbation_r_inf : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M M' : DiscountedMDP State Action),
    M'.transition = M.transition → M'.discount = M.discount →
    (∀ π : StationaryPolicy State Action,
      M.trajectoryExpectedQ π = M.policyFixedPoint π ∧
      M'.trajectoryExpectedQ π = M'.policyFixedPoint π ∧
      M.trajectoryExpectedValue π = (fun s ↦ (π s).expectation (M.policyFixedPoint π s)) ∧
      M'.trajectoryExpectedValue π = (fun s ↦ (π s).expectation (M'.policyFixedPoint π s))) ∧
    ((fun s a ↦ ⨆ π : StationaryPolicy State Action, M.policyFixedPoint π s a) =
        M.optimalityFixedPoint ∧
      (fun s a ↦ ⨆ π : StationaryPolicy State Action, M'.policyFixedPoint π s a) =
        M'.optimalityFixedPoint) ∧
    ‖(fun s a ↦ ⨆ π : StationaryPolicy State Action, M.policyFixedPoint π s a) -
        (fun s a ↦ ⨆ π : StationaryPolicy State Action, M'.policyFixedPoint π s a)‖ ≤
      (⨆ π : StationaryPolicy State Action,
        ‖M.policyFixedPoint π - M'.policyFixedPoint π‖) ∧
    (⨆ π : StationaryPolicy State Action,
        ‖M.policyFixedPoint π - M'.policyFixedPoint π‖) ≤
      ‖M.reward - M'.reward‖ / (1 - M.discount) ∧
    ‖(fun s ↦ ⨆ π : StationaryPolicy State Action,
          (π s).expectation (M.policyFixedPoint π s)) -
        (fun s ↦ ⨆ π : StationaryPolicy State Action,
          (π s).expectation (M'.policyFixedPoint π s))‖ ≤
      ‖M.reward - M'.reward‖ / (1 - M.discount)

/-- `eq:defn-Vpi-inf`, `chapters/prelim.tex:94–106` (display `:96–100`, bound
`:104–106`). `V^π(s)` is the integral of the actual infinite discounted return
`∑_t γ^t r(s_t,a_t)` (`infiniteDiscountedReturn`) under the controlled infinite trajectory law
from `s_0 = s` with `a_t ∼ π(·|s_t)`, `s_{t+1} ∼ P(·|s_t,a_t)` (`infiniteTrajectoryLaw`,
Ionescu-Tulcea); this is the definition of `trajectoryExpectedValue`. The entry records that
the printed expectation is well defined (the return is integrable) and the printed bound
`0 ≤ V^π(s) ≤ 1/(1−γ)`. Policies are stationary randomized `π : S → Δ(A)` (`:66`).
`V^π(ρ)` (`:107–111`) is a definition. The Bellman fixed-point property is
`Eq_bellman_consistency_V`. -/
def Eq_defn_Vpi_inf : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action) (s : State),
    Integrable (M.infiniteDiscountedReturn s) (M.infiniteTrajectoryLaw π s) ∧
    0 ≤ M.trajectoryExpectedValue π s ∧ M.trajectoryExpectedValue π s ≤ 1 / (1 - M.discount)

/-- `eq:defn-Qpi-inf-horizon`, `chapters/prelim.tex:117–121`, with
`eq:Vpi-a-function-of-Qpi-inf`, `chapters/prelim.tex:126–129`. `Q^π(s,a)` is the integral of
the actual infinite discounted return under the trajectory law with `s_0 = s`, the first
action forced to `a`, and `a_t ∼ π(·|s_t)` afterwards (`forcedActionTrajectoryLaw`; meaningful
also for actions outside the support of `π(s)`). The entry records integrability, the bound
`0 ≤ Q^π ≤ 1/(1−γ)` (not printed, implied by the reward range), and the printed identity
`V^π(s) = E_{a∼π(·|s)} Q^π(s,a)`. -/
def Eq_defn_Qpi_inf_horizon : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action) (s : State) (a : Action),
    Integrable (M.infiniteDiscountedReturn s) (M.forcedActionTrajectoryLaw π s a) ∧
    0 ≤ M.trajectoryExpectedQ π s a ∧ M.trajectoryExpectedQ π s a ≤ 1 / (1 - M.discount) ∧
    M.trajectoryExpectedValue π s = (π s).expectation (M.trajectoryExpectedQ π s)

/-- `eq:optimal-Vstar-Q-star-defn`, `chapters/prelim.tex:132–143`. There is a deterministic
stationary policy `π⋆ = f` (`π⋆(a|s) = 1{a = f s}`) that simultaneously maximizes `Q^π(s,a)`
and `V^π(s)` at every `(s,a)`, over all stationary randomized policies `π` (the class the
chapter restricts to, `:66`). The second conjunct records that the shorthand
`V⋆ := V^{π⋆}`, `Q⋆ := Q^{π⋆}` does not depend on which such `π⋆` is chosen. `V^π`, `Q^π` are
the actual trajectory expectations of `Eq_defn_Vpi_inf` and `Eq_defn_Qpi_inf_horizon`. -/
def Eq_optimal_Vstar_Qstar_defn : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action),
    (∃ f : State → Action, ∀ (π : StationaryPolicy State Action) (s : State) (a : Action),
      M.trajectoryExpectedQ π s a ≤
          M.trajectoryExpectedQ (fun x ↦ EnvironmentStage.pointMass (f x)) s a ∧
      M.trajectoryExpectedValue π s ≤
          M.trajectoryExpectedValue (fun x ↦ EnvironmentStage.pointMass (f x)) s) ∧
    ∀ f g : State → Action,
      (∀ (π : StationaryPolicy State Action) (s : State) (a : Action),
        M.trajectoryExpectedQ π s a ≤
            M.trajectoryExpectedQ (fun x ↦ EnvironmentStage.pointMass (f x)) s a ∧
        M.trajectoryExpectedValue π s ≤
            M.trajectoryExpectedValue (fun x ↦ EnvironmentStage.pointMass (f x)) s) →
      (∀ (π : StationaryPolicy State Action) (s : State) (a : Action),
        M.trajectoryExpectedQ π s a ≤
            M.trajectoryExpectedQ (fun x ↦ EnvironmentStage.pointMass (g x)) s a ∧
        M.trajectoryExpectedValue π s ≤
            M.trajectoryExpectedValue (fun x ↦ EnvironmentStage.pointMass (g x)) s) →
      M.trajectoryExpectedQ (fun x ↦ EnvironmentStage.pointMass (f x)) =
          M.trajectoryExpectedQ (fun x ↦ EnvironmentStage.pointMass (g x)) ∧
      M.trajectoryExpectedValue (fun x ↦ EnvironmentStage.pointMass (f x)) =
          M.trajectoryExpectedValue (fun x ↦ EnvironmentStage.pointMass (g x))

/-- `eq:defn-dpi-occupancy-discounted-dist`, `chapters/prelim.tex:145–160`, with
`eq:infinite-d-star-def`, `chapters/prelim.tex:163–176`. The occupancies are written as the
printed formulas: `d^π(s;ρ) = (1−γ) ∑_t γ^t ℙ(s_t = s | s_0 ∼ ρ)` and
`d^π(s,a;ρ) = (1−γ) ∑_t γ^t ℙ(s_t = s, a_t = a | s_0 ∼ ρ)`, with the event probabilities taken
under the actual infinite trajectory law and mixed over `ρ`. Conjuncts: both are normalized
(the "prefactor `1−γ` … ensuring that these distributions are normalized" claim, `:160`), and
for every deterministic stationary policy `f` (in particular `π⋆`),
`d(s,a;ρ) = d(s;ρ) 1{a = f(s)}` (`:171–174`). -/
def Eq_defn_dpi_occupancy_discounted_dist : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action] [DecidableEq Action]
    (M : DiscountedMDP State Action) (ρ : FiniteDistribution State),
    let d : StationaryPolicy State Action → State → ℝ := fun π s ↦
      (1 - M.discount) * ∑' t : ℕ, M.discount ^ t * ρ.expectation (fun x ↦
        (M.infiniteTrajectoryLaw π x).real
          {path | DiscountedMDP.trajectoryState x path t = s})
    let dj : StationaryPolicy State Action → State → Action → ℝ := fun π s a ↦
      (1 - M.discount) * ∑' t : ℕ, M.discount ^ t * ρ.expectation (fun x ↦
        (M.infiniteTrajectoryLaw π x).real
          {path | DiscountedMDP.trajectoryState x path t = s ∧ (path t).1 = a})
    (∀ π : StationaryPolicy State Action, ∑ s, d π s = 1 ∧ ∑ s, ∑ a, dj π s a = 1) ∧
    ∀ (f : State → Action) (s : State) (a : Action),
      dj (fun x ↦ EnvironmentStage.pointMass (f x)) s a =
        d (fun x ↦ EnvironmentStage.pointMass (f x)) s * (if a = f s then 1 else 0)

/-- `eq:bellman_consistency_operator`, `eq:bellman_consistency`, `chapters/prelim.tex:191–209`,
and `eq:bellman_consistency-V`, `chapters/prelim.tex:210–223`. With
`T^π(Q)(s,a) = r(s,a) + γ E_{s'∼P(·|s,a)} E_{a'∼π(·|s')} Q(s',a')` and
`T_π(V)(s) = E_{a∼π(·|s)} r(s,a) + γ E_{s'∼P(·|s,π)} V(s')`, where
`P(s'|s,π) = E_{a∼π(·|s)} P(s'|s,a)` (`eq:defn-P-s-pi-inf`, `:69–74`): the actual trajectory
`Q^π` is a fixed point of `T^π`, it is the unique fixed point (`:209`), and the actual
trajectory `V^π` is a fixed point of `T_π`. Every `γ ∈ [0,1)`. -/
def Eq_bellman_consistency_V : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action),
    let Tπ : (State → Action → ℝ) → State → Action → ℝ := fun Q s a ↦
      M.reward s a + M.discount *
        (M.transition s a).expectation (fun s' ↦ (π s').expectation (Q s'))
    let TV : (State → ℝ) → State → ℝ := fun V s ↦
      (π s).expectation (M.reward s) + M.discount *
        ∑ s', (π s).expectation (fun a ↦ (M.transition s a).prob s') * V s'
    Tπ (M.trajectoryExpectedQ π) = M.trajectoryExpectedQ π ∧
    (∀ Q : State → Action → ℝ, Tπ Q = Q → Q = M.trajectoryExpectedQ π) ∧
    TV (M.trajectoryExpectedValue π) = M.trajectoryExpectedValue π

/-- `eq:bellman_optimality_operator`, `eq:bellman_fix_point`, `chapters/prelim.tex:233–246`.
`T(Q)(s,a) = r(s,a) + γ E_{s'∼P(·|s,a)} max_{a'} Q(s',a')` (the finite maximum written as
`⨆ a'`, which is the maximum since the action set is finite and nonempty). For **every**
optimal deterministic stationary policy `π⋆ = f` (in the sense of
`Eq_optimal_Vstar_Qstar_defn`), `Q⋆ := Q^{π⋆}` is a fixed point of `T` and is its unique
fixed point. -/
def Eq_bellman_fix_point : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (f : State → Action),
    (∀ (π : StationaryPolicy State Action) (s : State) (a : Action),
      M.trajectoryExpectedQ π s a ≤
          M.trajectoryExpectedQ (fun x ↦ EnvironmentStage.pointMass (f x)) s a ∧
      M.trajectoryExpectedValue π s ≤
          M.trajectoryExpectedValue (fun x ↦ EnvironmentStage.pointMass (f x)) s) →
    let T : (State → Action → ℝ) → State → Action → ℝ := fun Q s a ↦
      M.reward s a + M.discount * (M.transition s a).expectation (fun s' ↦ ⨆ a', Q s' a')
    T (M.trajectoryExpectedQ (fun x ↦ EnvironmentStage.pointMass (f x))) =
        M.trajectoryExpectedQ (fun x ↦ EnvironmentStage.pointMass (f x)) ∧
    ∀ Q : State → Action → ℝ, T Q = Q →
      Q = M.trajectoryExpectedQ (fun x ↦ EnvironmentStage.pointMass (f x))

/-- `eq:gamma-contraction-preliminary-inf`, `chapters/prelim.tex:251–261`. For every policy
`π` and all `Q₁, Q₂ ∈ ℝ^{S×A}`, `‖T^π Q₁ − T^π Q₂‖∞ ≤ γ ‖Q₁ − Q₂‖∞` and
`‖T Q₁ − T Q₂‖∞ ≤ γ ‖Q₁ − Q₂‖∞`, with `T^π`, `T` as in `Eq_bellman_consistency_V` and
`Eq_bellman_fix_point`. `‖·‖` on `State → Action → ℝ` is Mathlib's sup norm on finite
products, i.e. `max_{s,a} |Q(s,a)|` (the printed `ℓ∞` norm). -/
def Eq_gamma_contraction_preliminary_inf : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (Q₁ Q₂ : State → Action → ℝ),
    let Tπ : (State → Action → ℝ) → State → Action → ℝ := fun Q s a ↦
      M.reward s a + M.discount *
        (M.transition s a).expectation (fun s' ↦ (π s').expectation (Q s'))
    let T : (State → Action → ℝ) → State → Action → ℝ := fun Q s a ↦
      M.reward s a + M.discount * (M.transition s a).expectation (fun s' ↦ ⨆ a', Q s' a')
    ‖Tπ Q₁ - Tπ Q₂‖ ≤ M.discount * ‖Q₁ - Q₂‖ ∧ ‖T Q₁ - T Q₂‖ ≤ M.discount * ‖Q₁ - Q₂‖

/-- `eq:dh-pi-defn`, `chapters/prelim.tex:749–774` (`eq:dh-pi-defn` `:749–758`,
`eqn:defn-d1rho-finite` `:760–763`, `eq:dhstar-finite` `:765–774`).
A finite-horizon episode with nonstationary transitions, rewards and randomized Markov
decision rules is a list of `DecisionStage`s (stage `i` is the source's step `h = i + 1`).
`d_h(s;ρ) = ℙ(s_h = s | s_1 ∼ ρ)` is written as the final-state event of the actual trajectory
law of the first `i` stages, mixed over `ρ`; `d_h(s,a;ρ) = ℙ(s_h = s, a_h = a | s_1 ∼ ρ)` adds
one more sampled stage and its action. Conjuncts: `d_h(s,a) = d_h(s) π_h(a|s)`; `d_1 = ρ` for
every policy; and for **every** deterministic Markov policy (`π_h(·|x) = 1{· = f_h(x)}` at every
step; in particular `π⋆`), `d_h(s,a) = d_h(s) 1{a = f_h(s)}`. -/
def Eq_dh_pi_defn : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    [DecidableEq State] [DecidableEq Action]
    (stages : List (DecisionStage State Action)) (ρ : FiniteDistribution State),
    let d : Fin stages.length → State → ℝ := fun i s ↦
      ρ.expectation (fun x ↦ (DecisionStage.trajectoryLaw (stages.take i.val) x).expectation
        (fun path ↦
          if DecisionStage.finalState (stages.take i.val).length x path = s then 1 else 0))
    let dj : Fin stages.length → State → Action → ℝ := fun i s a ↦
      ρ.expectation (fun x ↦ (DecisionStage.trajectoryLaw (stages.take i.val) x).expectation
        (fun path ↦
          (DecisionStage.trajectoryLaw [stages.get i]
              (DecisionStage.finalState (stages.take i.val).length x path)).expectation
            (fun next ↦
              if DecisionStage.finalState (stages.take i.val).length x path = s ∧ next.1 = a
              then 1 else 0)))
    (∀ (i : Fin stages.length) (s : State) (a : Action),
      dj i s a = d i s * ((stages.get i).policy s).prob a) ∧
    (∀ (i : Fin stages.length), i.val = 0 → ∀ s, d i s = ρ.prob s) ∧
    ∀ f : ℕ → State → Action,
      (∀ (i : Fin stages.length) (x : State),
        (stages.get i).policy x = EnvironmentStage.pointMass (f i.val x)) →
      ∀ (i : Fin stages.length) (s : State) (a : Action),
        dj i s a = d i s * (if a = f i.val s then 1 else 0)

/-- `eq:Bellman-finite-pi`, `chapters/prelim.tex:784–794`. For a finite-horizon episode with
nonstationary transitions, rewards and randomized Markov decision rules (a list of `H`
`DecisionStage`s; stage `i` is step `h = i + 1`), `V_h^π`, `Q_h^π` are the actual expected
cumulative rewards from step `h` (`trajectoryValue`, `trajectoryQ` of the suffix starting at
stage `i`). Terminal values `V_{H+1} = Q_{H+1} = 0` (`:784`), and for every `h ∈ [H]`:
`Q_h(s,a) = r_h(s,a) + E_{s'∼P_h(·|s,a)} V_{h+1}(s')` and `V_h(s) = E_{a∼π_h(·|s)} Q_h(s,a)`. -/
def Eq_Bellman_finite_pi : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (stages : List (DecisionStage State Action)),
    (∀ s, DecisionStage.trajectoryValue (stages.drop stages.length) s = 0) ∧
    (∀ s a, DecisionStage.trajectoryQ (stages.drop stages.length) s a = 0) ∧
    ∀ (i : Fin stages.length) (s : State) (a : Action),
      DecisionStage.trajectoryQ (stages.drop i.val) s a =
          (stages.get i).reward s a + ((stages.get i).transition s a).expectation
            (DecisionStage.trajectoryValue (stages.drop (i.val + 1))) ∧
      DecisionStage.trajectoryValue (stages.drop i.val) s =
          ((stages.get i).policy s).expectation (DecisionStage.trajectoryQ (stages.drop i.val) s)

/-- `eq:Bellman-finite-opt`, `chapters/prelim.tex:798–806`, with the existence claim at
`chapters/prelim.tex:738–746` (`eq:defn-optimalV-optimalQ-finite-prelim`). A finite-horizon
environment is a list of `H` `EnvironmentStage`s (nonstationary `P_h`, `r_h ∈ [0,1]`); a
randomized Markov policy `π = (π_h)` acts through `controlled`, and `V_h^π`, `Q_h^π` are the
actual expected cumulative rewards of the suffix from step `h` (index `n = h − 1`). A
deterministic Markov policy `f = (f_h)` is optimal if it maximizes `V_h^π(s)` and `Q_h^π(s,a)`
over all randomized Markov policies at every `(s,a,h) ∈ S × A × [H]`. Conjuncts: an optimal
deterministic policy exists (`:738–739`); and for **every** optimal deterministic `π⋆`,
`V⋆ := V^{π⋆}`, `Q⋆ := Q^{π⋆}` satisfy `V⋆_{H+1} = Q⋆_{H+1} = 0` and, for `h = H, …, 1`,
`Q⋆_h(s,a) = r_h(s,a) + E_{s'∼P_h(·|s,a)} V⋆_{h+1}(s')` and `V⋆_h(s) = max_a Q⋆_h(s,a)` (written
`⨆ a`). `Nonempty Action` is the printed 𝒜 = {1,…,A} (`chapters/prelim.tex:36`); each stage already
carries a nonempty action set, so it matters only for H = 0. -/
def Eq_Bellman_finite_opt : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action] [Nonempty Action]
    (es : List (EnvironmentStage State Action)),
    let V : (ℕ → StationaryPolicy State Action) → ℕ → State → ℝ := fun π n ↦
      DecisionStage.trajectoryValue ((EnvironmentStage.controlled es π).drop n)
    let Q : (ℕ → StationaryPolicy State Action) → ℕ → State → Action → ℝ := fun π n ↦
      DecisionStage.trajectoryQ ((EnvironmentStage.controlled es π).drop n)
    let det : (ℕ → State → Action) → ℕ → StationaryPolicy State Action := fun f n x ↦
      EnvironmentStage.pointMass (f n x)
    let IsOptimal : (ℕ → State → Action) → Prop := fun f ↦
      ∀ (π : ℕ → StationaryPolicy State Action) (n : ℕ) (s : State) (a : Action),
        n < es.length → V π n s ≤ V (det f) n s ∧ Q π n s a ≤ Q (det f) n s a
    (∃ f, IsOptimal f) ∧
    ∀ f, IsOptimal f →
      (∀ s, V (det f) es.length s = 0) ∧ (∀ s a, Q (det f) es.length s a = 0) ∧
      ∀ (i : Fin es.length) (s : State) (a : Action),
        Q (det f) i.val s a = (es.get i).reward s a +
            ((es.get i).transition s a).expectation (V (det f) (i.val + 1)) ∧
        V (det f) i.val s = ⨆ a', Q (det f) i.val s a'

end StatisticalRL.Statements.Ch2
