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

/-- `eq:Qpi-Vpi-matrix-notation-inf`, equations (2.24a–d), `chapters/prelim.tex:496–531`,
with the intermediate display `Q^π = r + γ P^π Q^π` of `chapters/prelim.tex:524–526`.
`Q^π` is the policy Bellman solution `M.policyFixedPoint π` (separately proved equal to the
expected infinite-trajectory Q-value, `trajectoryExpectedQ_eq_policyFixedPoint`), viewed as a
vector indexed by `State × Action`; `V^π = Π^π Q^π`, i.e. `V^π(s) = E_{a∼π(s)} Q^π(s,a)`
(`eq:Vpi-a-function-of-Qpi-inf`); `r` is the reward vector on `State × Action`,
`r_π(s) = E_{a∼π(s)} r(s,a)`; `P` is the `(S·A) × S` transition matrix; `P_π` and `P^π` are
the policy matrices exactly as in `Lemma2_3`; all stationary randomized policies are included.
The conjuncts, in order: (2.24a) `Q^π = r + γPV^π`; (2.24b) `V^π = r_π + γP_πV^π`;
(2.24c) `V^π = (I − γP_π)⁻¹ r_π`; the intermediate `Q^π = r + γP^πQ^π`; and (2.24d)
`Q^π = (I − γP^π)⁻¹ r`. The inverses are Mathlib's `Matrix` inverses; `I − γP_π` and
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
    Q = (1 - γ • Ppi)⁻¹ *ᵥ r

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

/-- Iteration count stated after Lemma 2.1, `chapters/prelim.tex:357–360` (lemma
`chapters/prelim.tex:339–343`, algorithms `eq:value_iteration` and `eq:policy_iteration`,
`chapters/prelim.tex:315–333`): to reach `‖Q_k − Q⋆‖∞ ≤ ε` it takes no more than
`(1/(1−γ)) log(‖Q₀ − Q⋆‖∞/ε)` iterations, for value iteration and for policy iteration
(`Q_k = Q^{π_k}`, `Q₀ = Q^{π₀}`). Read as: for every `ε > 0` and every iteration count
`k ≥ log(‖Q₀ − Q⋆‖∞/ε)/(1−γ)`, `‖Q_k − Q⋆‖∞ ≤ ε`. Objects and binders are those of `Lemma2_1`
(policy iteration with arbitrary maximizing tie choices). When `Q₀ = Q⋆` the printed `log 0`
is undefined; Lean's `log 0 = 0` turns the condition into `k ≥ 0`, and the conclusion holds
there since then every iterate equals `Q⋆`. -/
def Lemma2_1_iterationCount : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M : DiscountedMDP State Action) (ε : ℝ), 0 < ε →
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
As in `Lemma2_1`, `Q^π` is written as the policy Bellman solution `M.policyFixedPoint π`
(separately proved equal to the expected infinite-trajectory Q-value,
`trajectoryExpectedQ_eq_policyFixedPoint`), and `V^π(s) = E_{a∼π(s)} Q^π(s,a)`. The norms are
the finite sup norms (`‖·‖` on `State → Action → ℝ` and `State → ℝ` is the max of `|·|`). The
printed intermediate resolvent identities (`(I−γP^π)⁻¹ r` and `‖(I−γP^π)⁻¹‖₁ = 1/(1−γ)`) are
proof steps and are not restated here; the matrix facts are `Lemma2_3`. -/
def Eq_QV_pi_perturbation_r_inf : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M M' : DiscountedMDP State Action),
    M'.transition = M.transition → M'.discount = M.discount →
    ∀ π : StationaryPolicy State Action,
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
`V^π(s) = E_{a∼π(s)} Q^π(s,a)`). The first conjunct records that these suprema are the optimal
Bellman solution `optimalityFixedPoint` (the `Q⋆` of `Lemma2_1`) of each model, so the Q-suprema
are attained (by `optimalGreedyPolicy`); the V-suprema are bounded above by `1/(1−γ)` and the
norm-supremum by `‖r − r̃‖∞/(1−γ)`, so no `⨆` here is a junk value. -/
def Eq_QV_star_perturbation_r_inf : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (M M' : DiscountedMDP State Action),
    M'.transition = M.transition → M'.discount = M.discount →
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

end StatisticalRL.Statements
