import Formalization.ModelFree.TDSynchronousSampling
import Formalization.MDP.PrefixValueBridge
import Formalization.ModelFree.TDLearningWeights

/-! Actual pathwise TD error and source terminal-time-indexed innovations.
No martingale or conditional-expectation premise is introduced. -/
namespace StatisticalRL.TemporalDifference
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Error relative to the actual infinite-trajectory policy value. -/
noncomputable def tdErrorValue (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ)
    (samples : ℕ → State → State) (V₀ : State → ℝ) (t : ℕ) : State → ℝ :=
  tdIterate M π η samples V₀ t - M.trajectoryExpectedValue π

/-- Deterministic linear error transition I−η_i(I−γPπ), in row expectation form. -/
noncomputable def tdErrorTransition (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (i : ℕ) (U : State → ℝ) : State → ℝ :=
  fun s ↦ (1 - η i) * U s + η i * M.discount * (M.policyTransition π s).expectation U

/-- The actual centered row fluctuation at update k+1, using the synchronous
old iterate V_k. The unused time-zero innovation is zero. -/
noncomputable def tdCenteredRowNoise (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ)
    (samples : ℕ → State → State) (V₀ : State → ℝ) : ℕ → State → ℝ
  | 0 => fun _ ↦ 0
  | k + 1 => fun s ↦ tdIterate M π η samples V₀ k (samples (k + 1) s) -
      (M.policyTransition π s).expectation (tdIterate M π η samples V₀ k)

/-- Chronological propagation through updates start+1,...,finish.
This fixes operator orientation before identifying a matrix-product expression. -/
noncomputable def tdErrorPropagate (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (start : ℕ) : ℕ → (State → ℝ) → State → ℝ
  | 0, U => U
  | n + 1, U => if start ≤ n then tdErrorTransition M π η (n + 1)
      (tdErrorPropagate M π η start n U) else U

/-- Source Z_k at a FIXED terminal time t. Outside 1≤k≤t it is zero.
Future learning-rate factors are deterministic parameters, not random data. -/
noncomputable def tdWeightedErrorIncrement (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ)
    (samples : ℕ → State → State) (V₀ : State → ℝ) (t k : ℕ) : State → ℝ :=
  if 1 ≤ k ∧ k ≤ t then tdErrorPropagate M π η k t
    (fun s ↦ M.discount * η k * tdCenteredRowNoise M π η samples V₀ k s) else 0

theorem tdErrorTransition_add (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (i : ℕ) (U V : State → ℝ) :
    tdErrorTransition M π η i (U + V) = tdErrorTransition M π η i U + tdErrorTransition M π η i V := by
  funext s
  simp only [tdErrorTransition, Pi.add_apply, Pi.add_def, FiniteDistribution.expectation_add]
  ring

theorem tdErrorTransition_mul (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (i : ℕ) (c : ℝ) (U : State → ℝ) :
    tdErrorTransition M π η i (fun s ↦ c * U s) = fun s ↦ c * tdErrorTransition M π η i U s := by
  funext s
  simp only [tdErrorTransition, FiniteDistribution.expectation_mul]
  ring

/-- Source one-step error identity, with the Bellman equation proved for the
actual trajectory expectation rather than assumed as a target-shaped premise. -/
theorem tdErrorValue_succ (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ)
    (samples : ℕ → State → State) (V₀ : State → ℝ) (k : ℕ) :
    tdErrorValue M π η samples V₀ (k + 1) =
      tdErrorTransition M π η (k + 1) (tdErrorValue M π η samples V₀ k) +
      (fun s ↦ M.discount * η (k + 1) * tdCenteredRowNoise M π η samples V₀ (k + 1) s) := by
  funext s
  have hbell := congrFun (M.valueFixedPoint_spec π) s
  rw [← M.trajectoryExpectedValue_eq_valueFixedPoint π] at hbell
  change policyReward M π s + M.discount *
    (M.policyTransition π s).expectation (M.trajectoryExpectedValue π) = M.trajectoryExpectedValue π s at hbell
  have hbellScaled := congrArg (fun x : ℝ ↦ η (k + 1) * x) hbell
  simp only [tdErrorValue, tdIterate, tdErrorTransition, tdCenteredRowNoise, Pi.sub_apply, Pi.sub_def, Pi.add_apply,
    FiniteDistribution.expectation_sub]
  nlinarith

/- Intended next proof targets (not assumptions or admitted declarations):

1. tdErrorValue ... t = tdErrorPropagate M π η 0 t (V₀ - M.trajectoryExpectedValue π)
     + ∑ k ∈ Finset.Icc 1 t, tdWeightedErrorIncrement ... t k.

2. Construct the actual TD prefix sigma-algebra from coordinates with source
   time 1≤i≤n, excluding the unused time-zero array. Prove the iterate at n
   factors through it and the entire next layer is independent under tdSamplingLaw.

3. For k+1≤T and each state, prove actual conditional mean zero of the scalar
   tdCenteredRowNoise at k+1 given that prefix, then conditional second moment
   equal to the true policy-row variance of the random predictable V_k.

4. For fixed final t≤T, derive adaptedness and conditional centering of
   tdWeightedErrorIncrement ... t (k+1) coordinatewise via deterministic linear
   propagation, proving integrability from actual bounded iterates. No martingale
   or concentration conclusion is an input to these targets.
-/
end StatisticalRL.TemporalDifference
