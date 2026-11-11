import Formalization.ModelFree.TDSharpMartingale
import Formalization.ModelFree.TDLinearRowVariance
import Formalization.Probability.Variance

/-! Actual fixed-terminal TD centered-square variance definitions. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The actual source update at state `s` if its fresh next-state draw is `x`.
The old iterate and all other coordinates are held fixed. -/
noncomputable def tdSquareFreshUpdate (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T : ℕ)
    (V₀ : State → ℝ) (k : ℕ) (s x : State)
    (data : TDSamples State T) : ℝ :=
  (1 - η k) * tdValueBefore M π η T (k - 1) V₀ data s +
    η k * (policyReward M π s + M.discount *
      tdValueBefore M π η T (k - 1) V₀ data x)

/-- The actual policy-row variance of the square of the one-step update map.
This is the candidate finite-law expression for the conditional second moment
of the centered squared iterate at update `k`. -/
noncomputable def tdSquareFreshRowVariance (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T : ℕ)
    (V₀ : State → ℝ) (k : ℕ) (s : State)
    (data : TDSamples State T) : ℝ :=
  (M.policyTransition π s).variance
    (fun x ↦ tdSquareFreshUpdate M π η T V₀ k s x data ^ 2)

/-- Actual conditional second moment of the centered-square observation,
conditioned on the used source prefix through `k-1`. -/
noncomputable def tdSquareCenteredConditionalSecondMoment
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (V₀ : State → ℝ) (k : ℕ) (s : State) :
    TDSamples State T → ℝ :=
  (tdSamplingLaw M π T)[(fun data ↦
    tdSquareCentered M π η T V₀ k s data ^ 2) | tdPastSigma T (k - 1)]

/-- A deterministic row applied to the actual centered-square vector at source
update `k`. -/
noncomputable def tdSquareCenteredRow (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (η : ℕ → ℝ) (T : ℕ)
    (V₀ : State → ℝ) (k : ℕ) (u : State → ℝ)
    (data : TDSamples State T) : ℝ :=
  ∑ r, u r * tdSquareCentered M π η T V₀ k r data

/-! Intended exact-source lemmas, still open:

* For `1 ≤ k ≤ T`, `tdSquareCenteredConditionalSecondMoment ... k s` equals
  `tdSquareFreshRowVariance ... k s` almost surely.
* If the actual iterates lie in `[0,H]`, the finite-row Lipschitz estimate
  gives `Var(U²) ≤ 4 H² Var(U)`, and the affine fresh update gives
  `Var(U) = η_k² γ² Var_{Pπ(s)}(V_{k-1})`.
* For distinct `s,r`, the conditional product of their centered-square
  observations is zero. This must be derived from the actual distinct
  coordinates `(s,k)` and `(r,k)`, using the finite indicator expansion and
  conditional joint-indicator identity in `TDCrossCovariance`.
* Consequently, for a deterministic row `u`, the conditional second moment
  of `tdSquareCenteredRow` is the diagonal sum
  `∑ s, u s² * Var_{Pπ(s)}(U_s²)`; the tail-row proxy then uses positivity,
  row mass at most one, and `η_k² ≤ η̄ η_k`.

The square-specific results are not inherited from raw TD-noise covariance.
-/

end StatisticalRL.TemporalDifference
