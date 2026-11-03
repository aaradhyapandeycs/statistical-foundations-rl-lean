import Formalization.ModelFree.TDSourceRateFiniteExtension
import Formalization.ModelFree.TDSharpEnergyProxy

/-! The actual TD proxy and eligible-terminal event are invariant under the zero-tail schedule extension. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.TemporalDifference

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Exact source terminal eligibility, with the real-valued threshold kept
explicit rather than replaced by a half-horizon cutoff. -/
def tdSourceEligibleTerminal (T : ℕ) (c₂ : ℝ) (t : ℕ) : Prop :=
  (T : ℝ) / (c₂ * Real.log (T : ℝ)) ≤ (t : ℝ)

/-- At any terminal through T, the actual sample-dependent late-window proxy
is unchanged by replacing the finite schedule's tail with zeros. The active
sum uses only η_(n+1), values V_n with n<t≤T, and the actual suffix rows
A_(n+1:t), all of which have been proved invariant in the rate-extension module. -/
theorem tdSquareLateWindowRandomProxy_eq_sourceRateExtend
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T t : ℕ) (ht : t ≤ T) (V₀ : State → ℝ)
    (barη : ℝ) (q : State) (data : TDSamples State T) :
    tdSquareLateWindowRandomProxy M π (tdSourceRateExtend T η) T t V₀ barη q data =
      tdSquareLateWindowRandomProxy M π η T t V₀ barη q data := by
  unfold tdSquareLateWindowRandomProxy
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hactive : t / 2 ≤ n
  · simp only [if_pos hactive]
    have hnlt : n < t := Finset.mem_range.mp hn
    have hidx : n + 1 ≤ T := by omega
    have hvalue :
        tdValueBefore M π (tdSourceRateExtend T η) T n V₀ data =
          tdValueBefore M π η T n V₀ data := by
      unfold tdValueBefore
      exact tdIterate_eq_sourceRateExtend M π η
        (tdSamplesExtend M T data) V₀ T n (by omega)
    have hrate : tdSourceRateExtend T η (n + 1) = η (n + 1) :=
      tdSourceRateExtend_eq η hidx
    have hrow (r : State) :
        tdSquareLateTerminalRow M π (tdSourceRateExtend T η) t (n + 1) q r =
          tdSquareLateTerminalRow M π η t (n + 1) q r := by
      simpa [tdSquareLateTerminalRow] using
        tdPropagatorRow_eq_sourceRateExtend M π η T (n + 1) t ht q r
    rw [hrate, hvalue]
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    rw [hrow r]
  · simp [hactive]

/-- The event with simultaneous proxy control over the theorem's exact
eligible range. The `j.val+1` indexing is the positive terminal `1,…,T`. -/
def tdSourceEligibleProxyEvent
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (c₂ : ℝ) (V₀ : State → ℝ)
    (barη : ℝ) : Set (TDSamples State T) :=
  {data | ∀ q : State, ∀ j : Fin T,
    tdSourceEligibleTerminal T c₂ (j.val + 1) →
      tdSquareLateWindowRandomProxy M π η T (j.val + 1) V₀ barη q data ≤
        16 * barη * M.effectiveHorizon ^ 2}

/-- The full eligible-terminal event is literally the same event under the
zero-tail extension. This keeps the source range in the proposition and
transports every state/terminal coordinate, not merely a high-probability
subset of terminals. -/
theorem tdSourceEligibleProxyEvent_eq_sourceRateExtend
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (c₂ : ℝ) (V₀ : State → ℝ)
    (barη : ℝ) :
    tdSourceEligibleProxyEvent M π (tdSourceRateExtend T η) T c₂ V₀ barη =
      tdSourceEligibleProxyEvent M π η T c₂ V₀ barη := by
  ext data
  simp only [tdSourceEligibleProxyEvent, Set.mem_setOf_eq]
  constructor
  · intro h q j helig
    have ht : j.val + 1 ≤ T := by omega
    have hproxy := tdSquareLateWindowRandomProxy_eq_sourceRateExtend
      M π η T (j.val + 1) ht V₀ barη q data
    rw [← hproxy]
    exact h q j helig
  · intro h q j helig
    have ht : j.val + 1 ≤ T := by omega
    have hproxy := tdSquareLateWindowRandomProxy_eq_sourceRateExtend
      M π η T (j.val + 1) ht V₀ barη q data
    rw [hproxy]
    exact h q j helig

/-- Equality of event sets immediately gives equality of their actual
synchronous sampling probabilities; the sampling law is schedule-independent. -/
theorem tdSourceEligibleProxyEvent_probability_eq_sourceRateExtend
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (η : ℕ → ℝ) (T : ℕ) (c₂ : ℝ) (V₀ : State → ℝ)
    (barη : ℝ) :
    (tdSamplingLaw M π T).real
        (tdSourceEligibleProxyEvent M π (tdSourceRateExtend T η) T c₂ V₀ barη) =
      (tdSamplingLaw M π T).real
        (tdSourceEligibleProxyEvent M π η T c₂ V₀ barη) := by
  rw [tdSourceEligibleProxyEvent_eq_sourceRateExtend M π η T c₂ V₀ barη]

end StatisticalRL.TemporalDifference
