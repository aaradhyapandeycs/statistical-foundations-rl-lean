import Formalization.Online.Regret.W2.OnlineW2ObservedCoordinate
import Formalization.Online.Regret.W2.OnlineW2CoordinateRadius
import Formalization.Online.Regret.W2.OnlineW2WeightedCoordinate

/-! Conditional actual-history W₂ coordinate consumers. The coordinate event
is produced on the same sequential law in OnlineW2ObservedCoordinate;
it is an explicit hypothesis here. These are intermediate conditional estimates. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance w2ConsumerStateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance w2ConsumerActionDecidable : DecidableEq Action := Classical.decEq Action

/-- On the actual pre-episode history, all selected row coordinates obey the
source Bernstein radius simultaneously; no conditional iid assertion is used. -/
theorem onlineObservedW2_selected_coordinate_bound
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action) (δ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5)
    (history : List (OnlineMDPRow State Action H × State))
    (hcert : onlineObservedW2CoordinateCertificates H K E δ history)
    (k : Fin K) (r : OnlineMDPRow State Action H)
    (hn : 3 ≤ (onlineRowOutcomes (history.take (k.val * H)) r).length)
    (x : State) :
    let n := (onlineRowOutcomes (history.take (k.val * H)) r).length
    let emp := FiniteDistribution.empiricalRow n (by omega)
      (onlineObservedRowData (history.take (k.val * H)) r)
    |emp.prob x - (onlineMDPSuccessorRowLaw E r).prob x| ≤
      Real.sqrt (2 * (onlineMDPSuccessorRowLaw E r).prob x * Real.log (1 / δ) / n) +
        Real.log (1 / δ) / n := by
  have hc := hcert k r x hn
  have hr := onlineW2_indicator_radius_le (onlineMDPSuccessorRowLaw E r) x δ
    (onlineRowOutcomes (history.take (k.val * H)) r).length hδ hδsmall (by omega)
  simp only [onlineW2Indicator_expectation] at hc
  exact hc.trans hr

/-- Conditional pointwise W₂ estimate on the selected actual row. The bound
on the adaptive function is a local intermediate obligation, not a source
probability assumption. -/
theorem onlineObservedW2_selected_weighted_bound
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action) (δ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5)
    (history : List (OnlineMDPRow State Action H × State))
    (hcert : onlineObservedW2CoordinateCertificates H K E δ history)
    (k : Fin K) (r : OnlineMDPRow State Action H)
    (hn : 3 ≤ (onlineRowOutcomes (history.take (k.val * H)) r).length)
    (V : State → ℝ) (hV : ∀ x, 0 ≤ V x ∧ V x ≤ H) :
    let n := (onlineRowOutcomes (history.take (k.val * H)) r).length
    let emp := FiniteDistribution.empiricalRow n (by omega)
      (onlineObservedRowData (history.take (k.val * H)) r)
    emp.expectation V - (onlineMDPSuccessorRowLaw E r).expectation V ≤
      Real.sqrt (2 * (Fintype.card State : ℝ) * Real.log (1 / δ) / n) *
        Real.sqrt ((onlineMDPSuccessorRowLaw E r).variance V) +
      (Fintype.card State : ℝ) * H * Real.log (1 / δ) / n := by
  have hL : 0 ≤ Real.log (1 / δ) := by
    apply Real.log_nonneg
    apply (one_le_div hδ).2
    linarith
  apply onlineW2_weighted_coordinate_bound _ _ V H (Real.log (1 / δ)) _
    (by exact_mod_cast Nat.zero_le H) hL (by exact_mod_cast (show 0 < _ by omega)) hV
  intro x
  exact onlineObservedW2_selected_coordinate_bound H K E δ hδ hδsmall history hcert k r hn x
/-- Summing the actual selected-row certificates over any finite collection of
stage/episode pairs. The continuation functions may depend on the whole
realized history: the coordinate event was simultaneous before selection. -/
theorem onlineObservedW2_selected_sum_bound
    (H K : ℕ) (E : Fin H → EnvironmentStage State Action) (δ : ℝ)
    (hδ : 0 < δ) (hδsmall : δ ≤ 2 / 5)
    (history : List (OnlineMDPRow State Action H × State))
    (hcert : onlineObservedW2CoordinateCertificates H K E δ history)
    (rows : Fin H × Fin K → OnlineMDPRow State Action H)
    (values : Fin H × Fin K → State → ℝ)
    (indices : Finset (Fin H × Fin K))
    (hn : ∀ i ∈ indices, 3 ≤ (onlineRowOutcomes
      (history.take (i.2.val * H)) (rows i)).length)
    (hV : ∀ i ∈ indices, ∀ x, 0 ≤ values i x ∧ values i x ≤ H) :
    (∑ i ∈ indices,
      let n := (onlineRowOutcomes (history.take (i.2.val * H)) (rows i)).length
      if hp : 0 < n then
        let emp := FiniteDistribution.empiricalRow n hp
          (onlineObservedRowData (history.take (i.2.val * H)) (rows i))
        emp.expectation (values i) - (onlineMDPSuccessorRowLaw E (rows i)).expectation (values i)
      else 0) ≤
    ∑ i ∈ indices,
      let n := (onlineRowOutcomes (history.take (i.2.val * H)) (rows i)).length
      Real.sqrt (2 * (Fintype.card State : ℝ) * Real.log (1 / δ) / n) *
        Real.sqrt ((onlineMDPSuccessorRowLaw E (rows i)).variance (values i)) +
      (Fintype.card State : ℝ) * H * Real.log (1 / δ) / n := by
  apply Finset.sum_le_sum
  intro i hi
  have hp : 0 < (onlineRowOutcomes (history.take (i.2.val * H)) (rows i)).length := by
    have := hn i hi
    omega
  simp only [dif_pos hp]
  exact onlineObservedW2_selected_weighted_bound H K E δ hδ hδsmall history hcert
    i.2 (rows i) (hn i hi) (values i) (hV i hi)
end StatisticalRL.OnlineRL
