import Formalization.Probability.FiniteSampleDefinitions

/-! Actual joint law of offline state-action-next-state triples and its row
projections. Source: `chapters/offlineRL.tex:28–37`. This is a sampling-law
foundation, not the offline main theorem. -/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.OfflineRL.JointRow

open StatisticalRL

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Discrete σ-algebra on rows `(s, a)`. -/
local instance rowMeasurable : MeasurableSpace (State × Action) := ⊤
/-- Discrete σ-algebra on triples `((s, a), s')`. -/
local instance tripleMeasurable : MeasurableSpace ((State × Action) × State) := ⊤

/-- The actual joint law of one data triple: `(s,a) ~ ρ`, then `s' ~ P(·|s,a)`. -/
noncomputable def jointRow (ρ : FiniteDistribution (State × Action))
    (P : State → Action → FiniteDistribution State) :
    FiniteDistribution ((State × Action) × State) where
  prob x := ρ.prob x.1 * (P x.1.1 x.1.2).prob x.2
  prob_nonneg x := mul_nonneg (ρ.prob_nonneg _) ((P _ _).prob_nonneg _)
  sum_prob := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, FiniteDistribution.sum_prob, mul_one]
    exact ρ.sum_prob

/-- The `(s,a)`-marginal of the joint triple law is the behaviour row law. -/
theorem jointRow_rowMeasure_map_fst (ρ : FiniteDistribution (State × Action))
    (P : State → Action → FiniteDistribution State) :
    (jointRow ρ P).rowMeasure.map Prod.fst = ρ.rowMeasure := by
  classical
  unfold FiniteDistribution.rowMeasure
  rw [PMF.toMeasure_map (hf := measurable_from_top)]
  congr 1
  ext x
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type]
  unfold FiniteDistribution.toPMF
  simp only [PMF.ofFintype_apply, jointRow]
  have hinner : ∀ y : State × Action,
      (∑ s' : State, if x = (y, s').1 then ENNReal.ofReal (ρ.prob y * (P y.1 y.2).prob s') else 0) =
        if x = y then ∑ s' : State, ENNReal.ofReal (ρ.prob y * (P y.1 y.2).prob s') else 0 := by
    intro y
    by_cases h : x = y <;> simp [h]
  rw [Finset.sum_congr rfl (fun y _ => hinner y), Finset.sum_ite_eq, if_pos (Finset.mem_univ x),
    ← ENNReal.ofReal_sum_of_nonneg (fun s' _ => mul_nonneg (ρ.prob_nonneg _) ((P _ _).prob_nonneg _)),
    ← Finset.mul_sum, FiniteDistribution.sum_prob, mul_one]

/-- `N` i.i.d. triples, projected coordinatewise to `(s,a)`, have exactly the
`N`-sample product law of the behaviour row law. -/
theorem jointRow_sample_projection (ρ : FiniteDistribution (State × Action))
    (P : State → Action → FiniteDistribution State) (N : ℕ) :
    ((jointRow ρ P).sampleMeasure N).map (fun ω i => (ω i).1) = ρ.sampleMeasure N := by
  unfold FiniteDistribution.sampleMeasure
  have hσ : ∀ i : Fin N, SigmaFinite
      (((fun _ : Fin N => (jointRow ρ P).rowMeasure) i).map ((fun _ : Fin N => Prod.fst) i)) := by
    intro i
    show SigmaFinite ((jointRow ρ P).rowMeasure.map Prod.fst)
    rw [jointRow_rowMeasure_map_fst]
    unfold FiniteDistribution.rowMeasure
    infer_instance
  rw [Measure.pi_map_pi (f := fun _ => Prod.fst) (hμ := hσ) (fun _ => measurable_from_top.aemeasurable)]
  congr 1
  funext _
  exact jointRow_rowMeasure_map_fst ρ P

end StatisticalRL.OfflineRL.JointRow
