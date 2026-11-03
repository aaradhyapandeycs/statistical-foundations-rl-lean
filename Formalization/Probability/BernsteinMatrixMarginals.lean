import Formalization.Probability.BernsteinFamily

/-! Whole-matrix Bernstein inequality with arbitrary dependence across correctly sampled rows. -/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.FiniteDistribution

variable {State Action : Type*} [Fintype State] [Fintype Action] [Nonempty State] [Nonempty Action]
local instance bernsteinMatrixStateMeasurable : MeasurableSpace State := ⊤
local instance bernsteinMatrixRowMeasurable : MeasurableSpace (FiniteDistribution State) := ⊤

abbrev MarginalRowIndex (State Action : Type*) := State × Action
abbrev MarginalMatrixSamples (State Action : Type*) (N : ℕ) := MarginalRowIndex State Action → Fin N → State

/-- A perfectly coupled sample matrix: every row sees the same sample sequence. -/
def diagonalMatrixSamples (N : ℕ) (ω : Fin N → State) : MarginalMatrixSamples State Action N :=
  fun _ ↦ ω

omit [Fintype State] [Fintype Action] [Nonempty State] [Nonempty Action] in
theorem diagonalMatrixSamples_measurable (N : ℕ) :
    Measurable (diagonalMatrixSamples (State := State) (Action := Action) N) := by
  exact measurable_pi_lambda _ (fun _ ↦ measurable_id)

omit [Nonempty State] [Nonempty Action] in
/-- The perfectly coupled matrix still has the correct iid marginal at every row. -/
theorem diagonalMatrixSamples_row_marginal (d : FiniteDistribution State) (N : ℕ)
    (i : MarginalRowIndex State Action) :
    ((d.sampleMeasure N).map (diagonalMatrixSamples (State := State) (Action := Action) N)).map
      (fun ω ↦ ω i) = d.sampleMeasure N := by
  rw [Measure.map_map (measurable_pi_apply i) (diagonalMatrixSamples_measurable N)]
  exact Measure.map_id

omit [Fintype State] [Fintype Action] [Nonempty State] [Nonempty Action] in
/-- All rows are identically coupled pointwise, so cross-row independence is not built in. -/
theorem diagonalMatrixSamples_rows_equal (N : ℕ) (ω : Fin N → State)
    (i j : MarginalRowIndex State Action) :
    diagonalMatrixSamples (Action := Action) N ω i = diagonalMatrixSamples N ω j := rfl

noncomputable def marginalEmpiricalMatrix (N : ℕ) (hN : 0 < N) (ω : MarginalMatrixSamples State Action N) :
    MarginalRowIndex State Action → FiniteDistribution State := fun i ↦ empiricalRow N hN (ω i)

/-- The ordinary product σ-algebra on the real coordinate vector of each row. -/
noncomputable def marginalMatrixVectorSpace : MeasurableSpace (MarginalRowIndex State Action → FiniteDistribution State) :=
  letI : MeasurableSpace (FiniteDistribution State) := rowVectorSpace
  inferInstance

omit [Fintype Action] [Nonempty State] [Nonempty Action] in
theorem marginalMatrixVectorSpace_eval (i : MarginalRowIndex State Action) :
    @Measurable (MarginalRowIndex State Action → FiniteDistribution State) (FiniteDistribution State)
      marginalMatrixVectorSpace rowVectorSpace (fun rows ↦ rows i) := by
  letI : MeasurableSpace (FiniteDistribution State) := rowVectorSpace
  exact measurable_pi_apply i

omit [Nonempty State] in
/-- Every fixed-row Bernstein violation event is measurable jointly in a Borel family and samples. -/
theorem marginalBernsteinBad_measurable
    {Ω : Type*} [MeasurableSpace Ω] (d : FiniteDistribution State)
    (N : ℕ) (hN : 0 < N) (δ : ℝ) (draw : Ω → Fin N → State) (hdraw : Measurable draw)
    (family : Ω → Finset (State → ℝ))
    (hfamily : letI : MeasurableSpace (Finset (State → ℝ)) := finiteFamilyBorel
      Measurable family) :
    MeasurableSet {ω | bernsteinFamilyBadAt d N δ (family ω) (empiricalRow N hN (draw ω))} := by
  letI : MeasurableSpace (Finset (State → ℝ)) := finiteFamilyBorel
  have hbad : ∀ row ∈ empiricalRows N hN,
      MeasurableSet {c : Finset (State → ℝ) | bernsteinFamilyBadAt d N δ c row} := by
    intro row _
    apply (finiteFamilyBorel_measurableSet_iff _).2
    intro n
    exact enumerationFamily_bernsteinBad_measurable d N δ row n
  have hm := measurableSet_supportedBernsteinBad d N hN δ id hbad
  have hrow : Measurable (fun ω ↦ empiricalRow N hN (draw ω)) := by
    change Measurable ((empiricalRow N hN) ∘ draw)
    exact (measurable_of_countable _).comp hdraw
  have hp := hm.preimage (hfamily.prodMk hrow)
  convert hp using 1
  ext ω
  exact (mem_supportedBernsteinBad_empirical d N hN δ id (family ω) (draw ω)).symm

/-- Whole-matrix source bound under correct iid row marginals, with arbitrary cross-row dependence. -/
theorem randomBorelFamily_matrixBernstein_of_rowMarginals
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (d : MarginalRowIndex State Action → FiniteDistribution State) (N : ℕ) (hN : 0 < N)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (draw : Ω → MarginalMatrixSamples State Action N) (hdraw : Measurable draw)
    (hrowlaw : ∀ i : MarginalRowIndex State Action,
      μ.map (fun ω ↦ draw ω i) = (d i).sampleMeasure N)
    (family : Ω → Finset (State → ℝ))
    (hfamily : letI : MeasurableSpace (Finset (State → ℝ)) := finiteFamilyBorel
      Measurable family)
    (hindep : letI : MeasurableSpace (Finset (State → ℝ)) := finiteFamilyBorel
      letI : MeasurableSpace (MarginalRowIndex State Action → FiniteDistribution State) := marginalMatrixVectorSpace
      IndepFun family (fun ω ↦ marginalEmpiricalMatrix N hN (draw ω)) μ)
    (hV : ∀ᵐ ω ∂μ, ∀ V ∈ family ω, ∀ s, 0 ≤ V s) :
    1 - δ < μ.real {ω | ∀ i : MarginalRowIndex State Action, ∀ V ∈ family ω,
      |(marginalEmpiricalMatrix N hN (draw ω) i).expectation V - (d i).expectation V| ≤
        Real.sqrt (2 * Real.log (4 * Fintype.card State * Fintype.card Action *
          (family ω).card / δ) / N) * Real.sqrt ((d i).variance V) +
        2 * ‖V‖ * Real.log (4 * Fintype.card State * Fintype.card Action *
          (family ω).card / δ) / (3 * N)} := by
  classical
  let I := MarginalRowIndex State Action
  let m : ℝ := Fintype.card I
  have hm : 0 < m := by dsimp [m, I]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hm1 : 1 ≤ m := by dsimp [m, I]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  let η : ℝ := δ / m
  have hη : 0 < η := div_pos hδ hm
  have hη1 : η < 1 := by dsimp [η]; rw [div_lt_iff₀ hm]; linarith
  let bad (i : I) : Set Ω := {ω | bernsteinFamilyBadAt (d i) N η (family ω)
    (empiricalRow N hN (draw ω i))}
  have hrow (i : I) : Measurable (fun ω ↦ draw ω i) := (measurable_pi_apply i).comp hdraw
  have hindrow (i : I) : letI : MeasurableSpace (Finset (State → ℝ)) := finiteFamilyBorel
      letI : MeasurableSpace (FiniteDistribution State) := rowVectorSpace
      IndepFun family (fun ω ↦ empiricalRow N hN (draw ω i)) μ := by
    letI : MeasurableSpace (Finset (State → ℝ)) := finiteFamilyBorel
    letI : MeasurableSpace (FiniteDistribution State) := rowVectorSpace
    letI : MeasurableSpace (I → FiniteDistribution State) := marginalMatrixVectorSpace
    have h := hindep.comp measurable_id (marginalMatrixVectorSpace_eval i)
    exact h
  have hbadmeas (i : I) : MeasurableSet (bad i) :=
    marginalBernsteinBad_measurable (d i) N hN η _ (hrow i) family hfamily
  have hbad (i : I) : μ.real (bad i) < η := by
    have hs := (d i).randomBorelFamily_bernstein_success_gt μ N hN η hη hη1
      (fun ω ↦ draw ω i) (hrow i) (hrowlaw i) family hfamily (hindrow i) hV
    have heq : (bad i)ᶜ = {ω | ∀ V ∈ family ω,
        |(empiricalRow N hN (draw ω i)).expectation V - (d i).expectation V| ≤
          bernsteinRadius (d i) N (family ω).card η V} := by
      ext ω
      simp [bad, bernsteinFamilyBadAt, not_lt]
    have hc := measureReal_compl (μ := μ) (hbadmeas i)
    rw [heq, probReal_univ] at hc
    linarith
  have hbadall : μ.real (⋃ i : I, bad i) < δ := by
    have hi : (Finset.univ : Finset I).Nonempty := Finset.univ_nonempty
    calc
      _ ≤ ∑ i : I, μ.real (bad i) := measureReal_iUnion_fintype_le _
      _ < ∑ _i : I, η := Finset.sum_lt_sum_of_nonempty hi (fun i _ ↦ hbad i)
      _ = δ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change m * η = δ
        dsimp [η]
        field_simp
  have hlog (k : ℕ) : 4 * (k : ℝ) / η =
      4 * Fintype.card State * Fintype.card Action * k / δ := by
    dsimp [η, m, I]
    simp only [Fintype.card_prod, Nat.cast_mul]
    field_simp
  have heq : (⋃ i : I, bad i)ᶜ = {ω | ∀ i : I, ∀ V ∈ family ω,
      |(marginalEmpiricalMatrix N hN (draw ω) i).expectation V - (d i).expectation V| ≤
        Real.sqrt (2 * Real.log (4 * Fintype.card State * Fintype.card Action *
          (family ω).card / δ) / N) * Real.sqrt ((d i).variance V) +
        2 * ‖V‖ * Real.log (4 * Fintype.card State * Fintype.card Action *
          (family ω).card / δ) / (3 * N)} := by
    ext ω
    simp [bad, bernsteinFamilyBadAt, bernsteinRadius_eq_source, hlog, marginalEmpiricalMatrix, not_lt]
  have hc := measureReal_compl (μ := μ) (MeasurableSet.iUnion hbadmeas)
  rw [heq, probReal_univ] at hc
  linarith

end StatisticalRL.FiniteDistribution
