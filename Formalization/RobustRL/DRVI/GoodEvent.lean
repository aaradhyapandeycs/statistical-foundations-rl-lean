import Formalization.RobustRL.DRVI.RobustAbsorbing
import Formalization.Generative.PolicyLearningLeaveOneOutBernstein

/-!
# The concentration event (milestone 4, module E; plan §3.6)

For every row `(x,a)` let `G x a k code` (`k` in a fixed finite index type `ι`) be nonnegative
vectors computed from the off-state code of `x` only. Under the product sampling law, with
probability `> 1 − δ`, simultaneously for every row and every index,
`|⟨p̂_{xa} − p_{xa}, G⟩| ≤ √(2ℓ Var_{p_{xa}}(G)/N) + 2Bℓ/(3N)`, `ℓ = log(4|ι|SA/δ)`, where `B`
bounds the sup norm. This is `randomFamily_bernstein_success_gt` (pattern of
`PolicyLearningLeaveOneOutBernstein`) plus a union bound over the `SA` rows.
-/

open scoped BigOperators
open MeasureTheory ProbabilityTheory

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7
open StatisticalRL.ModelBasedPolicyLearning

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance goodEventStateMeasurable : MeasurableSpace State := ⊤
local instance goodEventRowMeasurable : MeasurableSpace (FiniteDistribution State) := ⊤

/-- The finite set of distinct members of an indexed family. -/
noncomputable def indexedFamily {ι : Type*} [Fintype ι] (G : ι → State → ℝ) :
    Finset (State → ℝ) := by
  classical
  exact Finset.univ.image G

theorem mem_indexedFamily {ι : Type*} [Fintype ι] (G : ι → State → ℝ) (k : ι) :
    G k ∈ indexedFamily G := by
  classical
  unfold indexedFamily
  exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, rfl⟩

theorem indexedFamily_card_le {ι : Type*} [Fintype ι] (G : ι → State → ℝ) :
    (indexedFamily G).card ≤ Fintype.card ι := by
  classical
  unfold indexedFamily
  exact (Finset.card_image_le).trans_eq Finset.card_univ

/-- One-row simultaneous Bernstein bound for an off-state-indexed family. -/
theorem row_indexed_bernstein {ι : Type*} [Fintype ι] (M : DiscountedMDP State Action) (N : ℕ)
    (hN : 0 < N) (x : State) (a : Action)
    (G : ι → OffStateCode (Action := Action) x N → State → ℝ) (hG : ∀ k c s, 0 ≤ G k c s)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw M N).real {data | ∀ V ∈
        indexedFamily (fun k ↦ G k (offStateData x N data)),
      |(empiricalRow N hN data x a).expectation V - (M.transition x a).expectation V| ≤
        FiniteDistribution.bernsteinRadius (M.transition x a) N
          (indexedFamily (fun k ↦ G k (offStateData x N data))).card δ V} := by
  classical
  let μ := samplingLaw M N
  let d := M.transition x a
  let draw : Samples State Action N → Fin N → State := fun data i ↦ data ((x,a),i)
  let code := offStateData (Action := Action) x N
  let family : OffStateCode (Action := Action) x N → Finset (State → ℝ) :=
    fun c ↦ indexedFamily (fun k ↦ G k c)
  have hdraw : Measurable draw := measurable_of_countable _
  have hlaw : μ.map draw = d.sampleMeasure N := samplingLaw_stateActionRow M N x a
  have hcode : Measurable code := offStateData_measurable x N
  have hindep : IndepFun code (fun data ↦ FiniteDistribution.empiricalRow N hN (draw data)) μ :=
    offStateData_indep_empiricalRow M N hN x a
  have hV : ∀ᵐ data ∂μ, ∀ V ∈ family (code data), ∀ s, 0 ≤ V s := by
    refine Filter.Eventually.of_forall (fun data V hV s ↦ ?_)
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hV
    exact hG k _ s
  have hVmeas : MeasurableSet {c | ∀ V ∈ family c, ∀ s, 0 ≤ V s} :=
    (Set.to_countable _).measurableSet
  have hbad : ∀ row ∈ FiniteDistribution.empiricalRows N hN,
      MeasurableSet {c | FiniteDistribution.bernsteinFamilyBadAt d N δ (family c) row} := by
    intro row _
    exact (Set.to_countable _).measurableSet
  exact d.randomFamily_bernstein_success_gt μ N hN δ hδ hδ1 draw hdraw hlaw code hcode family
    hindep hV hVmeas hbad

/-- Relaxing the Bernstein radius from the actual family size `k ≤ K`. -/
theorem bernsteinRadius_le_of_card (d : FiniteDistribution State) (N : ℕ) (hN : 0 < N)
    {k K : ℕ} (hk : 1 ≤ k) (hkK : k ≤ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1)
    (V : State → ℝ) {B : ℝ} (hV : ‖V‖ ≤ B) :
    FiniteDistribution.bernsteinRadius d N k δ V ≤
      Real.sqrt (2 * Real.log (4 * K / δ) * d.variance V / N) +
        2 * B * Real.log (4 * K / δ) / (3 * N) := by
  unfold FiniteDistribution.bernsteinRadius
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkKR : (k : ℝ) ≤ K := by exact_mod_cast hkK
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : 1 < 4 * (k : ℝ) / δ := by rw [lt_div_iff₀ hδ]; nlinarith
  have hl0 : 0 ≤ Real.log (4 * (k : ℝ) / δ) := (Real.log_pos h1).le
  have hlog : Real.log (4 * (k : ℝ) / δ) ≤ Real.log (4 * K / δ) := by
    apply Real.log_le_log (by linarith)
    exact div_le_div_of_nonneg_right (by linarith) hδ.le
  have hvar := d.variance_nonneg V
  apply add_le_add
  · apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ hNR.le
    nlinarith
  · apply div_le_div_of_nonneg_right _ (by positivity)
    have hn := norm_nonneg V
    have := mul_le_mul hV hlog hl0 (hn.trans hV)
    nlinarith

/-- The all-row good event (plan §3.6), with an index-dependent sup-norm bound `Bf k`. -/
theorem allRows_indexed_bernstein' {ι : Type*} [Fintype ι] [Nonempty ι]
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (G : ∀ x : State, Action → ι → OffStateCode (Action := Action) x N → State → ℝ)
    (hG : ∀ x a k c s, 0 ≤ G x a k c s) (Bf : ι → ℝ) (hGB : ∀ x a k c, ‖G x a k c‖ ≤ Bf k)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw M N).real {data | ∀ (x : State) (a : Action) (k : ι),
      |(empiricalRow N hN data x a).expectation (G x a k (offStateData x N data)) -
        (M.transition x a).expectation (G x a k (offStateData x N data))| ≤
      Real.sqrt (2 * Real.log (4 * Fintype.card ι * (Fintype.card State * Fintype.card Action) / δ) *
          (M.transition x a).variance (G x a k (offStateData x N data)) / N) +
        2 * Bf k * Real.log (4 * Fintype.card ι * (Fintype.card State * Fintype.card Action) / δ) /
          (3 * N)} := by
  classical
  letI : Nonempty State := M.state_nonempty
  letI : Nonempty Action := M.action_nonempty
  let μ := samplingLaw M N
  let S : ℝ := Fintype.card State
  let A : ℝ := Fintype.card Action
  let η := δ / (S * A)
  have hS1 : 1 ≤ S := by dsimp [S]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hA1 : 1 ≤ A := by dsimp [A]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hSA : 1 ≤ S * A := by nlinarith
  have hη : 0 < η := by dsimp [η]; positivity
  have hη1 : η < 1 := by
    dsimp [η]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  have hlogeq : Real.log (4 * Fintype.card ι / η) =
      Real.log (4 * Fintype.card ι * (Fintype.card State * Fintype.card Action) / δ) := by
    congr 1
    dsimp [η, S, A]
    field_simp
  let rowgood (x : State) (a : Action) : Set (Samples State Action N) := {data | ∀ V ∈
        indexedFamily (fun k ↦ G x a k (offStateData x N data)),
      |(empiricalRow N hN data x a).expectation V - (M.transition x a).expectation V| ≤
        FiniteDistribution.bernsteinRadius (M.transition x a) N
          (indexedFamily (fun k ↦ G x a k (offStateData x N data))).card η V}
  let rowsource (x : State) (a : Action) : Set (Samples State Action N) := {data |
    ∀ k : ι,
      |(empiricalRow N hN data x a).expectation (G x a k (offStateData x N data)) -
        (M.transition x a).expectation (G x a k (offStateData x N data))| ≤
      Real.sqrt (2 * Real.log (4 * Fintype.card ι * (Fintype.card State * Fintype.card Action) / δ) *
          (M.transition x a).variance (G x a k (offStateData x N data)) / N) +
        2 * Bf k * Real.log (4 * Fintype.card ι * (Fintype.card State * Fintype.card Action) / δ) /
          (3 * N)}
  have hrow (x : State) (a : Action) : 1 - η < μ.real (rowsource x a) := by
    have hs : 1 - η < μ.real (rowgood x a) :=
      row_indexed_bernstein M N hN x a (G x a) (hG x a) η hη hη1
    have hsub : rowgood x a ⊆ rowsource x a := by
      intro data hd k
      have hmem := mem_indexedFamily (fun k ↦ G x a k (offStateData x N data)) k
      have hcard1 : 1 ≤ (indexedFamily (fun k ↦ G x a k (offStateData x N data))).card :=
        Finset.card_pos.mpr ⟨_, hmem⟩
      have hle := bernsteinRadius_le_of_card (M.transition x a) N hN hcard1
        (indexedFamily_card_le _) hη hη1 _ (hGB x a k (offStateData x N data))
      rw [hlogeq] at hle
      exact (hd _ hmem).trans hle
    exact hs.trans_le (measureReal_mono hsub (measure_ne_top μ (rowsource x a)))
  let bad (p : State × Action) : Set (Samples State Action N) := (rowsource p.1 p.2)ᶜ
  have hbad (p : State × Action) : μ.real (bad p) < η := by
    have hc := measureReal_compl (μ := μ) ((Set.to_countable (rowsource p.1 p.2)).measurableSet)
    rw [probReal_univ] at hc
    have hs := hrow p.1 p.2
    change μ.real (rowsource p.1 p.2)ᶜ < η
    linarith
  have hbadall : μ.real (⋃ p : State × Action, bad p) < δ := by
    calc
      _ ≤ ∑ p : State × Action, μ.real (bad p) := measureReal_iUnion_fintype_le _
      _ < ∑ _p : State × Action, η :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun p _ ↦ hbad p)
      _ = δ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
          Nat.cast_mul]
        change (S * A) * η = δ
        dsimp [η]
        field_simp
  let target : Set (Samples State Action N) := {data | ∀ (x : State) (a : Action) (k : ι),
      |(empiricalRow N hN data x a).expectation (G x a k (offStateData x N data)) -
        (M.transition x a).expectation (G x a k (offStateData x N data))| ≤
      Real.sqrt (2 * Real.log (4 * Fintype.card ι * (Fintype.card State * Fintype.card Action) / δ) *
          (M.transition x a).variance (G x a k (offStateData x N data)) / N) +
        2 * Bf k * Real.log (4 * Fintype.card ι * (Fintype.card State * Fintype.card Action) / δ) /
          (3 * N)}
  have hsub : (⋃ p : State × Action, bad p)ᶜ ⊆ target := by
    intro data hd x a k
    have hrowgood : data ∈ rowsource x a := by
      by_contra h
      exact hd (Set.mem_iUnion.mpr ⟨(x,a), h⟩)
    exact hrowgood k
  have hmono := measureReal_mono hsub (measure_ne_top μ target)
  have hc := measureReal_compl (μ := μ)
    ((Set.to_countable (⋃ p : State × Action, bad p)).measurableSet)
  rw [probReal_univ] at hc
  change 1 - δ < μ.real target
  linarith

/-- The all-row good event with a uniform sup-norm bound `B`. -/
theorem allRows_indexed_bernstein {ι : Type*} [Fintype ι] [Nonempty ι]
    (M : DiscountedMDP State Action) (N : ℕ) (hN : 0 < N)
    (G : ∀ x : State, Action → ι → OffStateCode (Action := Action) x N → State → ℝ)
    (hG : ∀ x a k c s, 0 ≤ G x a k c s) {B : ℝ} (hGB : ∀ x a k c, ‖G x a k c‖ ≤ B)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw M N).real {data | ∀ (x : State) (a : Action) (k : ι),
      |(empiricalRow N hN data x a).expectation (G x a k (offStateData x N data)) -
        (M.transition x a).expectation (G x a k (offStateData x N data))| ≤
      Real.sqrt (2 * Real.log (4 * Fintype.card ι * (Fintype.card State * Fintype.card Action) / δ) *
          (M.transition x a).variance (G x a k (offStateData x N data)) / N) +
        2 * B * Real.log (4 * Fintype.card ι * (Fintype.card State * Fintype.card Action) / δ) /
          (3 * N)} :=
  allRows_indexed_bernstein' M N hN G hG (fun _ ↦ B) hGB δ hδ hδ1

end StatisticalRL.RobustRL.DRVI
