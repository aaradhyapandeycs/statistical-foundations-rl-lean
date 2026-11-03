import Formalization.Generative.FiniteHorizonFittedAuxiliaryContinuation
import Formalization.Probability.BernsteinFamily
import Mathlib.Data.Nat.Log

/-! One actual-law event for all auxiliary levels and both source policy families.
The log/cardinality factor is explicit; no sharp final theorem is asserted. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance allLevelStateMeasurable : MeasurableSpace State := ⊤
local instance allLevelRowMeasurable : MeasurableSpace (FiniteDistribution State) := ⊤

/-- Any nonnegative continuation that causally factors through the future block
has the actual current-row Bernstein law. No independence premise is added. -/
theorem futureValue_row_bernstein {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (h : Fin H) (s : State) (a : Action)
    (V : Samples State Action H N → State → ℝ)
    (hnonneg : ∀ data t, 0 ≤ V data t)
    (hfuture : ∀ x data, V data = V (completeFutureData h N x (futureData h N data)))
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw E N).real {data |
      |((empiricalStage E N hN data h).transition s a).expectation (V data) -
        ((E h).transition s a).expectation (V data)| ≤
      FiniteDistribution.bernsteinRadius ((E h).transition s a) N 1 δ (V data)} := by
  classical
  let μ := samplingLaw E N
  let d := (E h).transition s a
  let x := Classical.choice (E h).state_nonempty
  let code := futureData (State := State) (Action := Action) h N
  let value : FutureCode (State := State) (Action := Action) h N → State → ℝ :=
    fun c ↦ V (completeFutureData h N x c)
  let family : FutureCode (State := State) (Action := Action) h N → Finset (State → ℝ) :=
    fun c ↦ {value c}
  let draw : Samples State Action H N → Fin N → State := fun data i ↦ data ((h,s,a),i)
  have hdraw : Measurable draw := measurable_of_countable _
  have hlaw : μ.map draw = d.sampleMeasure N := samplingLaw_row E N h s a
  have hcode : Measurable code := measurable_of_countable _
  have hrow : Measurable (fun row : Fin N → State ↦ FiniteDistribution.empiricalRow N hN row) :=
    measurable_of_countable _
  have hi : IndepFun code (fun data ↦ FiniteDistribution.empiricalRow N hN (draw data)) μ :=
    (futureData_indep_row E N h s a).comp measurable_id hrow
  have hv : ∀ᵐ data ∂μ, ∀ V ∈ family (code data), ∀ t, 0 ≤ V t := by
    apply Filter.Eventually.of_forall
    intro data V hV t
    have he : V = value (code data) := Finset.mem_singleton.mp hV
    rw [he]
    exact hnonneg _ t
  have hvmeas : MeasurableSet {c | ∀ V ∈ family c, ∀ t, 0 ≤ V t} :=
    (Set.to_countable _).measurableSet
  have hbad : ∀ row ∈ FiniteDistribution.empiricalRows N hN,
      MeasurableSet {c | FiniteDistribution.bernsteinFamilyBadAt d N δ (family c) row} :=
    fun row hrow ↦ (Set.to_countable _).measurableSet
  have hs := d.randomFamily_bernstein_success_gt μ N hN δ hδ hδ1 draw hdraw hlaw code hcode family
    hi hv hvmeas hbad
  have he (data : Samples State Action H N) : value (code data) = V data :=
    (hfuture x data).symm
  let good : Set (Samples State Action H N) := {data | ∀ V ∈ family (code data),
      |(FiniteDistribution.empiricalRow N hN (draw data)).expectation V - d.expectation V| ≤
        FiniteDistribution.bernsteinRadius d N (family (code data)).card δ V}
  let target : Set (Samples State Action H N) := {data |
      |((empiricalStage E N hN data h).transition s a).expectation (V data) -
        d.expectation (V data)| ≤
        FiniteDistribution.bernsteinRadius d N 1 δ (V data)}
  have hsub : good ⊆ target := by
    intro data hd
    have hh := hd (value (code data)) (Finset.mem_singleton_self _)
    have hcard : (family (code data)).card = 1 := Finset.card_singleton _
    rw [hcard, he data] at hh
    exact hh
  exact hs.trans_le (measureReal_mono hsub (measure_ne_top μ target))


/-- Separate the fixed-policy true continuation from the fitted-policy true
continuation. The Bool is an event index, not a policy randomization. -/
noncomputable def sourceAuxiliaryContinuation {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (fallback : Action) (fixed : ℕ → State → Action) (b : Bool) (l : ℕ) (h : Fin H)
    (data : Samples State Action H N) : State → ℝ :=
  if b then trueAuxiliaryValueAt (List.ofFn E) fixed l (h.val + 1)
    else fittedTrueAuxiliaryContinuation E N hN fallback h l data

theorem sourceAuxiliaryContinuation_nonneg {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (fallback : Action) (fixed : ℕ → State → Action) (b : Bool) (l : ℕ) (h : Fin H)
    (data : Samples State Action H N) (t : State) :
    0 ≤ sourceAuxiliaryContinuation E N hN fallback fixed b l h data t := by
  cases b
  · exact fittedTrueAuxiliaryContinuation_nonneg E N hN fallback h l data t
  · exact trueAuxiliaryValue_nonneg _ _ _ _

theorem sourceAuxiliaryContinuation_factors_future {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (fallback : Action) (fixed : ℕ → State → Action) (b : Bool) (l : ℕ) (h : Fin H)
    (x : State) (data : Samples State Action H N) :
    sourceAuxiliaryContinuation E N hN fallback fixed b l h data =
      sourceAuxiliaryContinuation E N hN fallback fixed b l h
        (completeFutureData h N x (futureData h N data)) := by
  cases b
  · exact fittedTrueAuxiliaryContinuation_factors_future E N hN fallback h l x data
  · rfl

theorem sourceAuxiliaryContinuation_row_bernstein {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (fallback : Action) (fixed : ℕ → State → Action) (b : Bool) (l : ℕ)
    (h : Fin H) (s : State) (a : Action) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw E N).real {data |
      |((empiricalStage E N hN data h).transition s a).expectation
          (sourceAuxiliaryContinuation E N hN fallback fixed b l h data) -
        ((E h).transition s a).expectation (sourceAuxiliaryContinuation E N hN fallback fixed b l h data)| ≤
      FiniteDistribution.bernsteinRadius ((E h).transition s a) N 1 δ
        (sourceAuxiliaryContinuation E N hN fallback fixed b l h data)} :=
  futureValue_row_bernstein E N hN h s a _
    (sourceAuxiliaryContinuation_nonneg E N hN fallback fixed b l h)
    (sourceAuxiliaryContinuation_factors_future E N hN fallback fixed b l h) δ hδ hδ1

/-- One event covers both policy families, every source level, and every
stage/state/action row. The confidence cost is exactly 2*K*H*S*A. -/
theorem simultaneous_sourceAuxiliaryContinuation_bernstein {H : ℕ}
    (E : Fin H → EnvironmentStage State Action) (N : ℕ) (hN : 0 < N)
    (hH : 0 < H) (fallback : Action) (fixed : ℕ → State → Action)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 - δ < (samplingLaw E N).real {data |
      ∀ (b : Bool) (l : Fin (Nat.log 2 H + 1)) (h : Fin H) (s : State) (a : Action),
      |((empiricalStage E N hN data h).transition s a).expectation
          (sourceAuxiliaryContinuation E N hN fallback fixed b l.val h data) -
        ((E h).transition s a).expectation
          (sourceAuxiliaryContinuation E N hN fallback fixed b l.val h data)| ≤
      FiniteDistribution.bernsteinRadius ((E h).transition s a) N 1
        (δ / (2 * (Nat.log 2 H + 1) * Fintype.card (Fin H × State × Action)))
        (sourceAuxiliaryContinuation E N hN fallback fixed b l.val h data)} := by
  classical
  letI : Nonempty State := (E ⟨0,hH⟩).state_nonempty
  letI : Nonempty Action := ⟨fallback⟩
  letI : Nonempty (Fin H) := ⟨⟨0,hH⟩⟩
  let K := Nat.log 2 H + 1
  letI : Nonempty (Fin K) := ⟨⟨0, Nat.zero_lt_succ _⟩⟩
  let I := Fin H × State × Action
  let J := Bool × Fin K × I
  let m : ℝ := Fintype.card J
  let η := δ / m
  let μ := samplingLaw E N
  have hm : 0 < m := by dsimp [m]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hm1 : 1 ≤ m := by dsimp [m]; exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hη : 0 < η := div_pos hδ hm
  have hη1 : η < 1 := by dsimp [η]; exact (div_lt_iff₀ hm).2 (by linarith)
  let value (i : J) (data : Samples State Action H N) : State → ℝ :=
    sourceAuxiliaryContinuation E N hN fallback fixed i.1 i.2.1.val i.2.2.1 data
  let good (i : J) : Set (Samples State Action H N) := {data |
    |((empiricalStage E N hN data i.2.2.1).transition i.2.2.2.1 i.2.2.2.2).expectation (value i data) -
      ((E i.2.2.1).transition i.2.2.2.1 i.2.2.2.2).expectation (value i data)| ≤
      FiniteDistribution.bernsteinRadius ((E i.2.2.1).transition i.2.2.2.1 i.2.2.2.2) N 1 η (value i data)}
  let bad (i : J) := (good i)ᶜ
  have hs (i : J) : 1 - η < μ.real (good i) := by
    rcases i with ⟨b,l,h,s,a⟩
    exact sourceAuxiliaryContinuation_row_bernstein E N hN fallback fixed b l.val h s a η hη hη1
  have hb (i : J) : μ.real (bad i) < η := by
    have hp := measureReal_compl (μ := μ) ((Set.to_countable (good i)).measurableSet)
    rw [probReal_univ] at hp
    have hh := hs i
    change μ.real (good i)ᶜ < η
    linarith
  have hu : μ.real (⋃ i : J, bad i) < δ := by
    calc
      _ ≤ ∑ i : J, μ.real (bad i) := measureReal_iUnion_fintype_le _
      _ < ∑ _i : J, η := Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ ↦ hb i)
      _ = δ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change m * (δ / m) = δ
        field_simp [hm.ne']
  have hηeq : η = δ / (2 * (Nat.log 2 H + 1) * Fintype.card I) := by
    dsimp [η, m, J, K]
    simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat,
      Nat.cast_add, Nat.cast_one]
    ring
  have hcomp := measureReal_compl (μ := μ) ((Set.to_countable (⋃ i : J, bad i)).measurableSet)
  rw [probReal_univ] at hcomp
  have hp : 1 - δ < μ.real (⋃ i : J, bad i)ᶜ := by linarith
  apply hp.trans_le
  apply measureReal_mono _ (measure_ne_top μ _)
  intro data hd b l h s a
  have hh : data ∈ good (b,l,(h,s,a)) := by
    by_contra hn
    exact hd (Set.mem_iUnion.mpr ⟨(b,l,(h,s,a)), hn⟩)
  dsimp only [good, value] at hh
  rw [hηeq] at hh
  exact hh

end StatisticalRL.FiniteHorizonGenerative
