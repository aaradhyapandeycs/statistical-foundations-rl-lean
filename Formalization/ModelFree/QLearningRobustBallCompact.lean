import Formalization.ModelFree.QLearningRobustContraction
import Mathlib.Topology.Order.Compact

/-! compact support-aware χ² rows in actual real coordinates. -/
open scoped BigOperators
namespace StatisticalRL.QLearning
variable {State : Type*} [Fintype State]

/-- Coordinate χ² expression on the fixed positive nominal support. -/
noncomputable def qChiSquaredVector (p : FiniteDistribution State) (q : State → ℝ) : ℝ :=
  ∑ x ∈ Finset.univ.filter (fun x ↦ 0 < p.prob x), (q x - p.prob x)^2 / p.prob x

/-- Source uncertainty ball represented as a subset of the finite real vector
space. Zero nominal atoms have an explicit zero-mass constraint. -/
noncomputable def qChiBallVectors (p : FiniteDistribution State) (ρ : ℝ) : Set (State → ℝ) :=
  {q | (∀ x, 0 ≤ q x) ∧ (∑ x, q x) = 1 ∧
    (∀ x, p.prob x = 0 → q x = 0) ∧ qChiSquaredVector p q ≤ ρ}

/-- The vector representation is precisely the existing source ball. -/
theorem qChiBallVectors_iff (p : FiniteDistribution State) (ρ : ℝ) (q : State → ℝ) :
    q ∈ qChiBallVectors p ρ ↔
      ∃ d : FiniteDistribution State, d ∈ qChiBall p ρ ∧ d.prob = q := by
  constructor
  · rintro ⟨hq0, hsum, hsupport, hchi⟩
    let d : FiniteDistribution State := ⟨q, hq0, hsum⟩
    exact ⟨d, ⟨hsupport, hchi⟩, rfl⟩
  · rintro ⟨d, ⟨hsupport, hchi⟩, rfl⟩
    exact ⟨d.prob_nonneg, d.sum_prob, hsupport, hchi⟩

/-- χ² is continuous in q because p is fixed; no division by a varying or
zero denominator occurs in the filtered finite sum. -/
theorem qChiSquaredVector_continuous (p : FiniteDistribution State) :
    Continuous (qChiSquaredVector p) := by
  unfold qChiSquaredVector
  apply continuous_finset_sum
  intro x hx
  fun_prop

/-- The support-aware uncertainty ball is closed in real vector coordinates. -/
theorem qChiBallVectors_closed (p : FiniteDistribution State) (ρ : ℝ) :
    IsClosed (qChiBallVectors p ρ) := by
  have hnonneg : IsClosed {q : State → ℝ | ∀ x, 0 ≤ q x} := by
    have heq : {q : State → ℝ | ∀ x, 0 ≤ q x} =
        ⋂ x : State, {q : State → ℝ | 0 ≤ q x} := by ext q; simp
    rw [heq]
    exact isClosed_iInter (fun x ↦ isClosed_le continuous_const (continuous_apply x))
  have hsum : IsClosed {q : State → ℝ | (∑ x, q x) = 1} := by
    apply isClosed_eq _ continuous_const
    exact continuous_finset_sum _ (fun x hx ↦ continuous_apply x)
  have hsupport : IsClosed {q : State → ℝ | ∀ x, p.prob x = 0 → q x = 0} := by
    have heq : {q : State → ℝ | ∀ x, p.prob x = 0 → q x = 0} =
        ⋂ x : State, {q : State → ℝ | p.prob x = 0 → q x = 0} := by ext q; simp
    rw [heq]
    apply isClosed_iInter
    intro x
    by_cases hp : p.prob x = 0
    · simpa [hp] using isClosed_eq (continuous_apply x) continuous_const
    · simp [hp]
  have hχ : IsClosed {q : State → ℝ | qChiSquaredVector p q ≤ ρ} :=
    isClosed_le (qChiSquaredVector_continuous p) continuous_const
  simpa only [qChiBallVectors, Set.setOf_and] using hnonneg.inter (hsum.inter (hsupport.inter hχ))

/-- Each probability coordinate is at most one. -/
theorem qChiBallVectors_coord_le_one (p : FiniteDistribution State) (ρ : ℝ)
    (q : State → ℝ) (hq : q ∈ qChiBallVectors p ρ) (x : State) : q x ≤ 1 := by
  have hq0 := hq.1
  calc
    q x ≤ ∑ y, q y := Finset.single_le_sum (fun y hy ↦ hq0 y) (Finset.mem_univ x)
    _ = 1 := hq.2.1

/-- Finite simplex intersection and support constraints are compact. -/
theorem qChiBallVectors_compact (p : FiniteDistribution State) (ρ : ℝ) :
    IsCompact (qChiBallVectors p ρ) := by
  apply (isCompact_Icc : IsCompact (Set.Icc (0 : State → ℝ) 1)).of_isClosed_subset
    (qChiBallVectors_closed p ρ)
  intro q hq
  constructor
  · intro x
    exact hq.1 x
  · intro x
    exact qChiBallVectors_coord_le_one p ρ q hq x

/-- The actual finite expectation has continuous dependence on row coordinates. -/
theorem qVectorExpectation_continuous (v : State → ℝ) :
    Continuous (fun q : State → ℝ ↦ ∑ x, q x * v x) := by
  exact continuous_finset_sum _ (fun x hx ↦ (continuous_apply x).mul continuous_const)

/-- Both source extrema are attained by support-respecting finite distributions. -/
theorem qChiBall_extrema_attained (p : FiniteDistribution State) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (v : State → ℝ) :
    (∃ q ∈ qChiBall p ρ, ∀ d ∈ qChiBall p ρ, d.expectation v ≤ q.expectation v) ∧
    (∃ q ∈ qChiBall p ρ, ∀ d ∈ qChiBall p ρ, q.expectation v ≤ d.expectation v) := by
  have hnonempty : (qChiBallVectors p ρ).Nonempty :=
    ⟨p.prob, (qChiBallVectors_iff p ρ p.prob).2 ⟨p, qChiBall_self p ρ hρ, rfl⟩⟩
  have hc := qChiBallVectors_compact p ρ
  let f : (State → ℝ) → ℝ := fun q ↦ ∑ x, q x * v x
  have hcont : ContinuousOn f (qChiBallVectors p ρ) := (qVectorExpectation_continuous v).continuousOn
  obtain ⟨qmax, hmax, hmaximal⟩ := hc.exists_isMaxOn hnonempty hcont
  obtain ⟨qmin, hmin, hminimal⟩ := hc.exists_isMinOn hnonempty hcont
  obtain ⟨dmax, hdmax, hdmaxeq⟩ := (qChiBallVectors_iff p ρ qmax).1 hmax
  obtain ⟨dmin, hdmin, hdmineq⟩ := (qChiBallVectors_iff p ρ qmin).1 hmin
  constructor
  · refine ⟨dmax, hdmax, ?_⟩
    intro d hd
    have hdv := (qChiBallVectors_iff p ρ d.prob).2 ⟨d, hd, rfl⟩
    simpa [f, FiniteDistribution.expectation, hdmaxeq] using hmaximal hdv
  · refine ⟨dmin, hdmin, ?_⟩
    intro d hd
    have hdv := (qChiBallVectors_iff p ρ d.prob).2 ⟨d, hd, rfl⟩
    simpa [f, FiniteDistribution.expectation, hdmineq] using hminimal hdv

end StatisticalRL.QLearning
