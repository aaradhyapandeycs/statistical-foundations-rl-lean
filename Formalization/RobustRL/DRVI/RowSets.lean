import Formalization.RobustRL.Ch7.TrapInstance
import Formalization.ModelFree.QLearningRobustBallCompact
import Mathlib.Topology.Order.Compact

/-!
# Row uncertainty sets and the exact row infimum (Theorems 7.2/7.4, milestone 1, R0a)

Source: `chapters/robust_RL.tex:31–48` ((s,a)-rectangular sets), `:118–131` (inner infimum of
the robust Bellman operator). For an arbitrary set `U` of rows, `rowInf U V` is the exact
infimum `inf_{q ∈ U} ⟨q, V⟩`; `Ch7.rowRobustInf ball p σ V` is `rowInf (ball p σ) V` by
definition. A row set *attains* when every infimum is a minimum. TV balls, χ² balls (both for
`σ ≥ 0`) and singletons attain.
-/

open scoped BigOperators

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7

variable {State : Type*} [Fintype State]

/-- The exact row infimum `inf_{q ∈ U} ⟨q, V⟩` over an arbitrary row set. -/
noncomputable def rowInf (U : Set (FiniteDistribution State)) (V : State → ℝ) : ℝ :=
  sInf ((fun q : FiniteDistribution State ↦ q.expectation V) '' U)

theorem rowRobustInf_eq_rowInf (ball : RowBall State) (p : FiniteDistribution State) (σ : ℝ)
    (V : State → ℝ) : rowRobustInf ball p σ V = rowInf (ball p σ) V := rfl

/-- Every infimum over the row set is attained. -/
def RowAttains (U : Set (FiniteDistribution State)) : Prop :=
  ∀ V : State → ℝ, ∃ q ∈ U, ∀ q' ∈ U, q.expectation V ≤ q'.expectation V

theorem RowAttains.nonempty {U : Set (FiniteDistribution State)} (h : RowAttains U) :
    U.Nonempty := by
  obtain ⟨q, hq, -⟩ := h 0
  exact ⟨q, hq⟩

theorem abs_expectation_le_sum (q : FiniteDistribution State) (V : State → ℝ) :
    |q.expectation V| ≤ ∑ x, |V x| := by
  apply q.abs_expectation_le
  intro x
  exact Finset.single_le_sum (f := fun y ↦ |V y|) (fun y _ ↦ abs_nonneg _) (Finset.mem_univ x)

theorem rowInf_bddBelow (U : Set (FiniteDistribution State)) (V : State → ℝ) :
    BddBelow ((fun q : FiniteDistribution State ↦ q.expectation V) '' U) := by
  refine ⟨-∑ x, |V x|, ?_⟩
  rintro _ ⟨q, -, rfl⟩
  have := abs_expectation_le_sum q V
  exact neg_le_of_abs_le this

theorem rowInf_le {U : Set (FiniteDistribution State)} {q : FiniteDistribution State}
    (hq : q ∈ U) (V : State → ℝ) : rowInf U V ≤ q.expectation V :=
  csInf_le (rowInf_bddBelow U V) ⟨q, hq, rfl⟩

theorem le_rowInf {U : Set (FiniteDistribution State)} (hU : U.Nonempty) {V : State → ℝ}
    {c : ℝ} (h : ∀ q ∈ U, c ≤ q.expectation V) : c ≤ rowInf U V := by
  apply le_csInf (hU.image _)
  rintro _ ⟨q, hq, rfl⟩
  exact h q hq

/-- Attained infimum: some row of the set realizes `rowInf`. -/
theorem exists_rowInf_eq {U : Set (FiniteDistribution State)} (hU : RowAttains U)
    (V : State → ℝ) : ∃ q ∈ U, rowInf U V = q.expectation V := by
  obtain ⟨q, hq, hmin⟩ := hU V
  refine ⟨q, hq, le_antisymm (rowInf_le hq V) (le_rowInf ⟨q, hq⟩ hmin)⟩

/-- One-sided shift bound: `V ≤ W + c` implies `rowInf V ≤ rowInf W + c`. -/
theorem rowInf_le_add {U : Set (FiniteDistribution State)} (hU : U.Nonempty)
    {V W : State → ℝ} {c : ℝ} (h : ∀ x, V x ≤ W x + c) :
    rowInf U V ≤ rowInf U W + c := by
  have : rowInf U V - c ≤ rowInf U W := by
    apply le_rowInf hU
    intro q hq
    have h1 := rowInf_le hq V
    have h2 : q.expectation V ≤ q.expectation W + c := by
      calc q.expectation V ≤ q.expectation (fun x ↦ W x + c) := q.expectation_mono h
        _ = q.expectation W + c := by rw [q.expectation_add, q.expectation_const]
    linarith
  linarith

theorem rowInf_mono {U : Set (FiniteDistribution State)} (hU : U.Nonempty)
    {V W : State → ℝ} (h : ∀ x, V x ≤ W x) : rowInf U V ≤ rowInf U W := by
  have := rowInf_le_add hU (c := 0) (fun x ↦ by simpa using h x)
  simpa using this

/-- Nonexpansiveness of the row infimum (valid for every row set, empty or not). -/
theorem abs_rowInf_sub_le (U : Set (FiniteDistribution State)) {V W : State → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ x, |V x - W x| ≤ c) : |rowInf U V - rowInf U W| ≤ c := by
  rcases U.eq_empty_or_nonempty with hE | hU
  · simp [rowInf, hE, hc]
  · have h1 := rowInf_le_add hU (V := V) (W := W) (c := c)
      (fun x ↦ by have := (abs_le.mp (h x)).2; linarith)
    have h2 := rowInf_le_add hU (V := W) (W := V) (c := c)
      (fun x ↦ by have := (abs_le.mp (h x)).1; linarith)
    exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem rowInf_const {U : Set (FiniteDistribution State)} (hU : U.Nonempty) (c : ℝ) :
    rowInf U (fun _ ↦ c) = c := by
  obtain ⟨q, hq⟩ := hU
  apply le_antisymm
  · simpa using rowInf_le hq (fun _ ↦ c)
  · exact le_rowInf ⟨q, hq⟩ (fun q' _ ↦ by simp)

theorem rowInf_bounds {U : Set (FiniteDistribution State)} (hU : U.Nonempty)
    {V : State → ℝ} {lo hi : ℝ} (hlo : ∀ x, lo ≤ V x) (hhi : ∀ x, V x ≤ hi) :
    lo ≤ rowInf U V ∧ rowInf U V ≤ hi := by
  constructor
  · have := rowInf_mono hU (V := fun _ ↦ lo) (W := V) hlo
    rwa [rowInf_const hU] at this
  · have := rowInf_mono hU (V := V) (W := fun _ ↦ hi) hhi
    rwa [rowInf_const hU] at this

theorem rowInf_singleton (p : FiniteDistribution State) (V : State → ℝ) :
    rowInf {p} V = p.expectation V := by
  simp [rowInf]

/-! ## Attainment -/

theorem rowAttains_singleton (p : FiniteDistribution State) : RowAttains {p} := by
  intro V
  exact ⟨p, rfl, fun q hq ↦ by rw [Set.mem_singleton_iff.mp hq]⟩

theorem rowAttains_ite (c : Prop) [Decidable c] {U U' : Set (FiniteDistribution State)}
    (hU : RowAttains U) (hU' : RowAttains U') : RowAttains (if c then U else U') := by
  by_cases h : c
  · simpa [h] using hU
  · simpa [h] using hU'

/-- Attainment from a compact nonempty coordinate representation of the row set. -/
theorem rowAttains_of_vectors (U : Set (FiniteDistribution State)) (C : Set (State → ℝ))
    (hC : IsCompact C) (hne : C.Nonempty)
    (hiff : ∀ v, v ∈ C ↔ ∃ d ∈ U, d.prob = v) : RowAttains U := by
  intro V
  let f : (State → ℝ) → ℝ := fun q ↦ ∑ x, q x * V x
  have hcont : ContinuousOn f C :=
    (continuous_finset_sum _ (fun x _ ↦ (continuous_apply x).mul continuous_const)).continuousOn
  obtain ⟨qmin, hmin, hminimal⟩ := hC.exists_isMinOn hne hcont
  obtain ⟨d, hd, hdeq⟩ := (hiff qmin).1 hmin
  refine ⟨d, hd, ?_⟩
  intro d' hd'
  have hv := (hiff d'.prob).2 ⟨d', hd', rfl⟩
  have := hminimal hv
  simpa [f, FiniteDistribution.expectation, hdeq] using this

/-- Coordinates of the probability simplex lie in `[0,1]`. -/
theorem simplex_closed :
    IsClosed {v : State → ℝ | (∀ x, 0 ≤ v x) ∧ ∑ x, v x = 1} := by
  have hnonneg : IsClosed {q : State → ℝ | ∀ x, 0 ≤ q x} := by
    have heq : {q : State → ℝ | ∀ x, 0 ≤ q x} = ⋂ x : State, {q : State → ℝ | 0 ≤ q x} := by
      ext q; simp
    rw [heq]
    exact isClosed_iInter (fun x ↦ isClosed_le continuous_const (continuous_apply x))
  have hsum : IsClosed {q : State → ℝ | (∑ x, q x) = 1} := by
    apply isClosed_eq _ continuous_const
    exact continuous_finset_sum _ (fun x _ ↦ continuous_apply x)
  simpa only [Set.setOf_and] using hnonneg.inter hsum

/-- The TV ball (half-L1 form) around `p` attains its row infimum for `σ ≥ 0`. -/
theorem tvBall_rowAttains (p : FiniteDistribution State) {σ : ℝ} (hσ : 0 ≤ σ) :
    RowAttains (tvBall p σ) := by
  let C : Set (State → ℝ) := {v | ((∀ x, 0 ≤ v x) ∧ ∑ x, v x = 1) ∧
    (1 / 2 : ℝ) * ∑ x, |p.prob x - v x| ≤ σ}
  have hclosed : IsClosed C := by
    have h2 : IsClosed {v : State → ℝ | (1 / 2 : ℝ) * ∑ x, |p.prob x - v x| ≤ σ} := by
      apply isClosed_le _ continuous_const
      exact continuous_const.mul (continuous_finset_sum _ (fun x _ ↦
      (continuous_const.sub (continuous_apply x)).abs))
    exact simplex_closed.inter h2
  have hC : IsCompact C := by
    apply (isCompact_Icc : IsCompact (Set.Icc (0 : State → ℝ) 1)).of_isClosed_subset hclosed
    intro q hq
    refine ⟨fun x ↦ hq.1.1 x, fun x ↦ ?_⟩
    calc q x ≤ ∑ y, q y := Finset.single_le_sum (fun y _ ↦ hq.1.1 y) (Finset.mem_univ x)
      _ = 1 := hq.1.2
  apply rowAttains_of_vectors (tvBall p σ) C hC
  · exact ⟨p.prob, ⟨p.prob_nonneg, p.sum_prob⟩, by simp [hσ]⟩
  · intro v
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩
      exact ⟨⟨v, h0, h1⟩, h2, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨d.prob_nonneg, d.sum_prob⟩, hd⟩

/-- The support-aware χ² ball attains its row infimum for `σ ≥ 0`. -/
theorem chiBall_rowAttains (p : FiniteDistribution State) {σ : ℝ} (hσ : 0 ≤ σ) :
    RowAttains (chiBall p σ) := by
  intro V
  obtain ⟨q, hq, hmin⟩ := (QLearning.qChiBall_extrema_attained p σ hσ V).2
  exact ⟨q, hq, hmin⟩

theorem tvBall_self_mem (p : FiniteDistribution State) {σ : ℝ} (hσ : 0 ≤ σ) :
    p ∈ tvBall p σ := (HorizonTrap.tvBall_trapBall hσ).self_mem p

theorem chiBall_self_mem (p : FiniteDistribution State) {σ : ℝ} (hσ : 0 ≤ σ) :
    p ∈ chiBall p σ := (HorizonTrap.chiBall_trapBall hσ).self_mem p

end StatisticalRL.RobustRL.DRVI
