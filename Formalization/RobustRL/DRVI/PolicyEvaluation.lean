import Formalization.RobustRL.DRVI.RowSets
import Formalization.RobustRL.LowerBounds.LowerBound73Values
import Formalization.MDP.PrefixValueBridge
import Formalization.Analysis.Contraction

/-!
# Robust policy evaluation for generic row-set families (milestone 1, R0b)

Source: `chapters/robust_RL.tex:71–84` (robust value `V^{π,σ} = inf_P V^{π,P}`), `:103–117`
(robust Bellman consistency) and `:132–133` (unique fixed point, γ-contraction; cited there).

For a family `U s a` of row sets, the robust policy operator is
`T^π V (s) = Σ_a π(a|s) [r(s,a) + γ inf_{q ∈ U s a} ⟨q, V⟩]`. It is monotone and shifts by at
most `γ c` under a shift `c` (`ShiftBound`), hence a γ-contraction with a unique fixed point
`policyFix`. When every row set attains its infimum, the robust value
`inf_{K admissible} V^{π,K}` (actual infinite-trajectory values) equals that fixed point and the
infimum is attained by a worst-case kernel.
-/

open scoped BigOperators NNReal

set_option linter.unusedSectionVars false

namespace StatisticalRL.RobustRL.DRVI

open StatisticalRL.RobustRL.Ch7

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- A generic `(s,a)`-rectangular family of row sets. -/
abbrev RowFamily (State Action : Type*) [Fintype State] :=
  State → Action → Set (FiniteDistribution State)

/-- The ball family `U s a = ball (P^0_{s,a}) σ` of an RMDP. -/
def ballFamily (ball : RowBall State) (M : DiscountedMDP State Action) (σ : ℝ) :
    RowFamily State Action :=
  fun s a ↦ ball (M.transition s a) σ

/-! ## Shift-bounded operators -/

/-- A (monotone) operator whose output moves by at most `γ c` when the input is shifted
up by `c ≥ 0`. -/
def ShiftBound (γ : ℝ) (T : (State → ℝ) → State → ℝ) : Prop :=
  ∀ V W : State → ℝ, ∀ c : ℝ, 0 ≤ c → (∀ x, V x ≤ W x + c) → ∀ s, T V s ≤ T W s + γ * c

section ShiftBound

variable {γ : ℝ} {T : (State → ℝ) → State → ℝ}

theorem ShiftBound.abs_sub_le (hT : ShiftBound γ T) {V W : State → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, |V x - W x| ≤ c) (s : State) : |T V s - T W s| ≤ γ * c := by
  have h1 := hT V W c hc (fun x ↦ by have := (abs_le.mp (h x)).2; linarith) s
  have h2 := hT W V c hc (fun x ↦ by have := (abs_le.mp (h x)).1; linarith) s
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem ShiftBound.norm_sub_le (hT : ShiftBound γ T) (hγ : 0 ≤ γ) (V W : State → ℝ) :
    ‖T V - T W‖ ≤ γ * ‖V - W‖ := by
  have hc : 0 ≤ γ * ‖V - W‖ := mul_nonneg hγ (norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg hc).2
  intro s
  rw [Pi.sub_apply, Real.norm_eq_abs]
  apply hT.abs_sub_le (norm_nonneg _) _ s
  intro x
  simpa only [Pi.sub_apply, Real.norm_eq_abs] using norm_le_pi_norm (V - W) x

/-- Sub-solutions lie below fixed points. -/
theorem ShiftBound.le_of_sub (hT : ShiftBound γ T) (hγ : γ < 1) [Nonempty State]
    {F W : State → ℝ} (hF : T F = F) (hW : ∀ s, W s ≤ T W s) : ∀ s, W s ≤ F s := by
  obtain ⟨s₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun t ↦ W t - F t)
    Finset.univ_nonempty
  set m := W s₀ - F s₀
  by_contra hcon
  push_neg at hcon
  obtain ⟨s, hs⟩ := hcon
  have hm : 0 < m := lt_of_lt_of_le (by linarith) (hmax s (Finset.mem_univ s))
  have hstep := hT W F m hm.le (fun x ↦ by have := hmax x (Finset.mem_univ x); linarith) s₀
  have h1 := hW s₀
  rw [hF] at hstep
  have : m ≤ γ * m := by simp only [m] at *; linarith
  nlinarith

/-- Super-solutions lie above fixed points. -/
theorem ShiftBound.ge_of_super (hT : ShiftBound γ T) (hγ : γ < 1) [Nonempty State]
    {F W : State → ℝ} (hF : T F = F) (hW : ∀ s, T W s ≤ W s) : ∀ s, F s ≤ W s := by
  obtain ⟨s₀, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun t ↦ F t - W t)
    Finset.univ_nonempty
  set m := F s₀ - W s₀
  by_contra hcon
  push_neg at hcon
  obtain ⟨s, hs⟩ := hcon
  have hm : 0 < m := lt_of_lt_of_le (by linarith) (hmax s (Finset.mem_univ s))
  have hstep := hT F W m hm.le (fun x ↦ by have := hmax x (Finset.mem_univ x); linarith) s₀
  have h1 := hW s₀
  rw [hF] at hstep
  have : m ≤ γ * m := by simp only [m] at *; linarith
  nlinarith

theorem ShiftBound.contracting (hT : ShiftBound γ T) (hγ0 : 0 ≤ γ) (hγ : γ < 1) :
    ContractingWith ⟨γ, hγ0⟩ T := by
  refine ⟨hγ, ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro V W
  simpa only [dist_eq_norm, NNReal.coe_mk] using hT.norm_sub_le hγ0 V W

theorem ShiftBound.exists_unique (hT : ShiftBound γ T) (hγ0 : 0 ≤ γ) (hγ : γ < 1) :
    ∃! F : State → ℝ, T F = F :=
  StatisticalRL.Analysis.contraction_exists_unique (hT.contracting hγ0 hγ)

end ShiftBound

/-! ## Robust policy operator -/

/-- Robust policy Bellman operator `T^π V(s) = E_{a∼π(s)}[r(s,a) + γ inf_{q ∈ U s a} ⟨q,V⟩]`. -/
noncomputable def policyOp (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V : State → ℝ) (s : State) : ℝ :=
  (π s).expectation (fun a ↦ M.reward s a + M.discount * rowInf (U s a) V)

theorem policyOp_shiftBound (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : ShiftBound M.discount (policyOp U M π) := by
  intro V W c hc h s
  unfold policyOp
  have hrow : ∀ a, M.reward s a + M.discount * rowInf (U s a) V ≤
      (M.reward s a + M.discount * rowInf (U s a) W) + M.discount * c := by
    intro a
    have : rowInf (U s a) V ≤ rowInf (U s a) W + c := by
      rcases (U s a).eq_empty_or_nonempty with hE | hU
      · simp [rowInf, hE, hc]
      · exact rowInf_le_add hU h
    nlinarith [M.discount_nonneg]
  calc (π s).expectation (fun a ↦ M.reward s a + M.discount * rowInf (U s a) V)
      ≤ (π s).expectation (fun a ↦ (M.reward s a + M.discount * rowInf (U s a) W) +
          M.discount * c) := (π s).expectation_mono hrow
    _ = _ := by rw [(π s).expectation_add, (π s).expectation_const]

/-- The unique fixed point of the robust policy operator. -/
noncomputable def policyFix (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : State → ℝ :=
  Classical.choose ((policyOp_shiftBound U M π).exists_unique M.discount_nonneg
    M.discount_lt_one)

theorem policyFix_spec (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) : policyOp U M π (policyFix U M π) = policyFix U M π :=
  (Classical.choose_spec ((policyOp_shiftBound U M π).exists_unique M.discount_nonneg
    M.discount_lt_one)).1

theorem eq_policyFix (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) {V : State → ℝ} (hV : policyOp U M π V = V) :
    V = policyFix U M π :=
  (Classical.choose_spec ((policyOp_shiftBound U M π).exists_unique M.discount_nonneg
    M.discount_lt_one)).2 V hV

theorem policyOp_detPolicy (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (f : State → Action) (V : State → ℝ) (s : State) :
    policyOp U M (detPolicy f) V s = M.reward s (f s) + M.discount * rowInf (U s (f s)) V := by
  simp [policyOp, detPolicy, EnvironmentStage.expectation_pointMass]

/-- Fixed points of the robust policy operator lie in `[0, 1/(1-γ)]`. -/
theorem policyFix_bounds (U : RowFamily State Action) (hU : ∀ s a, (U s a).Nonempty)
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action) (s : State) :
    0 ≤ policyFix U M π s ∧ policyFix U M π s ≤ 1 / (1 - M.discount) := by
  haveI := M.state_nonempty
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  have hT := policyOp_shiftBound U M π
  have hF := policyFix_spec U M π
  constructor
  · refine hT.le_of_sub hγ1 hF (W := fun _ ↦ 0) (fun s ↦ ?_) s
    unfold policyOp
    apply (π s).expectation_nonneg
    intro a
    rw [rowInf_const (hU s a)]
    simpa using M.reward_nonneg s a
  · refine hT.ge_of_super hγ1 hF (W := fun _ ↦ 1 / (1 - M.discount)) (fun s ↦ ?_) s
    unfold policyOp
    apply (π s).expectation_le_const
    intro a
    rw [rowInf_const (hU s a)]
    have hr := M.reward_le_one s a
    have hpos : 0 < 1 - M.discount := by linarith
    have key : M.discount * (1 / (1 - M.discount)) = 1 / (1 - M.discount) - 1 := by
      field_simp; ring
    linarith

/-! ## Robust value = fixed point (R0b) -/

/-- Robust value over an arbitrary row family:
`inf_{K : K s a ∈ U s a} V^{π,K}(s)`, with actual infinite-trajectory values. -/
noncomputable def familyRobustValue (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (s : State) : ℝ :=
  sInf {v | ∃ K : State → Action → FiniteDistribution State, (∀ s a, K s a ∈ U s a) ∧
    v = (withKernel M K).trajectoryExpectedValue π s}

theorem robustPolicyValue_eq_familyRobustValue (ball : RowBall State)
    (M : DiscountedMDP State Action) (σ : ℝ) (π : StationaryPolicy State Action) :
    robustPolicyValue ball M σ π = familyRobustValue (ballFamily ball M σ) M π := rfl

/-- A worst-case kernel for a value vector: every row attains the row infimum. -/
noncomputable def worstKernel (U : RowFamily State Action) (hU : ∀ s a, RowAttains (U s a))
    (V : State → ℝ) (s : State) (a : Action) : FiniteDistribution State :=
  Classical.choose (exists_rowInf_eq (hU s a) V)

theorem worstKernel_mem (U : RowFamily State Action) (hU : ∀ s a, RowAttains (U s a))
    (V : State → ℝ) (s : State) (a : Action) : worstKernel U hU V s a ∈ U s a :=
  (Classical.choose_spec (exists_rowInf_eq (hU s a) V)).1

theorem worstKernel_spec (U : RowFamily State Action) (hU : ∀ s a, RowAttains (U s a))
    (V : State → ℝ) (s : State) (a : Action) :
    rowInf (U s a) V = (worstKernel U hU V s a).expectation V :=
  (Classical.choose_spec (exists_rowInf_eq (hU s a) V)).2

/-- For an admissible kernel the robust operator is below the kernel's Bellman operator. -/
theorem policyOp_le_valueBellman (U : RowFamily State Action) (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) {K : State → Action → FiniteDistribution State}
    (hK : ∀ s a, K s a ∈ U s a) (V : State → ℝ) (s : State) :
    policyOp U M π V s ≤ (withKernel M K).valueBellman π V s := by
  rw [LowerBound73.valueBellman_withKernel]
  apply (π s).expectation_mono
  intro a
  have := rowInf_le (hK s a) V
  nlinarith [M.discount_nonneg]

theorem policyOp_eq_valueBellman_worst (U : RowFamily State Action)
    (hU : ∀ s a, RowAttains (U s a)) (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (V : State → ℝ) :
    (withKernel M (worstKernel U hU V)).valueBellman π V = policyOp U M π V := by
  funext s
  rw [LowerBound73.valueBellman_withKernel]
  unfold policyOp
  congr 1
  funext a
  rw [worstKernel_spec U hU V s a]

/-- Robust Bellman consistency (R0b): the robust value of a stationary policy is the unique
fixed point of the robust policy operator, and the infimum over admissible kernels is attained
by the worst-case kernel of the fixed point. -/
theorem familyRobustValue_eq_policyFix (U : RowFamily State Action)
    (hU : ∀ s a, RowAttains (U s a)) (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) :
    familyRobustValue U M π = policyFix U M π ∧
      (withKernel M (worstKernel U hU (policyFix U M π))).trajectoryExpectedValue π =
        policyFix U M π := by
  haveI := M.state_nonempty
  set F := policyFix U M π with hFdef
  set Kw := worstKernel U hU F
  have hKw : (withKernel M Kw).trajectoryExpectedValue π = F := by
    rw [DiscountedMDP.trajectoryExpectedValue_eq_valueFixedPoint]
    symm
    apply ((withKernel M Kw).valueFixedPoint_characterization π F).1
    rw [policyOp_eq_valueBellman_worst U hU M π F]
    exact policyFix_spec U M π
  refine ⟨?_, hKw⟩
  funext s
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨Kw, worstKernel_mem U hU F, by rw [hKw]⟩
  · rintro v ⟨K, hK, rfl⟩
    have hT := policyOp_shiftBound U M π
    refine hT.ge_of_super M.discount_lt_one (policyFix_spec U M π) (fun t ↦ ?_) s
    have hfix : (withKernel M K).valueBellman π ((withKernel M K).trajectoryExpectedValue π) =
        (withKernel M K).trajectoryExpectedValue π := by
      rw [DiscountedMDP.trajectoryExpectedValue_eq_valueFixedPoint]
      exact (withKernel M K).valueFixedPoint_spec π
    calc policyOp U M π ((withKernel M K).trajectoryExpectedValue π) t
        ≤ (withKernel M K).valueBellman π ((withKernel M K).trajectoryExpectedValue π) t :=
          policyOp_le_valueBellman U M π hK _ t
      _ = _ := by rw [hfix]

/-- R0b for ball families: `V^{π,σ} = policyFix`. -/
theorem robustPolicyValue_eq_policyFix (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) (hU : ∀ s a, RowAttains (ball (M.transition s a) σ))
    (π : StationaryPolicy State Action) :
    robustPolicyValue ball M σ π = policyFix (ballFamily ball M σ) M π :=
  (familyRobustValue_eq_policyFix (ballFamily ball M σ) hU M π).1

end StatisticalRL.RobustRL.DRVI
