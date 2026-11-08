import Formalization.Online.RegretToPAC.Definitions
import Formalization.Online.RegretToPAC.Corrected

/-!
# Refutation of the printed regret-to-PAC conversion

Source: `eq:PAC-from-regret-conversion`, `chapters/onlineRL.tex:113–141`, proof :145–183,
protocol :17–41. The printed constant `C_{S,A,H+1}` is wrong.

Counterexample. The algorithm is deterministic and seedless (it ignores the seed, `K`, the
history and the carriers), so it lies in the book's algorithm class as well as in the restricted
class of the Lean propositions. It knows the horizon and the reward (`onlineRL.tex:20`; rewards in
`[0,1]`, `prelim.tex:682–683`): for `H = 1` it plays a reward-minimizing action, for `H ≠ 1` a
reward-maximizing action at every step. With one state myopic play is optimal, so its regret is
`≤ 0` for `H ≥ 2`; in every other case the regret is `≤ K H` because rewards lie in `[0,1]`. The
regret hypothesis therefore holds on every carrier pair with `α = 0` and the strictly positive
constants `C_{1,A,H} = 1/4` (`H ≠ 1`), `C_{S,A,H} = H + 1` otherwise. These constants are not
monotone in `H` (`C_{1,2,2} = 1/4 < 2 = C_{1,2,1}`); under monotone constants the printed claim
holds (`eq_PAC_from_regret_conversion_restricted`). On the instance `S = 1`, `A = 2`, `H = 1`,
`r = (1, 0)`, `K = 1`, `δ = 1/2` every deployed policy has gap `1`, while the printed conclusion
requires gap `≤ C_{1,2,2}/δ = 1/2` with probability `≥ 1/2`.

The construction uses the known-reward convention and rewards in `[0,1]`; whether the printed
constant fails with unknown rewards is not determined here.
-/

open scoped BigOperators
open MeasureTheory
namespace StatisticalRL.OnlineRL.RegretToPAC

universe u v

section General
variable {State : Type*} {Action : Type*} [Fintype State] [Fintype Action]

/-- A reward-maximizing action (counterexample helper). -/
noncomputable def rewardArgmax [Nonempty Action] (r : Action → ℝ) : Action :=
  (Finite.exists_max r).choose

/-- A reward-minimizing action (counterexample helper). -/
noncomputable def rewardArgmin [Nonempty Action] (r : Action → ℝ) : Action :=
  (Finite.exists_min r).choose

theorem le_rewardArgmax [Nonempty Action] (r : Action → ℝ) (a : Action) :
    r a ≤ r (rewardArgmax r) :=
  (Finite.exists_max r).choose_spec a

theorem rewardArgmin_le [Nonempty Action] (r : Action → ℝ) (a : Action) :
    r (rewardArgmin r) ≤ r a :=
  (Finite.exists_min r).choose_spec a

theorem expectation_of_subsingleton [Subsingleton State] (d : FiniteDistribution State)
    (f : State → ℝ) (s : State) : d.expectation f = f s := by
  letI : Unique State := ⟨⟨s⟩, fun y ↦ Subsingleton.elim y s⟩
  rw [FiniteDistribution.expectation, Fintype.sum_unique,
    FiniteDistribution.prob_eq_one_of_subsingleton, one_mul]
  rfl

theorem trajectoryValue_withPolicy_cons (e : EnvironmentStage State Action)
    (π : StationaryPolicy State Action) (tail : List (DecisionStage State Action)) (s : State) :
    DecisionStage.trajectoryValue (e.withPolicy π :: tail) s =
      (π s).expectation (fun a ↦ e.reward s a +
        (e.transition s a).expectation (DecisionStage.trajectoryValue tail)) := by
  rw [DecisionStage.trajectoryValue_cons]
  rfl

/-- The return of a deterministic Markov policy is nonnegative. -/
theorem trajectoryValue_pointMass_nonneg : ∀ (H : ℕ) (E : Fin H → EnvironmentStage State Action)
    (f : Fin H → State → Action) (s : State),
    0 ≤ DecisionStage.trajectoryValue (List.ofFn (fun h : Fin H ↦ (E h).withPolicy
        (fun t ↦ EnvironmentStage.pointMass (f h t)))) s := by
  intro H
  induction H with
  | zero => intro E f s; simp
  | succ H ih =>
    intro E f s
    rw [List.ofFn_succ, trajectoryValue_withPolicy_cons, EnvironmentStage.expectation_pointMass]
    have h1 := (E 0).reward_nonneg s (f 0 s)
    have h2 := FiniteDistribution.expectation_nonneg ((E 0).transition s (f 0 s))
      (fun t ↦ ih (fun i ↦ E i.succ) (fun i ↦ f i.succ) t)
    linarith

/-- The optimal value is at most the horizon (rewards lie in `[0,1]`). -/
theorem optimalValue_le_length : ∀ (H : ℕ) (E : Fin H → EnvironmentStage State Action)
    (s : State), EnvironmentStage.optimalValue (List.ofFn E) s ≤ H := by
  intro H
  induction H with
  | zero => intro E s; simp [EnvironmentStage.optimalValue]
  | succ H ih =>
    intro E s
    rw [List.ofFn_succ, EnvironmentStage.optimalValue]
    unfold actionMaximum
    refine Finset.sup'_le _ _ fun a _ ↦ ?_
    unfold EnvironmentStage.qBackup
    have h1 := (E 0).reward_le_one s a
    have h2 := FiniteDistribution.expectation_le_const ((E 0).transition s a)
      (fun t ↦ ih (fun i ↦ E i.succ) t)
    push_cast
    linarith

/-- With one state, myopic reward maximization attains the optimal value. -/
theorem optimalValue_le_myopic_of_subsingleton [Subsingleton State] [Nonempty Action] :
    ∀ (H : ℕ) (E : Fin H → EnvironmentStage State Action) (s : State),
    EnvironmentStage.optimalValue (List.ofFn E) s ≤
      DecisionStage.trajectoryValue (List.ofFn (fun h : Fin H ↦ (E h).withPolicy
        (fun t ↦ EnvironmentStage.pointMass (rewardArgmax ((E h).reward t))))) s := by
  intro H
  induction H with
  | zero => intro E s; simp [EnvironmentStage.optimalValue]
  | succ H ih =>
    intro E s
    rw [List.ofFn_succ, List.ofFn_succ, trajectoryValue_withPolicy_cons,
      EnvironmentStage.expectation_pointMass, EnvironmentStage.optimalValue]
    unfold actionMaximum
    refine Finset.sup'_le _ _ fun a _ ↦ ?_
    unfold EnvironmentStage.qBackup
    rw [expectation_of_subsingleton _ _ s, expectation_of_subsingleton _ _ s]
    have h1 := le_rewardArgmax ((E 0).reward s) a
    have h2 := ih (fun i ↦ E i.succ) s
    linarith

/-- One-stage return of a deterministic policy. -/
theorem trajectoryValue_pointMass_one_stage (E : Fin 1 → EnvironmentStage State Action)
    (f : Fin 1 → State → Action) (s : State) :
    DecisionStage.trajectoryValue (List.ofFn (fun h : Fin 1 ↦ (E h).withPolicy
        (fun t ↦ EnvironmentStage.pointMass (f h t)))) s = (E 0).reward s (f 0 s) := by
  rw [List.ofFn_succ, trajectoryValue_withPolicy_cons, EnvironmentStage.expectation_pointMass]
  have hnil : DecisionStage.trajectoryValue ([] : List (DecisionStage State Action)) =
      fun _ ↦ 0 := funext DecisionStage.trajectoryValue_nil
  simp [hnil]

theorem rowMeasure_real_setOf_eq_zero {Ω : Type*} [Fintype Ω] (d : FiniteDistribution Ω)
    (P : Ω → Prop) (h : ∀ x, ¬ P x) : d.rowMeasure.real {x | P x} = 0 := by
  have : {x | P x} = (∅ : Set Ω) := by
    ext x
    simp [h x]
  rw [this, measureReal_empty]

end General

/-- Counterexample only: one deterministic, seedless algorithm on every carrier pair. It plays a
reward-minimizing action if `H = 1` and a reward-maximizing action otherwise. -/
noncomputable def printedCexAlg : (State : Type u) → (Action : Type v) → [Fintype State] →
    [Fintype Action] → [Nonempty Action] → (H : ℕ) → ℕ → (Fin H → State → Action → ℝ) →
    Unit → OnlineEpisodePlanner State Action H :=
  fun _ _ _ _ _ H _ r _ _ h t ↦ if H = 1 then rewardArgmin (r h t) else rewardArgmax (r h t)

/-- Counterexample only: strictly positive regret constants, `1/4` on one-state classes with
`H ≠ 1` and `H + 1` otherwise. Not monotone in `H`. -/
noncomputable def printedCexConst : ℕ → ℕ → ℕ → ℝ := fun S _ H ↦
  if S = 1 ∧ H ≠ 1 then 1 / 4 else (H : ℝ) + 1

theorem printedCexConst_pos (S A H : ℕ) : 0 < printedCexConst S A H := by
  unfold printedCexConst; split_ifs <;> positivity

/-- The constants of the counterexample decrease from `H = 1` to `H = 2`. -/
theorem printedCexConst_two_lt_one : printedCexConst 1 2 2 < printedCexConst 1 2 1 := by
  norm_num [printedCexConst]

/-- Counterexample only: the fixed-carrier constants, `C_{·,·,1} = 1`, `C_{·,·,H} = 0` else. -/
noncomputable def fixedCarrierCexConst : ℕ → ℕ → ℕ → ℝ := fun _ _ H ↦ if H = 1 then 1 else 0

/-- Counterexample only: the one-state stage with `r(true) = 1`, `r(false) = 0`. -/
noncomputable def printedCexStage : EnvironmentStage Unit Bool where
  state_nonempty := ⟨()⟩
  action_nonempty := ⟨true⟩
  transition := fun _ _ ↦ EnvironmentStage.pointMass ()
  reward := fun _ a ↦ if a then 1 else 0
  reward_nonneg := fun _ a ↦ by cases a <;> simp
  reward_le_one := fun _ a ↦ by cases a <;> simp

/-- **The printed regret-to-PAC conversion is false**, in its weakest reading (all carriers,
strictly positive constants). -/
theorem not_Eq_PAC_from_regret_conversion_printed :
    ¬ Eq_PAC_from_regret_conversion_printed.{0, 0} := by
  intro hP
  have h := hP Unit (fun _ _ ↦ EnvironmentStage.pointMass ()) printedCexAlg printedCexConst 0
    printedCexConst_pos le_rfl zero_le_one
    (by
      intro State Action _ _ _ H K hH hK E ρ fallback planner law πk V Vstar
      have hVstar : ∀ s, Vstar s = EnvironmentStage.optimalValue (List.ofFn E) s :=
        fun s ↦ EnvironmentStage.greedy_trajectoryValue _ s
      by_cases hc : Fintype.card State = 1 ∧ H ≠ 1
      · have hcv : printedCexConst (Fintype.card State) (Fintype.card Action) H *
            (K : ℝ) ^ (1 - (0 : ℝ)) = 1 / 4 * K := by simp [printedCexConst, hc]
        rw [hcv]
        haveI : Subsingleton State := Fintype.card_le_one_iff_subsingleton.mp hc.1.le
        refine FiniteDistribution.expectation_le_const _ fun ω ↦ ?_
        refine FiniteDistribution.expectation_le_const _ fun sample ↦ ?_
        refine (Finset.sum_nonpos fun k _ ↦ ?_).trans (by positivity)
        have hf : πk ω sample k = fun h t ↦ rewardArgmax ((E h).reward t) := by
          funext h t
          simp [πk, planner, printedCexAlg, hc.2]
        rw [hf, hVstar]
        have := optimalValue_le_myopic_of_subsingleton H E (sample.1 k)
        simp only [V]
        linarith
      · have hcv : printedCexConst (Fintype.card State) (Fintype.card Action) H *
            (K : ℝ) ^ (1 - (0 : ℝ)) = ((H : ℝ) + 1) * K := by simp [printedCexConst, hc]
        rw [hcv]
        refine FiniteDistribution.expectation_le_const _ fun ω ↦ ?_
        refine FiniteDistribution.expectation_le_const _ fun sample ↦ ?_
        calc ∑ k : Fin K, (Vstar (sample.1 k) - V (πk ω sample k) (sample.1 k))
            ≤ ∑ _k : Fin K, ((H : ℝ) + 1) := by
              refine Finset.sum_le_sum fun k _ ↦ ?_
              have h1 := optimalValue_le_length H E (sample.1 k)
              have h2 := trajectoryValue_pointMass_nonneg H E (πk ω sample k) (sample.1 k)
              rw [hVstar]
              simp only [V]
              linarith
          _ = ((H : ℝ) + 1) * K := by simp; ring)
    Unit Bool 1 1 one_pos one_pos (fun _ ↦ printedCexStage) (EnvironmentStage.pointMass ())
    (1 / 2) (by norm_num)
  dsimp only at h
  refine absurd h (not_le.mpr (lt_of_le_of_lt ?_ (by norm_num : (0 : ℝ) < 1 - 1 / 2)))
  refine FiniteDistribution.expectation_le_const _ fun ω ↦ ?_
  refine mul_nonpos_of_nonneg_of_nonpos (by norm_num) (Finset.sum_nonpos fun k _ ↦ ?_)
  refine le_of_eq (rowMeasure_real_setOf_eq_zero _ _ fun sample hs ↦ ?_)
  simp only [EnvironmentStage.expectation_pointMass] at hs
  rw [trajectoryValue_pointMass_one_stage] at hs
  have hstar := trajectoryValue_pointMass_le_greedy one_pos (fun _ ↦ printedCexStage)
    (fun _ _ ↦ true) ()
  rw [trajectoryValue_pointMass_one_stage] at hstar
  have hmin := rewardArgmin_le (printedCexStage.reward ()) false
  simp [printedCexAlg, printedCexConst, printedCexStage] at hs hstar hmin
  norm_num at hs
  linarith

/-- The printed regret-to-PAC conversion is false in its fixed-carrier reading (constants
`C_{·,·,1} = 1`, `C_{·,·,H} = 0` for `H ≠ 1`; same algorithm on `Unit`, `Bool`). -/
theorem not_Eq_PAC_from_regret_conversion_printed_fixedCarrier :
    ¬ Eq_PAC_from_regret_conversion_printed_fixedCarrier.{0, 0} := by
  intro hP
  have h := hP Unit Bool Unit (fun _ _ ↦ EnvironmentStage.pointMass ())
    (printedCexAlg Unit Bool) fixedCarrierCexConst 0 le_rfl zero_le_one
    (by
      intro H K hH hK E ρ fallback planner law πk V Vstar
      have hVstar : ∀ s, Vstar s = EnvironmentStage.optimalValue (List.ofFn E) s :=
        fun s ↦ EnvironmentStage.greedy_trajectoryValue _ s
      by_cases hH1 : H = 1
      · have hc : fixedCarrierCexConst (Fintype.card Unit) (Fintype.card Bool) H *
            (K : ℝ) ^ (1 - (0 : ℝ)) = (K : ℝ) := by
          simp [fixedCarrierCexConst, hH1]
        rw [hc]
        refine FiniteDistribution.expectation_le_const _ fun ω ↦ ?_
        refine FiniteDistribution.expectation_le_const _ fun sample ↦ ?_
        calc ∑ k : Fin K, (Vstar (sample.1 k) - V (πk ω sample k) (sample.1 k))
            ≤ ∑ _k : Fin K, (1 : ℝ) := by
              refine Finset.sum_le_sum fun k _ ↦ ?_
              have h1 := optimalValue_le_length H E (sample.1 k)
              have h2 := trajectoryValue_pointMass_nonneg H E (πk ω sample k) (sample.1 k)
              rw [hVstar]
              have hHr : (H : ℝ) = 1 := by exact_mod_cast hH1
              simp only [V]
              linarith
          _ = K := by simp
      · have hc : fixedCarrierCexConst (Fintype.card Unit) (Fintype.card Bool) H *
            (K : ℝ) ^ (1 - (0 : ℝ)) = 0 := by
          simp [fixedCarrierCexConst, hH1]
        rw [hc]
        refine FiniteDistribution.expectation_le_const _ fun ω ↦ ?_
        refine FiniteDistribution.expectation_le_const _ fun sample ↦ ?_
        refine Finset.sum_nonpos fun k _ ↦ ?_
        have hf : πk ω sample k = fun h t ↦ rewardArgmax ((E h).reward t) := by
          funext h t
          simp [πk, planner, printedCexAlg, hH1]
        rw [hf, hVstar]
        have := optimalValue_le_myopic_of_subsingleton H E (sample.1 k)
        simp only [V]
        linarith)
    1 1 one_pos one_pos (fun _ ↦ printedCexStage) (EnvironmentStage.pointMass ())
    (1 / 2) (by norm_num)
  dsimp only at h
  refine absurd h (not_le.mpr (lt_of_le_of_lt ?_ (by norm_num : (0 : ℝ) < 1 - 1 / 2)))
  refine FiniteDistribution.expectation_le_const _ fun ω ↦ ?_
  refine mul_nonpos_of_nonneg_of_nonpos (by norm_num) (Finset.sum_nonpos fun k _ ↦ ?_)
  refine le_of_eq (rowMeasure_real_setOf_eq_zero _ _ fun sample hs ↦ ?_)
  simp only [EnvironmentStage.expectation_pointMass] at hs
  rw [trajectoryValue_pointMass_one_stage] at hs
  have hstar := trajectoryValue_pointMass_le_greedy one_pos (fun _ ↦ printedCexStage)
    (fun _ _ ↦ true) ()
  rw [trajectoryValue_pointMass_one_stage] at hstar
  have hmin := rewardArgmin_le (printedCexStage.reward ()) false
  simp [printedCexAlg, fixedCarrierCexConst, printedCexStage] at hs hstar hmin
  linarith

end StatisticalRL.OnlineRL.RegretToPAC
