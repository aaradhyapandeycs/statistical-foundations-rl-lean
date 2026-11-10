import Formalization.Online.Regret.MVP.OnlineMVPLiteralTriggerCounterexample
import Formalization.Online.Regret.MVP.MVPModelDefinitions
import Formalization.MDP.PolicyEnvironmentDefinitions
import Formalization.MDP.TrajectoryDefinitions
import Formalization.MDP.FiniteOptimal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Theorem 5.10 under the literal MVP trigger set (source issue C48)

`thm-mvp-regret` (Theorem 5.10, `chapters/onlineRL.tex:1339–1352`) claims that, with probability
at least `1-δ`, Algorithm `alg:main-mvp` (`:1256–1310`) with the Bernstein bonuses
`eq:bh-defn-Bernstein-ucbvi` (`:407–417`) has `Regret(K) ≤ Õ(min{√(SAH³K), HK})` for suitably
chosen constants `c₁, c₂ > 0`. The algorithm's trigger `line:trigger-set-mvp` (`:1280`) reads
`N^all_h(s,a) ∈ {1, 2, ⋯, 2^{log₂ K}}`; read literally this is every integer from `1` to
`2^{log₂ K}` (C13). This file transcribes the algorithm with that literal trigger and refutes
the printed regret bound.

Transcription choices (all generous to the source):
* `Õ(g)` (`chapters/intro.tex:192`: `O` with logarithmic factors suppressed) is read as
  `C · (1 + log(SAHK/δ))^p · g` for some real `C` and some natural `p`, both chosen before the
  instance; `c₁, c₂ > 0` are likewise existential (universal constants, `:413`).
* The bonus at stored count `0` is undefined in the source (C8). An arbitrary completion
  `b₀ ≥ 0` is chosen existentially together with the constants.
* `δ' = δ/(100 S²A²H²K²)` as at `:416`.
* `Q ← H` before the first trigger (`:1262`); afterwards `Q` is the backward clipped recursion
  `eq:updateq-mvp` (`:1298–1300`) on the stored empirical rows, with `V_{H+1} = 0`. Since
  stored rows only change at triggers and `Q` is recomputed exactly after triggering episodes,
  this equals the value the algorithm holds. With the literal trigger the first completed
  episode always triggers, so "before the first trigger" is the empty completed history.
* The source's `argmax` has no tie rule; the printed claim is about the algorithm, so it is
  quantified over every argmax selector `sel` (it may depend on stage and state).
* Regret, sampling law and policies use the same actual sequential experiment, completed-history
  policy and true trajectory values as `MVP_regret_corrected`.

The stored batch is computed by an operational per-row replay of `:1279–1287`: increment the
count, append the successor to the pending batch, and on a trigger store the pending batch
(`N_h(s,a) ← Σ N_h(s,a,·)`, `P̂ ← N_h(s,a,·)/N_h(s,a)`) and reset it. `log₂ K` is read as
`Nat.log 2 K` as in `onlineMVPLiteralRowTrigger`; the witness only uses that the set contains `1`.

**Witness.** `S = H = 1`, `A = 2` (`Unit`, `Bool`), deterministic transitions, `δ = 1/2`,
rewards `0` for one action `bad` and `1` for the other. With the literal trigger every visit
to `bad` triggers and stores a batch of size `1`, so its bonus `c₂ H log(1/δ')` never shrinks;
once `c₂ log(1/δ') ≥ 1` its clipped score is `H = 1`, the maximal possible value, as is the
other action's. Thus `bad` is an argmax in every episode. For the selector used in the
refutation `bad` is the tie winner; `thm510Literal_regret_eq` shows more generally that for
*every* selector, labelling its tie choice as `bad` gives regret exactly `K` on every sample
path. So the counterexample is not an artifact of one adversarial tie rule: any deterministic
tie rule fails on a relabelled instance. It does rely on the exact tie at the clip `H`, which is
forced (both scores saturate), not on a Lean junk value. Regret `K` contradicts
`C (1 + log 4K)^p √(2K)` for large `K`.

The dyadic (power-of-two) reading is proved as `MVP_regret_corrected` (with further disclosed
corrections); this file only concerns the literal reading. -/

namespace StatisticalRL.OnlineRL
open MeasureTheory Filter
open scoped BigOperators

/-- One visit of a fixed row under the literal trigger (`chapters/onlineRL.tex:1279–1287`).
The state is `(N^all, pending successors, stored batch)`: increment the count, append the
successor; on a trigger store the pending batch and reset it. -/
def onlineMVPLiteralRowReplayStep (K : ℕ) {Outcome : Type*}
    (st : ℕ × List Outcome × List Outcome) (x : Outcome) : ℕ × List Outcome × List Outcome :=
  if onlineMVPLiteralRowTrigger K (st.1 + 1) then (st.1 + 1, [], st.2.1 ++ [x])
  else (st.1 + 1, st.2.1 ++ [x], st.2.2)

/-- Stored batch of a row after replaying its chronological successor list from the initial
state (`N^all = 0`, nothing pending, nothing stored). -/
def onlineMVPLiteralStoredBatch (K : ℕ) {Outcome : Type*} (xs : List Outcome) : List Outcome :=
  (xs.foldl (onlineMVPLiteralRowReplayStep K) (0, [], [])).2.2

/-- Replay invariant: below the trigger bound nothing is pending, and after the first visit the
stored batch has exactly one element. -/
theorem onlineMVPLiteralRowReplay_invariant (K : ℕ) {Outcome : Type*} :
    ∀ (xs : List Outcome) (st : ℕ × List Outcome × List Outcome),
      (st.1 ≤ 2 ^ Nat.log 2 K → st.2.1 = []) → (1 ≤ st.1 → st.2.2.length = 1) →
      ((xs.foldl (onlineMVPLiteralRowReplayStep K) st).1 = st.1 + xs.length ∧
        ((xs.foldl (onlineMVPLiteralRowReplayStep K) st).1 ≤ 2 ^ Nat.log 2 K →
          (xs.foldl (onlineMVPLiteralRowReplayStep K) st).2.1 = []) ∧
        (1 ≤ (xs.foldl (onlineMVPLiteralRowReplayStep K) st).1 →
          (xs.foldl (onlineMVPLiteralRowReplayStep K) st).2.2.length = 1)) := by
  have hT : 1 ≤ 2 ^ Nat.log 2 K := Nat.one_le_two_pow
  intro xs
  induction xs with
  | nil => intro st h1 h2; exact ⟨by simp, h1, h2⟩
  | cons x xs ih =>
      intro st h1 h2
      rw [List.foldl_cons]
      have key := ih (onlineMVPLiteralRowReplayStep K st x) ?_ ?_
      · refine ⟨?_, key.2⟩
        rw [key.1]
        unfold onlineMVPLiteralRowReplayStep
        split_ifs <;> simp <;> omega
      · unfold onlineMVPLiteralRowReplayStep onlineMVPLiteralRowTrigger
        split_ifs with ht
        · intro _; rfl
        · intro hc; exfalso; apply ht; exact ⟨by omega, hc⟩
      · unfold onlineMVPLiteralRowReplayStep onlineMVPLiteralRowTrigger
        split_ifs with ht
        · intro _; simp [h1 (by omega)]
        · intro _; apply h2; by_contra hc; apply ht; exact ⟨by omega, by omega⟩

/-- Under the literal trigger every visited row stores a batch of size one. -/
theorem onlineMVPLiteralStoredBatch_length_of_ne_nil (K : ℕ) {Outcome : Type*}
    {xs : List Outcome} (hxs : xs ≠ []) : (onlineMVPLiteralStoredBatch K xs).length = 1 := by
  have := onlineMVPLiteralRowReplay_invariant K xs (0, [], []) (fun _ => rfl) (by simp)
  apply this.2.2
  rw [this.1]
  have : 0 < xs.length := List.length_pos_iff.mpr hxs
  simp only
  omega


section Planner
variable {State Action : Type*} [Fintype State] [Fintype Action]
noncomputable local instance thm510StateDecidable : DecidableEq State := Classical.decEq State
noncomputable local instance thm510ActionDecidable : DecidableEq Action := Classical.decEq Action

/-- Pre-episode planning stage with the literal-trigger stored batches. -/
noncomputable def onlineMVPLiteralPlanningStage {H : ℕ} (K : ℕ)
    (E : Fin H → EnvironmentStage State Action)
    (rowAt : ℕ → Fin H × State × Action) (nextAt : ℕ → State) (n : ℕ) (h : Fin H) :
    OnlineObservedPlanningStage State Action where
  environment := E h
  observations s a :=
    onlineMVPLiteralStoredBatch K (onlineMVPRowVisitList rowAt nextAt n (h, (s, a)))

/-- Printed clipped update `eq:updateq-mvp` with the Bernstein bonus
`eq:bh-defn-Bernstein-ucbvi` at positive stored count, and the completion `b₀` at count zero
(where the row is the uniform initialization `P̂ = 1/S`). -/
noncomputable def onlineMVPPrintedStageQ (cap L c₁ c₂ b₀ : ℝ)
    (stage : OnlineObservedPlanningStage State Action) (next : State → ℝ)
    (s : State) (a : Action) : ℝ :=
  min (stage.environment.reward s a + (onlineObservedPlanningRow stage s a).expectation next +
    (if 0 < (stage.observations s a).length then
      c₁ * Real.sqrt ((onlineObservedPlanningRow stage s a).variance next * L /
        (stage.observations s a).length) +
        c₂ * cap * L / (stage.observations s a).length
    else b₀)) cap

/-- Backward values `V_h = max_a Q_h`, with `V_{H+1} = 0`. -/
noncomputable def onlineMVPPrintedBackwardValue (cap L c₁ c₂ b₀ : ℝ) :
    List (OnlineObservedPlanningStage State Action) → State → ℝ
  | [] => fun _ => 0
  | stage :: stages => fun s =>
    letI : Nonempty Action := stage.environment.action_nonempty
    actionMaximum (onlineMVPPrintedStageQ cap L c₁ c₂ b₀ stage
      (onlineMVPPrintedBackwardValue cap L c₁ c₂ b₀ stages) s)

/-- Backward `Q` table sharing the continuation of the value recursion. -/
noncomputable def onlineMVPPrintedBackwardQ (cap L c₁ c₂ b₀ : ℝ) :
    List (OnlineObservedPlanningStage State Action) → State → Action → ℝ
  | [] => fun _ _ => 0
  | stage :: stages => onlineMVPPrintedStageQ cap L c₁ c₂ b₀ stage
      (onlineMVPPrintedBackwardValue cap L c₁ c₂ b₀ stages)

/-- Literal-trigger planning table from a completed history. -/
noncomputable def onlineMVPLiteralPlanningStages {H : ℕ} (hH : 0 < H) (K : ℕ)
    (E : Fin H → EnvironmentStage State Action) (fallback : State)
    (history : List (OnlineMDPRow State Action H × State)) :
    List (OnlineObservedPlanningStage State Action) :=
  List.ofFn (fun h : Fin H => onlineMVPLiteralPlanningStage K E
    (onlineMVPHistoryRowAt hH E fallback history) (onlineMVPHistoryNextAt fallback history)
    history.length h)

/-- Greedy step `:1268` of the literal-trigger MVP: `Q = H` before any update, otherwise the
printed clipped recursion on the stored batches; ties resolved by the selector `sel`. -/
noncomputable def onlineMVPLiteralPlanner {H : ℕ} (hH : 0 < H) (K : ℕ)
    (E : Fin H → EnvironmentStage State Action) (fallback : State) (L c₁ c₂ b₀ : ℝ)
    (sel : Fin H → State → (Action → ℝ) → Action) : OnlineEpisodePlanner State Action H :=
  fun history h s =>
    if history.length = 0 then sel h s (fun _ => (H : ℝ))
    else sel h s (onlineMVPPrintedBackwardQ (H : ℝ) L c₁ c₂ b₀
      ((onlineMVPLiteralPlanningStages hH K E fallback history).drop h.val) s)

end Planner

/-- Printed Theorem 5.10 (`thm-mvp-regret`, `chapters/onlineRL.tex:1339–1352`) for
Algorithm `alg:main-mvp` with the literal trigger set of `:1280`. `Õ` is an existential constant
`C` and polylog power `p` of `1 + log(SAHK/δ)`; `c₁, c₂ > 0` and the zero-count completion
`b₀ ≥ 0` are existential; the bound must hold for every argmax tie rule. See the module
docstring and `docs/SOURCE-ISSUES.md` C48/C13. -/
def Thm5_10_literalTrigger_printed : Prop :=
  ∃ (C : ℝ) (p : ℕ) (c₁ c₂ b₀ : ℝ), 0 < c₁ ∧ 0 < c₂ ∧ 0 ≤ b₀ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action] (H K : ℕ) (hH : 0 < H),
      1 ≤ K → ∀ (E : Fin H → EnvironmentStage State Action)
        (ρ : FiniteDistribution State) (δ : ℝ), 0 < δ → δ < 1 →
      ∀ sel : Fin H → State → (Action → ℝ) → Action,
        (∀ h s (f : Action → ℝ) a, f a ≤ f (sel h s f)) →
      let fallback : State := Classical.choice (E ⟨0, hH⟩).state_nonempty
      let S := Fintype.card State
      let A := Fintype.card Action
      let δp := δ / (100 * (S : ℝ)^2 * (A : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2)
      let planner := onlineMVPLiteralPlanner hH K E fallback (Real.log (1/δp)) c₁ c₂ b₀ sel
      1 - δ ≤ (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
        {sample : (Fin K → State) × OnlineOutcomePath.{0,0} State (K*H) |
          let history := onlineSequentialPathHistory
            (onlineEpisodicChoose H K hH sample.1 fallback planner) (K*H) [] sample.2
          (∑ k : Fin K,
            (DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E))
                (sample.1 k) -
              DecisionStage.trajectoryValue
                (List.ofFn (fun h : Fin H => (E h).withPolicy
                  (fun s => EnvironmentStage.pointMass (planner (history.take (k.val*H)) h s))))
                (sample.1 k))) ≤
            C * (1 + Real.log ((S : ℝ) * A * H * K / δ)) ^ p *
              min (Real.sqrt ((S : ℝ) * A * (H : ℝ)^3 * K)) ((H : ℝ) * K)}

/-- Printed Theorem 5.10 for one fixed deterministic tie rule `rule` (a selector for every
finite instance, depending on stage, state and Q-row): `Thm5_10_literalTrigger_printed` with the
quantifier over selectors replaced by this rule. `not_Thm5_10_literalTrigger_printed_rule` refutes
it for every rule (no argmax premise is needed), so any fixed implementation of the literal
algorithm fails. -/
def Thm5_10_literalTrigger_printed_rule
    (rule : ∀ (State Action : Type) [Fintype State] [Fintype Action] (H : ℕ),
      Fin H → State → (Action → ℝ) → Action) : Prop :=
  ∃ (C : ℝ) (p : ℕ) (c₁ c₂ b₀ : ℝ), 0 < c₁ ∧ 0 < c₂ ∧ 0 ≤ b₀ ∧
    ∀ (State Action : Type) [Fintype State] [Fintype Action] (H K : ℕ) (hH : 0 < H),
      1 ≤ K → ∀ (E : Fin H → EnvironmentStage State Action)
        (ρ : FiniteDistribution State) (δ : ℝ), 0 < δ → δ < 1 →
      let sel := rule State Action H
      let fallback : State := Classical.choice (E ⟨0, hH⟩).state_nonempty
      let S := Fintype.card State
      let A := Fintype.card Action
      let δp := δ / (100 * (S : ℝ)^2 * (A : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2)
      let planner := onlineMVPLiteralPlanner hH K E fallback (Real.log (1/δp)) c₁ c₂ b₀ sel
      1 - δ ≤ (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K*H)).rowMeasure.real
        {sample : (Fin K → State) × OnlineOutcomePath.{0,0} State (K*H) |
          let history := onlineSequentialPathHistory
            (onlineEpisodicChoose H K hH sample.1 fallback planner) (K*H) [] sample.2
          (∑ k : Fin K,
            (DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E))
                (sample.1 k) -
              DecisionStage.trajectoryValue
                (List.ofFn (fun h : Fin H => (E h).withPolicy
                  (fun s => EnvironmentStage.pointMass (planner (history.take (k.val*H)) h s))))
                (sample.1 k))) ≤
            C * (1 + Real.log ((S : ℝ) * A * H * K / δ)) ^ p *
              min (Real.sqrt ((S : ℝ) * A * (H : ℝ)^3 * K)) ((H : ℝ) * K)}

/-- One-state, two-action, horizon-one stage: reward `0` for `bad`, `1` otherwise. -/
noncomputable def thm510LiteralEnv (bad : Bool) : EnvironmentStage Unit Bool where
  state_nonempty := ⟨()⟩
  action_nonempty := ⟨true⟩
  transition _ _ := EnvironmentStage.pointMass ()
  reward _ a := if a = bad then 0 else 1
  reward_nonneg _ a := by split <;> norm_num
  reward_le_one _ a := by split <;> norm_num

/-- Value of a one-stage trajectory on the one-point state space. -/
theorem thm510Literal_trajectoryValue_single (d : DecisionStage Unit Bool) :
    DecisionStage.trajectoryValue [d] () =
      ∑ a : Bool, (d.policy ()).prob a * (d.transition () a).prob () * d.reward () a := by
  change (∑ path : Bool × Unit × PUnit, ((d.policy ()).prob path.1 *
      (d.transition () path.1).prob path.2.1 * 1) * (d.reward () path.1 + 0)) = _
  simp [Fintype.sum_prod_type]

theorem thm510Literal_pointMass_unit : (EnvironmentStage.pointMass () : FiniteDistribution Unit).prob () = 1 := by
  simp [EnvironmentStage.pointMass]

/-- Optimal value `1`; value `0` of always playing `bad`. -/
theorem thm510Literal_values (bad : Bool) :
    DecisionStage.trajectoryValue
        (EnvironmentStage.greedyStages (List.ofFn (fun _ : Fin 1 => thm510LiteralEnv bad))) () = 1 ∧
      DecisionStage.trajectoryValue
        (List.ofFn (fun _ : Fin 1 => (thm510LiteralEnv bad).withPolicy
          (fun _ => EnvironmentStage.pointMass bad))) () = 0 := by
  have hpm : ∀ b : Bool, ((EnvironmentStage.pointMass b : FiniteDistribution Bool)).prob = fun a => if a = b then 1 else 0 := by
    intro b; funext a; simp [EnvironmentStage.pointMass]
  constructor
  · rw [EnvironmentStage.greedy_trajectoryValue, List.ofFn_succ, List.ofFn_zero]
    simp only [EnvironmentStage.optimalValue, actionMaximum]
    apply le_antisymm
    · apply Finset.sup'_le
      intro a _
      simp only [EnvironmentStage.qBackup, thm510LiteralEnv, FiniteDistribution.expectation,
        mul_zero, Finset.sum_const_zero, add_zero]
      split <;> norm_num
    · have := Finset.le_sup' ((thm510LiteralEnv bad).qBackup
        (EnvironmentStage.optimalValue ([] : List (EnvironmentStage Unit Bool))) ())
        (Finset.mem_univ (!bad))
      refine le_trans ?_ this
      cases bad <;> simp [EnvironmentStage.qBackup, thm510LiteralEnv, FiniteDistribution.expectation,
        EnvironmentStage.optimalValue]
  · rw [List.ofFn_succ, List.ofFn_zero, thm510Literal_trajectoryValue_single]
    cases bad <;> simp [EnvironmentStage.withPolicy, thm510LiteralEnv, thm510Literal_pointMass_unit, hpm]

/-- In a nonempty all-`bad` history the `bad` row has a nonempty stored batch. -/
theorem thm510Literal_visitList_ne_nil (bad : Bool) (hH : 0 < 1) (K : ℕ) (fallback : Unit)
    (history : List (OnlineMDPRow Unit Bool 1 × Unit)) (hne : history.length ≠ 0)
    (hall : ∀ x ∈ history, x.1.2.2 = bad) (h : Fin 1) :
    (onlineMVPLiteralPlanningStage K (fun _ : Fin 1 => thm510LiteralEnv bad)
      (onlineMVPHistoryRowAt hH (fun _ : Fin 1 => thm510LiteralEnv bad) fallback history)
      (onlineMVPHistoryNextAt fallback history) history.length h).observations () bad ≠ [] := by
  have hlen : 0 < history.length := Nat.pos_of_ne_zero hne
  intro hnil
  have h1 := congrArg List.length hnil
  simp only [onlineMVPLiteralPlanningStage] at h1
  rw [onlineMVPLiteralStoredBatch_length_of_ne_nil] at h1
  · simp at h1
  · unfold onlineMVPRowVisitList
    rw [Ne, List.filterMap_eq_nil_iff]
    intro hall'
    have h0 := hall' 0 (List.mem_range.mpr hlen)
    have hrow : onlineMVPHistoryRowAt hH (fun _ : Fin 1 => thm510LiteralEnv bad) fallback history 0 =
        (h, ((), bad)) := by
      unfold onlineMVPHistoryRowAt
      rw [dif_pos hlen]
      have hb := hall _ (List.get_mem history ⟨0, hlen⟩)
      exact Prod.ext (Subsingleton.elim _ _) (Prod.ext (Subsingleton.elim _ _) hb)
    rw [if_pos hrow] at h0
    exact absurd h0 (by simp)

/-- On every all-`bad` completed history the literal planner plays `bad`: both clipped scores
equal `1` once `c₂ log(1/δ') ≥ 1`. -/
theorem thm510Literal_planner_eq_bad (bad : Bool)
    (sel : Fin 1 → Unit → (Bool → ℝ) → Bool) (hbad : sel 0 () (fun _ => 1) = bad)
    (hH : 0 < 1) (K : ℕ) (fallback : Unit) (L c₁ c₂ b₀ : ℝ) (hL : 0 ≤ L)
    (hc₂ : 0 ≤ c₂) (hc₂L : 1 ≤ c₂ * L) (hb₀ : 0 ≤ b₀)
    (history : List (OnlineMDPRow Unit Bool 1 × Unit)) (hall : ∀ x ∈ history, x.1.2.2 = bad)
    (h : Fin 1) (s : Unit) :
    onlineMVPLiteralPlanner hH K (fun _ : Fin 1 => thm510LiteralEnv bad) fallback L c₁ c₂ b₀ sel
      history h s = bad := by
  have hh : h = 0 := Subsingleton.elim _ _
  subst hh
  unfold onlineMVPLiteralPlanner
  split_ifs with h0
  · simpa using hbad
  · convert hbad using 2
    funext a
    simp only [Fin.val_zero, List.drop_zero, onlineMVPLiteralPlanningStages, List.ofFn_succ,
      List.ofFn_zero, onlineMVPPrintedBackwardQ, onlineMVPPrintedBackwardValue,
      onlineMVPPrintedStageQ, Nat.cast_one]
    have hE : ∀ d : FiniteDistribution Unit, d.expectation (fun _ => (0 : ℝ)) = 0 := by
      intro d; simp [FiniteDistribution.expectation]
    have hV : ∀ d : FiniteDistribution Unit, d.variance (fun _ => (0 : ℝ)) = 0 := by
      intro d; simp [FiniteDistribution.variance, FiniteDistribution.expectation]
    simp only [hE, hV, add_zero, zero_mul, zero_div, Real.sqrt_zero, mul_zero, zero_add]
    by_cases ha : a = bad
    · subst ha
      have hne := thm510Literal_visitList_ne_nil a hH K fallback history h0 hall 0
      have hlen : ((onlineMVPLiteralPlanningStage K (fun _ : Fin 1 => thm510LiteralEnv a)
          (onlineMVPHistoryRowAt hH (fun _ : Fin 1 => thm510LiteralEnv a) fallback history)
          (onlineMVPHistoryNextAt fallback history) history.length 0).observations () a).length = 1 := by
        simp only [onlineMVPLiteralPlanningStage] at hne ⊢
        apply onlineMVPLiteralStoredBatch_length_of_ne_nil
        intro hn; apply hne; rw [hn]; rfl
      rw [hlen]
      simp only [onlineMVPLiteralPlanningStage, thm510LiteralEnv]
      norm_num
      exact hc₂L
    · simp only [onlineMVPLiteralPlanningStage, thm510LiteralEnv, if_neg ha]
      apply min_eq_right
      have hbon : ∀ n : ℕ, 0 ≤ c₂ * 1 * L / (n : ℝ) := fun n =>
        div_nonneg (mul_nonneg (mul_nonneg hc₂ zero_le_one) hL) (Nat.cast_nonneg _)
      split_ifs
      · exact le_add_of_nonneg_right (hbon _)
      · exact le_add_of_nonneg_right hb₀


/-- `2C²(1 + log 4x)^{2p} < x` eventually. -/
theorem thm510Literal_polylog_eventually (C : ℝ) (p : ℕ) :
    ∀ᶠ x : ℝ in atTop, 2 * C ^ 2 * (1 + Real.log (4 * x)) ^ (2 * p) < x := by
  have hlo := (Real.isLittleO_pow_log_id_atTop (n := 2 * p)).def
    (c := 1 / (4 * (C ^ 2 + 1) * 4 ^ p)) (by positivity)
  filter_upwards [hlo, Real.tendsto_log_atTop.eventually_ge_atTop (1 + Real.log 4),
    eventually_gt_atTop (0 : ℝ)] with x hx hlog hpos
  have hlx : 0 ≤ Real.log x := le_trans (by positivity) hlog
  have h4 : 1 + Real.log (4 * x) ≤ 2 * Real.log x := by
    rw [Real.log_mul (by norm_num) hpos.ne']; linarith
  have h0 : 0 ≤ 1 + Real.log (4 * x) := by
    rw [Real.log_mul (by norm_num) hpos.ne']; linarith [Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num)]
  have hpow : (1 + Real.log (4 * x)) ^ (2 * p) ≤ 4 ^ p * Real.log x ^ (2 * p) := by
    calc (1 + Real.log (4 * x)) ^ (2 * p) ≤ (2 * Real.log x) ^ (2 * p) :=
          pow_le_pow_left₀ h0 h4 _
      _ = 4 ^ p * Real.log x ^ (2 * p) := by rw [mul_pow, pow_mul]; norm_num
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity), id,
    abs_of_pos hpos] at hx
  have hC : 0 ≤ C ^ 2 := sq_nonneg C
  calc 2 * C ^ 2 * (1 + Real.log (4 * x)) ^ (2 * p)
      ≤ 2 * (C ^ 2 + 1) * (4 ^ p * Real.log x ^ (2 * p)) := by
        apply mul_le_mul (by linarith) hpow (by positivity) (by positivity)
    _ ≤ 2 * (C ^ 2 + 1) * (4 ^ p * (1 / (4 * (C ^ 2 + 1) * 4 ^ p) * x)) := by
        gcongr
    _ = x / 2 := by field_simp; ring
    _ < x := by linarith

/-- A horizon `K` large enough for both the bonus saturation and the rate violation. -/
theorem thm510Literal_choose_K (C : ℝ) (p : ℕ) (c₂ : ℝ) (hc₂ : 0 < c₂) :
    ∃ K : ℕ, 1 ≤ K ∧ 1 ≤ c₂ * Real.log (800 * (K : ℝ) ^ 2) ∧
      C * (1 + Real.log (4 * (K : ℝ))) ^ p * min (Real.sqrt (2 * K)) (K : ℝ) < K := by
  have hA := tendsto_natCast_atTop_atTop.eventually (thm510Literal_polylog_eventually C p)
  have hB := tendsto_natCast_atTop_atTop.eventually
    (Real.tendsto_log_atTop.eventually_ge_atTop (1 / c₂))
  obtain ⟨K, hK1, hKA, hKB⟩ := ((eventually_ge_atTop 1).and (hA.and hB)).exists
  refine ⟨K, hK1, ?_, ?_⟩
  · have hKpos : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have : Real.log K ≤ Real.log (800 * (K : ℝ) ^ 2) :=
      Real.log_le_log (by linarith) (by nlinarith)
    have := mul_le_mul_of_nonneg_left (le_trans hKB this) hc₂.le
    rwa [mul_one_div_cancel hc₂.ne'] at this
  · have hKpos : (0 : ℝ) < K := by exact_mod_cast hK1
    have hu : 0 ≤ 1 + Real.log (4 * (K : ℝ)) := by
      rw [Real.log_mul (by norm_num) hKpos.ne']
      linarith [Real.log_nonneg (show (1:ℝ) ≤ 4 by norm_num),
        Real.log_nonneg (show (1:ℝ) ≤ K by exact_mod_cast hK1)]
    have hmin0 : 0 ≤ min (Real.sqrt (2 * K)) (K : ℝ) := le_min (Real.sqrt_nonneg _) hKpos.le
    rcases le_or_gt C 0 with hC | hC
    · have : C * (1 + Real.log (4 * (K : ℝ))) ^ p * min (Real.sqrt (2 * K)) (K : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hC (by positivity)) hmin0
      linarith
    · have hsq : C * (1 + Real.log (4 * (K : ℝ))) ^ p * Real.sqrt 2 < Real.sqrt K := by
        rw [Real.lt_sqrt (by positivity)]
        calc (C * (1 + Real.log (4 * (K : ℝ))) ^ p * Real.sqrt 2) ^ 2
            = 2 * C ^ 2 * (1 + Real.log (4 * (K : ℝ))) ^ (2 * p) := by
              rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), ← pow_mul]; ring
          _ < (K : ℝ) := hKA
      calc C * (1 + Real.log (4 * (K : ℝ))) ^ p * min (Real.sqrt (2 * K)) (K : ℝ)
          ≤ C * (1 + Real.log (4 * (K : ℝ))) ^ p * Real.sqrt (2 * K) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)
        _ = (C * (1 + Real.log (4 * (K : ℝ))) ^ p * Real.sqrt 2) * Real.sqrt K := by
            rw [Real.sqrt_mul (by norm_num)]; ring
        _ < Real.sqrt K * Real.sqrt K :=
            mul_lt_mul_of_pos_right hsq (Real.sqrt_pos.mpr hKpos)
        _ = K := Real.mul_self_sqrt hKpos.le

/-- Every realized record of the literal MVP run on the witness plays `bad`. -/
theorem thm510Literal_history_all_bad (bad : Bool)
    (sel : Fin 1 → Unit → (Bool → ℝ) → Bool) (hbad : sel 0 () (fun _ => 1) = bad)
    (hH : 0 < 1) (K : ℕ) (fallback : Unit) (L c₁ c₂ b₀ : ℝ) (hL : 0 ≤ L)
    (hc₂ : 0 ≤ c₂) (hc₂L : 1 ≤ c₂ * L) (hb₀ : 0 ≤ b₀) (initial : Fin K → Unit) :
    ∀ (n : ℕ) (hist : List (OnlineMDPRow Unit Bool 1 × Unit)) (path : OnlineOutcomePath Unit n),
      (∀ x ∈ hist, x.1.2.2 = bad) →
      ∀ x ∈ onlineSequentialPathHistory (onlineEpisodicChoose 1 K hH initial fallback
        (onlineMVPLiteralPlanner hH K (fun _ : Fin 1 => thm510LiteralEnv bad) fallback
          L c₁ c₂ b₀ sel)) n hist path, x.1.2.2 = bad := by
  intro n
  induction n with
  | zero => intro hist path hall; simpa [onlineSequentialPathHistory] using hall
  | succ n ih =>
      intro hist path hall
      simp only [onlineSequentialPathHistory]
      apply ih
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact hall x hx
      · rw [List.mem_singleton] at hx
        subst hx
        exact thm510Literal_planner_eq_bad bad sel hbad hH K fallback L c₁ c₂ b₀ hL hc₂ hc₂L hb₀
          _ (fun y hy => hall y (List.mem_of_mem_take hy)) _ _

/-- **Surely linear regret.** For every tie selector, labelling its choice on the constant
table as `bad`, the literal MVP run has regret exactly `K` on every sample path. -/
theorem thm510Literal_regret_eq (bad : Bool)
    (sel : Fin 1 → Unit → (Bool → ℝ) → Bool) (hbad : sel 0 () (fun _ => 1) = bad)
    (hH : 0 < 1) (K : ℕ) (fallback : Unit) (L c₁ c₂ b₀ : ℝ) (hL : 0 ≤ L)
    (hc₂ : 0 ≤ c₂) (hc₂L : 1 ≤ c₂ * L) (hb₀ : 0 ≤ b₀) (initial : Fin K → Unit)
    (path : OnlineOutcomePath.{0,0} Unit (K*1)) :
    (∑ k : Fin K,
      (DecisionStage.trajectoryValue
          (EnvironmentStage.greedyStages (List.ofFn (fun _ : Fin 1 => thm510LiteralEnv bad)))
          (initial k) -
        DecisionStage.trajectoryValue
          (List.ofFn (fun h : Fin 1 => (thm510LiteralEnv bad).withPolicy
            (fun s => EnvironmentStage.pointMass
              (onlineMVPLiteralPlanner hH K (fun _ : Fin 1 => thm510LiteralEnv bad) fallback
                L c₁ c₂ b₀ sel
                ((onlineSequentialPathHistory (onlineEpisodicChoose 1 K hH initial fallback
                  (onlineMVPLiteralPlanner hH K (fun _ : Fin 1 => thm510LiteralEnv bad) fallback
                    L c₁ c₂ b₀ sel)) (K*1) [] path).take (k.val*1)) h s))))
          (initial k))) = K := by
  have hall := thm510Literal_history_all_bad bad sel hbad hH K fallback L c₁ c₂ b₀ hL hc₂ hc₂L hb₀
    initial (K*1) [] path (by simp)
  have hterm : ∀ k : Fin K,
      (DecisionStage.trajectoryValue
          (EnvironmentStage.greedyStages (List.ofFn (fun _ : Fin 1 => thm510LiteralEnv bad)))
          (initial k) -
        DecisionStage.trajectoryValue
          (List.ofFn (fun h : Fin 1 => (thm510LiteralEnv bad).withPolicy
            (fun s => EnvironmentStage.pointMass
              (onlineMVPLiteralPlanner hH K (fun _ : Fin 1 => thm510LiteralEnv bad) fallback
                L c₁ c₂ b₀ sel
                ((onlineSequentialPathHistory (onlineEpisodicChoose 1 K hH initial fallback
                  (onlineMVPLiteralPlanner hH K (fun _ : Fin 1 => thm510LiteralEnv bad) fallback
                    L c₁ c₂ b₀ sel)) (K*1) [] path).take (k.val*1)) h s))))
          (initial k)) = 1 := by
    intro k
    have hpol : (fun h : Fin 1 => (thm510LiteralEnv bad).withPolicy
            (fun s => EnvironmentStage.pointMass
              (onlineMVPLiteralPlanner hH K (fun _ : Fin 1 => thm510LiteralEnv bad) fallback
                L c₁ c₂ b₀ sel
                ((onlineSequentialPathHistory (onlineEpisodicChoose 1 K hH initial fallback
                  (onlineMVPLiteralPlanner hH K (fun _ : Fin 1 => thm510LiteralEnv bad) fallback
                    L c₁ c₂ b₀ sel)) (K*1) [] path).take (k.val*1)) h s))) =
        (fun _ : Fin 1 => (thm510LiteralEnv bad).withPolicy
          (fun _ => EnvironmentStage.pointMass bad)) := by
      funext h
      congr 1
      funext s
      rw [thm510Literal_planner_eq_bad bad sel hbad hH K fallback L c₁ c₂ b₀ hL hc₂ hc₂L hb₀
        _ (fun y hy => hall y (List.mem_of_mem_take hy))]
    rw [hpol]
    have hv := thm510Literal_values bad
    rw [show initial k = () from rfl, hv.1, hv.2]
    norm_num
  rw [Finset.sum_congr rfl (fun k _ => hterm k)]
  simp

/-- **C48, machine-checked.** The printed MVP regret theorem is false for the algorithm with the
literal trigger set `{1, 2, ⋯, 2^{log₂ K}}`, for every choice of `C, p, c₁, c₂, b₀`. -/
theorem not_Thm5_10_literalTrigger_printed : ¬ Thm5_10_literalTrigger_printed := by
  rintro ⟨C, p, c₁, c₂, b₀, hc₁, hc₂, hb₀, hmain⟩
  obtain ⟨K, hK1, hKc, hKb⟩ := thm510Literal_choose_K C p c₂ hc₂
  let sel : Fin 1 → Unit → (Bool → ℝ) → Bool :=
    fun _ _ f => if f true ≤ f false then false else true
  have hsel : ∀ h s (f : Bool → ℝ) a, f a ≤ f (sel h s f) := by
    intro h s f a
    show f a ≤ f (if f true ≤ f false then false else true)
    split_ifs with hf
    · cases a
      · exact le_rfl
      · exact hf
    · cases a
      · exact (lt_of_not_ge hf).le
      · exact le_rfl
  have hmain' := hmain Unit Bool 1 K Nat.one_pos hK1
    (fun _ => thm510LiteralEnv (sel 0 () (fun _ => 1))) (EnvironmentStage.pointMass ())
    (1/2) (by norm_num) (by norm_num) sel hsel
  dsimp only at hmain'
  have hL : Real.log (1 / ((1 / 2 : ℝ) / (100 * ((Fintype.card Unit : ℕ) : ℝ) ^ 2 *
      ((Fintype.card Bool : ℕ) : ℝ) ^ 2 * ((1 : ℕ) : ℝ) ^ 2 * (K : ℝ) ^ 2))) =
      Real.log (800 * (K : ℝ) ^ 2) := by
    congr 1
    simp only [Fintype.card_unit, Fintype.card_bool, Nat.cast_one, Nat.cast_ofNat]
    field_simp
    ring
  rw [hL] at hmain'
  have hLnn : 0 ≤ Real.log (800 * (K : ℝ) ^ 2) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    nlinarith
  refine absurd hmain' (not_le.mpr ?_)
  rw [show (1 : ℝ) - 1/2 = 1/2 by norm_num]
  refine lt_of_eq_of_lt ?_ (by norm_num : (0 : ℝ) < 1/2)
  convert measureReal_empty using 2
  ext sample
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
  rw [thm510Literal_regret_eq (sel 0 () (fun _ => 1)) sel rfl Nat.one_pos K _ _ c₁ c₂ b₀ hLnn
    hc₂.le hKc hb₀]
  simp only [Fintype.card_unit, Fintype.card_bool, Nat.cast_one, Nat.cast_ofNat]
  convert hKb using 3 <;> ring_nf

/-- **C48, per tie rule.** For every deterministic tie rule (in particular every argmax tie
rule), the printed MVP regret bound fails for the literal-trigger algorithm using that rule, for
every choice of `C, p, c₁, c₂, b₀`: the witness labels the rule's choice on the constant row as
the reward-`0` action. -/
theorem not_Thm5_10_literalTrigger_printed_rule
    (rule : ∀ (State Action : Type) [Fintype State] [Fintype Action] (H : ℕ),
      Fin H → State → (Action → ℝ) → Action) :
    ¬ Thm5_10_literalTrigger_printed_rule rule := by
  rintro ⟨C, p, c₁, c₂, b₀, hc₁, hc₂, hb₀, hmain⟩
  obtain ⟨K, hK1, hKc, hKb⟩ := thm510Literal_choose_K C p c₂ hc₂
  let sel : Fin 1 → Unit → (Bool → ℝ) → Bool := rule Unit Bool 1
  have hmain' := hmain Unit Bool 1 K Nat.one_pos hK1
    (fun _ => thm510LiteralEnv (sel 0 () (fun _ => 1))) (EnvironmentStage.pointMass ())
    (1/2) (by norm_num) (by norm_num)
  dsimp only at hmain'
  have hL : Real.log (1 / ((1 / 2 : ℝ) / (100 * ((Fintype.card Unit : ℕ) : ℝ) ^ 2 *
      ((Fintype.card Bool : ℕ) : ℝ) ^ 2 * ((1 : ℕ) : ℝ) ^ 2 * (K : ℝ) ^ 2))) =
      Real.log (800 * (K : ℝ) ^ 2) := by
    congr 1
    simp only [Fintype.card_unit, Fintype.card_bool, Nat.cast_one, Nat.cast_ofNat]
    field_simp
    ring
  rw [hL] at hmain'
  have hLnn : 0 ≤ Real.log (800 * (K : ℝ) ^ 2) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    nlinarith
  refine absurd hmain' (not_le.mpr ?_)
  rw [show (1 : ℝ) - 1/2 = 1/2 by norm_num]
  refine lt_of_eq_of_lt ?_ (by norm_num : (0 : ℝ) < 1/2)
  convert measureReal_empty using 2
  ext sample
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_le]
  rw [thm510Literal_regret_eq (sel 0 () (fun _ => 1)) sel rfl Nat.one_pos K _ _ c₁ c₂ b₀ hLnn
    hc₂.le hKc hb₀]
  simp only [Fintype.card_unit, Fintype.card_bool, Nat.cast_one, Nat.cast_ofNat]
  convert hKb using 3 <;> ring_nf

end StatisticalRL.OnlineRL
