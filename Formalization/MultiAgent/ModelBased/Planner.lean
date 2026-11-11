import Formalization.MultiAgent.ModelBased.StageCCE
import Formalization.MultiAgent.ModelBased.BestResponse

/-!
# A causal CCE planning oracle (non-vacuity of the CCE clause)

`ccePlanner hA`: backward induction with a fixed stage-CCE selector (`stageCCE_exists`), in the
spirit of the stagewise CCE methods named at `marl.tex:377`. It is causal by construction
(`ccePlanner_causal`) and returns a CCE (`eq:defn-CCE`) of every game (`ccePlanner_isCCE`), so the
hypotheses of clause (a) of `Thm7_6_restricted` are satisfiable (`causalCCEOracle_exists`).
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl76

open StatisticalRL StatisticalRL.Ch7Rest.Marl

variable {m S H : ℕ} {A : Fin m → ℕ}

/-- A fixed stage-CCE selector. -/
noncomputable def cceSel (hA : ∀ i, 0 < A i) (u : Fin m → JointAction m A → ℝ) :
    FiniteDistribution (JointAction m A) :=
  Classical.choose (stageCCE_exists u hA)

theorem cceSel_spec (hA : ∀ i, 0 < A i) (u : Fin m → JointAction m A → ℝ) :
    IsStageCCE u (cceSel hA u) :=
  Classical.choose_spec (stageCCE_exists u hA)

/-- Stage payoffs at `(h, s)` with continuation values `V`. -/
def stageQ (G : MarkovGame m S H A) (V : Fin m → Fin S → ℝ) (h : ℕ) (s : Fin S) :
    Fin m → JointAction m A → ℝ :=
  fun i a => G.reward i h s a + (G.transition h s a).expectation (V i)

/-- Backward-induction values over `k` steps from step `h`. -/
noncomputable def biValue (hA : ∀ i, 0 < A i) (G : MarkovGame m S H A) :
    ℕ → ℕ → Fin m → Fin S → ℝ
  | _, 0, _, _ => 0
  | h, k + 1, i, s => ∑ a, (cceSel hA (stageQ G (biValue hA G (h + 1) k) h s)).prob a *
      stageQ G (biValue hA G (h + 1) k) h s i a

/-- The backward-induction CCE planner (horizon ending at step `H`). -/
noncomputable def ccePlanner (hA : ∀ i, 0 < A i) (G : MarkovGame m S H A) : JointPolicy m S A :=
  fun h s => cceSel hA (stageQ G (biValue hA G (h + 1) (H - h)) h s)

theorem valueJ_ccePlanner (hA : ∀ i, 0 < A i) (G : MarkovGame m S H A) (i : Fin m) :
    ∀ k h, h + k = H + 1 → valueJ G (ccePlanner hA G) i h k = biValue hA G h k i := by
  intro k
  induction k with
  | zero => intro h _; funext s; rfl
  | succ k ih =>
    intro h hk
    have hnext := ih (h + 1) (by omega)
    have hk' : H - h = k := by omega
    funext s
    simp only [valueJ, biValue, hnext]
    simp only [ccePlanner, hk']
    rfl

theorem brW_le_biValue (hA : ∀ i, 0 < A i) (G : MarkovGame m S H A) (i : Fin m) :
    ∀ k h, h + k = H + 1 → ∀ s, brW G (ccePlanner hA G) i h k s ≤ biValue hA G h k i s := by
  haveI : Nonempty (Fin (A i)) := ⟨⟨0, hA i⟩⟩
  intro k
  induction k with
  | zero => intro h _ s; simp [brW, biValue]
  | succ k ih =>
    intro h hk s
    have hnext := ih (h + 1) (by omega)
    have hk' : H - h = k := by omega
    simp only [brW]
    refine ciSup_le fun b => ?_
    calc brQ G (ccePlanner hA G) i (brW G (ccePlanner hA G) i (h + 1) k) h s b
        ≤ brQ G (ccePlanner hA G) i (biValue hA G (h + 1) k i) h s b := brQ_mono _ _ _ hnext _ _ _
      _ = ∑ a, (cceSel hA (stageQ G (biValue hA G (h + 1) k) h s)).prob a *
            stageQ G (biValue hA G (h + 1) k) h s i (Function.update a i b) := by
          simp only [brQ, ccePlanner, hk', stageQ]
      _ ≤ ∑ a, (cceSel hA (stageQ G (biValue hA G (h + 1) k) h s)).prob a *
            stageQ G (biValue hA G (h + 1) k) h s i a :=
          cceSel_spec hA _ i b
      _ = biValue hA G h (k + 1) i s := rfl

/-- The planner returns a CCE (`eq:defn-CCE`) of every game. -/
theorem ccePlanner_isCCE (hA : ∀ i, 0 < A i) (G : MarkovGame m S H A) :
    IsCCE G (ccePlanner hA G) := by
  intro s i
  haveI : Nonempty (PlayerPolicy S (A i)) :=
    ⟨fun _ _ => EnvironmentStage.pointMass ⟨0, hA i⟩⟩
  rw [valueJ_ccePlanner hA G i H 1 (by omega)]
  unfold bestResponseValueJ
  refine ciSup_le fun π' => ?_
  exact (valueJ_deviate_le_brW G _ i π' H 1 s).trans (brW_le_biValue hA G i H 1 (by omega) s)

theorem biValue_congr (hA : ∀ i, 0 < A i) (G G' : MarkovGame m S H A) :
    ∀ k h, (∀ t, h ≤ t → G.transition t = G'.transition t ∧ ∀ i, G.reward i t = G'.reward i t) →
      biValue hA G h k = biValue hA G' h k := by
  intro k
  induction k with
  | zero => intro h _; funext i s; rfl
  | succ k ih =>
    intro h hag
    have hnext := ih (h + 1) fun t ht => hag t (by omega)
    have hQ : stageQ G (biValue hA G (h + 1) k) h = stageQ G' (biValue hA G' (h + 1) k) h := by
      funext s i a
      simp only [stageQ, hnext, (hag h le_rfl).1, (hag h le_rfl).2 i]
    funext i s
    simp only [biValue]
    rw [hQ]

/-- The planner is causal. -/
theorem ccePlanner_causal (hA : ∀ i, 0 < A i) : CausalOracle (ccePlanner (S := S) (H := H) hA) := by
  intro G G' h hag
  have hV := biValue_congr hA G G' (H - h) (h + 1) fun t ht => hag t (by omega)
  have hQ : stageQ G (biValue hA G' (h + 1) (H - h)) h = stageQ G' (biValue hA G' (h + 1) (H - h)) h := by
    funext s i a
    simp only [stageQ, (hag h le_rfl).1, (hag h le_rfl).2 i]
  funext s
  simp only [ccePlanner, hV, hQ]

/-- Non-vacuity of the CCE clause: a causal planning oracle returning a CCE of every game (hence
of every empirical game) exists. -/
theorem causalCCEOracle_exists (hA : ∀ i, 0 < A i) :
    ∃ O : MarkovGame m S H A → JointPolicy m S A, CausalOracle O ∧ ∀ G', IsCCE G' (O G') :=
  ⟨ccePlanner hA, ccePlanner_causal hA, ccePlanner_isCCE hA⟩

end StatisticalRL.Ch7Rest.Marl76
