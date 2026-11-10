import Formalization.Online.Regret.Definitions
import Formalization.Online.Regret.T2.OnlineT2ActualDefinitions
import Formalization.Online.Regret.T3.T3Definitions
import Formalization.Online.Regret.W1.W1Definitions
import Formalization.Online.SourceOptimism.CappedGreedyPlannerDefinitions
import Formalization.Online.SourceOptimism.SequentialEpisodeDefinitions
import Formalization.Probability.EmpiricalRow

/-! # Printed Lemma 5.8 is false at `K = H = 1` (SOURCE-ISSUES C12, second endpoint)

Source: `lem:bound-T234`, `chapters/onlineRL.tex:988–1005` (confidence at `:990`), with
`δ' = δ/(100 S²A²H²K²)` and `ι = 40000 (log₂ K)³ log(3SAH) log(1/δ')`
(`eq:assumption-K-proof-B`, `:726–733`).

The printed lemma claims its event has probability *exceeding* `1 − 4 (log₂(KH)) δ'`. At
`K = H = 1` this is `1 − 0 = 1`, and no probability exceeds `1`; the side condition
`ι ≥ 8 max{c₁², c₂} (log₂ K) log(1/δ')` reads `0 ≤ 0` and holds. `Lemma5_8_printed` is the
statement-index entry `Lemma5_8_K2_corrected` (`Formalization/Statements/Ch5.lean`) verbatim with
its premise `2 ≤ K` replaced by the domain premise `1 ≤ K` (the main theorem allows every
`K ≥ 1`; the lemma itself states no restriction). The algorithm, bonus regime `4 ≤ c₁`,
`c₁² ≤ c₂`, zero-count completion (C8) and tie rule are those of the corrected entry.

Classification: boundary case (`K = H = 1`), not a Lean junk value: `log₂ 1 = 0` is the genuine
value. The refutation uses only the impossible confidence level; it says nothing about whether
the four displayed inequalities hold at `K = H = 1`, and nothing about the main regret theorem.
-/

open MeasureTheory

namespace StatisticalRL.OnlineRL

local instance lemma58StateMeasurable (State : Type*) : MeasurableSpace State := ⊤

universe u v

/-- Printed Lemma 5.8 (`lem:bound-T234`, `chapters/onlineRL.tex:988–1005`), transcribed as the
corrected entry `Lemma5_8_K2_corrected` with the domain premise `1 ≤ K` in place of `2 ≤ K`. -/
noncomputable def Lemma5_8_printed : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (H K : ℕ) (hH : 0 < H), 1 ≤ K →
    ∀ (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
      (δ c₁ c₂ : ℝ),
    0 < δ → δ ≤ 1 → 4 ≤ c₁ → c₁^2 ≤ c₂ →
    let fallback : State := Classical.choice (E ⟨0, hH⟩).state_nonempty
    let δ' := δ / (100 * (Fintype.card State : ℝ)^2 *
      (Fintype.card Action : ℝ)^2 * (H : ℝ)^2 * (K : ℝ)^2)
    let I := 40000 * (Real.log K / Real.log 2)^3 *
      Real.log (3 * (Fintype.card State : ℝ) * Fintype.card Action * H) *
        Real.log (1 / δ')
    8 * max (c₁^2) c₂ * (Real.log K / Real.log 2) * Real.log (1 / δ') ≤ I →
    let planner := onlineCappedGreedyPlanner E (Real.log (1 / δ')) c₁ c₂
    1 - 4 * (Real.log ((K : ℝ) * H) / Real.log 2) * δ' <
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H)).rowMeasure.real
        {sample : (Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H) |
          (∑ k : Fin K,
            (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ' c₁ c₂).2.1) ≤
            (1 / 2 : ℝ) * Real.sqrt ((Fintype.card State : ℝ) * Fintype.card Action * H *
              onlineActualT5 H K hH E sample.1 fallback sample.2 δ' c₁ c₂ * I) +
              (1 / 2 : ℝ) * (Fintype.card State : ℝ) * Fintype.card Action * H^2 * I ∧
          |∑ k : Fin K,
            (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ' c₁ c₂).2.2.1| ≤
            Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
              Real.log (1 / δ')) + 5 * (H : ℝ) * Real.log (1 / δ') ∧
          Real.sqrt (8 * onlineActualT6UCB H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
            Real.log (1 / δ')) + 5 * (H : ℝ) * Real.log (1 / δ') ≤
            4 * Real.sqrt (onlineActualT6Policy H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
              Real.log (1 / δ')) +
            4 * Real.sqrt (onlineActualT6Difference H K hH E sample.1 fallback sample.2 δ' c₁ c₂ *
              Real.log (1 / δ')) + 5 * (H : ℝ) * Real.log (1 / δ') ∧
          |∑ k : Fin K,
            (onlineActualEpisodeRegretTerms H K hH E sample.1 fallback sample.2 k δ' c₁ c₂).2.2.2| ≤
            Real.sqrt (2 * (K : ℝ) * (H : ℝ)^2 * Real.log (1 / δ'))}

/-- The probability vector on the one-point type. -/
noncomputable def lemma58UnitDist : FiniteDistribution Unit where
  prob := fun _ ↦ 1
  prob_nonneg := fun _ ↦ zero_le_one
  sum_prob := by simp

/-- One-state, one-action stage with zero reward. -/
noncomputable def lemma58UnitStage : EnvironmentStage Unit Unit where
  state_nonempty := ⟨()⟩
  action_nonempty := ⟨()⟩
  transition := fun _ _ ↦ lemma58UnitDist
  reward := fun _ _ ↦ 0
  reward_nonneg := fun _ _ ↦ le_rfl
  reward_le_one := fun _ _ ↦ zero_le_one

/-- **C12 (second endpoint).** Printed Lemma 5.8 is false: at `S = A = H = K = 1` (any
`δ ∈ (0,1]`, here `δ = 1/2`, `c₁ = 4`, `c₂ = 16`) its confidence level `1 − 4 log₂(1) δ'` is `1`,
and no event has probability exceeding `1`. Boundary case, not a junk value. -/
theorem not_Lemma5_8_printed : ¬ Lemma5_8_printed.{0, 0} := by
  intro h
  have key := h Unit Unit 1 1 one_pos le_rfl (fun _ ↦ lemma58UnitStage) lemma58UnitDist
    (1 / 2) 4 16 (by norm_num) (by norm_num) le_rfl (by norm_num)
    (by simp)
  simp only [Nat.cast_one, mul_one, Real.log_one, zero_div, mul_zero, zero_mul, sub_zero] at key
  exact absurd key (not_lt.mpr measureReal_le_one)

end StatisticalRL.OnlineRL
