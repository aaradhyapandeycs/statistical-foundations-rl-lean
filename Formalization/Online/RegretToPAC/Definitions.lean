import Formalization.Online.SourceOptimism.SequentialEpisodeDefinitions
import Formalization.Probability.FiniteSampleDefinitions
import Formalization.MDP.PolicyEnvironmentDefinitions
import Formalization.MDP.ControlledEnvironmentDefinitions
import Formalization.MDP.TrajectoryDefinitions
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Printed regret-to-PAC conversion as Lean propositions (definitions only)

Source: `eq:PAC-from-regret-conversion` (`-regret`, `-pac`) with `eq:uniform-policy-pihat`,
`chapters/onlineRL.tex:113–141` (labels :116, :122, :129, :138), proof :145–183; sampling
protocol `eq:generation-s1k-shk-online`, `chapters/onlineRL.tex:17–41`; the reward is known to
the agent (:20) and lies in `[0,1]` (`prelim.tex:682–683`).

The printed statement is refuted in `Formalization/Online/RegretToPAC/PrintedRefutation.lean`
(`not_Eq_PAC_from_regret_conversion_printed`, all carriers, strictly positive constants; and
`not_Eq_PAC_from_regret_conversion_printed_fixedCarrier`). The true versions are
`eq_PAC_from_regret_conversion_corrected` (constant `C_{S,A,H}`) and
`eq_PAC_from_regret_conversion_restricted` (printed constant `C_{S,A,H+1}` under `C`
nondecreasing in `H`) in `Corrected.lean`.

Model shared by all propositions. The online law is `onlineSequentialEpisodeLaw`: `K` i.i.d.
resets `s₁ᵏ ~ ρ` (protocol (i)) and a causal path in which the episode-k policy is
`planner (history.take (k*H))`, a function of the completed episodes `1..k-1` only (protocol
(ii)), executed in the true nonstationary MDP `E` (protocol (iii)). Algorithms are finite-seed
mixtures of deterministic causal planners: given the seed and the completed history the deployed
policy `πᵏ` is deterministic and Markov. The source also allows randomized deployed policies
(`a_h^k ~ π_h^k(·|s)`, :35–38) and arbitrary internal randomization; restricting the algorithm
class makes the printed propositions weaker, so their refutations are not affected. `π̂ = π^J`
with `J` uniform on the `K` episodes and independent of everything else; the probability of the
joint (seed, run, J) experiment is written as the seed- and J-average of the run probabilities.
Values are exact expected trajectory returns; `V⋆` is the return of the backward-induction
greedy policy. The algorithm sees the horizon, `K`, the known reward table and its seed, but not
the transitions or `ρ`. Episode counts and horizons are positive (`0 < H`, `0 < K`): the source
has `K` episodes of length `H` with `H, K ≥ 1`.
-/

open scoped BigOperators
namespace StatisticalRL.OnlineRL.RegretToPAC

universe u v

/-- Printed regret-to-PAC conversion, `eq:PAC-from-regret-conversion` with
`eq:uniform-policy-pihat`, `chapters/onlineRL.tex:113–141`, in its weakest reading.

One algorithm family (seed law `ν H K` on a finite `Seed`, planner `alg State Action H K r ω`)
is given on every finite carrier pair. The hypothesis is the printed regret bound
`E[Regret(K)] ≤ C_{S,A,H} K^{1-α}` for every carrier pair (nonempty action set), every horizon
`H > 0`, every `K > 0` and every MDP `E` and initial law `ρ`; the constants are strictly
positive, `0 < C_{S,A,H}`. The conclusion is the printed bound with `C_{S,A,H+1}` for every
`δ > 0` and every instance. Each feature (all carriers in the hypothesis, positive constants,
restricted algorithm class) only weakens the proposition. FALSE:
`not_Eq_PAC_from_regret_conversion_printed`. -/
def Eq_PAC_from_regret_conversion_printed : Prop :=
  ∀ (Seed : Type) [Fintype Seed] (ν : ℕ → ℕ → FiniteDistribution Seed)
    (alg : (State : Type u) → (Action : Type v) → [Fintype State] → [Fintype Action] →
      [Nonempty Action] → (H : ℕ) → ℕ → (Fin H → State → Action → ℝ) → Seed →
      OnlineEpisodePlanner State Action H)
    (C : ℕ → ℕ → ℕ → ℝ) (α : ℝ), (∀ S A H, 0 < C S A H) → 0 ≤ α → α ≤ 1 →
    (∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action] [Nonempty Action]
      (H K : ℕ) (hH : 0 < H), 0 < K →
      ∀ (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State),
      let fallback : State := Classical.choice (E ⟨0, hH⟩).state_nonempty
      let planner : Seed → OnlineEpisodePlanner State Action H :=
        alg State Action H K (fun h ↦ (E h).reward)
      let law : Seed →
          FiniteDistribution ((Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H)) :=
        fun ω ↦ onlineSequentialEpisodeLaw H K hH E ρ fallback (planner ω) (K * H)
      let πk : Seed → (Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H) →
          Fin K → Fin H → State → Action :=
        fun ω sample k ↦ planner ω ((onlineSequentialPathHistory
          (onlineEpisodicChoose H K hH sample.1 fallback (planner ω)) (K * H) [] sample.2).take
            (k.val * H))
      let V : (Fin H → State → Action) → State → ℝ := fun f ↦
        DecisionStage.trajectoryValue
          (List.ofFn (fun h : Fin H ↦ (E h).withPolicy (fun t ↦ EnvironmentStage.pointMass (f h t))))
      let Vstar : State → ℝ :=
        DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E))
      (ν H K).expectation (fun ω ↦ (law ω).expectation (fun sample ↦
          ∑ k : Fin K, (Vstar (sample.1 k) - V (πk ω sample k) (sample.1 k)))) ≤
        C (Fintype.card State) (Fintype.card Action) H * (K : ℝ) ^ (1 - α)) →
    ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action] [Nonempty Action]
      (H K : ℕ) (hH : 0 < H), 0 < K →
      ∀ (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State) (δ : ℝ),
      0 < δ →
      let fallback : State := Classical.choice (E ⟨0, hH⟩).state_nonempty
      let planner : Seed → OnlineEpisodePlanner State Action H :=
        alg State Action H K (fun h ↦ (E h).reward)
      let law : Seed →
          FiniteDistribution ((Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H)) :=
        fun ω ↦ onlineSequentialEpisodeLaw H K hH E ρ fallback (planner ω) (K * H)
      let πk : Seed → (Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H) →
          Fin K → Fin H → State → Action :=
        fun ω sample k ↦ planner ω ((onlineSequentialPathHistory
          (onlineEpisodicChoose H K hH sample.1 fallback (planner ω)) (K * H) [] sample.2).take
            (k.val * H))
      let V : (Fin H → State → Action) → State → ℝ := fun f ↦
        DecisionStage.trajectoryValue
          (List.ofFn (fun h : Fin H ↦ (E h).withPolicy (fun t ↦ EnvironmentStage.pointMass (f h t))))
      let Vstar : State → ℝ :=
        DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E))
      1 - δ ≤ (ν H K).expectation (fun ω ↦ (1 / (K : ℝ)) * ∑ k : Fin K,
        (law ω).rowMeasure.real {sample |
          ρ.expectation Vstar - ρ.expectation (V (πk ω sample k)) ≤
            C (Fintype.card State) (Fintype.card Action) (H + 1) * (K : ℝ) ^ (-α) / δ})

/-- Printed regret-to-PAC conversion, fixed-carrier reading, `chapters/onlineRL.tex:113–141`.

The state and action carriers are fixed; the algorithm (seed law `ν H K`, planner `alg H K r ω`)
and the regret hypothesis range over every MDP on these carriers ("for any MDP with S states, A
actions and horizon H" read inside one `(S, A)` class), every `H > 0` and `K > 0`. The constants
`C : ℕ → ℕ → ℕ → ℝ` carry no sign condition. FALSE:
`not_Eq_PAC_from_regret_conversion_printed_fixedCarrier`. Kept as a second, independent
refutation of the fixed-class reading; the all-carriers proposition
`Eq_PAC_from_regret_conversion_printed` is the primary one. -/
def Eq_PAC_from_regret_conversion_printed_fixedCarrier : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Fintype Action]
    (Seed : Type) [Fintype Seed] (ν : ℕ → ℕ → FiniteDistribution Seed)
    (alg : (H : ℕ) → ℕ → (Fin H → State → Action → ℝ) → Seed →
      OnlineEpisodePlanner State Action H)
    (C : ℕ → ℕ → ℕ → ℝ) (α : ℝ), 0 ≤ α → α ≤ 1 →
    (∀ (H K : ℕ) (hH : 0 < H), 0 < K →
      ∀ (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State),
      let fallback : State := Classical.choice (E ⟨0, hH⟩).state_nonempty
      let planner : Seed → OnlineEpisodePlanner State Action H :=
        alg H K (fun h ↦ (E h).reward)
      let law : Seed →
          FiniteDistribution ((Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H)) :=
        fun ω ↦ onlineSequentialEpisodeLaw H K hH E ρ fallback (planner ω) (K * H)
      let πk : Seed → (Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H) →
          Fin K → Fin H → State → Action :=
        fun ω sample k ↦ planner ω ((onlineSequentialPathHistory
          (onlineEpisodicChoose H K hH sample.1 fallback (planner ω)) (K * H) [] sample.2).take
            (k.val * H))
      let V : (Fin H → State → Action) → State → ℝ := fun f ↦
        DecisionStage.trajectoryValue
          (List.ofFn (fun h : Fin H ↦ (E h).withPolicy (fun t ↦ EnvironmentStage.pointMass (f h t))))
      let Vstar : State → ℝ :=
        DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E))
      (ν H K).expectation (fun ω ↦ (law ω).expectation (fun sample ↦
          ∑ k : Fin K, (Vstar (sample.1 k) - V (πk ω sample k) (sample.1 k)))) ≤
        C (Fintype.card State) (Fintype.card Action) H * (K : ℝ) ^ (1 - α)) →
    ∀ (H K : ℕ) (hH : 0 < H), 0 < K →
      ∀ (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State) (δ : ℝ),
      0 < δ →
      let fallback : State := Classical.choice (E ⟨0, hH⟩).state_nonempty
      let planner : Seed → OnlineEpisodePlanner State Action H :=
        alg H K (fun h ↦ (E h).reward)
      let law : Seed →
          FiniteDistribution ((Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H)) :=
        fun ω ↦ onlineSequentialEpisodeLaw H K hH E ρ fallback (planner ω) (K * H)
      let πk : Seed → (Fin K → State) × OnlineOutcomePath.{u, 0} State (K * H) →
          Fin K → Fin H → State → Action :=
        fun ω sample k ↦ planner ω ((onlineSequentialPathHistory
          (onlineEpisodicChoose H K hH sample.1 fallback (planner ω)) (K * H) [] sample.2).take
            (k.val * H))
      let V : (Fin H → State → Action) → State → ℝ := fun f ↦
        DecisionStage.trajectoryValue
          (List.ofFn (fun h : Fin H ↦ (E h).withPolicy (fun t ↦ EnvironmentStage.pointMass (f h t))))
      let Vstar : State → ℝ :=
        DecisionStage.trajectoryValue (EnvironmentStage.greedyStages (List.ofFn E))
      1 - δ ≤ (ν H K).expectation (fun ω ↦ (1 / (K : ℝ)) * ∑ k : Fin K,
        (law ω).rowMeasure.real {sample |
          ρ.expectation Vstar - ρ.expectation (V (πk ω sample k)) ≤
            C (Fintype.card State) (Fintype.card Action) (H + 1) * (K : ℝ) ^ (-α) / δ})

end StatisticalRL.OnlineRL.RegretToPAC
