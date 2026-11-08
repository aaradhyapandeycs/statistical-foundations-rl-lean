import Formalization.Statements.Ch3Definitions
import Formalization.ModelFree.QLearningRobustDefinitions

/-!
# Chapter 7 robust MDP objects (definitions only)

Source: arXiv:2610.41903v1, `chapters/robust_RL.tex`.

* RMDP `{S, A, γ, U^σ(P^0), r}` (:19–30). We represent it by a `DiscountedMDP`
  whose `transition` field is the nominal kernel `P^0` (reward in `[0,1]`,
  `0 ≤ γ < 1`), together with a row-ball family and the radius `σ`.
* `(s,a)`-rectangular uncertainty set (:31–48): a complete kernel is admissible
  when every row lies in the ball around the nominal row.
* The two divergences (:52): TV (`intro.tex:223`, represented on a finite carrier
  by the equivalent half-L1 distance, as in `Statements/Ch7.lean` `Lemma7_1`) and
  χ² (`intro.tex:228–234`, defined only for `P ≪ P^0`; reused from
  `QLearning.qChiBall`, which imposes the support condition explicitly).
* Robust value `V^{π,σ}(s) = inf_{P ∈ U^σ(P^0)} V^{π,P}(s)` (:71–84), with
  `V^{π,P}` the actual infinite-trajectory value of the stationary policy.
* Robust Q-function `Q^{π,σ}(s,a) = inf_{P ∈ U^σ(P^0)} Q^{π,P}(s,a)` (:77), with
  `Q^{π,P}` the actual forced-first-action infinite-trajectory value
  (`DiscountedMDP.trajectoryExpectedQ`, `defn:Qpi-inf-horizon`); static adversary (:78).
* Optimal robust value `V^{⋆,σ}(s) = max_π V^{π,σ}(s)` (:88–98), represented
  as the supremum over stationary randomized policies (no attainment assumed).
* Robust Bellman operator (:118–131, empirical version :230–236) with the inner
  infimum evaluated exactly over the row ball.
* DRVI (:243–289): `Q̂_0 = 0` (:245, :268), `Q̂_t = T̂^σ(Q̂_{t-1})`, run on the
  empirical nominal kernel (:206–212) built from `N` generative samples per
  state-action pair (:135–147); the output is any greedy selector of `Q̂_T`
  (:254–258, :286; ties unspecified in the source).

The sampling law and empirical model are reused from the Chapter 3
definitions (`ModelBasedPolicyLearning.samplingLaw`, `empiricalModel`).
-/

open scoped BigOperators

namespace StatisticalRL.RobustRL.Ch7

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- A family of row uncertainty balls `U^σ(p) ⊆ Δ(S)` indexed by the nominal
row `p` and the radius `σ` (`robust_RL.tex:41–46`). -/
abbrev RowBall (State : Type*) [Fintype State] :=
  FiniteDistribution State → ℝ → Set (FiniteDistribution State)

/-- TV ball `{q : TV(q,p) ≤ σ}`; on a finite carrier the event TV
`sup_A |P(A)-Q(A)|` (`intro.tex:223`) equals the half-L1 distance. -/
def tvBall : RowBall State :=
  fun p σ ↦ {q | (1 / 2 : ℝ) * ∑ x, |p.prob x - q.prob x| ≤ σ}

/-- χ² ball `{q : q ≪ p, χ²(q‖p) ≤ σ}` (`intro.tex:228–234`), reusing the
project's support-aware ball `QLearning.qChiBall`. -/
noncomputable def chiBall : RowBall State :=
  fun p σ ↦ QLearning.qChiBall p σ

/-- The same reward and discount with an arbitrary complete transition kernel
`P` in place of the nominal one; `V^{π,P}` is the value in this MDP. -/
def withKernel (M : DiscountedMDP State Action)
    (K : State → Action → FiniteDistribution State) : DiscountedMDP State Action where
  state_nonempty := M.state_nonempty
  action_nonempty := M.action_nonempty
  transition := K
  reward := M.reward
  reward_nonneg := M.reward_nonneg
  reward_le_one := M.reward_le_one
  discount := M.discount
  discount_nonneg := M.discount_nonneg
  discount_lt_one := M.discount_lt_one

/-- `(s,a)`-rectangular membership `P ∈ U^σ(P^0) = ⊗_{s,a} U^σ(P^0_{s,a})`
(`robust_RL.tex:39–46`), with `P^0 = M.transition`. -/
def RobustAdmissible (ball : RowBall State) (M : DiscountedMDP State Action) (σ : ℝ)
    (K : State → Action → FiniteDistribution State) : Prop :=
  ∀ s a, K s a ∈ ball (M.transition s a) σ

/-- Robust value `V^{π,σ}(s) = inf_{P ∈ U^σ(P^0)} V^{π,P}(s)` (`robust_RL.tex:76–79`),
the infimum of actual infinite-trajectory values over admissible kernels. -/
noncomputable def robustPolicyValue (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) (π : StationaryPolicy State Action) (s : State) : ℝ :=
  sInf {v | ∃ K, RobustAdmissible ball M σ K ∧
    v = (withKernel M K).trajectoryExpectedValue π s}

/-- Robust Q-function `Q^{π,σ}(s,a) = inf_{P ∈ U^σ(P^0)} Q^{π,P}(s,a)` (`robust_RL.tex:77`),
the infimum of actual forced-first-action infinite-trajectory values over admissible kernels. -/
noncomputable def robustPolicyQ (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) (π : StationaryPolicy State Action) (s : State) (a : Action) : ℝ :=
  sInf {v | ∃ K, RobustAdmissible ball M σ K ∧
    v = (withKernel M K).trajectoryExpectedQ π s a}

/-- Optimal robust value `V^{⋆,σ}(s) = max_π V^{π,σ}(s)` (`robust_RL.tex:94–96`),
as a supremum over stationary randomized policies. -/
noncomputable def robustOptimalValue (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) (s : State) : ℝ :=
  sSup (Set.range fun π : StationaryPolicy State Action ↦ robustPolicyValue ball M σ π s)

/-- `V(μ) = E_{s∼μ} V(s)` for an initial distribution `μ`. -/
noncomputable def robustPolicyValueAt (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) (π : StationaryPolicy State Action) (μ : FiniteDistribution State) : ℝ :=
  μ.expectation (robustPolicyValue ball M σ π)

/-- `V^{⋆,σ}(μ) = E_{s∼μ} V^{⋆,σ}(s)`. -/
noncomputable def robustOptimalValueAt (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) (μ : FiniteDistribution State) : ℝ :=
  μ.expectation (robustOptimalValue ball M σ)

/-- The exact inner infimum `inf_{q ∈ U^σ(p)} ⟨q, V⟩`. -/
noncomputable def rowRobustInf (ball : RowBall State) (p : FiniteDistribution State)
    (σ : ℝ) (V : State → ℝ) : ℝ :=
  sInf ((fun q : FiniteDistribution State ↦ q.expectation V) '' ball p σ)

/-- Robust Bellman operator `T^σ(Q)(s,a) = r(s,a) + γ inf_{P ∈ U^σ(P_{s,a})} ⟨P, V⟩`,
`V(s) = max_a Q(s,a)` (`robust_RL.tex:118–131`). Applied to the empirical model
this is `T̂^σ` (`robust_RL.tex:230–236`). -/
noncomputable def robustBellman (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) (Q : State → Action → ℝ) (s : State) (a : Action) : ℝ :=
  letI : Nonempty Action := M.action_nonempty
  M.reward s a + M.discount *
    rowRobustInf ball (M.transition s a) σ (fun t ↦ actionMaximum (Q t))

/-- DRVI iterates `Q̂_0 = 0`, `Q̂_t = T^σ(Q̂_{t-1})` (`robust_RL.tex:245–252`). -/
noncomputable def drviIterate (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) : ℕ → State → Action → ℝ
  | 0 => 0
  | t + 1 => robustBellman ball M σ (drviIterate ball M σ t)

/-- DRVI run on the empirical nominal kernel `P̂^0` of `N > 0` generative samples
per state-action pair (`robust_RL.tex:206–212`, Algorithm `alg:cvi-dro-infinite`). -/
noncomputable def empiricalDRVI (ball : RowBall State) (M : DiscountedMDP State Action)
    (σ : ℝ) (N : ℕ) (hN : 0 < N)
    (data : ModelBasedPolicyLearning.Samples State Action N) (T : ℕ) :
    State → Action → ℝ :=
  drviIterate ball (ModelBasedPolicyLearning.empiricalModel M N hN data) σ T

/-- `f` is a greedy selector `f(s) ∈ argmax_a Q(s,a)` (`robust_RL.tex:254–258`);
the source leaves the tie rule unspecified. -/
def IsGreedy (Q : State → Action → ℝ) (f : State → Action) : Prop :=
  ∀ s a, Q s a ≤ Q s (f s)

/-- The deterministic stationary policy `s ↦ δ_{f(s)}`. -/
noncomputable def detPolicy (f : State → Action) : StationaryPolicy State Action :=
  fun s ↦ EnvironmentStage.pointMass (f s)

end StatisticalRL.RobustRL.Ch7
