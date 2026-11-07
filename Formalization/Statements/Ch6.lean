import Formalization.OfflineRL.BanditDefinitions
import Formalization.OfflineRL.VILCBDefinitions
import Formalization.MDP.DiscountedOccupancy
import Formalization.MDP.OptimalTrajectoryValue
import Formalization.Probability.VarianceDefinitions
import Formalization.OfflineRL.LowerBoundFamilyDefinitions
import Formalization.Probability.FiniteSampleDefinitions
import Formalization.OfflineRL.VILCBDatasetDefinitions
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Independence.Basic
import Formalization.OfflineRL.LCBQDefinitions
import Formalization.OfflineRL.FiniteVILCB.Definitions
import Formalization.OfflineRL.FiniteLCBQ.Definitions
import Formalization.MDP.FiniteOccupancy

/-! Chapter 6 source-facing statements. Corrected variants are labeled explicitly;
this index does not claim that the full monograph is complete. -/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.Statements.Ch6

universe u v

/-- **Theorem 6.1, commented-fallback variant** (`thm:MAB_LCB_upper`,
`chapters/offlineRL.tex:456–471`; proof `:524–578`). The data law and sample
threshold are the printed ones. At zero count this statement uses the separately
commented convention mean 0, radius 1 (`:429–430`); the active pseudocode leaves
that branch undefined, and Lean's `x / 0 = 0` gives a different radius. See
`docs/SOURCE-ISSUES.md#C18`. This is not a proof for the active undefined
pseudocode. -/
def Thm6_1_zeroCountFallback_corrected : Prop :=
  ∀ (Arm : Type u) [Fintype Arm] [DecidableEq Arm] [MeasurableSpace Arm]
    [MeasurableSingletonClass Arm] (d : Measure Arm) [IsProbabilityMeasure d] (r : Arm → ℝ),
    (∀ b, 0 ≤ r b) → (∀ b, r b ≤ 1) →
    ∀ aStar : Arm, (∀ b, r b ≤ r aStar) → 0 < d.real {aStar} →
    ∀ (N : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
    8 * (1 / d.real {aStar}) * Real.log (2 / δ) ≤ N →
    1 - δ ≤ (StatisticalRL.OfflineRL.offlineBanditLaw d N).real
      {ω : (Fin N → Arm) × (Fin N → ℝ) | ∀ aL : Arm,
        (∀ b, StatisticalRL.OfflineRL.lcbFallback r ω.1 ω.2 δ b ≤
          StatisticalRL.OfflineRL.lcbFallback r ω.1 ω.2 δ aL) →
        r aStar - r aL ≤
          4 * Real.sqrt ((1 / d.real {aStar}) * Real.log (4 * Fintype.card Arm / δ) / N)}

/-- **Lemma 6.2, corrected variant** (`lem:monotone-contraction`,
`chapters/offlineRL.tex:872–890`; proof `:3205–3484`). It adds `1/2 ≤ γ`, used
in the printed proof at `:3343`, and retains the printed conclusions on that
restricted domain. The unrestricted standalone claim is documented at
`docs/SOURCE-ISSUES.md#C10`; this result does not refute parent Theorem 6.3,
whose hypotheses include `γ ≥ 1/2`. -/
def Lemma6_2_corrected : Prop :=
  ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A]
    (M : StatisticalRL.OfflineVILCB.Input S A) [Nonempty A],
    1 / 2 ≤ M.γ →
    ∃ Qstar : S → A → ℝ, M.pess Qstar = Qstar ∧
      (∀ Q, M.pess Q = Q → Q = Qstar) ∧
      (∀ τ : ℕ, M.iter τ ≤ Qstar ∧ ‖M.iter τ - Qstar‖ ≤ M.γ ^ τ / (1 - M.γ)) ∧
      (∀ τ : ℕ, Real.log (M.N / (1 - M.γ)) / Real.log (1 / M.γ) ≤ τ →
        ‖M.iter τ - Qstar‖ ≤ 1 / M.N)


section SampleSplitCorrected

universe w

open Classical in
/-- **Lemma 6.5, restricted sample-splitting result** (`lem:sample-split-infinite`,
`chapters/offlineRL.tex:1104–1114`; sampling model `:28–37`, count definition
`:672–678`). This formalized version assumes `2 ≤ N`; the standalone source lemma
does not state that restriction. The parent theorem's sample-size condition
implies it. See `docs/SOURCE-ISSUES.md#C19`. The event is under the actual iid
joint law of state-action-next-state triples; the row-projection and emitted
sample laws are proved dependencies. -/
noncomputable def Lemma6_5_sampleSplit_actualData_corrected : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (ρ : FiniteDistribution (State × Action))
    (P : State → Action → FiniteDistribution State)
    (Ω : Type w) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ), 2 ≤ N → ∀ δ : ℝ, 0 < δ → δ < 1 →
    letI : MeasurableSpace ((State × Action) × State) := ⊤
    ∀ X : Ω → Fin N → (State × Action) × State, Measurable X →
      iIndepFun (fun i ω => X ω i) μ →
      (∀ i, μ.map (fun ω => X ω i) =
        ∑ t : (State × Action) × State,
          ENNReal.ofReal (ρ.prob t.1 * (P t.1.1 t.1.2).prob t.2) • Measure.dirac t) →
      1 - δ < μ.real {ω | ∀ sa : State × Action,
        max (((Finset.univ.filter fun i : Fin N => (X ω i).1 = sa).card : ℕ) : ℝ)
            ((2 / 3 : ℝ) * Real.log ((Fintype.card State : ℝ) * N / δ)) ≥
          (N : ℝ) * ρ.prob sa / 12}

end SampleSplitCorrected


/-- **Lemma 6.4 in the parent Theorem 6.3 regime** (`lem:offline-prelim`,
`chapters/offlineRL.tex:1078–1094`; parent assumptions `:903–928`). The source
conditions `γ ≥ 1/2` and the stopping rule are explicit. The unique fixed point
is derived, not assumed; the result proves the source value-error and penalty-
difference estimates. It is an auxiliary result and does not establish the
parent policy guarantee. -/
def Lemma6_4 : Prop :=
  ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A]
    (M : StatisticalRL.OfflineVILCB.Input S A) [Nonempty A],
    1 / 2 ≤ M.γ →
    ∀ τ : ℕ,
      (1 / (1 - M.γ)) * Real.log (M.N / (1 - M.γ)) ≤ τ →
      ∃ Qstar : S → A → ℝ,
        M.pess Qstar = Qstar ∧
        (∀ Q, M.pess Q = Q → Q = Qstar) ∧
        ‖StatisticalRL.OfflineVILCB.Input.value (M.iter τ) -
          StatisticalRL.OfflineVILCB.Input.value Qstar‖ ≤ 1 / M.N ∧
        ∀ s a,
          |M.bonus s a (StatisticalRL.OfflineVILCB.Input.value Qstar) -
            M.bonus s a (StatisticalRL.OfflineVILCB.Input.value (M.iter τ))| ≤ 2 / M.N

/-- **Lemma 6.7, restricted to its displayed premises** (`lem:sum-d-Var-UB`,
`chapters/offlineRL.tex:1529–1537`; proof `:4277–4335`). The source's `π⋆` is the optimal
deterministic policy (`:138`); the entry quantifies over every stationary policy `π`, so it covers
every optimal deterministic policy and every tie rule among them. `P⋆` is the policy's transition rows (`eq:P-b-star-infinite`, `:1038–1045`) and `d⋆_ρ` its actual discounted
state occupancy. The source proves the lemma for the VI-LCB output `V̂` and penalty `b⋆` inside
the proof of Theorem 6.3, on its high-probability event; this entry instead assumes the facts that
the source's proof consumes: `0 ≤ V ≤ 1/(1-γ)`, `b ≥ 0` and `0 ≤ V - γ P⋆ V + 2b`
(a consequence of `eq:infinite-v-lower`, `:1311–1327`, since rewards are nonnegative), together
with `γ > 0`. It does not derive those facts for `V̂`. See
[`SOURCE-ISSUES.md#statement-index-scope-disclosures`](../../docs/SOURCE-ISSUES.md#statement-index-scope-disclosures). -/
def Lemma6_7_restricted : Prop :=
  ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A] (M : DiscountedMDP S A)
    (π : StationaryPolicy S A) (ρ : FiniteDistribution S) (V b : S → ℝ),
    0 < M.discount →
    (∀ s, 0 ≤ V s) → (∀ s, V s ≤ 1 / (1 - M.discount)) → (∀ s, 0 ≤ b s) →
    (∀ s, 0 ≤ V s - M.discount *
      (M.policyTransition π s).expectation V + 2 * b s) →
    ∑ s, M.discountedStateOccupancy π ρ s *
        (M.policyTransition π s).variance V ≤
      2 / (M.discount ^ 2 * (1 - M.discount)) +
        (4 / (M.discount ^ 2 * (1 - M.discount))) *
          ∑ s, M.discountedStateOccupancy π ρ s * b s

/-- **Lemma 6.14, restricted optimal-action clause** (`lemma:value-policy-LB-inf`, `chapters/offlineRL.tex:2544–2583`; proof
`:5502–5679`) for the hard family `M_θ` of `:2432–2516` (`lbMDP`): states `{0,…,S-1}` are
`Option (Fin m)` with `S = m + 1` (`none` = 0), actions `{0,1}` are `Bool` (`false` = 0),
`p = γ + 224(1-γ)²ε/γ`, `q = γ - 224(1-γ)²ε/γ`. The standing assumptions of the construction
(`eq:infinite-epsilon-assumption`: `2/3 ≤ γ < 1`, `224(1-γ)ε/γ ≤ 1/2`; `C > 2`; `S ≥ 2`) are
hypotheses; the values, the policy bound and `π⋆(0|0) = 1` are proved for every `ε ≥ 0`. The
identification `π⋆(θ_s|s) = 1` is restricted to `ε > 0`: Theorem 6.13 does not assume `ε > 0`,
and for `ε = 0` both actions at `s > 0` are optimal, so the fixed greedy tie rule need not pick
`θ_s`. See
[`SOURCE-ISSUES.md#statement-index-scope-disclosures`](../../docs/SOURCE-ISSUES.md#statement-index-scope-disclosures). `V⋆_θ` is the
trajectory value of the optimal greedy policy `π⋆_θ`; `V^π_θ` ranges over all stationary
randomized policies. -/
def Lemma6_14_restricted : Prop :=
  ∀ (m : ℕ) (hm : 1 ≤ m) (γ ε C : ℝ) (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1) (hε : 0 ≤ ε)
    (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C) (θ : Fin m → Bool),
    let M := StatisticalRL.OfflineRL.LowerBound.lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ
    let Vs := M.trajectoryExpectedValue M.optimalGreedyPolicy
    let p : ℝ := γ + 224 * (1 - γ) ^ 2 * ε / γ
    let q : ℝ := γ - 224 * (1 - γ) ^ 2 * ε / γ
    (∀ (π : StationaryPolicy (Option (Fin m)) Bool) (i : Fin m),
      let x := p * (π (some i)).prob (θ i) + q * (π (some i)).prob (!θ i)
      M.trajectoryExpectedValue π (some i) ≤
        (1 + γ * (1 - x) * (C⁻¹ * Vs (some i) + (1 - C⁻¹) * Vs none)) / (1 - γ * x)) ∧
    (∀ i : Fin m,
      let x := p * (M.optimalGreedyPolicy (some i)).prob (θ i) +
        q * (M.optimalGreedyPolicy (some i)).prob (!θ i)
      Vs (some i) =
        (1 + γ * (1 - x) * (C⁻¹ * Vs (some i) + (1 - C⁻¹) * Vs none)) / (1 - γ * x)) ∧
    (M.optimalGreedyPolicy none).prob false = 1 ∧
    (0 < ε → ∀ i, (M.optimalGreedyPolicy (some i)).prob (θ i) = 1) ∧
    Vs none = 4 / (7 * (1 - γ)) ∧
    ∀ i, Vs (some i) = (1 + γ * (1 - p) * (1 - C⁻¹) * Vs none) / (1 - γ * (p + (1 - p) * C⁻¹))

/-- **Lemma 6.15** (`lem:transition-KL-bound-infinite`, `chapters/offlineRL.tex:2835–2865`; proof
`:5680ff`) for the hard family of Lemma 6.14 (`lbMDP`, same encoding and standing assumptions).
For every `θ, θ̃ ∈ {0,1}^{S-1}` (in particular for the source's `Θ`), every positive state and
every action, the KL divergence between the two next-state laws vanishes when `θ_s = θ̃_s` and is
at most `c₃(1-γ)³ε²` otherwise, for one universal constant `c₃` (here `c₃ = 16 · 336²` works).
Next-state laws are the actual transition rows as probability measures on the finite state
space. -/
def Lemma6_15 : Prop :=
  ∃ c₃ : ℝ, 0 < c₃ ∧
    ∀ (m : ℕ) (hm : 1 ≤ m) (γ ε C : ℝ) (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1) (hε : 0 ≤ ε)
      (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C) (θ θ' : Fin m → Bool) (i : Fin m)
      (a : Bool),
      let M := StatisticalRL.OfflineRL.LowerBound.lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ
      let M' := StatisticalRL.OfflineRL.LowerBound.lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ'
      (θ i = θ' i →
        InformationTheory.klDiv (M.transition (some i) a).rowMeasure
          (M'.transition (some i) a).rowMeasure = 0) ∧
      (θ i ≠ θ' i →
        InformationTheory.klDiv (M.transition (some i) a).rowMeasure
          (M'.transition (some i) a).rowMeasure ≤ ENNReal.ofReal (c₃ * (1 - γ) ^ 3 * ε ^ 2))

/-- **Lemma 6.11, restricted** (`lemma:useful`, `chapters/offlineRL.tex:2292–2300`; proof
`:4674–4785`), with `H = ⌈4 log(SAT/δ)/(1-γ)⌉` (`eq:defn-H-lcbq-stepsize-proof`, `:1667–1672`),
`κ = γ(1+1/H)³` (`eq:defn-kappa-proof-lcbq`) and the source's `≲` made explicit as one universal
constant `C`. `ρᵀ P_π^j` is the actual time-`j` state law of the policy `π⋆` (the optimal greedy
policy) started from `ρ`, `d_ρ^⋆` its discounted occupancy and `‖W‖` the sup norm; `S = |𝒮|`.
The printed lemma is false without a premise of this kind: `κ < 1` can fail, and even with
`κ < 1` no universal constant works when `log(SAT/δ)` is small (candidate C22). This entry
assumes `log(SAT/δ) ≥ 1`, a sufficient condition. Theorem 6.8's hypotheses do not imply it. In
the remaining corner `δ > SAT/e` they give, for `c₂ ≥ 32`, `κ ≤ 1/2` and `δ/(ST⁴) > 1/(8e)`,
which yield the conclusion, so that theorem is unaffected; this entry does not cover that
corner. See
[`SOURCE-ISSUES.md#statement-index-scope-disclosures`](../../docs/SOURCE-ISSUES.md#statement-index-scope-disclosures). -/
def Lemma6_11_restricted : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A] (M : DiscountedMDP S A)
      (ρ : FiniteDistribution S) (δ : ℝ) (T : ℕ) (W : S → ℝ),
      0 < δ → δ < 1 → 1 ≤ T →
      1 ≤ Real.log ((Fintype.card S : ℝ) * Fintype.card A * T / δ) →
      (∀ s, 0 ≤ W s) →
      let γ := M.discount
      let H : ℕ := ⌈4 / (1 - γ) * Real.log ((Fintype.card S : ℝ) * Fintype.card A * T / δ)⌉₊
      let κ := γ * (1 + 1 / (H : ℝ)) ^ 3
      ∑' j : ℕ, κ ^ j * ∑ s, M.occupancyStateAt M.optimalGreedyPolicy ρ j s * W s ≤
        C * ((∑ s, M.discountedStateOccupancy M.optimalGreedyPolicy ρ s * W s) / (1 - γ) +
          δ * ‖W‖ / ((Fintype.card S : ℝ) * (T : ℝ) ^ 4 * (1 - γ)))

/-- **Theorem 6.13** (`thm:infinite-lwoer-bound`, `chapters/offlineRL.tex:2367–2402`; hard
instances `:2432–2634`, proof `:2638–2927`, Appendix C `:5498–5933`). There is a universal
`c₂ > 0` such that for every `γ ∈ [2/3, 1)`, `S > 12`, `C⋆ > 2` and `ε ≤ 1/(672(1-γ))` there are
a class `{M_θ : θ ∈ Θ}` of MDPs with `S` states and 2 actions (finite `Θ`, shared discount `γ`,
shared rewards), a test distribution `ρ` and a data distribution `d^b` whose single-policy
concentrability coefficient `C⋆_ρ = max_{(s,a)} d⋆(s,a;ρ)/d^b(s,a)` (`eq:concentrate-infinite-simple`,
`:128–140`) lies in `[C⋆, 2C⋆]` for every `θ`, such that for every `N ≤ c₂ S C⋆/((1-γ)³ε²)` and
every policy estimator `π̂` (a deterministic map from datasets to stationary randomized policies;
estimators using external randomness are not covered literally, though the Fano argument extends) some `θ` has
`P_θ(V⋆_θ(ρ) - V^π̂_θ(ρ) > ε) ≥ 1/4`. This `∃ θ` for every `π̂` is the printed
`inf_π̂ max_θ ≥ 1/4`.

Conventions: `d⋆` is the discounted joint occupancy of the optimal greedy (deterministic) policy
started from `ρ`. The ratio is taken in `ℝ≥0∞`, so `0/0 = 0` and `x/0 = ∞`. `V(ρ) = ∑_s ρ(s) V(s)`.
The dataset is `N` iid triples `((s,a),s')` with `(s,a) ~ d^b` and `s' ~ P_θ(·|s,a)`
(`eq:sampling-offline-inf-iid`, `:31–39`). Its law is the `N`-fold product of the displayed finite
sum of point masses on the discrete σ-algebra.

Accuracy endpoint (`docs/SOURCE-ISSUES.md#C9`): the printed hypotheses are kept. `ε > 0` is not
assumed. For `ε < 0` the event holds with probability one. At `ε = 0` the printed threshold
divides by zero; with Lean's `x/0 = 0` it reads `N ≤ 0`, and the statement then holds by a
construction at a positive admissible accuracy. This entry does not cover a reading of the
`ε = 0` threshold as "every `N`". -/
def Thm6_13 : Prop :=
  ∃ c₂ : ℝ, 0 < c₂ ∧
    ∀ (γ : ℝ) (S : ℕ) (Cstar ε : ℝ), 2 / 3 ≤ γ → γ < 1 → 12 < S → 2 < Cstar →
      ε ≤ 1 / (672 * (1 - γ)) →
      ∃ (State : Type) (_ : Fintype State) (Θ : Type) (_ : Fintype Θ)
        (M : Θ → DiscountedMDP State Bool) (ρ : FiniteDistribution State)
        (db : FiniteDistribution (State × Bool)),
        Fintype.card State = S ∧
        (∀ θ, (M θ).discount = γ) ∧
        (∀ θ θ', (M θ).reward = (M θ').reward) ∧
        (∀ θ,
          ENNReal.ofReal Cstar ≤
              ⨆ sa : State × Bool,
                ENNReal.ofReal
                    ((M θ).discountedJointOccupancy (M θ).optimalGreedyPolicy ρ sa.1 sa.2) /
                  ENNReal.ofReal (db.prob sa) ∧
            (⨆ sa : State × Bool,
                ENNReal.ofReal
                    ((M θ).discountedJointOccupancy (M θ).optimalGreedyPolicy ρ sa.1 sa.2) /
                  ENNReal.ofReal (db.prob sa)) ≤ ENNReal.ofReal (2 * Cstar)) ∧
        ∀ N : ℕ, (N : ℝ) ≤ c₂ * S * Cstar / ((1 - γ) ^ 3 * ε ^ 2) →
          letI : MeasurableSpace ((State × Bool) × State) := ⊤
          ∀ πhat : (Fin N → (State × Bool) × State) → StationaryPolicy State Bool,
            ∃ θ, (1 : ℝ) / 4 ≤
              (Measure.pi fun _ : Fin N =>
                  ∑ t : (State × Bool) × State,
                    ENNReal.ofReal (db.prob t.1 * ((M θ).transition t.1.1 t.1.2).prob t.2) •
                      Measure.dirac t).real
                {D | ε < ∑ s, ρ.prob s *
                    ((M θ).trajectoryExpectedValue (M θ).optimalGreedyPolicy s -
                      (M θ).trajectoryExpectedValue (πhat D) s)}

section BernsteinInfinite

universe w

/-- **Lemma 6.18** (`lem:Bernstein-infinite-proof`, `chapters/offlineRL.tex:3635–3662`; proof
`:4339–4405`). Conditional-on-counts encoding: for a fixed pair `(s,a)` with
`n = N_{s,a} > 0`, the source probability is conditional on the visitation counts, and under that
conditioning `P̂_{s,a}` is the empirical row of `n` iid draws from `P_{s,a}` (`:1126–1128`). This
entry quantifies over every probability space carrying such draws (`draw`, with law
`d.sampleMeasure n`, `d = P_{s,a}`) and a random vector `V` that is measurable, independent of that
empirical row (discrete σ-algebra on rows) and satisfies `0 ≤ V ≤ 1/(1-γ)`. With probability at
least `1 - 8δ`, both printed inequalities hold. -/
def Lemma6_18 : Prop :=
  ∀ (S : Type u) [Fintype S] (Ω : Type v) [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (d : StatisticalRL.FiniteDistribution S) (γ : ℝ), 0 ≤ γ → γ < 1 →
    ∀ δ : ℝ, 0 < δ → δ < 1 / 8 →
    ∀ (n : ℕ) (hn : 0 < n),
    letI : MeasurableSpace S := ⊤
    ∀ draw : Ω → Fin n → S, Measurable draw → μ.map draw = d.sampleMeasure n →
    ∀ V : Ω → S → ℝ, Measurable V →
      (letI : MeasurableSpace (StatisticalRL.FiniteDistribution S) := ⊤
       IndepFun V (fun ω => StatisticalRL.FiniteDistribution.empiricalRow n hn (draw ω)) μ) →
      (∀ ω s, 0 ≤ V ω s ∧ V ω s ≤ 1 / (1 - γ)) →
      1 - 8 * δ ≤ μ.real {ω |
        |(StatisticalRL.FiniteDistribution.empiricalRow n hn (draw ω)).expectation (V ω) -
            d.expectation (V ω)| ≤
          Real.sqrt (4 * (StatisticalRL.FiniteDistribution.empiricalRow n hn (draw ω)).variance (V ω) *
            Real.log (1 / δ) / n) + 5 * Real.log (1 / δ) / ((1 - γ) * n) ∧
        (StatisticalRL.FiniteDistribution.empiricalRow n hn (draw ω)).variance (V ω) ≤
          2 * d.variance (V ω) + 5 * Real.log (1 / δ) / (3 * (1 - γ) ^ 2 * n)}

/-- **Lemma 6.6** (`lem:Bernstein-infinite`, `chapters/offlineRL.tex:1147–1163`; proof
`:3630–4273`). Data: `N` iid triples with `(s,a) ~ ρ` and `s' ~ P(·|s,a)` (`:28–37`), with counts
`N_{s,a}` and empirical rows `P̂` (the uniform row when `N_{s,a} = 0`) as in `:672–695`, and the
penalty of `def:bonus-Bernstein-infinite` (`:808–824`) with parameters `p.cb`, `p.δ`.
`V̂⋆_pe` is the value of any fixed point `Q̂⋆_pe` of `T_pess` for the realized data; for
`γ ≥ 1/2` such a fixed point exists and is unique (corrected Lemma 6.2, `docs/SOURCE-ISSUES.md#C10`).
As printed, the same `δ` appears in the penalty and in the probability `1 - δ`.

Scope disclosure: the entry carries the premise `0 < N_{s,a}`. The printed right-hand sides divide
by `N_{s,a}`; the source's claim that the zero-count case is "trivial" (`:3632`) holds only when
those right sides are read as `+∞`, and is false under Lean's `x / 0 = 0` (the uniform row differs
from `P_{s,a}`). The printed proof's covering-set bound assumes `N ≥ 5` (`docs/SOURCE-ISSUES.md#C23`);
the formal proof splits per pair: pairs with `N_{s,a} ≤ 26` satisfy both bounds surely, and the
union bound runs over pairs with `N_{s,a} ≥ 27`. -/
def Lemma6_6 : Prop :=
  ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
    (ρ : StatisticalRL.FiniteDistribution (S × A))
    (P : S → A → StatisticalRL.FiniteDistribution S)
    (p : StatisticalRL.OfflineVILCB.Params S A), 1 / 2 ≤ p.γ →
    ∀ (Ω : Type w) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
    letI : MeasurableSpace ((S × A) × S) := ⊤
    ∀ X : Ω → Fin p.N → (S × A) × S, Measurable X →
      iIndepFun (fun i ω => X ω i) μ →
      (∀ i, μ.map (fun ω => X ω i) =
        ∑ t : (S × A) × S, ENNReal.ofReal (ρ.prob t.1 * (P t.1.1 t.1.2).prob t.2) • Measure.dirac t) →
      1 - p.δ ≤ μ.real {ω |
        ∀ Qstar : S → A → ℝ, (p.input (X ω)).pess Qstar = Qstar →
        ∀ (s : S) (a : A), 0 < (p.input (X ω)).count s a →
        ∀ Vt : S → ℝ,
          (∀ t, |Vt t - StatisticalRL.OfflineVILCB.Input.value Qstar t| ≤ 1 / p.N) →
          (∀ t, |Vt t| ≤ 1 / (1 - p.γ)) →
          |((p.input (X ω)).Phat s a).expectation Vt - (P s a).expectation Vt| ≤
              Real.sqrt (8 * Real.log (4 * p.N / ((1 - p.γ) * p.δ)) / (p.input (X ω)).count s a *
                ((p.input (X ω)).Phat s a).variance Vt) +
              26 * Real.log (4 * p.N / ((1 - p.γ) * p.δ)) / ((1 - p.γ) * (p.input (X ω)).count s a) ∧
          ((p.input (X ω)).Phat s a).variance Vt ≤
              2 * (P s a).variance Vt +
              24 * Real.log (4 * p.N / ((1 - p.γ) * p.δ)) /
                ((1 - p.γ) ^ 2 * (p.input (X ω)).count s a)}

end BernsteinInfinite


section LCBQ

universe w

/-- **Lemma 6.9** (`lemma:Q-recursion-pessimistic-Q`, `chapters/offlineRL.tex:1866–1893`; proof
`:4415–4528`). For some `c_b₀ > 0` and every `c_b ≥ c_b₀` ("provided that the constant `c_b` is
large enough", `:1884`), with probability at least `1 − δ`, simultaneously for all `1 ≤ t ≤ T`, all
`(s,a)` and all deterministic `π` (including data-dependent ones), `eq:qstar-recursion-lcbq` and
`eq:uniform-policy-pessimism-recursion` hold. `β_n = 3c_b√(Hι/(n(1-γ)²))` for `n ≥ 1`; `β_0 = +∞`
is encoded by stating (a) only for `0 < n`. The proof supplies `c_b₀ = 4`.

Model (`alg:q-infinite-lcb`, `chapters/offlineRL.tex:1701–1745`, parameters
`eq:stepsize-penalty-offlineQ` `:1663–1689`): `OfflineRL.LCBQ.run` runs the algorithm on the `T` data
triples `X ω`, which are iid with `(s,a) ~ d^b` and `s' ~ P(·|s,a)` (`eq:sampling-offline-inf-iid`,
`:28–39`), from `Q ≡ 0`, `V ≡ 0`, `n ≡ 0` and an arbitrary initial deterministic policy `π₀`.
`ι = log(SAT/δ)` and `H = ⌈4ι/(1-γ)⌉`. `visitTime (X ω) (s,a) i` is the zero-based index of the
`(i+1)`-st visit, so `(it (k i)).V` is the source's `V_{k_{i+1}(s,a)-1}`. `Q⋆` is the optimality
Bellman fixed point and `V⋆` is the trajectory value of the optimal greedy policy; `Q^π, V^π` are the
actual trajectory Q and V of the deterministic policy `π`.
Tie rule: the arg max in the policy update is `sel` applied to the current Q-row, for every `sel`
with the arg-max property. This covers every deterministic tie rule that depends only on the
Q-row (for example any rule on the arg-max set). It does not cover tie rules that depend on the
state, the iteration or the history.
Because the printed algorithm leaves the arg-max tie rule unspecified, this entry is indexed as
`Lemma6_9_restricted` (`docs/SOURCE-ISSUES.md#statement-index-scope-disclosures`).
Proof route: the printed proof applies Azuma–Hoeffding at random visit times without a filtration
(`docs/SOURCE-ISSUES.md#C28`, part 2). The formal proof instead conditions on the state-action
labels; given them the successors are independent, the visit ranks are fixed and the run is causal.
It applies Azuma–Hoeffding to each `(s,a,n)` and takes a union bound with radius
`2√(H log(2SAT/δ)/(n(1-γ)²))`, which is absorbed for `c_b ≥ 4` (at `T = 1` the martingale term is
`0`). This is an alternative proof, not a validation of the printed step. -/
def Lemma6_9_restricted : Prop :=
  ∃ cb₀ : ℝ, 0 < cb₀ ∧ ∀ cb : ℝ, cb₀ ≤ cb →
    ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A] (M : DiscountedMDP S A)
      (db : FiniteDistribution (S × A)) (sel : (A → ℝ) → A), (∀ (f : A → ℝ) (a : A), f a ≤ f (sel f)) →
      ∀ (π₀ : S → A) (T : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
      ∀ (Ω : Type w) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
      letI : MeasurableSpace ((S × A) × S) := ⊤
      ∀ X : Ω → Fin T → (S × A) × S, Measurable X → iIndepFun (fun i ω => X ω i) μ →
      (∀ i, μ.map (fun ω => X ω i) = ∑ x : (S × A) × S,
        ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) • Measure.dirac x) →
      1 - δ ≤ μ.real {ω | ∀ t, 1 ≤ t → t ≤ T → ∀ (s : S) (a : A),
        let γ := M.discount
        let ι := OfflineRL.LCBQ.iota S A T δ
        let H := OfflineRL.LCBQ.horizon γ ι
        let it := OfflineRL.LCBQ.run M cb δ sel π₀ (X ω)
        let k := OfflineRL.LCBQ.visitTime (X ω) (s, a)
        let n := (it t).count s a
        (0 < n → M.optimalityFixedPoint s a - (it t).Q s a ≤
            γ * ∑ i ∈ Finset.range n, OnlineRL.onlineQRateWeight H n (i + 1) *
              (M.transition s a).expectation (fun s' =>
                M.trajectoryExpectedValue M.optimalGreedyPolicy s' - (it (k i)).V s') +
            3 * cb * Real.sqrt (H * ι / (n * (1 - γ) ^ 2))) ∧
        ∀ π : S → A,
          γ * ∑ i ∈ Finset.range n, OnlineRL.onlineQRateWeight H n (i + 1) *
              (M.transition s a).expectation (fun s' =>
                M.trajectoryExpectedValue (fun x => EnvironmentStage.pointMass (π x)) s' -
                  (it (k i)).V s') ≤
            M.trajectoryExpectedQ (fun x => EnvironmentStage.pointMass (π x)) s a - (it t).Q s a}

/-- **Lemma 6.10, restricted variant** (`lemma:pessimistic-Q`, `chapters/offlineRL.tex:1907–1916`;
proof `:4530–4672`). With probability exceeding `1 − δ`, `Q_t ≤ Q⋆` and `V_t ≤ V^{π_t} ≤ V⋆` for all
`(s,a)` and all `1 ≤ t ≤ T` (`eq:pessimistic-lcbq`), where `π_t` is the policy iterate
(`eq:analysis-policy-lcbq`, `:1825–1831`).
Difference from the printed lemma: it adds the premise `∃ c_b₀ > 0, ∀ c_b ≥ c_b₀`. The printed
lemma states no condition on `c_b`, and for small `c_b` it is false (exact counterexample in
`docs/SOURCE-ISSUES.md#C28`). The premise is the standing assumption of Lemma 6.9 (`:1884`) and of
Theorem 6.8 (`:1764`), whose proof uses this lemma. The proof supplies `c_b₀ = 4`.

Model (`alg:q-infinite-lcb`, `chapters/offlineRL.tex:1701–1745`, parameters
`eq:stepsize-penalty-offlineQ` `:1663–1689`): `OfflineRL.LCBQ.run` runs the algorithm on the `T` data
triples `X ω`, which are iid with `(s,a) ~ d^b` and `s' ~ P(·|s,a)` (`eq:sampling-offline-inf-iid`,
`:28–39`), from `Q ≡ 0`, `V ≡ 0`, `n ≡ 0` and an arbitrary initial deterministic policy `π₀`.
`ι = log(SAT/δ)` and `H = ⌈4ι/(1-γ)⌉`. `visitTime (X ω) (s,a) i` is the zero-based index of the
`(i+1)`-st visit, so `(it (k i)).V` is the source's `V_{k_{i+1}(s,a)-1}`. `Q⋆` is the optimality
Bellman fixed point and `V⋆` is the trajectory value of the optimal greedy policy; `Q^π, V^π` are the
actual trajectory Q and V of the deterministic policy `π`.
Tie rule: the arg max in the policy update is `sel` applied to the current Q-row, for every `sel`
with the arg-max property. This covers every deterministic tie rule that depends only on the
Q-row (for example any rule on the arg-max set). It does not cover tie rules that depend on the
state, the iteration or the history.
Proof route: the printed proof applies Azuma–Hoeffding at random visit times without a filtration
(`docs/SOURCE-ISSUES.md#C28`, part 2). The formal proof instead conditions on the state-action
labels; given them the successors are independent, the visit ranks are fixed and the run is causal.
It applies Azuma–Hoeffding to each `(s,a,n)` and takes a union bound with radius
`2√(H log(2SAT/δ)/(n(1-γ)²))`, which is absorbed for `c_b ≥ 4` (at `T = 1` the martingale term is
`0`). This is an alternative proof, not a validation of the printed step. -/
def Lemma6_10_restricted : Prop :=
  ∃ cb₀ : ℝ, 0 < cb₀ ∧ ∀ cb : ℝ, cb₀ ≤ cb →
    ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A] (M : DiscountedMDP S A)
      (db : FiniteDistribution (S × A)) (sel : (A → ℝ) → A), (∀ (f : A → ℝ) (a : A), f a ≤ f (sel f)) →
      ∀ (π₀ : S → A) (T : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
      ∀ (Ω : Type w) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
      letI : MeasurableSpace ((S × A) × S) := ⊤
      ∀ X : Ω → Fin T → (S × A) × S, Measurable X → iIndepFun (fun i ω => X ω i) μ →
      (∀ i, μ.map (fun ω => X ω i) = ∑ x : (S × A) × S,
        ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) • Measure.dirac x) →
      1 - δ < μ.real {ω | ∀ t, 1 ≤ t → t ≤ T →
        let it := OfflineRL.LCBQ.run M cb δ sel π₀ (X ω) t
        (∀ s a, it.Q s a ≤ M.optimalityFixedPoint s a) ∧
        ∀ s, it.V s ≤ M.trajectoryExpectedValue (fun x => EnvironmentStage.pointMass (it.policy x)) s ∧
          M.trajectoryExpectedValue (fun x => EnvironmentStage.pointMass (it.policy x)) s ≤
            M.trajectoryExpectedValue M.optimalGreedyPolicy s}

/-- **Lemma 6.12, restricted variant** (`lem:lcbq-alpha-xi-psi-phi-bound`,
`chapters/offlineRL.tex:2309–2324`; proof `:4786–5496`). The five sequences are `eq:dj-offlineQ` and
`eq:five-sequence-def-offlineQ` (`:1970–2015`), and their limits `α, ξ, θ, ψ, φ` are those of
`eq:five-terms-def-offlineQ` (`:2276`). The algorithm, data model and `C⋆` are as in `Lemma6_9_restricted`,
and `C⋆` refers to the deterministic policy `πstar`.

Difference from the printed lemma: it adds the premise `log(SAT/δ) ≥ 1`. This premise is
sufficient (it gives `κ < 1` and `H ≍ ι/(1-γ)`). It is not the exact region where the printed
lemma fails. The printed lemma fails when `ι` is small, see `docs/SOURCE-ISSUES.md#C24`.

The following are faithful readings, not restrictions:
- "`c_b` large enough" is `∃ c_b₀, ∀ c_b ≥ c_b₀`, and `≲` is a constant `C` that depends only on
  `c_b`. The proof gives `c_b₀ = 4` and `C = 400000 + 5600 c_b`.
- `α = 0` is stated as `α_j → 0`. `ξ, θ, ψ, φ` are `HasSum` limits.
- The `θ` and `ψ + φ` bounds are guarded by `C⋆ ≠ ⊤`; when `C⋆ = ⊤` the printed right-hand sides
  are `+∞`.
- No sample-size condition on `T` is assumed, although the printed proof uses that of Theorem 6.8.
- The hypotheses that `πstar` is `Q⋆`-greedy and that `sel` maximises are carried as in the
  source. The proof does not use them.

The printed proof has gaps: the confidence budget, `φ` on poorly covered pairs, and Freedman on a
non-predictable event. See `docs/SOURCE-ISSUES.md#C29`. The formal proof repairs them: each of
five events is run at `δ/5`, there is a no-poorly-covered-sample event, and the Freedman tests are
gated. -/
def Lemma6_12_restricted : Prop :=
  ∃ cb₀ : ℝ, 0 < cb₀ ∧ ∀ cb : ℝ, cb₀ ≤ cb → ∃ C : ℝ, 0 < C ∧
    ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A] (M : DiscountedMDP S A)
      (db : FiniteDistribution (S × A)) (sel : (A → ℝ) → A), (∀ (f : A → ℝ) (a : A), f a ≤ f (sel f)) →
      ∀ (π₀ : S → A) (T : ℕ) (δ : ℝ), 0 < δ → δ < 1 →
      ∀ (ρ : FiniteDistribution S) (πstar : S → A),
      (∀ s, letI : Nonempty A := M.action_nonempty
        M.optimalityFixedPoint s (πstar s) = actionMaximum (M.optimalityFixedPoint s)) →
      1 ≤ OfflineRL.LCBQ.iota S A T δ →
      ∀ (Ω : Type w) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
      letI : MeasurableSpace ((S × A) × S) := ⊤
      ∀ X : Ω → Fin T → (S × A) × S, Measurable X → iIndepFun (fun i ω => X ω i) μ →
      (∀ i, μ.map (fun ω => X ω i) = ∑ x : (S × A) × S,
        ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) • Measure.dirac x) →
      1 - δ ≤ μ.real {ω |
        let γ := M.discount
        let ι := OfflineRL.LCBQ.iota S A T δ
        let Cs := OfflineRL.LCBQ.concentrability M ρ πstar db
        Filter.Tendsto (OfflineRL.LCBQ.alphaSeq M cb δ sel π₀ (X ω) ρ πstar) Filter.atTop
          (nhds 0) ∧
        (∃ ξ, HasSum (OfflineRL.LCBQ.xiSeq M cb δ sel π₀ (X ω) ρ πstar) ξ ∧ ξ ≤ C / (1 - γ) ^ 2) ∧
        (∃ θ, HasSum (OfflineRL.LCBQ.thetaSeq M cb δ sel π₀ (X ω) ρ πstar) θ ∧
          (Cs ≠ ⊤ → θ ≤ C * Real.sqrt (Cs.toReal * Fintype.card S * T * ι ^ 2 / (1 - γ) ^ 5))) ∧
        (∃ ψ φ, HasSum (OfflineRL.LCBQ.psiSeq M cb δ sel π₀ (X ω) ρ πstar db) ψ ∧
          HasSum (OfflineRL.LCBQ.phiSeq M cb δ sel π₀ (X ω) ρ πstar db) φ ∧
          (Cs ≠ ⊤ → ψ + φ ≤ C * Cs.toReal * ι ^ 2 / (1 - γ) ^ 3))}

/-- **Theorem 6.8, corrected** (`theorem:lcbq`, `chapters/offlineRL.tex:1754–1772`; sample-size
condition `eq:sample-size-lcbq-T-thm` at `:1767`; proof `:1804–2357`). The algorithm, data model and
`C⋆` are as in `Lemma6_9_restricted`. `π̂ = π_T` is the output policy of `OfflineRL.LCBQ.run` on the `T` iid
triples. `V⋆(ρ) − V^{π̂}(ρ)` is computed with the actual trajectory values, with `ρ` the test
distribution.

The only mathematical change from the printed theorem is in the sample-size condition: it uses
`log²(SAT/((1-γ)δ))` where the print has `log(SAT/((1-γ)δ))`. As printed, the theorem is false; see
`docs/SOURCE-ISSUES.md#C24`.

The guards are faithful readings:
- `1 ≤ T` is the well-definedness condition for `ι` and `H`.
- `C⋆ ≠ ⊤` encodes "`C⋆` finite". With `C⋆ = ∞` the printed condition cannot be met, but Lean's
  `⊤.toReal = 0` would make it trivially true.
- `c_b` sufficiently large is read as `∃ c_b₀, ∀ c_b ≥ c_b₀, ∃ c₂`. The proof gives `c_b₀ = 4` and
  `c₂ = 16 (400000 + 5600 c_b)²`.
- `π⋆` may be any `Q⋆`-greedy deterministic policy.
- `0 < ε ≤ 1/(1-γ)`, and the probability bound is strict, as printed.

Tie-rule scope: the source allows an arbitrary deterministic tie rule. Here the arg max in the
policy update is `sel` applied to the current Q-row only, so rules that depend on the state, the
iteration or the history are not covered. The corner `δ > SAT/e`, that is `log(SAT/δ) < 1`, is
handled inside the proof from the theorem's own hypotheses: it forces `|A| = 1`, where the gap is
`0`. See `docs/SOURCE-ISSUES.md#C22`. -/
def Thm6_8_corrected : Prop :=
  ∃ cb₀ : ℝ, 0 < cb₀ ∧ ∀ cb : ℝ, cb₀ ≤ cb → ∃ c₂ : ℝ, 0 < c₂ ∧
    ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A] (M : DiscountedMDP S A)
      (db : FiniteDistribution (S × A)) (sel : (A → ℝ) → A), (∀ (f : A → ℝ) (a : A), f a ≤ f (sel f)) →
      ∀ (π₀ : S → A) (T : ℕ) (δ : ℝ), 0 < δ → δ < 1 → 1 ≤ T →
      ∀ (ρ : FiniteDistribution S) (πstar : S → A),
      (∀ s, letI : Nonempty A := M.action_nonempty
        M.optimalityFixedPoint s (πstar s) = actionMaximum (M.optimalityFixedPoint s)) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (1 - M.discount) →
      OfflineRL.LCBQ.concentrability M ρ πstar db ≠ ⊤ →
      c₂ * Fintype.card S * (OfflineRL.LCBQ.concentrability M ρ πstar db).toReal *
          Real.log ((Fintype.card S : ℝ) * Fintype.card A * T / ((1 - M.discount) * δ)) ^ 2 /
          ((1 - M.discount) ^ 5 * ε ^ 2) ≤ T →
      ∀ (Ω : Type w) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
      letI : MeasurableSpace ((S × A) × S) := ⊤
      ∀ X : Ω → Fin T → (S × A) × S, Measurable X → iIndepFun (fun i ω => X ω i) μ →
      (∀ i, μ.map (fun ω => X ω i) = ∑ x : (S × A) × S,
        ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) • Measure.dirac x) →
      1 - δ < μ.real {ω | ρ.expectation (M.trajectoryExpectedValue M.optimalGreedyPolicy) -
        ρ.expectation (M.trajectoryExpectedValue (fun x => EnvironmentStage.pointMass
          ((OfflineRL.LCBQ.run M cb δ sel π₀ (X ω) T).policy x))) ≤ ε}

end LCBQ

section VILCBTheorem

universe w

/-- **Theorem 6.3** (`thm:infinite-offline`, `chapters/offlineRL.tex:899–920`; proof `:1031–1623`,
using the appendix proofs of Lemma 6.4 `:3489–`, Lemma 6.5 `:3541–`, Lemma 6.6 `:3630–` and
Lemma 6.7 `:4277–4342`). Algorithm `alg:vi-lcb-infinite` (`:827–852`) with the Bernstein penalty
`def:bonus-Bernstein-infinite` (`:808–824`), run for `τmax` iterations on `N` iid triples
`((s_i,a_i),s_i')` with `(s_i,a_i) ~ d^b` and `s_i' ~ P(·|s_i,a_i)` (`eq:sampling-offline-inf-iid`,
`:28–39`). This is the printed result, not a corrected or restricted variant.

Readings:
- "`c_b` sufficiently large … for some large enough universal constant `c₁`" is read as
  `∃ c_b₀, ∀ c_b ≥ c_b₀, ∃ c₁` (`c₁` depends on `c_b` only). The proof gives `c_b₀ = 96` and
  `c₁ = 10⁴ c_b`. A `c₁` uniform in `c_b` is false: with one state, two actions (`r = 1, 0`, self-loop),
  `γ = 1/2`, `d^b` on the rewarding action, a fixed `c₁` and `c_b` large enough that every penalty is
  clipped to `1/(1-γ) + 5/N`, every iterate is `Q̂ ≡ 0`, so the bad action is greedy and the gap is
  `2 > ε = 1` surely.
- `C⋆` (`assumption:concentrate-infinite-simple`, `:127–137`) is computed in `ℝ≥0∞` with `0/0 = 0` and
  `x/0 = ∞` for `x > 0`; the premise `C⋆ ≠ ⊤` only removes the case where the printed sample condition
  cannot hold (and blocks Lean's `⊤.toReal = 0`). `C⋆ ≥ 1` is proved, not assumed.
- `π⋆` is any deterministic policy greedy for `Q⋆` at every state, with `C⋆` computed from it; the event
  holds simultaneously for every greedy output `π̂` (every tie rule).
- `N ≥ 1` comes from `Params` (`p.N_pos`); `N ≥ 2` (`docs/SOURCE-ISSUES.md#C19`) is derived from the
  sample-size condition. The same `δ` (`p.δ`) appears in the penalty, the events and `1 - 2δ`.
- `V⋆(ρ)` is the trajectory value of the library's optimal greedy policy `M.optimalGreedyPolicy`;
  `V^{π̂}` is the trajectory value of the deterministic policy `π̂`.
- The restricted premises of `Lemma6_7_restricted` are discharged inside this proof for `V̂`, `b⋆` and
  `π⋆` on the event, as are the positive-count scope of `Lemma6_6` (C23) and the `γ ≥ 1/2` domain of
  `Lemma6_2_corrected` (C10). -/
def Thm6_3 : Prop :=
  ∃ cb₀ : ℝ, 0 < cb₀ ∧ ∀ cb : ℝ, cb₀ ≤ cb → ∃ c₁ : ℝ, 0 < c₁ ∧
    ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
      (M : DiscountedMDP S A) (db : FiniteDistribution (S × A))
      (p : StatisticalRL.OfflineVILCB.Params S A),
      p.γ = M.discount → p.r = M.reward → p.cb = cb → 1 / 2 ≤ M.discount →
      ∀ τmax : ℕ, (1 / (1 - M.discount)) * Real.log (p.N / (1 - M.discount)) ≤ τmax →
      ∀ (ρ : FiniteDistribution S) (πstar : S → A),
      (∀ s, M.optimalityFixedPoint s (πstar s) = actionMaximum (M.optimalityFixedPoint s)) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / (1 - M.discount) →
      OfflineRL.LCBQ.concentrability M ρ πstar db ≠ ⊤ →
      c₁ * Fintype.card S * (OfflineRL.LCBQ.concentrability M ρ πstar db).toReal *
          Real.log (p.N * Fintype.card S / ((1 - M.discount) * p.δ)) /
          ((1 - M.discount) ^ 3 * ε ^ 2) ≤ p.N →
      ∀ (Ω : Type w) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
      letI : MeasurableSpace ((S × A) × S) := ⊤
      ∀ X : Ω → Fin p.N → (S × A) × S, Measurable X → iIndepFun (fun i ω => X ω i) μ →
      (∀ i, μ.map (fun ω => X ω i) = ∑ x : (S × A) × S,
        ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) • Measure.dirac x) →
      1 - 2 * p.δ ≤ μ.real {ω | ∀ πhat : S → A,
        (∀ s a, (p.input (X ω)).iter τmax s a ≤ (p.input (X ω)).iter τmax s (πhat s)) →
        ρ.expectation (M.trajectoryExpectedValue M.optimalGreedyPolicy) -
          ρ.expectation (M.trajectoryExpectedValue (fun x => EnvironmentStage.pointMass (πhat x)))
            ≤ ε}

end VILCBTheorem

section FiniteVILCBTheorem

universe w

/-- **Theorem 6.16, restricted to one explicit variant** (`thm:finite-VI-LCB`,
`chapters/offlineRL.tex:3093–3112`; setting `:2943–2973`, `C⋆` `:2983–2993`, algorithm
`:3020–3062`). See `docs/SOURCE-ISSUES.md#C32`. The book asserts the guarantee for an undefined
"variant of VI-LCB" and gives no proof. This entry is instantiated with one explicit variant,
`FiniteVILCB.qhat`. It is our reconstruction; it is not asserted to be li2024settling's algorithm
(that paper was not consulted), and no claim is made about that paper's algorithm or constants.
* Two-fold split. Trajectories `k < ⌊K/2⌋` (auxiliary) only determine the trimmed counts
  `m_h(s) = ⌊X_a(h,s)/4⌋` if `X_a(h,s) > 16ι`, and `0` otherwise. From the remaining (main)
  trajectories, only the first `m_h(s)` visits to `(h,s)` (in index order) are used. Reading
  `:3061` ("two-fold sample splitting") as aux-determined subsampling of the main half is ours.
* Backward VI-LCB `Q̂_h = max{r_h + P̂_h V̂_{h+1} - b_h, 0}`, `V̂_H = 0` (stages `0,…,H-1`, the
  paper's `h+1`), with `ι = log(16HK/δ)`. The penalty is `‖V̂_{h+1}‖` at zero count, and otherwise
  `min{max{√(c_b ι Var_{P̂}(V̂_{h+1})/N), c_b H ι/N}, ‖V̂_{h+1}‖}` with `‖V‖ = max_s V(s)`; the
  empirical row is uniform at zero count. The clip at `‖V̂_{h+1}‖` (mirroring the `1/(1-γ)` clip of
  `def:bonus-Bernstein-infinite`, `:811–822`) gives `b ≡ 0` at the last stage, which is not
  literally `Θ̃(H/N)` there and not strictly decreasing in `N`.
* Output: the claim holds simultaneously for every greedy `π̂` (every tie rule).
The algorithm reads only `c_b`, `δ`, the rewards and the data.

Readings:
* Constants: `c_b₀ = 16`, `c_k = 69120 c_b` (the printed existential constant).
* `0 < K` is the domain of `log(KH/δ)`. At `K = 0`, Lean's `log 0 = 0` would make the condition
  hold while the claim fails.
* `C⋆ = max_{h,s,a} d⋆_h(s,a;ρ)/d^b_h(s,a)` is computed in `ℝ≥0∞` (`0/0 = 0`) from the library's
  `stateActionOccupancy`. The premise `C⋆ ≠ ⊤` is essential: the printed condition cannot hold
  otherwise, and `⊤.toReal = 0`.
* `π⋆` is any deterministic policy optimal at every stage and state (`prelim.tex:740–745`), with
  `C⋆` computed from it.
* `V⋆` is `EnvironmentStage.optimalValue`; `V^{π̂}` is `DecisionStage.trajectoryValue` of the
  deterministic `π̂`.
* Data: `K` iid trajectories `s_0 ~ ρ^b`, `a_h ~ π^b_h(·|s_h)`, `s_{h+1} ~ P_h(·|s_h,a_h)`
  (`eq:finite-batch-size-def`, law `FiniteVILCB.trajMeasure`). -/
def Thm6_16_restricted : Prop :=
  ∃ cb₀ : ℝ, 0 < cb₀ ∧ ∀ cb : ℝ, cb₀ ≤ cb → ∃ ck : ℝ, 0 < ck ∧
    ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
      (H : ℕ), 0 < H →
      ∀ (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
        (ρb ρ : FiniteDistribution S) (πs : Fin H → S → A),
      (∀ (h : Fin H) (s : S), DecisionStage.trajectoryValue
          (EnvironmentStage.controlled ((List.ofFn E).drop h.val)
            (fun j ↦ FiniteVILCB.extPolicy (FiniteVILCB.detPolicy πs) (h.val + j))) s =
        EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s) →
      ∀ ε δ : ℝ, 0 < ε → ε ≤ H → 0 < δ → δ < 1 →
      ∀ K : ℕ, 0 < K →
      let Cstar : ENNReal := ⨆ (h : Fin H) (s : S) (a : A),
        ENNReal.ofReal (DecisionStage.stateActionOccupancy
            (EnvironmentStage.controlled (List.ofFn E)
              (FiniteVILCB.extPolicy (FiniteVILCB.detPolicy πs))) ρ
            (FiniteVILCB.stageIndex E (FiniteVILCB.extPolicy (FiniteVILCB.detPolicy πs)) h) s a) /
          ENNReal.ofReal (DecisionStage.stateActionOccupancy
            (EnvironmentStage.controlled (List.ofFn E) (FiniteVILCB.extPolicy πb)) ρb
            (FiniteVILCB.stageIndex E (FiniteVILCB.extPolicy πb) h) s a)
      Cstar ≠ ⊤ →
      ck * (H : ℝ) ^ 3 * Fintype.card S * Cstar.toReal * Real.log (K * H / δ) / ε ^ 2 ≤ K →
      ∀ (Ω : Type w) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
      letI : MeasurableSpace (FiniteVILCB.Traj S A H) := ⊤
      ∀ X : Ω → Fin K → FiniteVILCB.Traj S A H, Measurable X → iIndepFun (fun k ω ↦ X ω k) μ →
      (∀ k, μ.map (fun ω ↦ X ω k) = FiniteVILCB.trajMeasure E πb ρb) →
      1 - δ ≤ μ.real {ω | ∀ πhat : Fin H → S → A,
        (∀ h s a, FiniteVILCB.qhat cb δ (fun h ↦ (E h).reward) (X ω) h s a ≤
          FiniteVILCB.qhat cb δ (fun h ↦ (E h).reward) (X ω) h s (πhat h s)) →
        ρ.expectation (EnvironmentStage.optimalValue (List.ofFn E)) -
          ρ.expectation (DecisionStage.trajectoryValue (EnvironmentStage.controlled (List.ofFn E)
            (FiniteVILCB.extPolicy (FiniteVILCB.detPolicy πhat)))) ≤ ε}

end FiniteVILCBTheorem

section FiniteLCBQTheorem

universe w

/-- **Theorem 6.17, restricted to one explicit variant** (`thm:lcbq`,
`chapters/offlineRL.tex:3176–3192`; setting `:2943–2973`, `C⋆` `:2983–2993`, algorithm prose
`:3126–3148`, penalty `eq:lcb-q-penalty` `:3141–3143`). See `docs/SOURCE-ISSUES.md#C33`. The book
cites the result without proof, its algorithm box (`:3150–3173`) is commented out, and the prose
leaves the algorithm under-specified. This entry is instantiated with one explicit completion,
`LCBQFinite.output` (our reconstruction; the cited paper was not consulted):
* zero initialisation of `Q`, `V`, the counts, terminal `V_H ≡ 0`, arbitrary initial policy `π₀`
  (universally quantified);
* one pass over the episodes in index order; inside an episode the stages are processed in
  **forward** order `h = 0, …, H-1` (the natural reading of `:3132`; the commented box runs
  backward), so the stage-`h` update reads `V_{h+1}` from the previous episode;
* `η_n = (H+1)/(H+n)` (`:3139`) and the Hoeffding-style penalty **restricted** to
  `b_n = c_b √(H³ L / n)`, for every `L` with `ι ≤ L ≤ max(ι, ι³)`, `ι = log(SAK/δ)` (this is
  `[ι, ι³]` when `ι ≥ 1`; `L = ι, ι², ι³` give the log powers `1/2, 1, 3/2` outside the root).
  The L-range is never empty (when `ι < 1` it is `{ι}`); for `|A| ≥ 2` the printed size
  condition already forces `ι ≥ 1`, so the widening adds content only when `|A| = 1`. The upper end `ι³` is
  sharp (C33: for `L = ι^{2a}`, `a > 3/2`, the claim fails for every `c_a`); the lower end is
  what the proof needs. The reading "any `Θ̃(√(H³/n))` penalty works" is **false** (C33);
* monotone `V_h(s) ← max{V_h(s), max_a Q_h(s,a)}`;
* **output rule**: `π̂_h(s)` changes only on a strict increase of `V_h(s)`, to `sel(Q_h(s,·))`,
  where `sel` is any deterministic selector of a maximizer (universally quantified); this is the
  rule of `alg:q-infinite-lcb` (`:1726–1731`). It **departs** from the literal reading of `:3145`
  (greedy with respect to the final `Q`), for which the claim is not proved here.
The algorithm reads only `c_b`, `L`, `sel`, `π₀`, the rewards and the data.

Readings:
* Constants: the quantifier shape is `∃ c_b₀ > 0, ∀ c_b ≥ c_b₀, ∃ c_a > 0` (the printed `c_a` is
  existential and must depend on `c_b`); the proof gives `c_b₀ = 5`, `c_a = 10⁶ c_b²`.
* `0 < K` is the domain of `log(SAK/δ)`. At `K = 0`, Lean's `log 0 = 0` would make the size
  condition hold while the claim fails.
* `C⋆ = max_{h,s,a} d⋆_h(s,a;ρ)/d^b_h(s,a)` is computed in `ℝ≥0∞` (`0/0 = 0`) from the library's
  `stateActionOccupancy`, with `d⋆` the occupancy of a **deterministic** optimal policy `π⋆`
  (any deterministic policy optimal at every stage and state, `prelim.tex:740–745`); a stochastic
  optimal policy can have a smaller `C⋆`, so this is a mild restriction of
  `assumption:concentrate-finite`, which does not say which optimal policy defines `d⋆`. The
  premise `C⋆ ≠ ⊤` is essential: the printed condition cannot hold otherwise, and `⊤.toReal = 0`.
* `V⋆` is `EnvironmentStage.optimalValue`; `V^{π̂}` is `DecisionStage.trajectoryValue` of the
  deterministic `π̂`.
* Data: `K` iid trajectories `s_0 ~ ρ^b`, `a_h ~ π^b_h(·|s_h)`, `s_{h+1} ~ P_h(·|s_h,a_h)`
  (`eq:finite-batch-size-def`, law `FiniteVILCB.trajMeasure`). -/
def Thm6_17_restricted : Prop :=
  ∃ cb₀ : ℝ, 0 < cb₀ ∧ ∀ cb : ℝ, cb₀ ≤ cb → ∃ ca : ℝ, 0 < ca ∧
    ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
      (H : ℕ), 0 < H →
      ∀ (E : Fin H → EnvironmentStage S A) (πb : Fin H → StationaryPolicy S A)
        (ρb ρ : FiniteDistribution S) (πs : Fin H → S → A),
      (∀ (h : Fin H) (s : S), DecisionStage.trajectoryValue
          (EnvironmentStage.controlled ((List.ofFn E).drop h.val)
            (fun j ↦ FiniteVILCB.extPolicy (FiniteVILCB.detPolicy πs) (h.val + j))) s =
        EnvironmentStage.optimalValue ((List.ofFn E).drop h.val) s) →
      ∀ ε δ : ℝ, 0 < ε → ε ≤ H → 0 < δ → δ < 1 →
      ∀ K : ℕ, 0 < K →
      ∀ L : ℝ, Real.log (Fintype.card S * Fintype.card A * K / δ) ≤ L →
      L ≤ max (Real.log (Fintype.card S * Fintype.card A * K / δ))
        (Real.log (Fintype.card S * Fintype.card A * K / δ) ^ 3) →
      ∀ sel : (A → ℝ) → A, (∀ (f : A → ℝ) (a : A), f a ≤ f (sel f)) →
      ∀ π₀ : Fin H → S → A,
      let Cstar : ENNReal := ⨆ (h : Fin H) (s : S) (a : A),
        ENNReal.ofReal (DecisionStage.stateActionOccupancy
            (EnvironmentStage.controlled (List.ofFn E)
              (FiniteVILCB.extPolicy (FiniteVILCB.detPolicy πs))) ρ
            (FiniteVILCB.stageIndex E (FiniteVILCB.extPolicy (FiniteVILCB.detPolicy πs)) h) s a) /
          ENNReal.ofReal (DecisionStage.stateActionOccupancy
            (EnvironmentStage.controlled (List.ofFn E) (FiniteVILCB.extPolicy πb)) ρb
            (FiniteVILCB.stageIndex E (FiniteVILCB.extPolicy πb) h) s a)
      Cstar ≠ ⊤ →
      ca * (H : ℝ) ^ 5 * Fintype.card S * Cstar.toReal *
          Real.log (Fintype.card S * Fintype.card A * K / δ) ^ 3 / ε ^ 2 ≤ K →
      ∀ (Ω : Type w) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
      letI : MeasurableSpace (FiniteVILCB.Traj S A H) := ⊤
      ∀ X : Ω → Fin K → FiniteVILCB.Traj S A H, Measurable X → iIndepFun (fun k ω ↦ X ω k) μ →
      (∀ k, μ.map (fun ω ↦ X ω k) = FiniteVILCB.trajMeasure E πb ρb) →
      1 - δ ≤ μ.real {ω |
        ρ.expectation (EnvironmentStage.optimalValue (List.ofFn E)) -
          ρ.expectation (DecisionStage.trajectoryValue (EnvironmentStage.controlled (List.ofFn E)
            (FiniteVILCB.extPolicy (FiniteVILCB.detPolicy
              (LCBQFinite.output cb L sel π₀ (fun h ↦ (E h).reward) (X ω)))))) ≤ ε}

end FiniteLCBQTheorem

end StatisticalRL.Statements.Ch6
