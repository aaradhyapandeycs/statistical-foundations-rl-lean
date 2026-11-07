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
`chapters/offlineRL.tex:1529–1537`; proof `:4277–4335`). `π⋆` is the optimal greedy policy,
`P⋆` its transition rows (`eq:P-b-star-infinite`, `:1038–1045`) and `d⋆_ρ` its actual discounted
state occupancy. The source proves the lemma for the VI-LCB output `V̂` and penalty `b⋆` inside
the proof of Theorem 6.3, on its high-probability event; this entry instead assumes the facts that
the source's proof consumes: `0 ≤ V ≤ 1/(1-γ)`, `b ≥ 0` and `0 ≤ V - γ P⋆ V + 2b`
(a consequence of `eq:infinite-v-lower`, `:1311–1327`, since rewards are nonnegative), together
with `γ > 0`. It does not derive those facts for `V̂`. See
[`SOURCE-ISSUES.md#statement-index-scope-disclosures`](../../docs/SOURCE-ISSUES.md#statement-index-scope-disclosures). -/
def Lemma6_7_restricted : Prop :=
  ∀ (S : Type u) (A : Type v) [Fintype S] [Fintype A] (M : DiscountedMDP S A)
    (ρ : FiniteDistribution S) (V b : S → ℝ),
    0 < M.discount →
    (∀ s, 0 ≤ V s) → (∀ s, V s ≤ 1 / (1 - M.discount)) → (∀ s, 0 ≤ b s) →
    (∀ s, 0 ≤ V s - M.discount *
      (M.policyTransition M.optimalGreedyPolicy s).expectation V + 2 * b s) →
    ∑ s, M.discountedStateOccupancy M.optimalGreedyPolicy ρ s *
        (M.policyTransition M.optimalGreedyPolicy s).variance V ≤
      2 / (M.discount ^ 2 * (1 - M.discount)) +
        (4 / (M.discount ^ 2 * (1 - M.discount))) *
          ∑ s, M.discountedStateOccupancy M.optimalGreedyPolicy ρ s * b s

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

end StatisticalRL.Statements.Ch6
