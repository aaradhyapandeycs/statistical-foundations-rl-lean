import Formalization.OfflineRL.BanditDefinitions
import Formalization.OfflineRL.VILCBDefinitions
import Formalization.MDP.DiscountedOccupancy
import Formalization.MDP.OptimalTrajectoryValue
import Formalization.Probability.VarianceDefinitions
import Formalization.OfflineRL.LowerBoundFamilyDefinitions
import Formalization.Probability.FiniteSampleDefinitions
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

end StatisticalRL.Statements.Ch6
