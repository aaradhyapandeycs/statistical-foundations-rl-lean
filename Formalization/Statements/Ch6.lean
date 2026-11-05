import Formalization.OfflineRL.BanditDefinitions
import Formalization.OfflineRL.VILCBDefinitions
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

end StatisticalRL.Statements.Ch6
