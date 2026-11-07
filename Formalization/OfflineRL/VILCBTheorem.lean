import Formalization.OfflineRL.VILCBDeterministic
import Formalization.OfflineRL.SampleSplitActual

/-!
# Theorem 6.3 (`thm:infinite-offline`, VI-LCB): the high-probability guarantee

Source: `chapters/offlineRL.tex:899–920` (statement), `:1031–1623` (proof). The dataset is `N` iid
triples `((s_i,a_i), s_i')` with `(s_i,a_i) ~ d^b` and `s_i' ~ P(·|s_i,a_i)`
(`eq:sampling-offline-inf-iid`, `:28–39`). The proof works on the intersection of the Lemma 6.5
count event (probability `> 1-δ`, `SampleSplitActual.sampleSplit_count_lower_of_jointLaw`) and the
Lemma 6.6 event (probability `≥ 1-δ`, `LeaveOneOut.bernsteinInfinite_iid` at level `p.δ`), so with
probability at least `1 - 2δ` every greedy VI-LCB output is `ε`-optimal. Constants:
`c_b ≥ 96` and `c₁ = 10⁴ c_b`.
-/

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace StatisticalRL.OfflineVILCB.Theorem63

open StatisticalRL StatisticalRL.OfflineVILCB StatisticalRL.OfflineRL.LCBQ

universe u v w

/-- The sample-size condition forces `N ≥ 2` (the `N ≥ 2` premise of the Lemma 6.5 export,
`docs/SOURCE-ISSUES.md#C19`). -/
theorem two_le_N_of_sample_size {cb Sc C L₂ k ε N : ℝ} (hcb : 96 ≤ cb) (hS : 1 ≤ Sc)
    (hC : 1 ≤ C) (hL₂ : 1 / 2 ≤ L₂) (hk : 0 < k) (hk1 : k ≤ 1 / 2) (hε : 0 < ε)
    (hε1 : ε ≤ 1 / k)
    (hNcond : 10000 * cb * Sc * C * L₂ / (k ^ 3 * ε ^ 2) ≤ N) : 2 ≤ N := by
  have hden : 0 < k ^ 3 * ε ^ 2 := by positivity
  have hkε : k * ε ≤ 1 := by rw [le_div_iff₀ hk] at hε1; linarith
  have hden1 : k ^ 3 * ε ^ 2 ≤ 1 := by
    have e : k ^ 3 * ε ^ 2 = k * (k * ε) ^ 2 := by ring
    rw [e]
    have : (k * ε) ^ 2 ≤ 1 := by
      have h0 : 0 ≤ k * ε := by positivity
      nlinarith
    nlinarith
  rw [div_le_iff₀ hden] at hNcond
  have hnum : 2 ≤ 10000 * cb * Sc * C * L₂ := by
    have h1 : 1 ≤ Sc * C := by nlinarith
    have h2 : 48 ≤ cb * L₂ := by nlinarith
    have h3 : cb * L₂ ≤ cb * L₂ * (Sc * C) := by
      have : 0 ≤ cb * L₂ := by linarith
      nlinarith
    nlinarith
  have hN0 : 0 ≤ N := by nlinarith
  nlinarith

/-- The Lemma 6.5 count event, read on the realized counts of a dataset. -/
theorem count_event_dataCount {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty S] [Nonempty A] (db : FiniteDistribution (S × A)) (N : ℕ) (δ : ℝ)
    (x : Fin N → (S × A) × S) :
    letI : MeasurableSpace (S × A) := ⊤
    OfflineRL.SampleSplitActual.rowLabels x ∈
        OfflineRL.sampleSplitCountLowerEvent db.rowMeasure N δ →
      ∀ s a, max ((dataCount x s a : ℕ) : ℝ)
        ((2 / 3 : ℝ) * Real.log ((Fintype.card S : ℝ) * N / δ)) ≥ (N : ℝ) * db.prob (s, a) / 12 := by
  letI : MeasurableSpace (S × A) := ⊤
  intro hx s a
  classical
  have h := hx (s, a)
  have hmass : db.rowMeasure.real {(s, a)} = db.prob (s, a) := by
    unfold Measure.real FiniteDistribution.rowMeasure
    rw [@PMF.toMeasure_apply_singleton _ ⊤ _ (s, a) MeasurableSpace.measurableSet_top]
    unfold FiniteDistribution.toPMF
    rw [PMF.ofFintype_apply, ENNReal.toReal_ofReal (db.prob_nonneg (s, a))]
  have hcount : ((OfflineRL.visitCount (fun i (y : Fin N → S × A) => y i) (s, a)
      (OfflineRL.SampleSplitActual.rowLabels x) : ℕ) : ℝ) = ((dataCount x s a : ℕ) : ℝ) := by
    unfold OfflineRL.visitCount OfflineRL.SampleSplitActual.rowLabels dataCount
    rw [Finset.card_filter]
  rw [hmass, hcount] at h
  exact h

/-- **Theorem 6.3** (`thm:infinite-offline`, `offlineRL.tex:899–920`) with `c_b ≥ 96` and
`c₁ = 10⁴ c_b`: for `N` iid triples from `d^b ⊗ P`, with probability at least `1 - 2δ`, every
greedy VI-LCB policy `π̂` (any tie rule) satisfies `V⋆(ρ) − V^{π̂}(ρ) ≤ ε`. `π⋆` is any
`Q⋆`-greedy deterministic policy and `C⋆` (in `ℝ≥0∞`) is computed from it; the premises of Lemma 6.7
are discharged inside the proof (`lemma67_instance`). The statement-index entry is `Thm6_3`. -/
theorem vilcb_infinite_offline (cb : ℝ) (hcb : 96 ≤ cb)
    (S : Type u) (A : Type v) [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
    (M : DiscountedMDP S A) (db : FiniteDistribution (S × A)) (p : Params S A)
    (hγ : p.γ = M.discount) (hr : p.r = M.reward) (hpcb : p.cb = cb) (hhalf : 1 / 2 ≤ M.discount)
    (τmax : ℕ) (hτ : (1 / (1 - M.discount)) * Real.log (p.N / (1 - M.discount)) ≤ τmax)
    (ρ : FiniteDistribution S) (πstar : S → A)
    (hopt : ∀ s, M.optimalityFixedPoint s (πstar s) = actionMaximum (M.optimalityFixedPoint s))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1 / (1 - M.discount))
    (hC : concentrability M ρ πstar db ≠ ⊤)
    (hNcond : 10000 * cb * Fintype.card S * (concentrability M ρ πstar db).toReal *
        Real.log (p.N * Fintype.card S / ((1 - M.discount) * p.δ)) /
        ((1 - M.discount) ^ 3 * ε ^ 2) ≤ p.N)
    (Ω : Type w) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    letI : MeasurableSpace ((S × A) × S) := ⊤
    ∀ X : Ω → Fin p.N → (S × A) × S, Measurable X → iIndepFun (fun i ω => X ω i) μ →
      (∀ i, μ.map (fun ω => X ω i) = ∑ x : (S × A) × S,
        ENNReal.ofReal (db.prob x.1 * (M.transition x.1.1 x.1.2).prob x.2) • Measure.dirac x) →
      1 - 2 * p.δ ≤ μ.real {ω | ∀ πhat : S → A,
        (∀ s a, (p.input (X ω)).iter τmax s a ≤ (p.input (X ω)).iter τmax s (πhat s)) →
        ρ.expectation (M.trajectoryExpectedValue M.optimalGreedyPolicy) -
          ρ.expectation (M.trajectoryExpectedValue (fun x => EnvironmentStage.pointMass (πhat x)))
            ≤ ε} := by
  letI : MeasurableSpace (S × A) := ⊤
  letI : MeasurableSpace ((S × A) × S) := ⊤
  intro X hX hind hmarg
  subst hpcb
  have hhalfp : 1 / 2 ≤ p.γ := hγ ▸ hhalf
  have hδ := p.δ_pos
  have hδ1 := p.δ_lt_one
  -- `N ≥ 2`
  have hS1 : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hN1 : (1 : ℝ) ≤ p.N := by exact_mod_cast p.N_pos
  have hk' : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  obtain ⟨-, hL₂half, -⟩ := log_facts hhalf M.discount_lt_one hδ hδ1 hN1 hS1
  have hN2 : 2 ≤ p.N := by
    have h := two_le_N_of_sample_size hcb hS1 (one_le_concentrability M ρ πstar db hC) hL₂half
      hk' (by linarith) hε hε1 hNcond
    exact_mod_cast h
  -- the two events
  have hlaw := LeaveOneOut.iidTriples_map_eq_jointRow db M.transition μ p.N X hX hind hmarg
  have h65 := OfflineRL.SampleSplitActual.sampleSplit_count_lower_of_jointLaw μ db M.transition
    p.N hN2 p.δ hδ hδ1 X hX hlaw
  have h66 := LeaveOneOut.bernsteinInfinite_iid p hhalfp db M.transition μ p.δ hδ hδ1 X hX hind
    hmarg
  set E5 := {ω | OfflineRL.SampleSplitActual.rowLabels (X ω) ∈
    OfflineRL.sampleSplitCountLowerEvent db.rowMeasure p.N p.δ} with hE5
  set E6 := {ω | X ω ∈ LeaveOneOut.goodSet p M.transition p.δ} with hE6
  have hsub : E5 ∩ E6 ⊆ {ω | ∀ πhat : S → A,
      (∀ s a, (p.input (X ω)).iter τmax s a ≤ (p.input (X ω)).iter τmax s (πhat s)) →
      ρ.expectation (M.trajectoryExpectedValue M.optimalGreedyPolicy) -
        ρ.expectation (M.trajectoryExpectedValue (fun x => EnvironmentStage.pointMass (πhat x)))
          ≤ ε} := by
    rintro ω ⟨h5, h6⟩ πhat hgreedy
    exact gap_le_of_good M db p hγ hr hcb hhalf τmax hτ ρ πstar hopt ε hε hε1 hC hNcond (X ω) h6
      (count_event_dataCount db p.N p.δ (X ω) h5) πhat hgreedy
  -- probability of the intersection
  have hm5 : MeasurableSet E5 :=
    hX (t := {x | OfflineRL.SampleSplitActual.rowLabels x ∈
      OfflineRL.sampleSplitCountLowerEvent db.rowMeasure p.N p.δ}) ((Set.to_countable _).measurableSet)
  have hm6 : MeasurableSet E6 :=
    hX (t := LeaveOneOut.goodSet p M.transition p.δ) ((Set.to_countable _).measurableSet)
  have hc5 := measureReal_compl (μ := μ) hm5
  have hc6 := measureReal_compl (μ := μ) hm6
  have hc56 := measureReal_compl (μ := μ) (hm5.inter hm6)
  rw [probReal_univ] at hc5 hc6 hc56
  have hu : μ.real (E5 ∩ E6)ᶜ ≤ μ.real E5ᶜ + μ.real E6ᶜ := by
    rw [Set.compl_inter]; exact measureReal_union_le _ _
  have hmono := measureReal_mono (μ := μ) hsub
  linarith

end StatisticalRL.OfflineVILCB.Theorem63
