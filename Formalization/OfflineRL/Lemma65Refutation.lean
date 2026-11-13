import Formalization.MDP.CoreDefinitions
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Printed Lemma 6.5 is false at `N = 1` (SOURCE-ISSUES C19 addendum)

Source: `lem:sample-split-infinite`, `chapters/offlineRL.tex:1104–1115`, sampling model
`eq:sampling-offline-inf-iid` (`:28–37`), counts `N_{s,a}` (`:672–678`); `\infs` is an empty
macro (`chapters/commands.tex:223`).

`Lemma6_5_printed` is the statement-index entry `Lemma6_5_sampleSplit_actualData_corrected`
(`Formalization/Statements/Ch6.lean`) with its added premise `2 ≤ N` removed; the printed lemma
states no restriction on `N`. Instance: `S = 1`, `A = 2`, `ρ` uniform, `N = 1`, `δ = 31/32`. The
single sample leaves one action unseen; for it `N_{s,a} = 0` and
`(2/3) log(SN/δ) = (2/3) log(32/31) ≤ 2/93 < 1/24 = N ρ(s,a)/12`, so the event is empty, although
the lemma claims probability exceeding `1/32`. The probability space is the law of one triple
itself (`Ω = (S × A) × S`, `X = id`), so the iid and marginal premises hold.

Classification: genuine counterexample at a boundary case (`S N = 1`), not a Lean junk value:
every quantity (`log(32/31) > 0`, the count `0`) has its genuine value. Whenever `S N ≥ 2` the
printed proof step `|N_large| ≤ N/(8L) ≤ N` holds (C19 addendum).
-/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.OfflineRL

universe u v w

open Classical in
/-- Printed Lemma 6.5 (`lem:sample-split-infinite`, `chapters/offlineRL.tex:1104–1115`):
`Lemma6_5_sampleSplit_actualData_corrected` without the added premise `2 ≤ N`. -/
noncomputable def Lemma6_5_printed : Prop :=
  ∀ (State : Type u) (Action : Type v) [Fintype State] [Nonempty State]
    [Fintype Action] [Nonempty Action]
    (ρ : FiniteDistribution (State × Action))
    (P : State → Action → FiniteDistribution State)
    (Ω : Type w) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : ℕ), ∀ δ : ℝ, 0 < δ → δ < 1 →
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

/-- The uniform data distribution on `Unit × Bool`. -/
noncomputable def lemma65Rho : FiniteDistribution (Unit × Bool) where
  prob := fun _ ↦ 1 / 2
  prob_nonneg := fun _ ↦ by norm_num
  sum_prob := by simp

/-- The (only) transition row on `Unit`. -/
noncomputable def lemma65UnitDist : FiniteDistribution Unit :=
  FiniteDistribution.ofUnique Unit

/-- The discrete σ-algebra on triples (as in the printed statement). -/
local instance lemma65TripleMeasurable : MeasurableSpace ((Unit × Bool) × Unit) := ⊤

/-- The law of one triple `((s,a),s')`: `(s,a) ∼ ρ`, `s' ∼ P(·|s,a)`. -/
noncomputable def lemma65Law : Measure ((Unit × Bool) × Unit) :=
  ∑ t : (Unit × Bool) × Unit,
    ENNReal.ofReal (lemma65Rho.prob t.1 * lemma65UnitDist.prob t.2) • Measure.dirac t

theorem lemma65Law_univ : lemma65Law Set.univ = 1 := by
  simp only [lemma65Law, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply,
    measure_univ, smul_eq_mul, mul_one, lemma65Rho, lemma65UnitDist, FiniteDistribution.ofUnique_prob]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
  simp [Fintype.card_prod]

instance lemma65Law_isProb : IsProbabilityMeasure lemma65Law := ⟨lemma65Law_univ⟩

/-- The `(2/3) log(SN/δ)` threshold at `S = N = 1`, `δ = 31/32` is below `1/24`. -/
theorem lemma65_threshold :
    (2 / 3 : ℝ) * Real.log (((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / (31 / 32)) < 1 / 24 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 32 / 31 by norm_num)
  have he : ((1 : ℕ) : ℝ) * ((1 : ℕ) : ℝ) / (31 / 32) = 32 / 31 := by norm_num
  rw [he]
  linarith

/-- **C19 addendum.** Printed Lemma 6.5 is false at `S = 1`, `A = 2`, `N = 1`, `δ = 31/32`:
the simultaneous event is empty. Boundary case `S N = 1`, not a junk value. -/
theorem not_Lemma6_5_printed : ¬ Lemma6_5_printed.{0, 0, 0} := by
  intro h
  have key := @h Unit Bool _ _ _ _ lemma65Rho (fun _ _ ↦ lemma65UnitDist)
    ((Unit × Bool) × Unit) lemma65TripleMeasurable lemma65Law lemma65Law_isProb 1 (31 / 32)
    (by norm_num) (by norm_num) (fun ω _ ↦ ω) measurable_from_top
    (iIndepFun.of_subsingleton) (fun _ ↦ by rw [Measure.map_id']; rfl)
  have hz : ∀ E : Set ((Unit × Bool) × Unit), (∀ ω, ω ∉ E) → lemma65Law.real E = 0 :=
    fun E hE ↦ by
      rw [Set.eq_empty_iff_forall_notMem.mpr hE, Measure.real, measure_empty, ENNReal.toReal_zero]
  rw [hz _ ?_] at key
  · norm_num at key
  intro ω hω
  have h1 := hω ((), !ω.1.2)
  have hne : ω.1 ≠ ((), !ω.1.2) := by
    intro he
    have := congrArg Prod.snd he
    cases hb : ω.1.2 <;> simp [hb] at this
  simp only [hne, Finset.filter_false, Finset.card_empty, Nat.cast_zero,
    Fintype.card_unique, Nat.cast_one] at h1
  have ht := lemma65_threshold
  simp only [Nat.cast_one] at ht
  have hρ : lemma65Rho.prob ((), !ω.1.2) = 1 / 2 := rfl
  rw [hρ, ge_iff_le, le_max_iff] at h1
  rcases h1 with h1 | h1 <;> linarith

end StatisticalRL.OfflineRL
