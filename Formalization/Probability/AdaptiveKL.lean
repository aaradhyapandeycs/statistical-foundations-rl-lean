import Formalization.Probability.AdaptiveKLDefinitions
import Formalization.Probability.FiniteSampleDefinitions
import Formalization.Generative.GenerativeLowerBoundFiniteKLDataProcessing

/-!
# Finite adaptive-data KL chain rule

The KL divergence between the history laws of two adaptive interactions that share the learner
decomposes as the sum over steps of the expected per-step KL divergence of the environments; the
learner terms cancel. This is the "chain rule for KL divergence" used without a label in the proof
of `lem:online-lb-testing` (`chapters/onlineRL.tex:4991–5009`, `eq:KL-factorize…`) and needed for
`thm:minimax-lower-online` (`:2443–2456`).

Main results (definitions in `Formalization/Probability/AdaptiveKLDefinitions.lean`):

* `seqLaw_finiteKLExpression`, `seqLaw_klDiv`: the generic sequential chain rule
  `KL(P_T ‖ Q_T) = ∑_{t<T} E_{P_t}[KL(κ_t(h) ‖ κ'_t(h))]` for step kernels `κ, κ'`, under atomwise
  absolute continuity of `κ_t(h)` w.r.t. `κ'_t(h)` at `P`-reachable histories `h`.
* `seqLaw_sum_prefix`, `seqLaw_sum_step`: marginalization of the joint law to a prefix.
* `interactionLaw_klDiv`, `interactionLaw_klDiv_eq_expectation`: the adaptive interaction form
  `KL(P_T ‖ Q_T) = E_P[∑_{t<T} KL(e_t(·|h_t,a_t) ‖ e'_t(·|h_t,a_t))]`.
* `interactionLaw_klDiv_le`, `interactionLaw_klDiv_le_visits`, `interactionLaw_klDiv_le_masked`:
  stepwise bounds, in particular `KL ≤ ∑_x δ_x · E_P[N_T(x)]` (expected visit counts times per-pair
  KL bounds) and the masked form `KL ≤ δ · E_P[#{t : M t h_t a_t}]` when the environments agree off
  the mask `M`.

KL divergences are Mathlib's `InformationTheory.klDiv` of the measures `d.toPMF.toMeasure` for
any measurable structure with measurable singletons (in particular the discrete `⊤` structure, for
which `d.toPMF.toMeasure` is `FiniteDistribution.rowMeasure d`).
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace StatisticalRL.AdaptiveKL

open StatisticalRL GenerativeLowerBound

section Expression

/-- One-step chain rule for the finite atomic KL expression of a two-stage law
`(w, z) ↦ a w · b w z` against `(w, z) ↦ c w · d w z`, allowing zero-mass atoms. -/
theorem finiteKLExpression_comp {W Z : Type*} [Fintype W] [Fintype Z] (a c : W → ℝ)
    (b d : W → Z → ℝ) (hbsum : ∀ w, a w ≠ 0 → ∑ z, b w z = 1)
    (hac : ∀ w, c w = 0 → a w = 0) (hbac : ∀ w, a w ≠ 0 → ∀ z, d w z = 0 → b w z = 0) :
    ∑ w, ∑ z, a w * b w z * Real.log (a w * b w z / (c w * d w z)) =
      finiteKLExpression a c + ∑ w, a w * finiteKLExpression (b w) (d w) := by
  unfold finiteKLExpression
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  by_cases haw : a w = 0
  · simp [haw]
  have hcw : c w ≠ 0 := fun h => haw (hac w h)
  have key : ∀ z, a w * b w z * Real.log (a w * b w z / (c w * d w z)) =
      b w z * (a w * Real.log (a w / c w)) + a w * (b w z * Real.log (b w z / d w z)) := by
    intro z
    by_cases hbz : b w z = 0
    · simp [hbz]
    have hdz : d w z ≠ 0 := fun h => hbz (hbac w haw z h)
    rw [mul_div_mul_comm, Real.log_mul (div_ne_zero haw hcw) (div_ne_zero hbz hdz)]
    ring
  simp_rw [key]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, hbsum w haw, one_mul, ← Finset.mul_sum]

/-- The atomic KL expression of a law against itself vanishes. -/
theorem finiteKLExpression_self {W : Type*} [Fintype W] (a : W → ℝ) :
    finiteKLExpression a a = 0 := by
  unfold finiteKLExpression
  refine Finset.sum_eq_zero fun w _ => ?_
  by_cases h : a w = 0
  · simp [h]
  · rw [div_self h, Real.log_one, mul_zero]

end Expression

section Sequential

variable {Z : Type*} [Fintype Z]

/-- The joint law inherits atomwise absolute continuity from the step kernels at reachable
histories. -/
theorem seqLaw_ac (κ κ' : (t : ℕ) → (Fin t → Z) → FiniteDistribution Z)
    (hac : ∀ t (h : Fin t → Z), (seqLaw κ t).prob h ≠ 0 →
      ∀ z, (κ' t h).prob z = 0 → (κ t h).prob z = 0) (T : ℕ) :
    ∀ h, (seqLaw κ' T).prob h = 0 → (seqLaw κ T).prob h = 0 := by
  induction T with
  | zero => intro h hq; simp [seqLaw_zero_prob] at hq
  | succ T ih =>
    intro h hq
    rw [seqLaw_succ_prob] at hq ⊢
    by_cases hp : (seqLaw κ T).prob (Fin.init h) = 0
    · rw [hp, zero_mul]
    rcases mul_eq_zero.mp hq with h1 | h1
    · exact absurd (ih _ h1) hp
    · rw [hac T _ hp _ h1, mul_zero]

/-- **Sequential KL chain rule** for the atomic expression. -/
theorem seqLaw_finiteKLExpression (κ κ' : (t : ℕ) → (Fin t → Z) → FiniteDistribution Z)
    (hac : ∀ t (h : Fin t → Z), (seqLaw κ t).prob h ≠ 0 →
      ∀ z, (κ' t h).prob z = 0 → (κ t h).prob z = 0) (T : ℕ) :
    finiteKLExpression (seqLaw κ T).prob (seqLaw κ' T).prob =
      ∑ t ∈ Finset.range T, ∑ h : Fin t → Z,
        (seqLaw κ t).prob h * finiteKLExpression (κ t h).prob (κ' t h).prob := by
  induction T with
  | zero => simp [finiteKLExpression, seqLaw_zero_prob]
  | succ T ih =>
    let F : (Fin T → Z) → Z → ℝ := fun p z =>
      (seqLaw κ T).prob p * (κ T p).prob z *
        Real.log ((seqLaw κ T).prob p * (κ T p).prob z /
          ((seqLaw κ' T).prob p * (κ' T p).prob z))
    calc finiteKLExpression (seqLaw κ (T + 1)).prob (seqLaw κ' (T + 1)).prob
        = ∑ h : Fin (T + 1) → Z, F (Fin.init h) (h (Fin.last T)) := rfl
      _ = ∑ p, ∑ z, F p z := sum_tuple_succ T F
      _ = finiteKLExpression (seqLaw κ T).prob (seqLaw κ' T).prob +
          ∑ p, (seqLaw κ T).prob p * finiteKLExpression (κ T p).prob (κ' T p).prob :=
        finiteKLExpression_comp _ _ (fun p z => (κ T p).prob z) (fun p z => (κ' T p).prob z)
          (fun p _ => (κ T p).sum_prob) (seqLaw_ac κ κ' hac T) (fun p hp z hz => hac T p hp z hz)
      _ = _ := by rw [Finset.sum_range_succ, ih]

/-- Marginalizing the joint law of `T` entries to its length-`t` prefix. -/
theorem seqLaw_sum_prefix (κ : (t : ℕ) → (Fin t → Z) → FiniteDistribution Z) {t T : ℕ}
    (hle : t ≤ T) (f : (Fin t → Z) → ℝ) :
    ∑ h : Fin T → Z, (seqLaw κ T).prob h * f (fun i => h (Fin.castLE hle i)) =
      ∑ h : Fin t → Z, (seqLaw κ t).prob h * f h := by
  induction T, hle using Nat.le_induction with
  | base => rfl
  | succ T hle ih =>
    calc ∑ h : Fin (T + 1) → Z, (seqLaw κ (T + 1)).prob h *
          f (fun i => h (Fin.castLE (hle.trans (Nat.le_succ T)) i))
        = ∑ h : Fin (T + 1) → Z,
            (fun p z => (seqLaw κ T).prob p * (κ T p).prob z * f (fun i => p (Fin.castLE hle i)))
              (Fin.init h) (h (Fin.last T)) := rfl
      _ = ∑ p : Fin T → Z, ∑ z,
            (seqLaw κ T).prob p * (κ T p).prob z * f (fun i => p (Fin.castLE hle i)) :=
        sum_tuple_succ T
          (fun p z => (seqLaw κ T).prob p * (κ T p).prob z * f (fun i => p (Fin.castLE hle i)))
      _ = ∑ p : Fin T → Z, (seqLaw κ T).prob p * f (fun i => p (Fin.castLE hle i)) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← Finset.sum_mul, ← Finset.mul_sum, (κ T p).sum_prob, mul_one]
      _ = _ := ih

/-- The law of the `t`-th entry together with its history: the expectation under the joint law
of `T > t` entries of a function of `(h_t, z_t)`. -/
theorem seqLaw_sum_step (κ : (t : ℕ) → (Fin t → Z) → FiniteDistribution Z) {t T : ℕ}
    (ht : t < T) (g : (Fin t → Z) → Z → ℝ) :
    ∑ h : Fin T → Z, (seqLaw κ T).prob h * g (fun i => h (Fin.castLE ht.le i)) (h ⟨t, ht⟩) =
      ∑ h : Fin t → Z, (seqLaw κ t).prob h * ∑ z, (κ t h).prob z * g h z := by
  have hpre := seqLaw_sum_prefix κ (Nat.succ_le_of_lt ht)
    (fun h' : Fin (t + 1) → Z => g (Fin.init h') (h' (Fin.last t)))
  refine hpre.trans ?_
  calc ∑ h' : Fin (t + 1) → Z, (seqLaw κ (t + 1)).prob h' * g (Fin.init h') (h' (Fin.last t))
      = ∑ h' : Fin (t + 1) → Z,
          (fun p z => (seqLaw κ t).prob p * ((κ t p).prob z * g p z))
            (Fin.init h') (h' (Fin.last t)) := by
        refine Finset.sum_congr rfl fun h' _ => ?_
        rw [seqLaw_succ_prob]; ring
    _ = _ := by
        rw [sum_tuple_succ t (fun p z => (seqLaw κ t).prob p * ((κ t p).prob z * g p z))]
        simp_rw [← Finset.mul_sum]

end Sequential

section Measure

variable {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]

theorem toMeasure_singleton (d : FiniteDistribution Ω) (x : Ω) :
    d.toPMF.toMeasure {x} = ENNReal.ofReal (d.prob x) := by
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x)]
  unfold FiniteDistribution.toPMF
  rw [PMF.ofFintype_apply]

theorem toMeasure_real_singleton (d : FiniteDistribution Ω) (x : Ω) :
    d.toPMF.toMeasure.real {x} = d.prob x := by
  rw [measureReal_def, toMeasure_singleton, ENNReal.toReal_ofReal (d.prob_nonneg x)]

/-- Absolute continuity of finite laws from the vanishing of atoms. -/
theorem toMeasure_ac (d d' : FiniteDistribution Ω) (h : ∀ x, d'.prob x = 0 → d.prob x = 0) :
    d.toPMF.toMeasure ≪ d'.toPMF.toMeasure := by
  intro s hs
  rw [← Set.biUnion_of_singleton s]
  refine (measure_biUnion_null_iff (Set.toFinite s).countable).mpr fun x hx => ?_
  have hx0 : d'.toPMF.toMeasure {x} = 0 :=
    measure_mono_null (Set.singleton_subset_iff.mpr hx) hs
  rw [toMeasure_singleton, ENNReal.ofReal_eq_zero] at hx0
  rw [toMeasure_singleton, h x (le_antisymm hx0 (d'.prob_nonneg x)), ENNReal.ofReal_zero]

/-- KL divergence of two finite laws with `d ≪ d'` (atomwise): finite, and equal to the atomic
expression `∑ₓ d(x) log (d(x)/d'(x))`. -/
theorem toMeasure_klDiv (d d' : FiniteDistribution Ω) (h : ∀ x, d'.prob x = 0 → d.prob x = 0) :
    InformationTheory.klDiv d.toPMF.toMeasure d'.toPMF.toMeasure ≠ ∞ ∧
      (InformationTheory.klDiv d.toPMF.toMeasure d'.toPMF.toMeasure).toReal =
        finiteKLExpression d.prob d'.prob := by
  have hac := toMeasure_ac d d' h
  refine ⟨finite_klDiv_ne_top_of_ac _ _ hac, ?_⟩
  rw [finite_klDiv_eq_expression_of_ac _ _ hac]
  simp only [toMeasure_real_singleton]

end Measure

section SequentialKL

variable {Z : Type*} [Fintype Z]

/-- **Sequential KL chain rule** for `klDiv`: if every step kernel `κ_t(h)` is absolutely
continuous (atomwise) w.r.t. `κ'_t(h)` at every `P`-reachable history `h`, then
`KL(P_T ‖ Q_T)` is finite and equals `∑_{t<T} E_{P_t}[KL(κ_t(h) ‖ κ'_t(h))]`. -/
theorem seqLaw_klDiv (κ κ' : (t : ℕ) → (Fin t → Z) → FiniteDistribution Z)
    (hac : ∀ t (h : Fin t → Z), (seqLaw κ t).prob h ≠ 0 →
      ∀ z, (κ' t h).prob z = 0 → (κ t h).prob z = 0) (T : ℕ)
    [MeasurableSpace (Fin T → Z)] [MeasurableSingletonClass (Fin T → Z)]
    [MeasurableSpace Z] [MeasurableSingletonClass Z] :
    InformationTheory.klDiv (seqLaw κ T).toPMF.toMeasure (seqLaw κ' T).toPMF.toMeasure ≠ ∞ ∧
      (InformationTheory.klDiv (seqLaw κ T).toPMF.toMeasure
          (seqLaw κ' T).toPMF.toMeasure).toReal =
        ∑ t ∈ Finset.range T, ∑ h : Fin t → Z, (seqLaw κ t).prob h *
          (InformationTheory.klDiv (κ t h).toPMF.toMeasure (κ' t h).toPMF.toMeasure).toReal := by
  obtain ⟨hne, heq⟩ := toMeasure_klDiv (seqLaw κ T) (seqLaw κ' T) (seqLaw_ac κ κ' hac T)
  refine ⟨hne, ?_⟩
  rw [heq, seqLaw_finiteKLExpression κ κ' hac T]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun h _ => ?_
  by_cases hp : (seqLaw κ t).prob h = 0
  · simp [hp]
  · rw [(toMeasure_klDiv (κ t h) (κ' t h) (hac t h hp)).2]

end SequentialKL

section Interaction

variable {A O : Type*} [Fintype A] [Fintype O]

/-- Atomwise absolute continuity of the interaction kernels from that of the environments. -/
theorem interactionKernel_ac (π : (t : ℕ) → (Fin t → A × O) → FiniteDistribution A)
    (e e' : (t : ℕ) → (Fin t → A × O) → A → FiniteDistribution O)
    (hac : ∀ t h a o, (e' t h a).prob o = 0 → (e t h a).prob o = 0) (t : ℕ) (h : Fin t → A × O)
    (z : A × O) : (interactionKernel π e' t h).prob z = 0 → (interactionKernel π e t h).prob z = 0 := by
  intro hz
  change (π t h).prob z.1 * (e' t h z.1).prob z.2 = 0 at hz
  change (π t h).prob z.1 * (e t h z.1).prob z.2 = 0
  rcases mul_eq_zero.mp hz with h1 | h1
  · rw [h1, zero_mul]
  · rw [hac _ _ _ _ h1, mul_zero]

/-- With a common learner, the one-step KL expression is the learner-averaged environment KL. -/
theorem interactionKernel_finiteKLExpression
    (π : (t : ℕ) → (Fin t → A × O) → FiniteDistribution A)
    (e e' : (t : ℕ) → (Fin t → A × O) → A → FiniteDistribution O)
    (hac : ∀ t h a o, (e' t h a).prob o = 0 → (e t h a).prob o = 0) (t : ℕ) (h : Fin t → A × O) :
    finiteKLExpression (interactionKernel π e t h).prob (interactionKernel π e' t h).prob =
      ∑ a, (π t h).prob a * finiteKLExpression (e t h a).prob (e' t h a).prob := by
  have hc := finiteKLExpression_comp (π t h).prob (π t h).prob
    (fun a o => (e t h a).prob o) (fun a o => (e' t h a).prob o)
    (fun a _ => (e t h a).sum_prob) (fun _ ha => ha) (fun a _ o ho => hac t h a o ho)
  rw [finiteKLExpression_self, zero_add] at hc
  rw [← hc]
  exact Fintype.sum_prod_type _

/-- **Adaptive KL chain rule.** For a common (history-dependent, randomized) learner `π` and two
environments `e, e'` with `e_t(·|h,a) ≪ e'_t(·|h,a)` atomwise, the KL divergence of the length-`T`
history laws is finite and equals `∑_{t<T} E_P[KL(e_t(·|h_t,a_t) ‖ e'_t(·|h_t,a_t))]`, written with
the marginal law of `h_t` and the learner's law of `a_t`. -/
theorem interactionLaw_klDiv (π : (t : ℕ) → (Fin t → A × O) → FiniteDistribution A)
    (e e' : (t : ℕ) → (Fin t → A × O) → A → FiniteDistribution O)
    (hac : ∀ t h a o, (e' t h a).prob o = 0 → (e t h a).prob o = 0) (T : ℕ)
    [MeasurableSpace (Fin T → A × O)] [MeasurableSingletonClass (Fin T → A × O)]
    [MeasurableSpace O] [MeasurableSingletonClass O] :
    InformationTheory.klDiv (interactionLaw π e T).toPMF.toMeasure
        (interactionLaw π e' T).toPMF.toMeasure ≠ ∞ ∧
      (InformationTheory.klDiv (interactionLaw π e T).toPMF.toMeasure
          (interactionLaw π e' T).toPMF.toMeasure).toReal =
        ∑ t ∈ Finset.range T, ∑ h : Fin t → A × O, (interactionLaw π e t).prob h *
          ∑ a, (π t h).prob a *
            (InformationTheory.klDiv (e t h a).toPMF.toMeasure
              (e' t h a).toPMF.toMeasure).toReal := by
  have hacK : ∀ t (h : Fin t → A × O), (seqLaw (interactionKernel π e) t).prob h ≠ 0 →
      ∀ z, (interactionKernel π e' t h).prob z = 0 → (interactionKernel π e t h).prob z = 0 :=
    fun t h _ z => interactionKernel_ac π e e' hac t h z
  obtain ⟨hne, heq⟩ := toMeasure_klDiv (interactionLaw π e T) (interactionLaw π e' T)
    (seqLaw_ac _ _ hacK T)
  refine ⟨hne, ?_⟩
  rw [heq]
  unfold interactionLaw
  rw [seqLaw_finiteKLExpression _ _ hacK T]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun h _ => ?_
  rw [interactionKernel_finiteKLExpression π e e' hac t h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [(toMeasure_klDiv (e t h a) (e' t h a) (hac t h a)).2]

/-- Expectation of a function of `(t, h_t, a_t)` under the interaction law, as an iterated
marginal sum. -/
theorem interactionLaw_sum_steps (π : (t : ℕ) → (Fin t → A × O) → FiniteDistribution A)
    (e : (t : ℕ) → (Fin t → A × O) → A → FiniteDistribution O) (T : ℕ)
    (g : (t : ℕ) → (Fin t → A × O) → A → ℝ) :
    ∑ h : Fin T → A × O, (interactionLaw π e T).prob h * ∑ t : Fin T, g t (fun i => h (Fin.castLE t.isLt.le i)) (h t).1 =
      ∑ t ∈ Finset.range T, ∑ h : Fin t → A × O, (interactionLaw π e t).prob h *
        ∑ a, (π t h).prob a * g t h a := by
  rw [Finset.sum_range]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hs := seqLaw_sum_step (interactionKernel π e) t.isLt (fun h z => g t h z.1)
  simp_rw [← Finset.mul_sum]
  refine hs.trans (Finset.sum_congr rfl fun h _ => ?_)
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  change ∑ o, (π t h).prob a * (e t h a).prob o * g t h a = _
  rw [← Finset.sum_mul, ← Finset.mul_sum, (e t h a).sum_prob, mul_one]

/-- **Adaptive KL chain rule, expectation form**:
`KL(P_T ‖ Q_T) = E_P[∑_{t<T} KL(e_t(·|h_t,a_t) ‖ e'_t(·|h_t,a_t))]`, the expectation taken under
the full history law. -/
theorem interactionLaw_klDiv_eq_expectation
    (π : (t : ℕ) → (Fin t → A × O) → FiniteDistribution A)
    (e e' : (t : ℕ) → (Fin t → A × O) → A → FiniteDistribution O)
    (hac : ∀ t h a o, (e' t h a).prob o = 0 → (e t h a).prob o = 0) (T : ℕ)
    [MeasurableSpace (Fin T → A × O)] [MeasurableSingletonClass (Fin T → A × O)]
    [MeasurableSpace O] [MeasurableSingletonClass O] :
    (InformationTheory.klDiv (interactionLaw π e T).toPMF.toMeasure
        (interactionLaw π e' T).toPMF.toMeasure).toReal =
      ∑ h : Fin T → A × O, (interactionLaw π e T).prob h *
        ∑ t : Fin T, (InformationTheory.klDiv (e t (fun i => h (Fin.castLE t.isLt.le i)) (h t).1).toPMF.toMeasure
          (e' t (fun i => h (Fin.castLE t.isLt.le i)) (h t).1).toPMF.toMeasure).toReal := by
  rw [(interactionLaw_klDiv π e e' hac T).2]
  exact (interactionLaw_sum_steps π e T (fun t h a =>
    (InformationTheory.klDiv (e t h a).toPMF.toMeasure (e' t h a).toPMF.toMeasure).toReal)).symm

/-- Stepwise upper bound: if every per-step environment KL is at most `g t h a`, then the history
KL is at most `E_P[∑_{t<T} g t h_t a_t]`. -/
theorem interactionLaw_klDiv_le (π : (t : ℕ) → (Fin t → A × O) → FiniteDistribution A)
    (e e' : (t : ℕ) → (Fin t → A × O) → A → FiniteDistribution O)
    (hac : ∀ t h a o, (e' t h a).prob o = 0 → (e t h a).prob o = 0) (T : ℕ)
    [MeasurableSpace (Fin T → A × O)] [MeasurableSingletonClass (Fin T → A × O)]
    [MeasurableSpace O] [MeasurableSingletonClass O]
    (g : (t : ℕ) → (Fin t → A × O) → A → ℝ)
    (hg : ∀ t h a, (InformationTheory.klDiv (e t h a).toPMF.toMeasure
      (e' t h a).toPMF.toMeasure).toReal ≤ g t h a) :
    InformationTheory.klDiv (interactionLaw π e T).toPMF.toMeasure
        (interactionLaw π e' T).toPMF.toMeasure ≤
      ENNReal.ofReal (∑ h : Fin T → A × O, (interactionLaw π e T).prob h *
        ∑ t : Fin T, g t (fun i => h (Fin.castLE t.isLt.le i)) (h t).1) := by
  rw [← ENNReal.ofReal_toReal (interactionLaw_klDiv π e e' hac T).1]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [interactionLaw_klDiv_eq_expectation π e e' hac T]
  refine Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left ?_ ((interactionLaw π e T).prob_nonneg h)
  exact Finset.sum_le_sum fun t _ => hg _ _ _

/-- **Visit-count bound**: if the per-step environment KL at `(t, h, a)` is at most `δ (φ t h a)`
(for instance `φ` the state-action pair visited and `δ` a per-pair KL bound), then
`KL(P_T ‖ Q_T) ≤ ∑_x δ x · E_P[N_T(x)]` with `N_T(x)` the number of steps with feature `x`. -/
theorem interactionLaw_klDiv_le_visits (π : (t : ℕ) → (Fin t → A × O) → FiniteDistribution A)
    (e e' : (t : ℕ) → (Fin t → A × O) → A → FiniteDistribution O)
    (hac : ∀ t h a o, (e' t h a).prob o = 0 → (e t h a).prob o = 0) (T : ℕ)
    [MeasurableSpace (Fin T → A × O)] [MeasurableSingletonClass (Fin T → A × O)]
    [MeasurableSpace O] [MeasurableSingletonClass O]
    {X : Type*} [Fintype X] [DecidableEq X] (φ : (t : ℕ) → (Fin t → A × O) → A → X) (δ : X → ℝ)
    (hδ : ∀ t h a, (InformationTheory.klDiv (e t h a).toPMF.toMeasure
      (e' t h a).toPMF.toMeasure).toReal ≤ δ (φ t h a)) :
    InformationTheory.klDiv (interactionLaw π e T).toPMF.toMeasure
        (interactionLaw π e' T).toPMF.toMeasure ≤
      ENNReal.ofReal (∑ x, δ x * expectedVisits π e T φ x) := by
  have hle := interactionLaw_klDiv_le π e e' hac T (fun t h a => δ (φ t h a)) hδ
  refine hle.trans_eq (congrArg ENNReal.ofReal ?_)
  unfold expectedVisits
  have hpt : ∀ y : X, δ y = ∑ x, δ x * (if y = x then 1 else 0) := by
    intro y
    simp [mul_ite]
  let P := (interactionLaw π e T).prob
  let I : (Fin T → A × O) → Fin T → X → ℝ := fun h t x =>
    if φ t (fun i => h (Fin.castLE t.isLt.le i)) (h t).1 = x then 1 else 0
  calc ∑ h : Fin T → A × O, P h * ∑ t : Fin T, δ (φ t (fun i => h (Fin.castLE t.isLt.le i)) (h t).1)
      = ∑ h : Fin T → A × O, ∑ t : Fin T, ∑ x : X, P h * (δ x * I h t x) := by
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hpt (φ t (fun i => h (Fin.castLE t.isLt.le i)) (h t).1), Finset.mul_sum]
    _ = ∑ h : Fin T → A × O, ∑ x : X, ∑ t : Fin T, P h * (δ x * I h t x) :=
        Finset.sum_congr rfl fun h _ => Finset.sum_comm
    _ = ∑ x : X, ∑ h : Fin T → A × O, ∑ t : Fin T, P h * (δ x * I h t x) := Finset.sum_comm
    _ = ∑ x : X, δ x * ∑ h : Fin T → A × O, P h * ∑ t : Fin T, I h t x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun t _ => ?_
        ring

open Classical in
/-- **Masked bound**: if the two environments coincide wherever the predicate `M` fails, and the
per-step KL is at most `δ` wherever it holds, then `KL(P_T ‖ Q_T) ≤ δ · E_P[#{t < T : M t h_t a_t}]`.
-/
theorem interactionLaw_klDiv_le_masked (π : (t : ℕ) → (Fin t → A × O) → FiniteDistribution A)
    (e e' : (t : ℕ) → (Fin t → A × O) → A → FiniteDistribution O)
    (hac : ∀ t h a o, (e' t h a).prob o = 0 → (e t h a).prob o = 0) (T : ℕ)
    [MeasurableSpace (Fin T → A × O)] [MeasurableSingletonClass (Fin T → A × O)]
    [MeasurableSpace O] [MeasurableSingletonClass O]
    (M : (t : ℕ) → (Fin t → A × O) → A → Prop) (δ : ℝ)
    (hsame : ∀ t h a, ¬ M t h a → e t h a = e' t h a)
    (hδ : ∀ t h a, M t h a → (InformationTheory.klDiv (e t h a).toPMF.toMeasure
      (e' t h a).toPMF.toMeasure).toReal ≤ δ) :
    InformationTheory.klDiv (interactionLaw π e T).toPMF.toMeasure
        (interactionLaw π e' T).toPMF.toMeasure ≤
      ENNReal.ofReal (δ * expectedCount π e T M) := by
  have hg : ∀ t h a, (InformationTheory.klDiv (e t h a).toPMF.toMeasure
      (e' t h a).toPMF.toMeasure).toReal ≤ if M t h a then δ else 0 := by
    intro t h a
    by_cases hM : M t h a
    · rw [if_pos hM]; exact hδ t h a hM
    · rw [if_neg hM, hsame t h a hM, InformationTheory.klDiv_self, ENNReal.toReal_zero]
  have hle := interactionLaw_klDiv_le π e e' hac T _ hg
  refine hle.trans_eq (congrArg ENNReal.ofReal ?_)
  unfold expectedCount
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs <;> ring

end Interaction

end StatisticalRL.AdaptiveKL
