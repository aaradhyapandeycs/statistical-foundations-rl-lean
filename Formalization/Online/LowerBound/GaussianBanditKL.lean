import Formalization.Online.LowerBound.GaussianBanditChangeOfMeasure
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.InformationTheory.KullbackLeibler.Basic

/-!
# KL divergence of the adapted Gaussian tilt (Remark 5.12)

With `f = logDensity` (the log-density from the means `μ` to the means `μ + c`) and
`P = ν ⊗ table`, the tilted measure `Q = P.tilted f` satisfies:
* `Q {a_s ≠ j}` (arms under `μ`) equals `P {a_s ≠ j}` (arms under `μ + c`);
* `KL(P ‖ Q) = E_P [Σ_{s<T} c(a_s)² / 2]` (only observed coordinates count).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

noncomputable section

namespace StatisticalRL.GaussianBanditLB

open StatisticalRL.Bandit

variable {A : ℕ}

/-! ### Predictable zero mean -/

theorem extendNoise_insertNth_of_lt {n : ℕ} (s : Fin (n + 1)) (w : Fin n → Fin A → ℝ)
    (y y' : Fin A → ℝ) {r : ℕ} (hr : r < s.val) :
    extendNoise (Fin.insertNth (α := fun _ => Fin A → ℝ) s y w) r =
      extendNoise (Fin.insertNth (α := fun _ => Fin A → ℝ) s y' w) r := by
  have h1 : r < n + 1 := lt_trans hr s.isLt
  simp only [extendNoise, h1, dif_pos]
  have hlt : (⟨r, h1⟩ : Fin (n + 1)) < s := hr
  rw [Fin.insertNth_apply_below hlt, Fin.insertNth_apply_below hlt]

theorem integrable_table_coord (T : ℕ) (s : Fin T) (b : Fin A) :
    Integrable (fun z : Fin T → Fin A → ℝ => z s b) (gaussianNoiseTable T A) :=
  integrable_comp_eval (μ := fun _ : Fin T => rowLaw A) (i := s) (f := fun r : Fin A → ℝ => r b)
    (integrable_coord b)

/-- A function of the table that is, given all rows but row `s`, a fixed multiple of one coordinate
of row `s`, has mean zero. -/
theorem integral_table_coord_zero {n : ℕ} (s : Fin (n + 1))
    (F : (Fin (n + 1) → Fin A → ℝ) → ℝ) (hFm : Measurable F) (K : ℝ)
    (hFb : ∀ z, |F z| ≤ K * ∑ b, |z s b|)
    (hdep : ∀ w, ∃ b k, ∀ y, F (Fin.insertNth (α := fun _ => Fin A → ℝ) s y w) = k * y b) :
    ∫ z, F z ∂gaussianNoiseTable (n + 1) A = 0 := by
  have hb : Integrable (fun z : Fin (n + 1) → Fin A → ℝ => K * ∑ b, |z s b|)
      (gaussianNoiseTable (n + 1) A) :=
    (integrable_finset_sum univ fun b _ => (integrable_table_coord (n + 1) s b).abs).const_mul K
  have hint : Integrable F (gaussianNoiseTable (n + 1) A) := by
    refine Integrable.mono' hb hFm.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs]; exact hFb z
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => rowLaw A) s
  unfold gaussianNoiseTable at hint ⊢
  rw [← hmp.symm.integral_comp' F]
  have hint2 : Integrable (fun p => F ((MeasurableEquiv.piFinSuccAbove _ s).symm p))
      ((rowLaw A).prod (Measure.pi fun _ : Fin n => rowLaw A)) :=
    (hmp.symm.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hint
  rw [integral_prod_symm _ hint2]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun w => ?_)
  obtain ⟨b, k, hk⟩ := hdep w
  change ∫ y, F (Fin.insertNth (α := fun _ => Fin A → ℝ) s y w) ∂rowLaw A = 0
  simp_rw [hk]
  rw [integral_const_mul, integral_coord, mul_zero]

theorem abs_eval_le_sum (v : Fin A → ℝ) (a : Fin A) : |v a| ≤ ∑ b, |v b| :=
  Finset.single_le_sum (f := fun b => |v b|) (fun _ _ => abs_nonneg _) (mem_univ a)

section seed

variable {Seed : Type*} [MeasurableSpace Seed]
  {arm : (t : ℕ) → Seed → (Fin t → Fin A × ℝ) → Fin A}
  (harm : ∀ t, Measurable (Function.uncurry (arm t)))
  (μ c : Fin A → ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (T : ℕ)
include harm

theorem measurable_armAt_joint (s : ℕ) :
    Measurable fun ω : Seed × (Fin T → Fin A → ℝ) => armAt arm μ ω.1 (extendNoise ω.2) s :=
  measurable_armAt μ harm measurable_fst ((measurable_extendNoise T).comp measurable_snd) s

omit harm in
theorem bound_predictable (z : Fin T → Fin A → ℝ) (s : Fin T) (a : Fin A) :
    |c a * z s a| ≤ (∑ b, |c b|) * ∑ b, |z s b| := by
  rw [abs_mul]
  exact mul_le_mul (abs_eval_le_sum c a) (abs_eval_le_sum (z s) a) (abs_nonneg _)
    (Finset.sum_nonneg fun b _ => abs_nonneg _)

theorem integrable_predictable_coord (s : Fin T) :
    Integrable (fun ω : Seed × (Fin T → Fin A → ℝ) =>
      c (armAt arm μ ω.1 (extendNoise ω.2) s) * ω.2 s (armAt arm μ ω.1 (extendNoise ω.2) s))
      (ν.prod (gaussianNoiseTable T A)) := by
  have ha := measurable_armAt_joint harm μ T s
  have hm : Measurable fun ω : Seed × (Fin T → Fin A → ℝ) =>
      c (armAt arm μ ω.1 (extendNoise ω.2) s) * ω.2 s (armAt arm μ ω.1 (extendNoise ω.2) s) :=
    ((measurable_of_countable c).comp ha).mul
      (measurable_eval_fin ha ((measurable_pi_apply s).comp measurable_snd))
  have hb : Integrable (fun z : Fin T → Fin A → ℝ => (∑ b, |c b|) * ∑ b, |z s b|)
      (gaussianNoiseTable T A) :=
    (integrable_finset_sum univ fun b _ => (integrable_table_coord T s b).abs).const_mul _
  refine Integrable.mono' (hb.comp_snd ν) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact bound_predictable c T ω.2 s _

/-- Predictable zero mean: `E[c(a_s) z_{s,a_s}] = 0`, since `a_s` reads only rows `< s`. -/
theorem integral_predictable_coord (s : Fin T) :
    ∫ ω, c (armAt arm μ ω.1 (extendNoise ω.2) s) * ω.2 s (armAt arm μ ω.1 (extendNoise ω.2) s)
      ∂(ν.prod (gaussianNoiseTable T A)) = 0 := by
  rw [integral_prod _ (integrable_predictable_coord harm μ c ν T s)]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun σ => ?_)
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by have := s.isLt; omega⟩
  have ha : Measurable fun z : Fin (n + 1) → Fin A → ℝ => armAt arm μ σ (extendNoise z) s :=
    measurable_armAt μ harm measurable_const (measurable_extendNoise (n + 1)) s
  refine integral_table_coord_zero s _ (((measurable_of_countable c).comp ha).mul
    (measurable_eval_fin ha (measurable_pi_apply s))) (∑ b, |c b|)
    (fun z => bound_predictable c (n + 1) z s _) (fun w => ?_)
  refine ⟨armAt arm μ σ (extendNoise (Fin.insertNth (α := fun _ => Fin A → ℝ) s 0 w)) s,
    c (armAt arm μ σ (extendNoise (Fin.insertNth (α := fun _ => Fin A → ℝ) s 0 w)) s),
    fun y => ?_⟩
  have harm_eq : armAt arm μ σ (extendNoise (Fin.insertNth (α := fun _ => Fin A → ℝ) s y w)) s =
      armAt arm μ σ (extendNoise (Fin.insertNth (α := fun _ => Fin A → ℝ) s 0 w)) s := by
    unfold armAt
    rw [history_congr arm μ σ s (fun r hr => extendNoise_insertNth_of_lt s w y 0 hr)]
  simp only
  rw [harm_eq, Fin.insertNth_apply_same]

/-! ### The tilt -/

/-- `∫⁻ exp f dP = 1`: the case `g = 1` of the change of measure. -/
theorem lintegral_exp_logDensity :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (logDensity arm μ c T ω.1 ω.2))
      ∂(ν.prod (gaussianNoiseTable T A)) = 1 := by
  have h := lintegral_history_shift_joint arm harm μ c ν T (fun _ => 1) measurable_const
  simp only [one_mul, lintegral_const, measure_univ, mul_one] at h
  exact h.symm

theorem measurable_exp_logDensity :
    Measurable fun ω : Seed × (Fin T → Fin A → ℝ) =>
      Real.exp (logDensity arm μ c T ω.1 ω.2) :=
  Real.measurable_exp.comp (measurable_logDensity arm harm μ c T)

theorem integrable_exp_logDensity :
    Integrable (fun ω : Seed × (Fin T → Fin A → ℝ) => Real.exp (logDensity arm μ c T ω.1 ω.2))
      (ν.prod (gaussianNoiseTable T A)) := by
  have hm : Measurable fun ω : Seed × (Fin T → Fin A → ℝ) =>
      ENNReal.ofReal (Real.exp (logDensity arm μ c T ω.1 ω.2)) :=
    ENNReal.measurable_ofReal.comp (measurable_exp_logDensity harm μ c T)
  have h := integrable_toReal_of_lintegral_ne_top (μ := ν.prod (gaussianNoiseTable T A))
    hm.aemeasurable (by rw [lintegral_exp_logDensity harm μ c ν T]; exact ENNReal.one_ne_top)
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  exact ENNReal.toReal_ofReal (Real.exp_pos _).le

theorem integral_exp_logDensity :
    ∫ ω, Real.exp (logDensity arm μ c T ω.1 ω.2) ∂(ν.prod (gaussianNoiseTable T A)) = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)
    (measurable_exp_logDensity harm μ c T).aestronglyMeasurable,
    lintegral_exp_logDensity harm μ c ν T]
  rfl

omit harm in
theorem integrable_fin_valued {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    {a : Ω → Fin A} (ha : Measurable a) (φ : Fin A → ℝ) : Integrable (fun ω => φ (a ω)) P :=
  Integrable.of_bound ((measurable_of_countable φ).comp ha).aestronglyMeasurable (∑ b, |φ b|)
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact abs_eval_le_sum φ _)

theorem integrable_logDensity :
    Integrable (fun ω : Seed × (Fin T → Fin A → ℝ) => logDensity arm μ c T ω.1 ω.2)
      (ν.prod (gaussianNoiseTable T A)) := by
  unfold logDensity
  refine integrable_finset_sum _ fun s _ => ?_
  exact (integrable_predictable_coord harm μ c ν T s).sub
    (integrable_fin_valued _ (measurable_armAt_joint harm μ T s) fun b => c b ^ 2 / 2)

/-- `E_P f = −E_P[Σ_s c(a_s)²/2]`. -/
theorem integral_logDensity :
    ∫ ω, logDensity arm μ c T ω.1 ω.2 ∂(ν.prod (gaussianNoiseTable T A)) =
      -∫ ω, ∑ s : Fin T, c (armAt arm μ ω.1 (extendNoise ω.2) s) ^ 2 / 2
        ∂(ν.prod (gaussianNoiseTable T A)) := by
  unfold logDensity
  have hY : ∀ s ∈ (univ : Finset (Fin T)), Integrable (fun ω : Seed × (Fin T → Fin A → ℝ) =>
      c (armAt arm μ ω.1 (extendNoise ω.2) s) ^ 2 / 2) (ν.prod (gaussianNoiseTable T A)) :=
    fun s _ => integrable_fin_valued _ (measurable_armAt_joint harm μ T s) fun b => c b ^ 2 / 2
  have hXY : ∀ s ∈ (univ : Finset (Fin T)), Integrable (fun ω : Seed × (Fin T → Fin A → ℝ) =>
      c (armAt arm μ ω.1 (extendNoise ω.2) s) * ω.2 s (armAt arm μ ω.1 (extendNoise ω.2) s)
        - c (armAt arm μ ω.1 (extendNoise ω.2) s) ^ 2 / 2) (ν.prod (gaussianNoiseTable T A)) :=
    fun s hs => (integrable_predictable_coord harm μ c ν T s).sub (hY s hs)
  rw [integral_finset_sum univ hXY, integral_finset_sum univ hY, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [integral_sub (integrable_predictable_coord harm μ c ν T s) (hY s hs),
    integral_predictable_coord harm μ c ν T s, zero_sub]

/-- The tilted measure. -/
abbrev tiltQ : Measure (Seed × (Fin T → Fin A → ℝ)) :=
  (ν.prod (gaussianNoiseTable T A)).tilted fun ω => logDensity arm μ c T ω.1 ω.2

omit harm [IsProbabilityMeasure ν] in
theorem tiltQ_def : tiltQ μ c ν T (arm := arm) =
    (ν.prod (gaussianNoiseTable T A)).tilted fun ω => logDensity arm μ c T ω.1 ω.2 := rfl

theorem isProbabilityMeasure_tiltQ : IsProbabilityMeasure (tiltQ μ c ν T (arm := arm)) :=
  isProbabilityMeasure_tilted (integrable_exp_logDensity harm μ c ν T)

/-- `KL(P ‖ Q) = E_P[Σ_s c(a_s)²/2]`. -/
theorem klDiv_tiltQ :
    InformationTheory.klDiv (ν.prod (gaussianNoiseTable T A)) (tiltQ μ c ν T (arm := arm)) =
      ENNReal.ofReal (∫ ω, ∑ s : Fin T, c (armAt arm μ ω.1 (extendNoise ω.2) s) ^ 2 / 2
        ∂(ν.prod (gaussianNoiseTable T A))) := by
  set P := ν.prod (gaussianNoiseTable T A) with hP
  haveI := isProbabilityMeasure_tiltQ harm μ c ν T
  have hexp := integrable_exp_logDensity harm μ c ν T
  have hac : P ≪ tiltQ μ c ν T (arm := arm) := absolutelyContinuous_tilted hexp
  have hself : Integrable (MeasureTheory.llr P P) P :=
    (integrable_zero _ _ P).congr (MeasureTheory.llr_self P).symm
  have hllr := integrable_llr_tilted_right (Measure.AbsolutelyContinuous.refl P)
    (integrable_logDensity harm μ c ν T) hself hexp
  rw [InformationTheory.klDiv_of_ac_of_integrable hac hllr, probReal_univ, probReal_univ,
    add_sub_cancel_right, integral_llr_tilted_right (Measure.AbsolutelyContinuous.refl P)
      (integrable_logDensity harm μ c ν T) hexp hself,
    integral_exp_logDensity harm μ c ν T, Real.log_one, add_zero,
    integral_congr_ae (MeasureTheory.llr_self P)]
  simp only [Pi.zero_apply, integral_zero, zero_sub]
  rw [hP, integral_logDensity harm μ c ν T, neg_neg]

/-- The tilted measure of the event "arm at round `s` differs from `j`" (arms under `μ`) is the
base probability of the same event for the learner run on the means `μ + c`. -/
theorem tiltQ_arm_ne (s : ℕ) (hs : s ≤ T) (j : Fin A) :
    tiltQ μ c ν T (arm := arm) {ω | armAt arm μ ω.1 (extendNoise ω.2) s ≠ j} =
      (ν.prod (gaussianNoiseTable T A))
        {ω | armAt arm (fun a => μ a + c a) ω.1 (extendNoise ω.2) s ≠ j} := by
  set P := ν.prod (gaussianNoiseTable T A) with hP
  have hS : ∀ μ' : Fin A → ℝ,
      MeasurableSet {ω : Seed × (Fin T → Fin A → ℝ) | armAt arm μ' ω.1 (extendNoise ω.2) s ≠ j} :=
    fun μ' => (measurable_armAt_joint harm μ' T s) (measurableSet_singleton j).compl
  let S : Set (Seed × (Fin T → Fin A × ℝ)) :=
    {p | arm s p.1 (fun i : Fin s => p.2 (Fin.castLE hs i)) ≠ j}
  have hSm : MeasurableSet S := by
    have : Measurable fun p : Seed × (Fin T → Fin A × ℝ) =>
        arm s p.1 (fun i : Fin s => p.2 (Fin.castLE hs i)) :=
      (harm s).comp (measurable_fst.prodMk
        (measurable_pi_lambda _ fun i => (measurable_pi_apply _).comp measurable_snd))
    exact this (measurableSet_singleton j).compl
  have hcom := lintegral_history_shift_joint arm harm μ c ν T (S.indicator 1)
    (measurable_one.indicator hSm)
  have hrestr : ∀ (μ' : Fin A → ℝ) (ω : Seed × (Fin T → Fin A → ℝ)),
      arm s ω.1 (fun i : Fin s => history arm μ' ω.1 (extendNoise ω.2) T (Fin.castLE hs i)) =
        armAt arm μ' ω.1 (extendNoise ω.2) s := by
    intro μ' ω
    rw [history_restrict arm μ' ω.1 (extendNoise ω.2) hs]
    rfl
  rw [tiltQ_def, tilted_apply' _ _ (hS μ), integral_exp_logDensity harm μ c ν T,
    ← lintegral_indicator_one (hS _), ← lintegral_indicator (hS μ)]
  simp_rw [div_one]
  convert hcom.symm using 1
  · refine lintegral_congr fun ω => ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq, S, hrestr, Pi.one_apply]
    split_ifs <;> simp
  · refine lintegral_congr fun ω => ?_
    simp only [Set.indicator_apply, Set.mem_setOf_eq, S, hrestr, Pi.one_apply]

end seed

end StatisticalRL.GaussianBanditLB
