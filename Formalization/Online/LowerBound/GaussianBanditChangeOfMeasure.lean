import Formalization.Online.LowerBound.GaussianBanditMeasurability
import Formalization.Online.LowerBound.GaussianBanditShift

/-!
# Adapted change of measure for Gaussian bandits (Remark 5.12)

Running a learner on the means `μ + c` gives the same law of (seed, history) as running it on the
means `μ` under the measure with density `exp f`, where
`f = Σ_{s<T} (c(a_s) z_{s,a_s} − c(a_s)²/2)` and `a_s` are the arms pulled under `μ`.
Only the observed coordinates enter the density.
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

noncomputable section

namespace StatisticalRL.GaussianBanditLB

open StatisticalRL.Bandit

variable {A : ℕ}

/-- The law of one noise row. -/
abbrev rowLaw (A : ℕ) : Measure (Fin A → ℝ) := Measure.pi fun _ : Fin A => gaussianReal 0 1

theorem measurable_eval_fin {X : Type*} [MeasurableSpace X] {a : X → Fin A} (ha : Measurable a)
    {y : X → Fin A → ℝ} (hy : Measurable y) : Measurable fun x => y x (a x) := by
  have h1 : Measurable fun q : Fin A × X => y q.2 q.1 := by
    apply measurable_from_prod_countable_right
    intro b
    exact (measurable_pi_apply b).comp hy
  exact h1.comp (ha.prodMk measurable_id)

theorem measurable_snoc {X : Type*} [MeasurableSpace X] (t : ℕ) :
    Measurable fun q : (Fin t → X) × X => (Fin.snoc (α := fun _ => X) q.1 q.2 : Fin (t + 1) → X) := by
  refine measurable_pi_lambda _ fun i => ?_
  induction i using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using measurable_snd
  | cast j => simpa only [Fin.snoc_castSucc] using (measurable_pi_apply j).comp measurable_fst

/-- Split one row off the noise table. -/
theorem lintegral_table_split {T : ℕ} (i : Fin (T + 1)) (F : (Fin (T + 1) → Fin A → ℝ) → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ z, F z ∂gaussianNoiseTable (T + 1) A =
      ∫⁻ w, ∫⁻ y, F (Fin.insertNth (α := fun _ => Fin A → ℝ) i y w) ∂rowLaw A
        ∂gaussianNoiseTable T A := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (T + 1) => rowLaw A) i
  unfold gaussianNoiseTable
  rw [← hmp.symm.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _),
    lintegral_prod_symm' (fun p => F ((MeasurableEquiv.piFinSuccAbove _ i).symm p))
      (hF.comp (MeasurableEquiv.measurable _))]
  rfl

/-- Split the last row off the noise table. -/
theorem lintegral_table_snoc {T : ℕ} (F : (Fin (T + 1) → Fin A → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂gaussianNoiseTable (T + 1) A =
      ∫⁻ w, ∫⁻ y, F (Fin.snoc (α := fun _ => Fin A → ℝ) w y) ∂rowLaw A ∂gaussianNoiseTable T A := by
  rw [lintegral_table_split (Fin.last T) F hF]
  simp only [Fin.insertNth_last']

theorem extendNoise_snoc_of_lt {T : ℕ} (w : Fin T → Fin A → ℝ) (y : Fin A → ℝ) {s : ℕ}
    (hs : s < T) :
    extendNoise (Fin.snoc (α := fun _ => Fin A → ℝ) w y) s = extendNoise w s := by
  have h1 : s < T + 1 := Nat.lt_succ_of_lt hs
  simp only [extendNoise, h1, hs, dif_pos]
  have : (⟨s, h1⟩ : Fin (T + 1)) = Fin.castSucc ⟨s, hs⟩ := rfl
  rw [this, Fin.snoc_castSucc]

theorem extendNoise_snoc_last {T : ℕ} (w : Fin T → Fin A → ℝ) (y : Fin A → ℝ) :
    extendNoise (Fin.snoc (α := fun _ => Fin A → ℝ) w y) T = y := by
  have h1 : T < T + 1 := Nat.lt_succ_self T
  simp only [extendNoise, h1, dif_pos]
  have : (⟨T, h1⟩ : Fin (T + 1)) = Fin.last T := rfl
  rw [this, Fin.snoc_last]

section seed

variable {Seed : Type*} (arm : (t : ℕ) → Seed → (Fin t → Fin A × ℝ) → Fin A)

theorem history_snoc (μ : Fin A → ℝ) (σ : Seed) {T : ℕ} (w : Fin T → Fin A → ℝ)
    (y : Fin A → ℝ) :
    history arm μ σ (extendNoise (Fin.snoc (α := fun _ => Fin A → ℝ) w y)) (T + 1) =
      Fin.snoc (α := fun _ => Fin A × ℝ) (history arm μ σ (extendNoise w) T)
        (arm T σ (history arm μ σ (extendNoise w) T),
          μ (arm T σ (history arm μ σ (extendNoise w) T))
            + y (arm T σ (history arm μ σ (extendNoise w) T))) := by
  rw [history, history_congr arm μ σ T (fun s hs => extendNoise_snoc_of_lt w y hs),
    extendNoise_snoc_last]

theorem armAt_snoc_of_le (μ : Fin A → ℝ) (σ : Seed) {T : ℕ} (w : Fin T → Fin A → ℝ)
    (y : Fin A → ℝ) {s : ℕ} (hs : s ≤ T) :
    armAt arm μ σ (extendNoise (Fin.snoc (α := fun _ => Fin A → ℝ) w y)) s =
      armAt arm μ σ (extendNoise w) s := by
  unfold armAt
  rw [history_congr arm μ σ s (fun r hr => extendNoise_snoc_of_lt w y (lt_of_lt_of_le hr hs))]

/-- The log-density `f = Σ_{s<T} (c(a_s) z_{s,a_s} − c(a_s)²/2)` of the change of measure from the
means `μ` to the means `μ + c`; the arms `a_s` are those pulled under `μ`. -/
def logDensity (μ c : Fin A → ℝ) (T : ℕ) (σ : Seed) (z : Fin T → Fin A → ℝ) : ℝ :=
  ∑ s : Fin T, (c (armAt arm μ σ (extendNoise z) s) * z s (armAt arm μ σ (extendNoise z) s)
    - c (armAt arm μ σ (extendNoise z) s) ^ 2 / 2)

theorem logDensity_snoc (μ c : Fin A → ℝ) (σ : Seed) {T : ℕ} (w : Fin T → Fin A → ℝ)
    (y : Fin A → ℝ) :
    logDensity arm μ c (T + 1) σ (Fin.snoc (α := fun _ => Fin A → ℝ) w y) =
      logDensity arm μ c T σ w +
        (c (arm T σ (history arm μ σ (extendNoise w) T)) *
            y (arm T σ (history arm μ σ (extendNoise w) T))
          - c (arm T σ (history arm μ σ (extendNoise w) T)) ^ 2 / 2) := by
  unfold logDensity
  rw [Fin.sum_univ_castSucc]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    simp only [Fin.val_castSucc, Fin.snoc_castSucc]
    rw [armAt_snoc_of_le arm μ σ w y s.isLt.le]
  · simp only [Fin.val_last, Fin.snoc_last]
    rw [armAt_snoc_of_le arm μ σ w y le_rfl]
    rfl

variable [MeasurableSpace Seed]

theorem measurable_logDensity (harm : ∀ t, Measurable (Function.uncurry (arm t)))
    (μ c : Fin A → ℝ) (T : ℕ) :
    Measurable fun ω : Seed × (Fin T → Fin A → ℝ) => logDensity arm μ c T ω.1 ω.2 := by
  unfold logDensity
  refine Finset.measurable_sum _ fun s _ => ?_
  have ha := measurable_armAt μ harm measurable_fst
    ((measurable_extendNoise T).comp measurable_snd) s
  have hc := (measurable_of_countable c).comp ha
  exact (hc.mul (measurable_eval_fin ha ((measurable_pi_apply s).comp measurable_snd))).sub
    (hc.pow_const 2 |>.div_const 2)

/-- Change of measure at a fixed seed. -/
theorem lintegral_history_shift (harm : ∀ t, Measurable (Function.uncurry (arm t)))
    (μ c : Fin A → ℝ) (σ : Seed) :
    ∀ (T : ℕ) (g : (Fin T → Fin A × ℝ) → ℝ≥0∞), Measurable g →
      ∫⁻ z, g (history arm (fun a => μ a + c a) σ (extendNoise z) T) ∂gaussianNoiseTable T A =
        ∫⁻ z, g (history arm μ σ (extendNoise z) T) *
          ENNReal.ofReal (Real.exp (logDensity arm μ c T σ z)) ∂gaussianNoiseTable T A
  | 0, g, _ => by
    simp [history, logDensity]
  | T + 1, g, hg => by
    set μ' : Fin A → ℝ := fun a => μ a + c a with hμ'
    have hH : ∀ ν : Fin A → ℝ, Measurable fun z : Fin T → Fin A → ℝ =>
        history arm ν σ (extendNoise z) T :=
      fun ν => measurable_history ν harm measurable_const (measurable_extendNoise T) T
    have hH1 : ∀ ν : Fin A → ℝ, Measurable fun z : Fin (T + 1) → Fin A → ℝ =>
        history arm ν σ (extendNoise z) (T + 1) :=
      fun ν => measurable_history ν harm measurable_const (measurable_extendNoise (T + 1)) (T + 1)
    have hLD : Measurable fun z : Fin (T + 1) → Fin A → ℝ => logDensity arm μ c (T + 1) σ z :=
      (measurable_logDensity arm harm μ c (T + 1)).comp (measurable_const.prodMk measurable_id)
    -- the one-step integrand
    have harmT : Measurable fun h : Fin T → Fin A × ℝ => arm T σ h :=
      (harm T).comp (measurable_const.prodMk measurable_id)
    let G : (Fin A → ℝ) → (Fin T → Fin A × ℝ) → ℝ≥0∞ := fun ν h =>
      ∫⁻ y, g (Fin.snoc (α := fun _ => Fin A × ℝ) h (arm T σ h, ν (arm T σ h) + y (arm T σ h)))
        ∂rowLaw A
    have hG : ∀ ν : Fin A → ℝ, Measurable (G ν) := by
      intro ν
      refine Measurable.lintegral_prod_right' (f := fun q : (Fin T → Fin A × ℝ) × (Fin A → ℝ) =>
        g (Fin.snoc (α := fun _ => Fin A × ℝ) q.1
          (arm T σ q.1, ν (arm T σ q.1) + q.2 (arm T σ q.1)))) ?_
      have ha : Measurable fun q : (Fin T → Fin A × ℝ) × (Fin A → ℝ) => arm T σ q.1 :=
        harmT.comp measurable_fst
      exact hg.comp ((measurable_snoc T).comp (measurable_fst.prodMk
        (ha.prodMk (((measurable_of_countable ν).comp ha).add
          (measurable_eval_fin ha measurable_snd)))))
    -- left side
    have hL : Measurable fun z : Fin (T + 1) → Fin A → ℝ =>
        g (history arm μ' σ (extendNoise z) (T + 1)) := hg.comp (hH1 μ')
    rw [lintegral_table_snoc _ hL]
    simp_rw [history_snoc]
    change ∫⁻ w, G μ' (history arm μ' σ (extendNoise w) T) ∂gaussianNoiseTable T A = _
    rw [lintegral_history_shift harm μ c σ T (G μ') (hG μ')]
    -- right side
    have hR : Measurable fun z : Fin (T + 1) → Fin A → ℝ =>
        g (history arm μ σ (extendNoise z) (T + 1)) *
          ENNReal.ofReal (Real.exp (logDensity arm μ c (T + 1) σ z)) :=
      (hg.comp (hH1 μ)).mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hLD))
    rw [lintegral_table_snoc _ hR]
    simp_rw [history_snoc, logDensity_snoc]
    refine lintegral_congr fun w => ?_
    set h := history arm μ σ (extendNoise w) T
    set a := arm T σ h
    set D := ENNReal.ofReal (Real.exp (logDensity arm μ c T σ w))
    have hshift := lintegral_coord_shift a
      (fun x => g (Fin.snoc (α := fun _ => Fin A × ℝ) h (a, μ a + x)))
      (hg.comp ((measurable_snoc T).comp (measurable_const.prodMk
        (measurable_const.prodMk (measurable_const.add measurable_id))))) (c a)
    simp only [G]
    have hl : ∀ y : Fin A → ℝ, μ' a + y a = μ a + (y a + c a) := fun y => by
      show (μ a + c a) + y a = μ a + (y a + c a); ring
    change (∫⁻ y, g (Fin.snoc (α := fun _ => Fin A × ℝ) h (a, μ' a + y a)) ∂rowLaw A) * D = _
    have e1 : ∫⁻ y, g (Fin.snoc (α := fun _ => Fin A × ℝ) h (a, μ' a + y a)) ∂rowLaw A =
        ∫⁻ y, g (Fin.snoc (α := fun _ => Fin A × ℝ) h (a, μ a + (y a + c a))) ∂rowLaw A :=
      lintegral_congr fun y => by rw [hl y]
    rw [e1, hshift]
    rw [← lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun y => ?_
    rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    ring

/-- Change of measure on the joint space of seed and noise table. -/
theorem lintegral_history_shift_joint (harm : ∀ t, Measurable (Function.uncurry (arm t)))
    (μ c : Fin A → ℝ) (ν : Measure Seed) [SFinite ν] (T : ℕ)
    (g : Seed × (Fin T → Fin A × ℝ) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ ω, g (ω.1, history arm (fun a => μ a + c a) ω.1 (extendNoise ω.2) T)
        ∂(ν.prod (gaussianNoiseTable T A)) =
      ∫⁻ ω, g (ω.1, history arm μ ω.1 (extendNoise ω.2) T) *
        ENNReal.ofReal (Real.exp (logDensity arm μ c T ω.1 ω.2))
        ∂(ν.prod (gaussianNoiseTable T A)) := by
  have hH : ∀ ν' : Fin A → ℝ, Measurable fun ω : Seed × (Fin T → Fin A → ℝ) =>
      history arm ν' ω.1 (extendNoise ω.2) T :=
    fun ν' => measurable_history ν' harm measurable_fst
      ((measurable_extendNoise T).comp measurable_snd) T
  have hL : Measurable fun ω : Seed × (Fin T → Fin A → ℝ) =>
      g (ω.1, history arm (fun a => μ a + c a) ω.1 (extendNoise ω.2) T) :=
    hg.comp (measurable_fst.prodMk (hH _))
  have hR : Measurable fun ω : Seed × (Fin T → Fin A → ℝ) =>
      g (ω.1, history arm μ ω.1 (extendNoise ω.2) T) *
        ENNReal.ofReal (Real.exp (logDensity arm μ c T ω.1 ω.2)) :=
    (hg.comp (measurable_fst.prodMk (hH _))).mul (ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_logDensity arm harm μ c T)))
  rw [lintegral_prod _ hL.aemeasurable, lintegral_prod _ hR.aemeasurable]
  refine lintegral_congr fun σ => ?_
  exact lintegral_history_shift arm harm μ c σ T (fun h => g (σ, h))
    (hg.comp (measurable_const.prodMk measurable_id))

end seed

end StatisticalRL.GaussianBanditLB
