import Formalization.Probability.BernoulliTailDefinitions
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Map

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.Probability

universe u


/-- The two tails in `lem:tail-bound-sum-Bernoulli`, with an actual iid
Bernoulli law on an arbitrary probability space.  A Boolean draw is embedded
as the real random variable `0` or `1`; its expectation is the integral under
the supplied probability measure, not an additional premise. -/
def bernoulliTailBoundSource : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1),
    ∀ (n : ℕ) (Z : Fin n → Ω → ℝ),
      (∀ i, Measurable (Z i)) → iIndepFun Z μ →
      (∀ i, HasLaw (Z i) (bernoulliRealLaw p hp.le hp1) μ) →
      (∀ a : ℝ, 0 < a →
        μ.real {ω | (∑ i : Fin n,
          (Z i ω - ∫ ω', Z i ω' ∂μ)) <
            -(a * (n : ℝ))} ≤ Real.exp (-(a ^ 2 * (n : ℝ) / (2 * p))) ) ∧
      (∀ τ : ℝ, 2 * p * (n : ℝ) ≤ τ →
        μ.real {ω | (∑ i : Fin n, Z i ω) > τ} ≤
          2 * Real.exp (-(0.19 : ℝ) * τ))

private theorem exp_neg_le_quadratic {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  let q : ℝ := 1 - x + x ^ 2 / 2
  let r : ℝ := 1 + x + x ^ 2 / 2
  have hq : 0 ≤ q := by
    dsimp [q]
    nlinarith [sq_nonneg (x - 1)]
  have hqr : 1 ≤ q * r := by
    dsimp [q, r]
    nlinarith [sq_nonneg (x ^ 2)]
  have hr : r ≤ Real.exp x := by
    dsimp [r]
    exact Real.quadratic_le_exp_of_nonneg hx
  have hprod : 1 ≤ q * Real.exp x := hqr.trans (mul_le_mul_of_nonneg_left hr hq)
  have hinv : (Real.exp x)⁻¹ ≤ q := by
    calc
      (Real.exp x)⁻¹ = (Real.exp x)⁻¹ * 1 := by simp
      _ ≤ (Real.exp x)⁻¹ * (q * Real.exp x) :=
        mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr (Real.exp_pos x).le)
      _ = q := by field_simp [ne_of_gt (Real.exp_pos x)]
  simpa [Real.exp_neg, q] using hinv

private theorem bernoulli_centered_mgf_lower_bound (p lam : ℝ)
    (hp : 0 ≤ p) (hlam : 0 ≤ lam) :
    Real.exp (lam * p) * (1 - p + p * Real.exp (-lam)) ≤
      Real.exp (p * lam ^ 2 / 2) := by
  have hexp := exp_neg_le_quadratic hlam
  have hlin : 1 - p + p * Real.exp (-lam) ≤ 1 - p * lam + p * lam ^ 2 / 2 := by
    calc
      1 - p + p * Real.exp (-lam) ≤ 1 - p + p * (1 - lam + lam ^ 2 / 2) := by
        gcongr
      _ = 1 - p * lam + p * lam ^ 2 / 2 := by ring
  have hbracket : 1 - p * lam + p * lam ^ 2 / 2 ≤ Real.exp (-p * lam + p * lam ^ 2 / 2) := by
    calc
      1 - p * lam + p * lam ^ 2 / 2 = 1 + (-p * lam + p * lam ^ 2 / 2) := by ring
      _ ≤ Real.exp (-p * lam + p * lam ^ 2 / 2) := by
        simpa [add_comm] using Real.add_one_le_exp (-p * lam + p * lam ^ 2 / 2)
  calc
    Real.exp (lam * p) * (1 - p + p * Real.exp (-lam)) ≤
        Real.exp (lam * p) * Real.exp (-p * lam + p * lam ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (hlin.trans hbracket) (Real.exp_pos _).le
    _ = Real.exp (p * lam ^ 2 / 2) := by rw [← Real.exp_add]; congr 1 <;> ring

private theorem bernoulli_real_law_integral {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    {f : ℝ → ℝ} (hf : AEStronglyMeasurable f (bernoulliRealLaw p hp hp1)) :
    ∫ x, f x ∂bernoulliRealLaw p hp hp1 =
      ∫ b, f (bernoulliBoolReal b) ∂
        (PMF.bernoulli p.toNNReal (by
          apply NNReal.coe_le_coe.mp
          simpa only [Real.coe_toNNReal p hp] using hp1)).toMeasure := by
  have hg : Measurable bernoulliBoolReal := by fun_prop
  simpa [bernoulliRealLaw] using
    (MeasureTheory.integral_map hg.aemeasurable hf)

private theorem bernoulli_real_centered_mgf_formula {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (Z : Ω → ℝ) (hZ : HasLaw Z (bernoulliRealLaw p hp.le hp1) μ) (t : ℝ) :
    ProbabilityTheory.mgf (fun ω => Z ω - p) μ t =
      Real.exp (-t * p) * (1 - p + p * Real.exp t) := by
  unfold ProbabilityTheory.mgf
  let f : ℝ → ℝ := fun x => Real.exp (t * (x - p))
  have hf : AEStronglyMeasurable f (bernoulliRealLaw p hp.le hp1) := by fun_prop
  change μ[f ∘ Z] = _
  rw [hZ.integral_comp hf]
  rw [bernoulli_real_law_integral hp.le hp1 hf]
  have hpc : (p.toNNReal : ℝ) = p := Real.coe_toNNReal p hp.le
  have hpNN : p.toNNReal ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    simpa only [Real.coe_toNNReal p hp.le] using hp1
  have hcomp : ((1 - p.toNNReal : NNReal) : ℝ) = 1 - p := by
    rw [NNReal.coe_sub hpNN, hpc]
    norm_num
  have hexp : Real.exp (t * (1 - p)) = Real.exp t * Real.exp (-t * p) := by
    rw [show t * (1 - p) = t + (-t * p) by ring, Real.exp_add]
  rw [PMF.integral_eq_sum]
  simp [PMF.bernoulli_apply, f, bernoulliBoolReal, hpc, hcomp, hexp] <;> ring

private theorem bernoulli_real_mgf_formula {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (Z : Ω → ℝ) (hZ : HasLaw Z (bernoulliRealLaw p hp.le hp1) μ) (t : ℝ) :
    ProbabilityTheory.mgf Z μ t = 1 - p + p * Real.exp t := by
  unfold ProbabilityTheory.mgf
  let f : ℝ → ℝ := fun x => Real.exp (t * x)
  have hf : AEStronglyMeasurable f (bernoulliRealLaw p hp.le hp1) := by fun_prop
  change μ[f ∘ Z] = _
  rw [hZ.integral_comp hf]
  rw [bernoulli_real_law_integral hp.le hp1 hf]
  have hpc : (p.toNNReal : ℝ) = p := Real.coe_toNNReal p hp.le
  have hpNN : p.toNNReal ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    simpa only [Real.coe_toNNReal p hp.le] using hp1
  have hcomp : ((1 - p.toNNReal : NNReal) : ℝ) = 1 - p := by
    rw [NNReal.coe_sub hpNN, hpc]
    norm_num
  rw [PMF.integral_eq_sum]
  simp [PMF.bernoulli_apply, f, bernoulliBoolReal, hpc, hcomp] <;> ring

private theorem bernoulli_real_mean_formula {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (Z : Ω → ℝ) (hZ : HasLaw Z (bernoulliRealLaw p hp.le hp1) μ) :
    ∫ ω, Z ω ∂μ = p := by
  let f : ℝ → ℝ := fun x => x
  have hf : AEStronglyMeasurable f (bernoulliRealLaw p hp.le hp1) := by fun_prop
  calc
    ∫ ω, Z ω ∂μ = ∫ x, f x ∂bernoulliRealLaw p hp.le hp1 := by
      simpa [f, Function.comp_def] using hZ.integral_comp hf
    _ = ∫ b, bernoulliBoolReal b ∂
        (PMF.bernoulli p.toNNReal (by
          apply NNReal.coe_le_coe.mp
          simpa only [Real.coe_toNNReal p hp.le] using hp1)).toMeasure :=
      bernoulli_real_law_integral hp.le hp1 hf
    _ = p := by
      have hpc : (p.toNNReal : ℝ) = p := Real.coe_toNNReal p hp.le
      rw [PMF.integral_eq_sum]
      simp [PMF.bernoulli_apply, bernoulliBoolReal, hpc]

private theorem bernoulliRealLaw_ae_range (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ᵐ x ∂bernoulliRealLaw p hp hp1, x ∈ Set.range bernoulliBoolReal := by
  have hset : MeasurableSet (Set.range bernoulliBoolReal) := by
    have hrange : Set.range bernoulliBoolReal = ({0, 1} : Set ℝ) := by
      ext x
      simp [bernoulliBoolReal]
    rw [hrange]
    exact MeasurableSet.union (measurableSet_singleton (0 : ℝ))
      (measurableSet_singleton (1 : ℝ))
  simpa [bernoulliRealLaw] using
    (ae_map_mem_range bernoulliBoolReal hset
      ((PMF.bernoulli p.toNNReal (by
        apply NNReal.coe_le_coe.mp
        simpa only [Real.coe_toNNReal p hp] using hp1)).toMeasure))

private theorem bernoulli_real_ae_range {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (Z : Ω → ℝ) (hZ : HasLaw Z (bernoulliRealLaw p hp hp1) μ) :
    ∀ᵐ ω ∂μ, Z ω ∈ Set.range bernoulliBoolReal := by
  have hLaw := bernoulliRealLaw_ae_range p hp hp1
  have hmap : ∀ᵐ x ∂μ.map Z, x ∈ Set.range bernoulliBoolReal := by
    rw [hZ.map_eq]
    exact hLaw
  exact ae_of_ae_map hZ.aemeasurable hmap

private theorem bernoulli_iid_sum_lower_mgf_bound {Ω : Type u} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ℝ)
    (hp : 0 ≤ p) (hppos : 0 < p) (hp1 : p ≤ 1)
    (Z : Fin n → Ω → ℝ) (hZm : ∀ i, Measurable (Z i))
    (hZi : iIndepFun Z μ)
    (hZlaw : ∀ i, HasLaw (Z i) (bernoulliRealLaw p hp hp1) μ)
    (t : ℝ) (ht : 0 ≤ t) :
    ProbabilityTheory.mgf (fun ω => ∑ i : Fin n, (p - Z i ω)) μ t ≤
      Real.exp ((n : ℝ) * p * t ^ 2 / 2) := by
  classical
  let X : Fin n → Ω → ℝ := fun i ω => p - Z i ω
  have hmeas : ∀ i, Measurable (X i) := by
    intro i
    exact measurable_const.sub (hZm i)
  have hind : iIndepFun X μ := by
    apply hZi.comp (fun _ x => p - x)
    intro i
    fun_prop
  have hfactor := hind.mgf_sum (t := t) hmeas Finset.univ
  have hsum : (fun ω => ∑ i : Fin n, (p - Z i ω)) = ∑ i : Fin n, X i := by
    funext ω
    simp [X]
  rw [hsum, hfactor]
  calc
    ∏ i ∈ Finset.univ, ProbabilityTheory.mgf (fun ω => p - Z i ω) μ t ≤
        ∏ i ∈ Finset.univ, Real.exp (p * t ^ 2 / 2) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact ProbabilityTheory.mgf_nonneg
      · intro i hi
        have hform := bernoulli_real_centered_mgf_formula μ p hppos hp1 (Z i) (hZlaw i) (-t)
        have hneg : ProbabilityTheory.mgf (fun ω => p - Z i ω) μ t =
            ProbabilityTheory.mgf (fun ω => Z i ω - p) μ (-t) := by
          rw [show (fun ω => p - Z i ω) = -(fun ω => Z i ω - p) by ext ω; simp]
          exact ProbabilityTheory.mgf_neg
        rw [hneg, hform]
        simpa [neg_mul] using bernoulli_centered_mgf_lower_bound p t hp ht
    _ = Real.exp ((n : ℝ) * p * t ^ 2 / 2) := by
      simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_comm, mul_assoc,
        ← Real.exp_nat_mul]
      ring

private theorem bernoulli_iid_sum_upper_mgf_bound {Ω : Type u} [MeasurableSpace Ω]
    {n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ℝ)
    (hp : 0 ≤ p) (hppos : 0 < p) (hp1 : p ≤ 1)
    (Z : Fin n → Ω → ℝ) (hZm : ∀ i, Measurable (Z i))
    (hZi : iIndepFun Z μ)
    (hZlaw : ∀ i, HasLaw (Z i) (bernoulliRealLaw p hp hp1) μ) :
    ProbabilityTheory.mgf (fun ω => ∑ i : Fin n, Z i ω) μ (Real.log 2) ≤
      Real.exp ((n : ℝ) * p) := by
  classical
  have hfactor := hZi.mgf_sum (t := Real.log 2) hZm Finset.univ
  have hsum : (fun ω => ∑ i : Fin n, Z i ω) = ∑ i : Fin n, Z i := by
    funext ω
    simp
  rw [hsum]
  rw [hfactor]
  calc
    ∏ i ∈ Finset.univ, ProbabilityTheory.mgf (Z i) μ (Real.log 2) ≤
        ∏ i ∈ Finset.univ, Real.exp p := by
      apply Finset.prod_le_prod
      · intro i hi
        exact ProbabilityTheory.mgf_nonneg
      · intro i hi
        have hform := bernoulli_real_mgf_formula μ p hppos hp1 (Z i) (hZlaw i) (Real.log 2)
        have hexp : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
        have hscalar : 1 - p + p * Real.exp (Real.log 2) ≤ Real.exp p := by
          rw [hexp]
          calc
            1 - p + p * 2 = 1 + p := by ring
            _ ≤ Real.exp p := by simpa [add_comm] using Real.add_one_le_exp p
        rw [hform]
        exact hscalar
    _ = Real.exp ((n : ℝ) * p) := by
      simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.exp_nat_mul]

private theorem bernoulli_log_two_gap : (0.19 : ℝ) + 1 / 2 < Real.log 2 := by
  have h := Real.log_two_gt_d9
  norm_num at h ⊢
  linarith

private theorem bernoulli_tail_bounds {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (p : ℝ) (hp : 0 < p) (hp1 : p ≤ 1)
    (n : ℕ) (Z : Fin n → Ω → ℝ)
    (hZm : ∀ i, Measurable (Z i)) (hZi : iIndepFun Z μ)
    (hZlaw : ∀ i, HasLaw (Z i) (bernoulliRealLaw p hp.le hp1) μ) :
    (∀ a : ℝ, 0 < a →
      μ.real {ω | (∑ i : Fin n, (Z i ω - ∫ ω', Z i ω' ∂μ)) <
          -(a * (n : ℝ))} ≤ Real.exp (-(a ^ 2 * (n : ℝ) / (2 * p)))) ∧
    (∀ τ : ℝ, 2 * p * (n : ℝ) ≤ τ →
      μ.real {ω | (∑ i : Fin n, Z i ω) > τ} ≤
        2 * Real.exp (-(0.19 : ℝ) * τ)) := by
  constructor
  · intro a ha
    let X : Ω → ℝ := fun ω => ∑ i : Fin n, (p - Z i ω)
    have hmean : ∀ i, ∫ ω, Z i ω ∂μ = p :=
      fun i => bernoulli_real_mean_formula μ p hp hp1 (Z i) (hZlaw i)
    have hsub : {ω | (∑ i : Fin n, (Z i ω - ∫ ω', Z i ω' ∂μ)) <
          -(a * (n : ℝ))} ⊆ {ω | a * (n : ℝ) ≤ X ω} := by
      intro ω hω
      change (∑ i : Fin n, (Z i ω - ∫ ω', Z i ω' ∂μ)) < _ at hω
      simp_rw [hmean] at hω
      have hx : X ω = -∑ i : Fin n, (Z i ω - p) := by
        dsimp [X]
        calc
          ∑ i : Fin n, (p - Z i ω) = ∑ i : Fin n, -(Z i ω - p) := by
            apply Finset.sum_congr rfl
            intro i hi
            ring
          _ = -∑ i : Fin n, (Z i ω - p) := by rw [Finset.sum_neg_distrib]
      change a * (n : ℝ) ≤ X ω
      rw [hx]
      simpa using le_of_lt (neg_lt_neg hω)
    have hXmeas : Measurable X := by dsimp [X]; fun_prop
    have hZall : ∀ᵐ ω ∂μ, ∀ i, Z i ω ∈ Set.range bernoulliBoolReal := by
      apply ae_all_iff.2
      intro i
      exact bernoulli_real_ae_range μ p hp.le hp1 (Z i) (hZlaw i)
    have hXbound : ∀ᵐ ω ∂μ, X ω ≤ (n : ℝ) * p := by
      filter_upwards [hZall] with ω hω
      dsimp [X]
      calc
        ∑ i : Fin n, (p - Z i ω) ≤ ∑ _i : Fin n, p := by
          apply Finset.sum_le_sum
          intro i hi
          rcases hω i with ⟨b, hb⟩
          rw [← hb]
          cases b <;> simp [bernoulliBoolReal] <;> linarith [hp.le]
        _ = (n : ℝ) * p := by simp [mul_comm]
    have hInt : Integrable (fun ω => Real.exp (a / p * X ω)) μ :=
      integrable_exp_mul_of_le (a / p) ((n : ℝ) * p) (by positivity) hXmeas.aemeasurable hXbound
    have hmgf := bernoulli_iid_sum_lower_mgf_bound μ p hp.le hp hp1 Z hZm hZi hZlaw
      (a / p) (by positivity)
    have hchern := ProbabilityTheory.measure_ge_le_exp_mul_mgf (μ := μ) (X := X)
      (a * (n : ℝ)) (by positivity) hInt
    calc
      μ.real {ω | (∑ i : Fin n, (Z i ω - ∫ ω', Z i ω' ∂μ)) <
            -(a * (n : ℝ))} ≤ μ.real {ω | a * (n : ℝ) ≤ X ω} := measureReal_mono hsub
      _ ≤ Real.exp (-(a / p) * (a * (n : ℝ))) *
            ProbabilityTheory.mgf X μ (a / p) := hchern
      _ ≤ Real.exp (-(a / p) * (a * (n : ℝ))) *
            Real.exp ((n : ℝ) * p * (a / p) ^ 2 / 2) := by gcongr
      _ = Real.exp (-(a ^ 2 * (n : ℝ) / (2 * p))) := by
          rw [← Real.exp_add]
          congr 1
          field_simp
          <;> ring
  · intro τ hτ
    let X : Ω → ℝ := fun ω => ∑ i : Fin n, Z i ω
    have hXmeas : Measurable X := by dsimp [X]; fun_prop
    have hZall : ∀ᵐ ω ∂μ, ∀ i, Z i ω ∈ Set.range bernoulliBoolReal := by
      apply ae_all_iff.2
      intro i
      exact bernoulli_real_ae_range μ p hp.le hp1 (Z i) (hZlaw i)
    have hXbound : ∀ᵐ ω ∂μ, X ω ≤ (n : ℝ) := by
      filter_upwards [hZall] with ω hω
      dsimp [X]
      calc
        ∑ i : Fin n, Z i ω ≤ ∑ _i : Fin n, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          rcases hω i with ⟨b, hb⟩
          rw [← hb]
          cases b <;> simp [bernoulliBoolReal]
        _ = (n : ℝ) := by simp
    have hInt : Integrable (fun ω => Real.exp (Real.log 2 * X ω)) μ :=
      integrable_exp_mul_of_le (Real.log 2) (n : ℝ) (by positivity) hXmeas.aemeasurable hXbound
    have hmgf := bernoulli_iid_sum_upper_mgf_bound μ p hp.le hp hp1 Z hZm hZi hZlaw
    have hchern := ProbabilityTheory.measure_ge_le_exp_mul_mgf (μ := μ) (X := X)
      τ (by exact Real.log_nonneg (by norm_num)) hInt
    have hlog := bernoulli_log_two_gap
    calc
      μ.real {ω | (∑ i : Fin n, Z i ω) > τ} ≤ μ.real {ω | τ ≤ X ω} := measureReal_mono (by
        intro ω hω
        change (∑ i : Fin n, Z i ω) > _ at hω
        exact le_of_lt hω)
      _ ≤ Real.exp (-(Real.log 2) * τ) * ProbabilityTheory.mgf X μ (Real.log 2) := hchern
      _ ≤ Real.exp (-(Real.log 2) * τ) * Real.exp ((n : ℝ) * p) := by gcongr
      _ ≤ Real.exp (-(0.19 : ℝ) * τ) := by
          have hn : (n : ℝ) * p ≤ τ / 2 := by nlinarith [hτ]
          have hgap : 0 < Real.log 2 - 1 / 2 - (0.19 : ℝ) := by linarith [hlog]
          have hτnonneg : 0 ≤ τ := by nlinarith [hτ]
          have hmul : 0 ≤ (Real.log 2 - 1 / 2 - (0.19 : ℝ)) * τ :=
            mul_nonneg hgap.le hτnonneg
          have hexp : -(Real.log 2) * τ + (n : ℝ) * p ≤ -(0.19 : ℝ) * τ := by
            nlinarith [hn, hmul]
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr hexp
      _ ≤ 2 * Real.exp (-(0.19 : ℝ) * τ) := by
          linarith [Real.exp_nonneg (-(0.19 : ℝ) * τ)]

/-- The exact Chapter 2 Bernoulli tail statement, specialized to the actual
real-valued Bernoulli law and an arbitrary probability space. -/
theorem bernoulliTailBound_source : bernoulliTailBoundSource := by
  intro Ω inst μ hμ p hp hp1 n Z hZm hZi hZlaw
  exact bernoulli_tail_bounds μ p hp hp1 n Z hZm hZi hZlaw

end StatisticalRL.Probability
