import Formalization.Probability.BernoulliTailProofs
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Multiplicative lower tail for offline visitation counts

Source: `lem:sample-split-infinite`, `chapters/offlineRL.tex:1100–1117`, proof
`:3540–3615`; sampling law `:28–37`; count definition `:672–678`. For one fixed
state-action pair, the indicator variables are derived from the actual iid sample
law and the Bernoulli tail bound. A union over pairs is a separate step.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace StatisticalRL.OfflineRL

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X]

/-- Visitation count `N_x = ∑ᵢ 1{Y i = x}` (`eq:defn-Nsa-infinite`). -/
def visitCount {Ω : Type*} {N : ℕ} (Y : Fin N → Ω → X) (x : X) (ω : Ω) : ℕ :=
  ∑ i, if Y i ω = x then 1 else 0

/-- Real-valued hit indicator `1{Y i = x}`. -/
def hitReal {Ω : Type*} {N : ℕ} (Y : Fin N → Ω → X) (x : X) (i : Fin N) (ω : Ω) : ℝ :=
  if Y i ω = x then 1 else 0

/-- Boolean hit indicator on the sample space. -/
def hitBool (x : X) (y : X) : Bool := decide (y = x)

theorem measurable_hitBool (x : X) : Measurable (hitBool x) := by
  refine measurable_to_countable' fun b => ?_
  cases b
  · have : hitBool x ⁻¹' {false} = ({x} : Set X)ᶜ := by
      ext y; simp [hitBool]
    rw [this]; exact (measurableSet_singleton x).compl
  · have : hitBool x ⁻¹' {true} = ({x} : Set X) := by
      ext y; simp [hitBool]
    rw [this]; exact measurableSet_singleton x

theorem measurable_hitIndicator (x : X) :
    Measurable (fun y : X => if y = x then (1 : ℝ) else 0) :=
  Measurable.ite (measurableSet_singleton x) measurable_const measurable_const

/-- The law of the indicator `1{y = x}` under `ρ` is the source real Bernoulli
law with parameter `ρ{x}`. -/
theorem map_hitIndicator_eq_bernoulliRealLaw (ρ : Measure X) [IsProbabilityMeasure ρ] (x : X) :
    ρ.map (fun y : X => if y = x then (1 : ℝ) else 0) =
      StatisticalRL.Probability.bernoulliRealLaw (ρ.real {x}) measureReal_nonneg
        measureReal_le_one := by
  have hg : (fun y : X => if y = x then (1 : ℝ) else 0) =
      StatisticalRL.Probability.bernoulliBoolReal ∘ hitBool x := by
    funext y
    by_cases h : y = x <;> simp [hitBool, StatisticalRL.Probability.bernoulliBoolReal, h]
  rw [hg, ← Measure.map_map (measurable_of_countable _) (measurable_hitBool x)]
  unfold StatisticalRL.Probability.bernoulliRealLaw
  congr 1
  rw [Measure.ext_iff_singleton]
  intro b
  rw [Measure.map_apply (measurable_hitBool x) (measurableSet_singleton b),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b), PMF.bernoulli_apply]
  have hfin : ρ {x} ≠ ∞ := measure_ne_top ρ _
  have hc : (((ρ.real {x}).toNNReal : ℝ≥0) : ℝ≥0∞) = ρ {x} := by
    show ENNReal.ofReal (ρ.real {x}) = ρ {x}
    rw [measureReal_def]
    exact ENNReal.ofReal_toReal hfin
  cases b
  · have : hitBool x ⁻¹' {false} = ({x} : Set X)ᶜ := by
      ext y; simp [hitBool]
    rw [this, prob_compl_eq_one_sub (measurableSet_singleton x)]
    simp only [cond_false]
    rw [ENNReal.coe_sub, ENNReal.coe_one, hc]
  · have : hitBool x ⁻¹' {true} = ({x} : Set X) := by
      ext y; simp [hitBool]
    rw [this]
    simp only [cond_true]
    exact hc.symm

/-- Multiplicative lower tail for one visitation count (proof display
`eq:count-lower-tail-offline`). The samples `Y i` are independent with common
law `ρ` under `μ`; `ρ{x} = 0` is allowed. -/
theorem visitCount_lower_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ρ : Measure X) [IsProbabilityMeasure ρ] (N : ℕ) (Y : Fin N → Ω → X)
    (hYm : ∀ i, Measurable (Y i)) (hYind : iIndepFun Y μ)
    (hYlaw : ∀ i, HasLaw (Y i) ρ μ) (x : X) :
    μ.real {ω | (visitCount Y x ω : ℝ) < (N : ℝ) * ρ.real {x} / 2} ≤
      Real.exp (-((N : ℝ) * ρ.real {x} / 8)) := by
  set p := ρ.real {x} with hpdef
  have hcount : ∀ ω, (visitCount Y x ω : ℝ) = ∑ i, hitReal Y x i ω := by
    intro ω
    unfold visitCount hitReal
    push_cast
    rfl
  rcases eq_or_lt_of_le (measureReal_nonneg : 0 ≤ p) with hp0 | hp0
  · have hempty : {ω | (visitCount Y x ω : ℝ) < (N : ℝ) * p / 2} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      rw [hpdef, ← hp0]
      simp
    rw [hempty, measureReal_empty]
    exact (Real.exp_pos _).le
  · have hp1 : p ≤ 1 := measureReal_le_one
    have hg := measurable_hitIndicator x
    have hZm : ∀ i, Measurable (hitReal Y x i) := fun i => hg.comp (hYm i)
    have hZi : iIndepFun (hitReal Y x) μ :=
      hYind.comp (fun _ y => if y = x then (1 : ℝ) else 0) (fun _ => hg)
    have hZlaw : ∀ i, HasLaw (hitReal Y x i)
        (StatisticalRL.Probability.bernoulliRealLaw p hp0.le hp1) μ := by
      intro i
      refine ⟨(hZm i).aemeasurable, ?_⟩
      have hcomp : hitReal Y x i = (fun y : X => if y = x then (1 : ℝ) else 0) ∘ Y i := rfl
      rw [hcomp, ← Measure.map_map hg (hYm i), (hYlaw i).map_eq]
      exact map_hitIndicator_eq_bernoulliRealLaw ρ x
    have hmean : ∀ i, ∫ ω, hitReal Y x i ω ∂μ = p := by
      intro i
      have hind : hitReal Y x i = (Y i ⁻¹' {x}).indicator 1 := by
        funext ω
        by_cases h : Y i ω = x <;> simp [hitReal, Set.indicator, h]
      rw [hind, integral_indicator_one ((hYm i) (measurableSet_singleton x)),
        ← map_measureReal_apply (hYm i) (measurableSet_singleton x), (hYlaw i).map_eq]
    have h1 := (StatisticalRL.Probability.bernoulliTailBound_source Ω μ p hp0 hp1 N
      (hitReal Y x) hZm hZi hZlaw).1 (p / 2) (by linarith)
    have hset : {ω | (visitCount Y x ω : ℝ) < (N : ℝ) * p / 2} =
        {ω | (∑ i : Fin N, (hitReal Y x i ω - ∫ ω', hitReal Y x i ω' ∂μ)) <
          -(p / 2 * (N : ℝ))} := by
      ext ω
      simp only [Set.mem_setOf_eq, hmean, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hcount]
      constructor <;> intro h <;> linarith
    rw [hset]
    calc _ ≤ Real.exp (-((p / 2) ^ 2 * (N : ℝ) / (2 * p))) := h1
      _ = Real.exp (-((N : ℝ) * p / 8)) := by
        congr 1
        field_simp
        ring

end StatisticalRL.OfflineRL
