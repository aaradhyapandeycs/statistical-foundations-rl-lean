import Formalization.Generative.FiniteHorizonGenerativeSampling
import Formalization.Probability.Variance
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-! Counterexample to the necessary S=2,A=H=1,K=4,l=2
specialization of Lemma 5.13 (`lemma:uniform`, onlineRL.tex:1696–1712). The source family indices stop at H while the bound uses h+1. Under the
natural bounded continuation-family reading, the generic continuation
family has no terminal-zero restriction. This is separate from its use on
the actual algorithm's terminal values. -/
namespace StatisticalRL.SourceCounterexamples.MVPUniform

open MeasureTheory ProbabilityTheory
open scoped BigOperators
local instance : MeasurableSpace Bool := ⊤

noncomputable def fair : FiniteDistribution Bool where
  prob _ := 1/2
  prob_nonneg _ := by norm_num
  sum_prob := by norm_num [Fintype.sum_bool]

noncomputable def environment : Fin 1 → EnvironmentStage Bool Unit := fun _ =>
  { state_nonempty := inferInstance
    action_nonempty := inferInstance
    transition := fun _ _ => fair
    reward := fun _ _ => 0
    reward_nonneg := fun _ _ => le_rfl
    reward_le_one := fun _ _ => by norm_num }

abbrev Samples := FiniteHorizonGenerative.Samples Bool Unit 1 4

/-- Batch l=2 is the single sample at position 2 (zero-based index 1). -/
def picked (data : Samples) (row : Bool) : Bool :=
  data ((⟨0, by decide⟩, row, ()), ⟨1, by decide⟩)

def indicator (b x : Bool) : ℝ := if x = b then 1 else 0

def test (i : Fin 3) : Bool → ℝ :=
  if i.val = 0 then fun _ => 0 else if i.val = 1 then indicator false else indicator true

noncomputable def family : Finset (Bool → ℝ) := by
  classical
  exact Finset.univ.image test

theorem family_card : family.card ≤ 5 := by
  classical
  have h : family.card ≤ 3 := by
    exact (Finset.card_image_le).trans (by simp)
  omega

theorem family_zero : (fun _ : Bool => (0 : ℝ)) ∈ family := by
  classical
  exact Finset.mem_image.mpr ⟨⟨0, by decide⟩, Finset.mem_univ _, rfl⟩

theorem family_indicator (b : Bool) : indicator b ∈ family := by
  classical
  cases b
  · exact Finset.mem_image.mpr ⟨⟨1, by decide⟩, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_image.mpr ⟨⟨2, by decide⟩, Finset.mem_univ _, rfl⟩

theorem family_bounds (V : Bool → ℝ) (hV : V ∈ family) (x : Bool) :
    0 ≤ V x ∧ V x ≤ 1 := by
  classical
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hV
  by_cases h0 : i.val = 0
  · simp [test, h0]
  · by_cases h1 : i.val = 1
    · by_cases hx : x = false <;> simp [test, h1, indicator, hx]
    · by_cases hx : x = true <;> simp [test, h0, h1, indicator, hx]

theorem fair_mean (b : Bool) : fair.expectation (indicator b) = 1/2 := by
  cases b <;> norm_num [fair, indicator, FiniteDistribution.expectation, Fintype.sum_bool]

theorem fair_variance (b : Bool) : fair.variance (indicator b) = 1/4 := by
  cases b <;> norm_num [fair, indicator, FiniteDistribution.variance,
    FiniteDistribution.expectation, Fintype.sum_bool]

noncomputable def batch (data : Samples) (row : Bool) : FiniteDistribution Bool :=
  FiniteDistribution.empiricalRow 1 (by decide) (fun _ => picked data row)

theorem picked_deviation (data : Samples) (row : Bool) :
    (batch data row).expectation (indicator (picked data row)) -
      fair.expectation (indicator (picked data row)) = 1/2 := by
  rw [fair_mean]
  unfold batch
  rw [FiniteDistribution.empiricalRow_expectation]
  norm_num [indicator]

noncomputable def epsilon : ℝ := (320000 * Real.log 6)⁻¹
noncomputable def deltaPrime : ℝ := Real.exp (-epsilon)
noncomputable def delta : ℝ := (16/25) * deltaPrime
noncomputable def iota : ℝ :=
  40000 * (Real.log 4 / Real.log 2)^3 * Real.log 6 * Real.log (1/deltaPrime)

theorem epsilon_pos : 0 < epsilon := by
  have h : 0 < Real.log (6 : ℝ) := Real.log_pos (by norm_num)
  unfold epsilon
  positivity

theorem deltaPrime_pos : 0 < deltaPrime := Real.exp_pos _
theorem deltaPrime_lt_one : deltaPrime < 1 := by
  apply Real.exp_lt_one_iff.mpr
  exact neg_neg_of_pos epsilon_pos

theorem delta_valid : 0 < delta ∧ delta < 1 := by
  constructor
  · unfold delta
    exact mul_pos (by norm_num) deltaPrime_pos
  · calc
      delta < (16/25 : ℝ) * 1 := mul_lt_mul_of_pos_left deltaPrime_lt_one (by norm_num)
      _ < 1 := by norm_num

theorem printed_allocation :
    100 * delta / ((2:ℝ)^2 * 1^2 * 1^2 * 4^2) = deltaPrime := by
  unfold delta
  ring

theorem iota_one : iota = 1 := by
  have h2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have h6 : Real.log (6 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hratio : Real.log (4 : ℝ) / Real.log 2 = 2 := by
    rw [h4]
    field_simp
  have hlog : Real.log (1/deltaPrime) = epsilon := by
    simp [deltaPrime, one_div]
  unfold iota
  rw [hratio, hlog]
  unfold epsilon
  field_simp
  ring

/-- The printed episode-count premise holds with equality. -/
theorem source_K_budget : (4 : ℝ) ≥ 2 * (Real.log 4 / Real.log 2) := by
  have h2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
  field_simp
  norm_num

/-- The stronger standing large-K regime of the surrounding proof also holds. -/
theorem source_large_budget : (4 : ℝ) ≥ 2 * iota := by
  rw [iota_one]
  norm_num

/-- Necessary event at one fixed admissible profile and l=2, tested only on
the two indicator choices in the deterministic three-vector family. Unit
stage and action sums have been collapsed; every printed coefficient is
written out with S=2,A=1,H=1,K=4. -/
noncomputable def necessaryEvent : Set Samples := {data |
  ∀ choice : Bool → Bool,
    (∑ row : Bool, max ((batch data row).expectation (indicator (choice row)) -
      fair.expectation (indicator (choice row))) 0) ≤
    Real.sqrt ((2 * iota / (2^2 * (Real.log 4/Real.log 2))) *
      ∑ row : Bool, fair.variance (indicator (choice row))) +
      2 * 1^2 * iota / (2^2 * (Real.log 4/Real.log 2))}

theorem necessaryEvent_empty : necessaryEvent = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro data hdata
  have h := hdata (picked data)
  have hratio : Real.log (4 : ℝ) / Real.log 2 = 2 := by
    have h2 : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    field_simp
    norm_num
  simp only [picked_deviation, fair_variance, iota_one, hratio] at h
  norm_num at h
  have hroot : Real.sqrt (1/8 : ℝ) + 1/4 < 1 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1/8)
    have hn := Real.sqrt_nonneg (1/8 : ℝ)
    nlinarith
  norm_num at hroot
  linarith

theorem actualLaw_probability :
    IsProbabilityMeasure (FiniteHorizonGenerative.samplingLaw environment 4) := inferInstance

theorem actual_event_probability_zero :
    (FiniteHorizonGenerative.samplingLaw environment 4).real necessaryEvent = 0 := by
  rw [necessaryEvent_empty]
  simp

theorem printed_uniform_probability_false :
    ¬ (1-deltaPrime ≤ (FiniteHorizonGenerative.samplingLaw environment 4).real necessaryEvent) := by
  rw [actual_event_probability_zero]
  have h := deltaPrime_lt_one
  linarith

end StatisticalRL.SourceCounterexamples.MVPUniform
