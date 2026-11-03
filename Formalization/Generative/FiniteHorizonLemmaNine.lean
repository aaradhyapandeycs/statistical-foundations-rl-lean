import Formalization.Generative.FiniteHorizonAuxiliaryTerminal
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Deterministic, sample-parameter-shaped wrapper for Li et al. Lemma 9.
Bernstein conditions are explicit; no probability or policy-selection law is claimed. -/
namespace StatisticalRL.FiniteHorizonGenerative
variable {State Action : Type*} [Fintype State] [Fintype Action]

theorem auxiliaryResidualCondition_drop
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (l h : ℕ) (a b : ℝ)
    (hres : auxiliaryResidualCondition pairs f l a b) :
    auxiliaryResidualCondition (pairs.drop h) (fun k ↦ f (h + k)) l a b := by
  induction h generalizing pairs f with
  | zero => simpa only [List.drop_zero, Nat.zero_add] using hres
  | succ h ih =>
    cases pairs with
    | nil => trivial
    | cons p tail =>
      have ht := ih tail (fun k ↦ f (k + 1)) hres.2
      simpa only [List.drop_succ_cons, Nat.succ_add, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ht

/-- The paper's sample threshold implies exactly the contraction used in the
proved natural-depth closure; no contraction estimate is an added premise. -/
theorem auxiliary_sample_contraction (H N : ℕ) (β : ℝ)
    (hβ : 0 ≤ β) (hN : 0 < N) (hsize : 12 * (H : ℝ) * β ≤ N) :
    Real.sqrt (β / (N : ℝ)) * Real.sqrt (3 * (H : ℝ)) ≤ 1 / 2 := by
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have harg : 0 ≤ β / (N : ℝ) := div_nonneg hβ hNr.le
  have ha2 := Real.sq_sqrt harg
  have hc2 := Real.sq_sqrt (by positivity : 0 ≤ 3 * (H : ℝ))
  have hratio : 12 * (H : ℝ) * (β / (N : ℝ)) ≤ 1 := by
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hNr).2 (by simpa using hsize)
  have he : (Real.sqrt (β / (N : ℝ)) * Real.sqrt (3 * (H : ℝ))) ^ 2 =
      3 * (H : ℝ) * (β / (N : ℝ)) := by rw [mul_pow, ha2, hc2]; ring
  have hp : 0 ≤ Real.sqrt (β / (N : ℝ)) * Real.sqrt (3 * (H : ℝ)) := by positivity
  nlinarith

/-- Source Lemma 9's deterministic conclusion with a weak sample threshold.
The positive-N domain makes its coefficient expressions actual sampling quantities. -/
theorem auxiliaryErrorNorm_le_lemmaNine_of_le
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (H N : ℕ) (β : ℝ)
    (hH : 0 < H) (hN : 0 < N) (hβ : 0 ≤ β) (hlen : pairs.length ≤ H)
    (hsize : 12 * (H : ℝ) * β ≤ N)
    (hres : ∀ l ≤ Nat.log 2 H,
      auxiliaryResidualCondition pairs f l (Real.sqrt (β / (N : ℝ))) (β / (N : ℝ))) :
    auxiliaryErrorNorm pairs f 0 ≤ 6 * H * Real.sqrt (3 * β * H / (N : ℝ)) := by
  have harg : 0 ≤ β / (N : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  have ha2 := Real.sq_sqrt harg
  have hh := auxiliaryErrorNorm_le_six pairs f H (Real.sqrt (β / (N : ℝ))) hH
    (Real.sqrt_nonneg _) hlen (auxiliary_sample_contraction H N β hβ hN hsize)
    (by intro l hl; rw [ha2]; exact hres l hl)
  have he : Real.sqrt (β / (N : ℝ)) * Real.sqrt (3 * (H : ℝ)) =
      Real.sqrt (3 * β * H / (N : ℝ)) := by
    rw [← Real.sqrt_mul harg]
    congr 1
    ring
  simpa only [he] using hh

/-- Source strict sample-size domain. Positivity of N is derived, not added. -/
theorem auxiliaryErrorNorm_le_lemmaNine
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (H N : ℕ) (β : ℝ)
    (hH : 0 < H) (hβ : 0 ≤ β) (hlen : pairs.length ≤ H)
    (hsize : 12 * (H : ℝ) * β < N)
    (hres : ∀ l ≤ Nat.log 2 H,
      auxiliaryResidualCondition pairs f l (Real.sqrt (β / (N : ℝ))) (β / (N : ℝ))) :
    auxiliaryErrorNorm pairs f 0 ≤ 6 * H * Real.sqrt (3 * β * H / (N : ℝ)) := by
  have hNr : 0 < (N : ℝ) := lt_of_le_of_lt (by positivity) hsize
  exact auxiliaryErrorNorm_le_lemmaNine_of_le pairs f H N β hH (Nat.cast_pos.mp hNr)
    hβ hlen hsize.le hres

/-- All starting stages share the same source radius. The recursive residual
condition supplies every suffix without assuming a new event for each stage. -/
theorem auxiliaryErrorNormAt_le_lemmaNine
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (H N : ℕ) (β : ℝ)
    (hH : 0 < H) (hβ : 0 ≤ β) (hlen : pairs.length ≤ H)
    (hsize : 12 * (H : ℝ) * β < N)
    (hres : ∀ l ≤ Nat.log 2 H,
      auxiliaryResidualCondition pairs f l (Real.sqrt (β / (N : ℝ))) (β / (N : ℝ)))
    (h : ℕ) :
    ‖comparisonAuxiliaryValueAt pairs f 0 h - trueAuxiliaryValueAt (pairs.map Prod.fst) f 0 h‖ ≤
      6 * H * Real.sqrt (3 * β * H / (N : ℝ)) := by
  have hh := auxiliaryErrorNorm_le_lemmaNine (pairs.drop h) (fun k ↦ f (h + k)) H N β
    hH hβ (by simp only [List.length_drop]; omega) hsize
    (fun l hl ↦ auxiliaryResidualCondition_drop pairs f l h _ _ (hres l hl))
  simpa only [auxiliaryErrorNorm, comparisonAuxiliaryValueAt, trueAuxiliaryValueAt,
    List.map_drop] using hh

/-- The printed real-log level domain suffices for the natural-depth proof.
This theorem adds no residual level beyond l≤log₂H. -/
theorem auxiliaryErrorNormAt_le_source_lemmaNine
    (pairs : List (EnvironmentStage State Action × EnvironmentStage State Action))
    (f : ℕ → State → Action) (H N : ℕ) (β : ℝ)
    (hH : 0 < H) (hβ : 0 ≤ β) (hlen : pairs.length ≤ H)
    (hsize : 12 * (H : ℝ) * β < N)
    (hres : ∀ l : ℕ, (l : ℝ) ≤ Real.logb 2 (H : ℝ) →
      auxiliaryResidualCondition pairs f l (Real.sqrt (β / (N : ℝ))) (β / (N : ℝ)))
    (h : ℕ) :
    ‖comparisonAuxiliaryValueAt pairs f 0 h - trueAuxiliaryValueAt (pairs.map Prod.fst) f 0 h‖ ≤
      6 * H * Real.sqrt (3 * β * H / (N : ℝ)) := by
  apply auxiliaryErrorNormAt_le_lemmaNine pairs f H N β hH hβ hlen hsize _ h
  intro l hl
  exact hres l ((Nat.cast_le.mpr hl).trans (Real.natLog_le_logb H 2))

end StatisticalRL.FiniteHorizonGenerative
