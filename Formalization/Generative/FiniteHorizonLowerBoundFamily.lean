import Formalization.Generative.FiniteHorizonSamplingAtoms
import Formalization.Online.LowerBound.ValueGap
import Formalization.Generative.FiniteHorizonPolicyEvaluationConsumption

/-!
# Hard instances for the finite-horizon generative minimax lower bound

Hard family for the prose claim `generative_model_model_based.tex:2585`: the book's own online
lower-bound family `onlineLBStages` (`chapters/onlineRL.tex:2512–3075`) with accuracy parameter
`ε₀`, hidden bits `σ : Fin H → Bool` carried by copy `0` (hidden action `1` if `σ h`, else `0`), and
every other copy with hidden action `0`.

* `controlled_congr`, `policyTrajectorySuffix_congr`: values only read the first `H` policy steps.
* `hardStages_prob_eq_of_ne`: flipping `σ h` changes only the row `(h, 0, 1)`.
* `flipped_row_ge`: the Bhattacharyya coefficient of that row is at least
  `1 − (ε₀/H²)² (H + 1)/2`.
-/

open MeasureTheory Finset
open scoped BigOperators

namespace StatisticalRL.FiniteHorizonLowerBound

open StatisticalRL OnlineLowerBound FiniteHorizonGenerative Assouad

section Locality

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- `controlled` only reads the policy at the stages of the list. -/
theorem controlled_congr (es : List (EnvironmentStage State Action))
    (π π' : ℕ → StationaryPolicy State Action) (h : ∀ n < es.length, π n = π' n) :
    EnvironmentStage.controlled es π = EnvironmentStage.controlled es π' := by
  induction es generalizing π π' with
  | nil => rfl
  | cons e es ih =>
    simp only [EnvironmentStage.controlled]
    rw [h 0 (by simp), ih (fun n ↦ π (n + 1)) (fun n ↦ π' (n + 1))
      (fun n hn ↦ h (n + 1) (by simp; omega))]

/-- The trajectory value of a deterministic policy only reads the first `length` steps. -/
theorem policyTrajectorySuffix_congr (es : List (EnvironmentStage State Action))
    (f f' : ℕ → State → Action) (hf : ∀ n < es.length, f n = f' n) (k : ℕ) :
    policyTrajectorySuffix es f k = policyTrajectorySuffix es f' k := by
  unfold policyTrajectorySuffix
  rw [controlled_congr es (deterministicPolicy f) (deterministicPolicy f')
    fun n hn ↦ by unfold deterministicPolicy; rw [hf n hn]]

end Locality

variable {S A H : ℕ}

/-- Hidden actions: copy `0` at step `h` has hidden action `1` if `σ h`, else `0`; every other copy
has hidden action `0`. -/
def hiddenAction (hA : 2 ≤ A) (σ : Fin H → Bool) : Fin (S / 2) × Fin H → Fin A :=
  fun jh ↦ if (jh.1 : ℕ) = 0 ∧ σ jh.2 = true then ⟨1, by omega⟩ else ⟨0, by omega⟩

/-- The hard instance with hidden bits `σ`. -/
noncomputable def hardStages (hS : 2 ≤ S) (hA : 2 ≤ A) (hH : 2 ≤ H) (ε₀ : ℝ) (hε : 0 < ε₀)
    (hεH : ε₀ ≤ (H : ℝ) / 2) (σ : Fin H → Bool) : Fin H → EnvironmentStage (Fin S) (Fin A) :=
  onlineLBStages S H ε₀ hS hH hε hεH (hiddenAction hA σ)

variable (hS : 2 ≤ S) (hA : 2 ≤ A) (hH : 2 ≤ H) {ε₀ : ℝ} (hε : 0 < ε₀) (hεH : ε₀ ≤ (H : ℝ) / 2)

/-- The rewards do not depend on the hidden bits. -/
theorem hardStages_reward (σ τ : Fin H → Bool) (h : Fin H) :
    (hardStages hS hA hH ε₀ hε hεH σ h).reward = (hardStages hS hA hH ε₀ hε hεH τ h).reward := rfl

/-- Explicit row probabilities. -/
theorem hardStages_prob (σ : Fin H → Bool) (h : Fin H) (s : Fin S) (a : Fin A) :
    ((hardStages hS hA hH ε₀ hε hεH σ h).transition s a).prob =
      if hs : (s : ℕ) < S / 2 then
        (fun y ↦ if y = ⟨s + S / 2, by omega⟩ then onlineLBq H ε₀ (hiddenAction hA σ (⟨s, hs⟩, h)) a
          else if y = s then 1 - onlineLBq H ε₀ (hiddenAction hA σ (⟨s, hs⟩, h)) a else 0)
      else (fun y ↦ if y = s then 1 else 0) := by
  by_cases hs : (s : ℕ) < S / 2
  · simp only [hardStages, onlineLBStages, onlineLBStage, dif_pos hs]; rfl
  · simp only [hardStages, onlineLBStages, onlineLBStage, dif_neg hs]; rfl

/-- The exit probability at copy `0` and action `1`: `1/H − ε₀/H²` if `σ h`, else `1/H`. -/
theorem onlineLBq_hidden_one (σ : Fin H → Bool) (h : Fin H) :
    onlineLBq H ε₀ (hiddenAction (S := S) hA σ (⟨0, by omega⟩, h)) ⟨1, by omega⟩ =
      if σ h then 1 / (H : ℝ) - ε₀ / (H : ℝ) ^ 2 else 1 / (H : ℝ) := by
  cases hσ : σ h <;> simp [hiddenAction, onlineLBq, hσ]

/-- Flipping bit `h` leaves every row other than `(h, 0, 1)` unchanged. -/
theorem hardStages_prob_eq_of_ne (σ : Fin H → Bool) (h h' : Fin H) (s : Fin S) (a : Fin A)
    (hne : ¬ (h' = h ∧ (s : ℕ) = 0 ∧ (a : ℕ) = 1)) :
    ((hardStages hS hA hH ε₀ hε hεH σ h').transition s a).prob =
      ((hardStages hS hA hH ε₀ hε hεH (flipAt h σ) h').transition s a).prob := by
  rw [hardStages_prob, hardStages_prob]
  by_cases hs : (s : ℕ) < S / 2
  · rw [dif_pos hs, dif_pos hs]
    have hq : onlineLBq H ε₀ (hiddenAction hA σ (⟨s, hs⟩, h')) a =
        onlineLBq H ε₀ (hiddenAction hA (flipAt h σ) (⟨s, hs⟩, h')) a := by
      by_cases hh : h' = h
      · subst hh
        by_cases hs0 : (s : ℕ) = 0
        · have ha : (a : ℕ) ≠ 1 := fun ha ↦ hne ⟨rfl, hs0, ha⟩
          cases hσ : σ h' <;>
            simp [hiddenAction, onlineLBq, hσ, hs0, Fin.ext_iff, ha]
        · simp [hiddenAction, hs0]
      · simp [hiddenAction, flipAt_of_ne hh]
    rw [hq]
  · rw [dif_neg hs, dif_neg hs]

/-- Row coefficient of an unchanged row. -/
theorem sum_sqrt_self {Ω : Type*} [Fintype Ω] (d : FiniteDistribution Ω) :
    ∑ y, Real.sqrt (d.prob y * d.prob y) = 1 := by
  simp_rw [Real.sqrt_mul_self (d.prob_nonneg _)]
  exact d.sum_prob

/-- Row coefficient of the flipped row. -/
theorem flipped_row_ge (σ : Fin H → Bool) (h : Fin H) :
    1 - (ε₀ / (H : ℝ) ^ 2) ^ 2 * ((H : ℝ) + 1) / 2 ≤
      ∑ y, Real.sqrt
        (((hardStages hS hA hH ε₀ hε hεH σ h).transition ⟨0, by omega⟩ ⟨1, by omega⟩).prob y *
          ((hardStages hS hA hH ε₀ hε hεH (flipAt h σ) h).transition ⟨0, by omega⟩
            ⟨1, by omega⟩).prob y) := by
  have hs : ((⟨0, by omega⟩ : Fin S) : ℕ) < S / 2 := by simp; omega
  rw [hardStages_prob, hardStages_prob, dif_pos hs, dif_pos hs]
  have hq1 := onlineLBq_hidden_one (hS := hS) (hA := hA) (ε₀ := ε₀) σ h
  have hq2 := onlineLBq_hidden_one (hS := hS) (hA := hA) (ε₀ := ε₀) (flipAt h σ) h
  set a := onlineLBq H ε₀ (hiddenAction hA σ (⟨0, by omega⟩, h)) ⟨1, by omega⟩ with ha
  set b := onlineLBq H ε₀ (hiddenAction hA (flipAt h σ) (⟨0, by omega⟩, h)) ⟨1, by omega⟩ with hb
  set bad : Fin S := ⟨(⟨0, by omega⟩ : Fin S) + S / 2, by simp; omega⟩ with hbad
  set good : Fin S := ⟨0, by omega⟩ with hgood
  have hne : bad ≠ good := by
    intro heq; have := congrArg Fin.val heq; simp [hbad, hgood] at this; omega
  have hpair := Finset.sum_le_sum_of_subset_of_nonneg (f := fun y : Fin S ↦ Real.sqrt
      ((if y = bad then a else if y = good then 1 - a else 0) *
        (if y = bad then b else if y = good then 1 - b else 0)))
    (Finset.subset_univ {bad, good}) (fun _ _ _ ↦ Real.sqrt_nonneg _)
  rw [Finset.sum_pair hne] at hpair
  simp only [if_true, if_neg hne.symm] at hpair
  have hHpos : (0 : ℝ) < H := by exact_mod_cast (by omega : 0 < H)
  have hH2 : (2 : ℝ) ≤ H := by exact_mod_cast hH
  have hba := onlineLBq_bounds hH hε hεH (hiddenAction hA σ (⟨0, by omega⟩, h)) ⟨1, by omega⟩
  have hbb := onlineLBq_bounds hH hε hεH (hiddenAction hA (flipAt h σ) (⟨0, by omega⟩, h))
    ⟨1, by omega⟩
  rw [← ha] at hba
  rw [← hb] at hbb
  have hinv : 1 / (2 * (H : ℝ)) + 1 / (2 * (H : ℝ)) = 1 / H := by field_simp; ring
  have hinv1 : 2 * (1 / (H : ℝ)) ≤ 1 := by
    rw [mul_one_div, div_le_one hHpos]; exact hH2
  have hκ : (0 : ℝ) < 1 / H := by positivity
  have hbern := bernoulli_bhattacharyya_ge a b (1 / H) (by linarith) (by linarith) (by linarith)
    (by linarith) hκ (by linarith) (by linarith)
  have hdiff : (a - b) ^ 2 = (ε₀ / (H : ℝ) ^ 2) ^ 2 := by
    rw [hq1, hq2, flipAt_self]
    cases σ h <;> simp
  rw [hdiff, one_div_one_div] at hbern
  linarith

end StatisticalRL.FiniteHorizonLowerBound
