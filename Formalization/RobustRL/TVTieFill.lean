import Mathlib

/-! TV proof finite tie-filling helper for the robust-TV
fractional-knapsack reduction. Given a threshold whose strict-above mass is
at most capacity and whose strict-above plus tie mass reaches capacity, the
piecewise proportional fill is coordinatewise feasible and uses exactly the
capacity. The finite sorted-prefix argument that supplies such a threshold
is separate. -/

open scoped BigOperators

namespace StatisticalRL.RobustRL.TVProof.TieFill

variable {ι : Type*} [Fintype ι]

/-- Weight strictly above a given threshold. -/
noncomputable def aboveMass (p c : ι → ℝ) (threshold : ℝ) : ℝ :=
  ∑ i, if threshold < c i then p i else 0

/-- Weight tied exactly at a given threshold. -/
noncomputable def tieMass (p c : ι → ℝ) (threshold : ℝ) : ℝ :=
  ∑ i, if c i = threshold then p i else 0

/-- Proportional threshold fill: take all above threshold and the needed fraction of
the weight tied at threshold. -/
noncomputable def thresholdFill (p c : ι → ℝ) (σ threshold : ℝ) (i : ι) : ℝ :=
  if threshold < c i then p i
  else if c i = threshold then
    ((σ - aboveMass p c threshold) / tieMass p c threshold) * p i
  else 0

/-- Under the crossing inequalities and positive tie mass, every filled
coordinate lies between zero and its available mass. -/
theorem thresholdFill_bounds (p c : ι → ℝ) (σ threshold : ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (hbelow : aboveMass p c threshold ≤ σ)
    (habove : σ ≤ aboveMass p c threshold + tieMass p c threshold)
    (htie : 0 < tieMass p c threshold) (i : ι) :
    0 ≤ thresholdFill p c σ threshold i ∧ thresholdFill p c σ threshold i ≤ p i := by
  have hnum : 0 ≤ σ - aboveMass p c threshold := sub_nonneg.mpr hbelow
  have hratio_nonneg :
      0 ≤ (σ - aboveMass p c threshold) / tieMass p c threshold :=
    div_nonneg hnum (le_of_lt htie)
  have hnum_le : σ - aboveMass p c threshold ≤ tieMass p c threshold := by linarith
  have hratio_le :
      (σ - aboveMass p c threshold) / tieMass p c threshold ≤ 1 := by
    calc
      (σ - aboveMass p c threshold) / tieMass p c threshold ≤
          tieMass p c threshold / tieMass p c threshold :=
        div_le_div_of_nonneg_right hnum_le (le_of_lt htie)
      _ = 1 := div_self (ne_of_gt htie)
  by_cases hgt : threshold < c i
  · simp [thresholdFill, hgt, hp i]
  · by_cases heq : c i = threshold
    · simp only [thresholdFill, hgt, heq, lt_irrefl, ↓reduceIte]
      constructor
      · exact mul_nonneg hratio_nonneg (hp i)
      · simpa using mul_le_mul_of_nonneg_right hratio_le (hp i)
    · simp [thresholdFill, hgt, heq, hp i]

/-- The sum of the threshold fill is the strict-above mass plus the
proportional tie allocation. -/
theorem thresholdFill_sum_eq (p c : ι → ℝ) (σ threshold : ℝ)
    (htie : 0 < tieMass p c threshold) :
    (∑ i, thresholdFill p c σ threshold i) =
      aboveMass p c threshold +
        ((σ - aboveMass p c threshold) / tieMass p c threshold) * tieMass p c threshold := by
  have hpoint (i : ι) :
      thresholdFill p c σ threshold i =
        (if threshold < c i then p i else 0) +
          (if c i = threshold then
            ((σ - aboveMass p c threshold) / tieMass p c threshold) * p i else 0) := by
    by_cases hgt : threshold < c i
    · have hne : c i ≠ threshold := by
        intro h
        rw [h] at hgt
        exact (lt_irrefl threshold) hgt
      simp [thresholdFill, hgt, hne]
    · simp [thresholdFill, hgt]
  calc
    ∑ i, thresholdFill p c σ threshold i =
        ∑ i, ((if threshold < c i then p i else 0) +
          (if c i = threshold then
            ((σ - aboveMass p c threshold) / tieMass p c threshold) * p i else 0)) :=
      Finset.sum_congr rfl fun i _ ↦ hpoint i
    _ = (∑ i, if threshold < c i then p i else 0) +
        ∑ i, if c i = threshold then
          ((σ - aboveMass p c threshold) / tieMass p c threshold) * p i else 0 :=
      Finset.sum_add_distrib
    _ = aboveMass p c threshold +
        ((σ - aboveMass p c threshold) / tieMass p c threshold) * tieMass p c threshold := by
      simp only [aboveMass, tieMass]
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      split_ifs <;> simp

/-- With a threshold crossing witness, proportional tie filling consumes
exactly the prescribed capacity. -/
theorem thresholdFill_sum_eq_capacity (p c : ι → ℝ) (σ threshold : ℝ)
    (hbelow : aboveMass p c threshold ≤ σ)
    (habove : σ ≤ aboveMass p c threshold + tieMass p c threshold)
    (htie : 0 < tieMass p c threshold) :
    (∑ i, thresholdFill p c σ threshold i) = σ := by
  rw [thresholdFill_sum_eq p c σ threshold htie]
  have hnum : σ - aboveMass p c threshold ≤ tieMass p c threshold := by linarith
  have hcancel :
      ((σ - aboveMass p c threshold) / tieMass p c threshold) * tieMass p c threshold =
        σ - aboveMass p c threshold := by
    field_simp [ne_of_gt htie]
  linarith

end StatisticalRL.RobustRL.TVProof.TieFill
