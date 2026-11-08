import Formalization.Ch7Rest.VPODefs712
import Formalization.Ch7Rest.VPOElementary712
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Corrected Theorem 7.12: Gibbs policies and calibrated values

Proof steps: L1 (Gibbs variational principle, closed form of `J⋆`), L2 (density
ratios), L3 (VPO objective of a Gibbs policy), L4 (existence of a ball minimizer), L5
(calibration gap), and the local-curvature bound (step 1 of the local-curvature argument).
-/

namespace StatisticalRL.Ch7Rest.Rlhf

open Finset Real

set_option linter.unusedSectionVars false

section Rows

variable {Y : Type} [Fintype Y]

/-- Gibbs inequality: for `p ≥ 0`, `pol > 0` with `∑ p = ∑ pol = 1`, `0 ≤ ∑ p log(p/pol)`. -/
theorem kl_nonneg_row (p pol : Y → ℝ) (hp : ∀ y, 0 ≤ p y) (hπ : ∀ y, 0 < pol y)
    (hp1 : ∑ y, p y = 1) (hπ1 : ∑ y, pol y = 1) : 0 ≤ ∑ y, p y * log (p y / pol y) := by
  have h := sum_le_sum fun y (_ : y ∈ univ) ↦ sub_le_mul_log_div (hp y) (hπ y)
  rw [sum_sub_distrib, hp1, hπ1, sub_self] at h
  exact h

/-- Row Gibbs variational principle (L1). With `Z = ∑ q e^{r/β}` and `pol = q e^{r/β}/Z`:
for every `p` in the simplex, `∑ p r − β ∑ p log(p/q) ≤ β log Z`, with equality at `p = pol`. -/
theorem row_value_le (q r p : Y → ℝ) (β : ℝ) (hβ : 0 < β) (hq : ∀ y, 0 < q y)
    (hp : ∀ y, 0 ≤ p y) (hp1 : ∑ y, p y = 1) :
    ∑ y, p y * r y - β * ∑ y, p y * log (p y / q y) ≤
      β * log (∑ y, q y * exp (r y / β)) := by
  set Z := ∑ y, q y * exp (r y / β) with hZ
  have hne : (univ : Finset Y).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.1 h, sum_empty] at hp1
    exact zero_ne_one hp1
  have hZ0 : 0 < Z := sum_pos (fun y _ ↦ mul_pos (hq y) (exp_pos _)) hne
  set pol : Y → ℝ := fun y ↦ q y * exp (r y / β) / Z with hπdef
  have hπ0 : ∀ y, 0 < pol y := fun y ↦ div_pos (mul_pos (hq y) (exp_pos _)) hZ0
  have hπ1 : ∑ y, pol y = 1 := by
    simp only [hπdef]; rw [← sum_div, div_self hZ0.ne']
  have hsplit : ∀ y, p y * log (p y / q y) =
      p y * log (p y / pol y) + p y * (r y / β - log Z) := by
    intro y
    rcases (hp y).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have : log (p y / q y) = log (p y / pol y) + (r y / β - log Z) := by
        rw [log_div hpos.ne' (hq y).ne', log_div hpos.ne' (hπ0 y).ne', hπdef]
        simp only
        rw [log_div (mul_pos (hq y) (exp_pos _)).ne' hZ0.ne', log_mul (hq y).ne' (exp_pos _).ne',
          log_exp]
        ring
      rw [this]; ring
  have hkl := kl_nonneg_row p pol hp hπ0 hp1 hπ1
  rw [sum_congr rfl fun y _ ↦ hsplit y, sum_add_distrib]
  have h2 : ∑ y, p y * (r y / β - log Z) = (∑ y, p y * r y) / β - log Z := by
    have : ∀ y, p y * (r y / β - log Z) = p y * r y / β - p y * log Z := fun y ↦ by ring
    rw [sum_congr rfl fun y _ ↦ this y, sum_sub_distrib, ← sum_div, ← sum_mul, hp1, one_mul]
  rw [h2]
  have : β * ((∑ y, p y * r y) / β) = ∑ y, p y * r y := by field_simp
  nlinarith

end Rows

section Gibbs

variable {X Y : Type} [Fintype X] [Fintype Y]

/-- Partition function `Z_r(x) = ∑_y π_ref(y|x) e^{r(x,y)/β}`. -/
noncomputable def partitionFn (π_ref r : X → Y → ℝ) (β : ℝ) (x : X) : ℝ :=
  ∑ y, π_ref x y * exp (r x y / β)

/-- Closed form of `J⋆(r; π_cal) = β E_ρ log Z_r − E_{ρ,π_cal} r` (`RLHF.tex:116–124`). -/
noncomputable def optClosed (ρ : X → ℝ) (π_ref π_cal : X → Y → ℝ) (β : ℝ) (r : X → Y → ℝ) : ℝ :=
  ∑ x, ρ x * (β * log (partitionFn π_ref r β x)) - ∑ x, ρ x * ∑ y, π_cal x y * r x y

/-- Negative log-likelihood `ℓ(r, D) = −∑_{(x,y₊,y₋) ∈ D} log σ(r(x,y₊) − r(x,y₋))`. -/
noncomputable def nll (r : X → Y → ℝ) (D : List (X × Y × Y)) : ℝ :=
  -(D.map fun z ↦ log (sigmoid (r z.1 z.2.1 - r z.1 z.2.2))).sum

variable {π_ref : X → Y → ℝ}

omit [Fintype X] in
theorem univ_nonempty_of_pos (href : IsPositivePolicy π_ref) (x : X) :
    (univ : Finset Y).Nonempty := by
  by_contra h
  have := href.2 x
  rw [not_nonempty_iff_eq_empty.1 h, sum_empty] at this
  exact zero_ne_one this

omit [Fintype X] in
theorem partitionFn_pos (href : IsPositivePolicy π_ref) (r : X → Y → ℝ) (β : ℝ) (x : X) :
    0 < partitionFn π_ref r β x :=
  sum_pos (fun y _ ↦ mul_pos (href.1 x y) (exp_pos _)) (univ_nonempty_of_pos href x)

omit [Fintype X] in
theorem gibbsPolicy_eq (r : X → Y → ℝ) (β : ℝ) (x : X) (y : Y) :
    gibbsPolicy π_ref r β x y = π_ref x y * exp (r x y / β) / partitionFn π_ref r β x := rfl

theorem gibbsPolicy_pos (href : IsPositivePolicy π_ref) (r : X → Y → ℝ) (β : ℝ) (x : X) (y : Y) :
    0 < gibbsPolicy π_ref r β x y :=
  div_pos (mul_pos (href.1 x y) (exp_pos _)) (partitionFn_pos href r β x)

theorem gibbsPolicy_sum (href : IsPositivePolicy π_ref) (r : X → Y → ℝ) (β : ℝ) (x : X) :
    ∑ y, gibbsPolicy π_ref r β x y = 1 := by
  simp only [gibbsPolicy_eq]
  rw [← sum_div]
  exact div_self (partitionFn_pos href r β x).ne'

theorem gibbsPolicy_isPositive (href : IsPositivePolicy π_ref) (r : X → Y → ℝ) (β : ℝ) :
    IsPositivePolicy (gibbsPolicy π_ref r β) :=
  ⟨gibbsPolicy_pos href r β, gibbsPolicy_sum href r β⟩

theorem log_gibbs_div (href : IsPositivePolicy π_ref) (r : X → Y → ℝ) (β : ℝ) (x : X) (y : Y) :
    log (gibbsPolicy π_ref r β x y / π_ref x y) = r x y / β - log (partitionFn π_ref r β x) := by
  have h : gibbsPolicy π_ref r β x y / π_ref x y = exp (r x y / β) / partitionFn π_ref r β x := by
    rw [gibbsPolicy_eq]; field_simp [(href.1 x y).ne']
  rw [h, log_div (exp_pos _).ne' (partitionFn_pos href r β x).ne', log_exp]

/-- L1: every policy has calibrated value at most the closed form. -/
theorem calValue_le_optClosed (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (href : IsPositivePolicy π_ref)
    (π_cal : X → Y → ℝ) {β : ℝ} (hβ : 0 < β) (r pol : X → Y → ℝ) (hπ : IsCondPolicy pol) :
    calValue ρ π_ref π_cal β r pol ≤ optClosed ρ π_ref π_cal β r := by
  unfold calValue optClosed klDiv
  refine sub_le_sub_right (sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left ?_ (hρ x)) _
  exact row_value_le (π_ref x) (r x) (pol x) β hβ (href.1 x) (hπ.1 x) (hπ.2 x)

/-- L1: the Gibbs policy attains the closed form. -/
theorem calValue_gibbs (ρ : X → ℝ) (href : IsPositivePolicy π_ref) (π_cal : X → Y → ℝ) {β : ℝ}
    (hβ : 0 < β) (r : X → Y → ℝ) :
    calValue ρ π_ref π_cal β r (gibbsPolicy π_ref r β) = optClosed ρ π_ref π_cal β r := by
  unfold calValue optClosed klDiv
  congr 1
  refine sum_congr rfl fun x _ ↦ ?_
  congr 1
  simp_rw [log_gibbs_div href r β x]
  have h1 := gibbsPolicy_sum href r β x
  have : ∀ y, gibbsPolicy π_ref r β x y * (r x y / β - log (partitionFn π_ref r β x)) =
      gibbsPolicy π_ref r β x y * r x y / β -
        gibbsPolicy π_ref r β x y * log (partitionFn π_ref r β x) := fun y ↦ by ring
  rw [sum_congr rfl fun y _ ↦ this y, sum_sub_distrib, ← sum_div, ← sum_mul, h1, one_mul]
  field_simp
  ring

theorem gibbsPolicy_isCondPolicy (href : IsPositivePolicy π_ref) (r : X → Y → ℝ) (β : ℝ) :
    IsCondPolicy (gibbsPolicy π_ref r β) :=
  ⟨fun x y ↦ (gibbsPolicy_pos href r β x y).le, gibbsPolicy_sum href r β⟩

/-- L1: `J⋆(r; π_cal)` (supremum over all policies) equals the closed form. -/
theorem optCalValue_eq (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (href : IsPositivePolicy π_ref)
    (π_cal : X → Y → ℝ) {β : ℝ} (hβ : 0 < β) (r : X → Y → ℝ) :
    optCalValue ρ π_ref π_cal β r = optClosed ρ π_ref π_cal β r := by
  refine IsGreatest.csSup_eq ⟨⟨gibbsPolicy π_ref r β, gibbsPolicy_isCondPolicy href r β,
    calValue_gibbs ρ href π_cal hβ r⟩, ?_⟩
  rintro v ⟨pol, hπ, rfl⟩
  exact calValue_le_optClosed ρ hρ href π_cal hβ r pol hπ

/-- L3: the printed VPO objective at a Gibbs policy is `ℓ(r, D) − α J⋆(r; π_cal)`. -/
theorem vpoObjective_gibbs (ρ : X → ℝ) (href : IsPositivePolicy π_ref) (π_cal : X → Y → ℝ)
    (hcal : ∀ x, ∑ y, π_cal x y = 1) (α : ℝ) {β : ℝ} (hβ : 0 < β) (r : X → Y → ℝ)
    (D : List (X × Y × Y)) :
    vpoObjective ρ π_ref π_cal α β D (gibbsPolicy π_ref r β) =
      nll r D - α * optClosed ρ π_ref π_cal β r := by
  unfold vpoObjective nll optClosed
  have hlik : ∀ z : X × Y × Y,
      β * log (gibbsPolicy π_ref r β z.1 z.2.1 / π_ref z.1 z.2.1) -
        β * log (gibbsPolicy π_ref r β z.1 z.2.2 / π_ref z.1 z.2.2) =
        r z.1 z.2.1 - r z.1 z.2.2 := by
    intro z
    rw [log_gibbs_div href, log_gibbs_div href]
    field_simp
    ring
  simp_rw [hlik]
  have hcal' : ∀ x, ∑ y, π_cal x y * (log (gibbsPolicy π_ref r β x y) - log (π_ref x y)) =
      (∑ y, π_cal x y * r x y) / β - log (partitionFn π_ref r β x) := by
    intro x
    have : ∀ y, π_cal x y * (log (gibbsPolicy π_ref r β x y) - log (π_ref x y)) =
        π_cal x y * r x y / β - π_cal x y * log (partitionFn π_ref r β x) := by
      intro y
      rw [← log_div (gibbsPolicy_pos href r β x y).ne' (href.1 x y).ne', log_gibbs_div href]
      ring
    rw [sum_congr rfl fun y _ ↦ this y, sum_sub_distrib, ← sum_div, ← sum_mul, hcal x, one_mul]
  simp_rw [hcal']
  have : ∀ x, ρ x * ((∑ y, π_cal x y * r x y) / β - log (partitionFn π_ref r β x)) =
      (ρ x * ∑ y, π_cal x y * r x y) / β - ρ x * log (partitionFn π_ref r β x) := fun x ↦ by
    ring
  rw [sum_congr rfl fun x _ ↦ this x, sum_sub_distrib, ← sum_div]
  have h2 : ∀ x, ρ x * (β * log (partitionFn π_ref r β x)) =
      β * (ρ x * log (partitionFn π_ref r β x)) := fun x ↦ by ring
  rw [sum_congr rfl fun x _ ↦ h2 x, ← mul_sum]
  field_simp
  ring

/-- L2: if `|r| ≤ c` on row `x`, then `π_ref ≤ e^{2c/β} π_r` and `π_r ≤ e^{2c/β} π_ref`. -/
theorem gibbs_ratio_bounds (href : IsPositivePolicy π_ref) (r : X → Y → ℝ) {β c : ℝ} (hβ : 0 < β)
    (x : X) (hr : ∀ y, |r x y| ≤ c) (y : Y) :
    π_ref x y ≤ exp (2 * c / β) * gibbsPolicy π_ref r β x y ∧
      gibbsPolicy π_ref r β x y ≤ exp (2 * c / β) * π_ref x y := by
  have hZ := partitionFn_pos href r β x
  have hbound : ∀ y, exp (-c / β) ≤ exp (r x y / β) ∧ exp (r x y / β) ≤ exp (c / β) := by
    intro y
    have := abs_le.1 (hr y)
    refine ⟨exp_le_exp.2 ?_, exp_le_exp.2 ?_⟩
    · exact div_le_div_of_nonneg_right this.1 hβ.le
    · exact div_le_div_of_nonneg_right this.2 hβ.le
  have hZu : partitionFn π_ref r β x ≤ exp (c / β) := by
    calc partitionFn π_ref r β x ≤ ∑ y, π_ref x y * exp (c / β) :=
          sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_left (hbound y).2 (href.1 x y).le
      _ = exp (c / β) := by rw [← sum_mul, href.2 x, one_mul]
  have hZl : exp (-c / β) ≤ partitionFn π_ref r β x := by
    calc exp (-c / β) = ∑ y, π_ref x y * exp (-c / β) := by rw [← sum_mul, href.2 x, one_mul]
      _ ≤ _ := sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_left (hbound y).1 (href.1 x y).le
  have he1 : exp (2 * c / β) = exp (c / β) * exp (c / β) := by rw [← exp_add]; ring_nf
  have he2 : exp (c / β) * exp (-c / β) = 1 := by rw [← exp_add]; ring_nf; simp
  have hp := href.1 x y
  rw [gibbsPolicy_eq]
  constructor
  · rw [mul_div_assoc', le_div_iff₀ hZ]
    calc π_ref x y * partitionFn π_ref r β x ≤ π_ref x y * exp (c / β) :=
          mul_le_mul_of_nonneg_left hZu hp.le
      _ = exp (2 * c / β) * (π_ref x y * exp (-c / β)) := by
          rw [he1]; linear_combination (-(π_ref x y * exp (c / β))) * he2
      _ ≤ exp (2 * c / β) * (π_ref x y * exp (r x y / β)) := by
          gcongr; exact (abs_le.1 (hr y)).1
  · rw [div_le_iff₀ hZ]
    calc π_ref x y * exp (r x y / β) ≤ π_ref x y * exp (c / β) :=
          mul_le_mul_of_nonneg_left (hbound y).2 hp.le
      _ = exp (2 * c / β) * π_ref x y * exp (-c / β) := by
          rw [he1]; linear_combination (-(π_ref x y * exp (c / β))) * he2
      _ ≤ exp (2 * c / β) * π_ref x y * partitionFn π_ref r β x := by gcongr

end Gibbs

end StatisticalRL.Ch7Rest.Rlhf
