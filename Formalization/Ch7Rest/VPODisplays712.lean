import Formalization.Ch7Rest.VPOGibbs712

/-!
# RLHF displays: Gibbs closed form, reward–policy identity, `J⋆`, shift invariance

Source: `chapters/RLHF.tex`.

* `eq:RLHF-policy-closed-form` (:47–59): the Gibbs policy `π_r` maximizes the KL-regularized
  value `J(r, pol)` of `eq:KL_reward` (:41–45) over conditional policies, and the maximizers are
  exactly the conditional policies that agree with `π_r` on the support of `ρ`
  (`isMaximizer_klValue_iff`).
* `eq:reward-policy-eq` (:63–66): `r = β (log π_r − log π_ref + log Z(r, ·))`.
* `eq:Jstar` (:115–124): the four printed expressions of `J⋆(r; π_cal)`.
* :90–98: prompt-shift invariance of the Bradley–Terry likelihood and of the calibrated value
  `J(r, pol; π_cal)` (`eq:calibrated_value`), and the shift `J⋆(r + c) = J⋆(r) + E_ρ c` of the
  uncalibrated optimal value.

The ambient conventions are those of `VPODefs712`: finite `X`, `Y`, `KL(p‖q) = ∑ p log(p/q)` with
Lean's `log 0 = 0` (so `0 log 0 = 0`), and a full-support reference policy.
-/

namespace StatisticalRL.Ch7Rest.Rlhf

open Finset Real

set_option linter.unusedSectionVars false

section Rows

variable {Y : Type} [Fintype Y]

/-- Equality case of the pointwise inequality `p − q ≤ p log(p/q)`. -/
theorem eq_of_mul_log_div_eq_sub {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q)
    (h : p * log (p / q) = p - q) : p = q := by
  rcases hp.eq_or_lt with h0 | hpos
  · rw [← h0] at h; simp at h; linarith
  · set t := q / p with ht
    have htpos : 0 < t := div_pos hq hpos
    have hlog : log (p / q) = -log t := by
      rw [ht, ← log_inv, inv_div]
    have hq' : q = p * t := by rw [ht]; field_simp
    rw [hlog, hq'] at h
    have hlt : log t = t - 1 := by
      have : p * (log t - (t - 1)) = 0 := by linarith
      rcases mul_eq_zero.mp this with h1 | h1
      · exact absurd h1 hpos.ne'
      · linarith
    by_contra hne
    have ht1 : t ≠ 1 := by
      intro h1; apply hne; rw [hq', h1, mul_one]
    have := log_lt_sub_one_of_pos htpos ht1
    linarith

/-- Gibbs' inequality, equality case: `∑ p log(p/pol) = 0` forces `p = pol`. -/
theorem eq_of_kl_eq_zero (p pol : Y → ℝ) (hp : ∀ y, 0 ≤ p y) (hπ : ∀ y, 0 < pol y)
    (hp1 : ∑ y, p y = 1) (hπ1 : ∑ y, pol y = 1) (h0 : ∑ y, p y * log (p y / pol y) = 0) :
    p = pol := by
  have hnn : ∀ y ∈ (univ : Finset Y), 0 ≤ p y * log (p y / pol y) - (p y - pol y) :=
    fun y _ ↦ sub_nonneg.mpr (sub_le_mul_log_div (hp y) (hπ y))
  have hsum : ∑ y, (p y * log (p y / pol y) - (p y - pol y)) = 0 := by
    rw [sum_sub_distrib, sum_sub_distrib, h0, hp1, hπ1]; ring
  have hz := (sum_eq_zero_iff_of_nonneg hnn).mp hsum
  funext y
  exact eq_of_mul_log_div_eq_sub (hp y) (hπ y) (by linarith [hz y (mem_univ y)])

/-- Row decomposition (L1): with `Z = ∑ q e^{r/β}` and `pol = q e^{r/β}/Z`, for every `p` in the
simplex, `∑ p r − β ∑ p log(p/q) = β log Z − β ∑ p log(p/pol)`. -/
theorem row_value_eq (q r p : Y → ℝ) (β : ℝ) (hβ : 0 < β) (hq : ∀ y, 0 < q y)
    (hp : ∀ y, 0 ≤ p y) (hp1 : ∑ y, p y = 1) :
    ∑ y, p y * r y - β * ∑ y, p y * log (p y / q y) =
      β * log (∑ y, q y * exp (r y / β)) - β * ∑ y, p y * log (p y /
        (q y * exp (r y / β) / ∑ y', q y' * exp (r y' / β))) := by
  set Z := ∑ y, q y * exp (r y / β) with hZ
  have hne : (univ : Finset Y).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.1 h, sum_empty] at hp1
    exact zero_ne_one hp1
  have hZ0 : 0 < Z := sum_pos (fun y _ ↦ mul_pos (hq y) (exp_pos _)) hne
  have hsplit : ∀ y, p y * log (p y / q y) =
      p y * log (p y / (q y * exp (r y / β) / Z)) + p y * (r y / β - log Z) := by
    intro y
    rcases (hp y).eq_or_lt with h0 | hpos
    · rw [← h0]; simp
    · have hπ0 : 0 < q y * exp (r y / β) / Z := div_pos (mul_pos (hq y) (exp_pos _)) hZ0
      have : log (p y / q y) = log (p y / (q y * exp (r y / β) / Z)) + (r y / β - log Z) := by
        rw [log_div hpos.ne' (hq y).ne', log_div hpos.ne' hπ0.ne',
          log_div (mul_pos (hq y) (exp_pos _)).ne' hZ0.ne', log_mul (hq y).ne' (exp_pos _).ne',
          log_exp]
        ring
      rw [this]; ring
  rw [sum_congr rfl fun y _ ↦ hsplit y, sum_add_distrib]
  have h2 : ∑ y, p y * (r y / β - log Z) = (∑ y, p y * r y) / β - log Z := by
    have : ∀ y, p y * (r y / β - log Z) = p y * r y / β - p y * log Z := fun y ↦ by ring
    rw [sum_congr rfl fun y _ ↦ this y, sum_sub_distrib, ← sum_div, ← sum_mul, hp1, one_mul]
  rw [h2]
  have : β * ((∑ y, p y * r y) / β) = ∑ y, p y * r y := by field_simp
  linarith

end Rows

section Displays

variable {X Y : Type} [Fintype X] [Fintype Y] {π_ref : X → Y → ℝ}

/-- `eq:reward-policy-eq` (`RLHF.tex:63–66`):
`r(x,y) = β (log π_r(y|x) − log π_ref(y|x) + log Z(r,x))`. -/
theorem reward_eq_log_gibbs (href : IsPositivePolicy π_ref) {β : ℝ} (hβ : 0 < β)
    (r : X → Y → ℝ) (x : X) (y : Y) :
    r x y = β * (log (gibbsPolicy π_ref r β x y) - log (π_ref x y) +
      log (∑ y', π_ref x y' * exp (r x y' / β))) := by
  have h := log_gibbs_div href r β x y
  rw [log_div (gibbsPolicy_pos href r β x y).ne' (href.1 x y).ne'] at h
  have h' : log (∑ y', π_ref x y' * exp (r x y' / β)) = log (partitionFn π_ref r β x) := rfl
  rw [h', h]
  field_simp
  ring

/-- `log π_r − log π_ref = r/β − log Z` (rearranged `eq:RLHF-policy-closed-form`). -/
theorem log_gibbs_sub_log (href : IsPositivePolicy π_ref) (r : X → Y → ℝ) (β : ℝ) (x : X)
    (y : Y) :
    log (gibbsPolicy π_ref r β x y) - log (π_ref x y) =
      r x y / β - log (partitionFn π_ref r β x) := by
  rw [← log_div (gibbsPolicy_pos href r β x y).ne' (href.1 x y).ne']
  exact log_gibbs_div href r β x y

/-- `eq:Jstar` (`RLHF.tex:115–124`): all four printed expressions of `J⋆(r; π_cal)`. -/
theorem optCalValue_printed_lines (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (href : IsPositivePolicy π_ref)
    (π_cal : X → Y → ℝ) (hcal : IsCondPolicy π_cal) {β : ℝ} (hβ : 0 < β) (r : X → Y → ℝ) :
    (optCalValue ρ π_ref π_cal β r =
        ∑ x, ρ x * ∑ y, gibbsPolicy π_ref r β x y *
          (r x y - β * (log (gibbsPolicy π_ref r β x y) - log (π_ref x y))) -
        ∑ x, ρ x * ∑ y, π_cal x y * r x y) ∧
    (optCalValue ρ π_ref π_cal β r =
        β * ∑ x, ρ x * log (∑ y', π_ref x y' * exp (r x y' / β)) -
        ∑ x, ρ x * ∑ y, π_cal x y * r x y) ∧
    (optCalValue ρ π_ref π_cal β r =
        ∑ x, ρ x * ∑ y, π_cal x y *
          (β * log (∑ y', π_ref x y' * exp (r x y' / β)) - r x y)) ∧
    (optCalValue ρ π_ref π_cal β r =
        -β * ∑ x, ρ x * ∑ y, π_cal x y *
          (log (gibbsPolicy π_ref r β x y) - log (π_ref x y))) := by
  have hopt := optCalValue_eq ρ hρ href π_cal hβ r
  have hZ : ∀ x, log (∑ y', π_ref x y' * exp (r x y' / β)) = log (partitionFn π_ref r β x) :=
    fun x ↦ rfl
  simp_rw [hZ]
  have L2 : optCalValue ρ π_ref π_cal β r =
      β * ∑ x, ρ x * log (partitionFn π_ref r β x) - ∑ x, ρ x * ∑ y, π_cal x y * r x y := by
    rw [hopt, optClosed, mul_sum]
    congr 1
    exact sum_congr rfl fun x _ ↦ by ring
  refine ⟨?_, L2, ?_, ?_⟩
  · rw [hopt, ← calValue_gibbs ρ href π_cal hβ r, calValue]
    simp only [klDiv]
    congr 1
    refine sum_congr rfl fun x _ ↦ ?_
    congr 1
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun y _ ↦ ?_
    rw [log_div (gibbsPolicy_pos href r β x y).ne' (href.1 x y).ne']
    ring
  · rw [L2, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun x _ ↦ ?_
    have h1 : ∑ y, π_cal x y * (β * log (partitionFn π_ref r β x) - r x y) =
        β * log (partitionFn π_ref r β x) * ∑ y, π_cal x y - ∑ y, π_cal x y * r x y := by
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun y _ ↦ by ring
    rw [h1, hcal.2 x]
    ring
  · rw [L2]
    simp_rw [log_gibbs_sub_log href r β]
    have h1 : ∀ x, ∑ y, π_cal x y * (r x y / β - log (partitionFn π_ref r β x)) =
        (∑ y, π_cal x y * r x y) / β - log (partitionFn π_ref r β x) := by
      intro x
      have e : ∑ y, π_cal x y * (r x y / β - log (partitionFn π_ref r β x)) =
          (∑ y, π_cal x y * r x y) / β - log (partitionFn π_ref r β x) * ∑ y, π_cal x y := by
        rw [sum_div, mul_sum, ← sum_sub_distrib]
        exact sum_congr rfl fun y _ ↦ by ring
      rw [e, hcal.2 x, mul_one]
    simp_rw [h1]
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun x _ ↦ ?_
    field_simp
    ring

/-- The KL-regularized value `J(r, pol)` of `eq:KL_reward` is the calibrated value with the zero
calibration term. -/
theorem calValue_zero_cal (ρ : X → ℝ) (β : ℝ) (r pol : X → Y → ℝ) :
    calValue ρ π_ref (fun _ _ ↦ 0) β r pol =
      ∑ x, ρ x * (∑ y, pol x y * r x y - β * klDiv (pol x) (π_ref x)) := by
  simp [calValue]

/-- Row value at the Gibbs row: `∑ π_r r − β KL(π_r‖π_ref) = β log Z`. -/
theorem row_value_gibbs (href : IsPositivePolicy π_ref) {β : ℝ} (hβ : 0 < β) (r : X → Y → ℝ)
    (x : X) :
    ∑ y, gibbsPolicy π_ref r β x y * r x y - β * klDiv (gibbsPolicy π_ref r β x) (π_ref x) =
      β * log (partitionFn π_ref r β x) := by
  have h := row_value_eq (π_ref x) (r x) (gibbsPolicy π_ref r β x) β hβ (href.1 x)
    (fun y ↦ (gibbsPolicy_pos href r β x y).le) (gibbsPolicy_sum href r β x)
  have hself : ∀ y, gibbsPolicy π_ref r β x y /
      (π_ref x y * exp (r x y / β) / ∑ y', π_ref x y' * exp (r x y' / β)) = 1 := fun y ↦
    div_self (gibbsPolicy_pos href r β x y).ne'
  simp only [hself, log_one, mul_zero, sum_const_zero, sub_zero] at h
  unfold klDiv
  exact h

/-- `eq:RLHF-policy-closed-form` (`RLHF.tex:47–59`), existence part: the Gibbs policy maximizes
`J(r, ·)` over conditional policies. -/
theorem klValue_le_gibbs (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (href : IsPositivePolicy π_ref)
    {β : ℝ} (hβ : 0 < β) (r pol : X → Y → ℝ) (hπ : IsCondPolicy pol) :
    ∑ x, ρ x * (∑ y, pol x y * r x y - β * klDiv (pol x) (π_ref x)) ≤
      ∑ x, ρ x * (∑ y, gibbsPolicy π_ref r β x y * r x y -
        β * klDiv (gibbsPolicy π_ref r β x) (π_ref x)) := by
  rw [← calValue_zero_cal, ← calValue_zero_cal, calValue_gibbs ρ href _ hβ r]
  exact calValue_le_optClosed ρ hρ href _ hβ r pol hπ

/-- `eq:RLHF-policy-closed-form`, characterization of the maximizers: a conditional policy
maximizes `J(r, ·)` over conditional policies iff it agrees with the Gibbs policy on the support
of `ρ`. -/
theorem isMaximizer_klValue_iff (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (href : IsPositivePolicy π_ref)
    {β : ℝ} (hβ : 0 < β) (r pol : X → Y → ℝ) (hπ : IsCondPolicy pol) :
    (∀ pol', IsCondPolicy pol' →
        ∑ x, ρ x * (∑ y, pol' x y * r x y - β * klDiv (pol' x) (π_ref x)) ≤
          ∑ x, ρ x * (∑ y, pol x y * r x y - β * klDiv (pol x) (π_ref x))) ↔
      ∀ x, 0 < ρ x → ∀ y, pol x y = gibbsPolicy π_ref r β x y := by
  set g := gibbsPolicy π_ref r β
  set row : (X → Y → ℝ) → X → ℝ := fun p x ↦ ∑ y, p x y * r x y - β * klDiv (p x) (π_ref x)
    with hrow
  have hg : ∀ x, row g x = β * log (partitionFn π_ref r β x) := row_value_gibbs href hβ r
  have hle : ∀ p, IsCondPolicy p → ∀ x, row p x ≤ row g x := by
    intro p hp x
    rw [hg]
    exact row_value_le (π_ref x) (r x) (p x) β hβ (href.1 x) (hp.1 x) (hp.2 x)
  constructor
  · intro hmax x hx y
    have hge := hmax g (gibbsPolicy_isCondPolicy href r β)
    have hnn : ∀ x ∈ (univ : Finset X), 0 ≤ ρ x * row g x - ρ x * row pol x :=
      fun x _ ↦ by rw [← mul_sub]; exact mul_nonneg (hρ x) (sub_nonneg.mpr (hle pol hπ x))
    have hsum : ∑ x, (ρ x * row g x - ρ x * row pol x) = 0 := by
      rw [sum_sub_distrib]
      exact le_antisymm (by linarith) (sub_nonneg.mpr (sum_le_sum fun x _ ↦
        mul_le_mul_of_nonneg_left (hle pol hπ x) (hρ x)))
    have hz := (sum_eq_zero_iff_of_nonneg hnn).mp hsum x (mem_univ x)
    rw [← mul_sub] at hz
    have hrowx : row pol x = row g x := by
      rcases mul_eq_zero.mp hz with h | h
      · exact absurd h hx.ne'
      · linarith
    have hdec := row_value_eq (π_ref x) (r x) (pol x) β hβ (href.1 x) (hπ.1 x) (hπ.2 x)
    have hkl : ∑ y, pol x y * log (pol x y /
        (π_ref x y * exp (r x y / β) / ∑ y', π_ref x y' * exp (r x y' / β))) = 0 := by
      have e1 : row pol x = β * log (partitionFn π_ref r β x) - β * ∑ y, pol x y * log (pol x y /
          (π_ref x y * exp (r x y / β) / ∑ y', π_ref x y' * exp (r x y' / β))) := hdec
      rw [hrowx, hg] at e1
      have : β * ∑ y, pol x y * log (pol x y /
          (π_ref x y * exp (r x y / β) / ∑ y', π_ref x y' * exp (r x y' / β))) = 0 := by
        linarith
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hβ.ne'
      · exact h
    have := eq_of_kl_eq_zero (pol x) (g x) (hπ.1 x) (gibbsPolicy_pos href r β x)
      (hπ.2 x) (gibbsPolicy_sum href r β x) hkl
    exact congrFun this y
  · intro hagree pol' hπ'
    have heq : ∀ x, ρ x * row pol x = ρ x * row g x := by
      intro x
      rcases (hρ x).eq_or_lt with h0 | hpos
      · rw [← h0, zero_mul, zero_mul]
      · have : pol x = g x := funext (hagree x hpos)
        simp only [hrow, this]
    calc ∑ x, ρ x * row pol' x ≤ ∑ x, ρ x * row g x :=
          sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (hle pol' hπ' x) (hρ x)
      _ = ∑ x, ρ x * row pol x := sum_congr rfl fun x _ ↦ (heq x).symm

/-- Prompt shift of the partition function: `log Z(r + c, x) = c(x)/β + log Z(r, x)`. -/
theorem log_partitionFn_shift (href : IsPositivePolicy π_ref) (r : X → Y → ℝ) (c : X → ℝ)
    (β : ℝ) (x : X) :
    log (partitionFn π_ref (fun x y ↦ r x y + c x) β x) =
      c x / β + log (partitionFn π_ref r β x) := by
  have h : partitionFn π_ref (fun x y ↦ r x y + c x) β x =
      exp (c x / β) * partitionFn π_ref r β x := by
    unfold partitionFn
    rw [mul_sum]
    refine sum_congr rfl fun y _ ↦ ?_
    rw [add_div, exp_add]
    ring
  rw [h, log_mul (exp_pos _).ne' (partitionFn_pos href r β x).ne', log_exp]

/-- `J⋆(r) = max_π J(r, pol)` (uncalibrated, `RLHF.tex:86–89`) equals `β E_ρ log Z(r, ·)`. -/
theorem sSup_klValue_eq (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (href : IsPositivePolicy π_ref)
    {β : ℝ} (hβ : 0 < β) (r : X → Y → ℝ) :
    sSup {v | ∃ pol, IsCondPolicy pol ∧
        ∑ x, ρ x * (∑ y, pol x y * r x y - β * klDiv (pol x) (π_ref x)) = v} =
      ∑ x, ρ x * (β * log (partitionFn π_ref r β x)) := by
  have hset : {v | ∃ pol, IsCondPolicy pol ∧
        ∑ x, ρ x * (∑ y, pol x y * r x y - β * klDiv (pol x) (π_ref x)) = v} =
      {v | ∃ pol, IsCondPolicy pol ∧ calValue ρ π_ref (fun _ _ ↦ 0) β r pol = v} := by
    ext v
    simp only [Set.mem_setOf_eq, calValue_zero_cal]
  rw [hset]
  change optCalValue ρ π_ref (fun _ _ ↦ 0) β r = _
  rw [optCalValue_eq ρ hρ href _ hβ r, optClosed]
  simp

/-- Prompt-shift invariance (`RLHF.tex:90–98`): pairwise reward differences, the Bradley–Terry
log-likelihood, the calibrated value and `J⋆(·; π_cal)` are invariant under `r ↦ r + c(x)`, and the
uncalibrated `J⋆` shifts by `E_ρ c`. -/
theorem prompt_shift_invariance (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (href : IsPositivePolicy π_ref)
    (π_cal : X → Y → ℝ) (hcal : IsCondPolicy π_cal) {β : ℝ} (hβ : 0 < β) (r : X → Y → ℝ)
    (c : X → ℝ) :
    (∀ (x : X) (y₁ y₂ : Y), (r x y₁ + c x) - (r x y₂ + c x) = r x y₁ - r x y₂) ∧
    (∀ D : List (X × Y × Y),
      -(D.map fun z ↦ log (sigmoid ((r z.1 z.2.1 + c z.1) - (r z.1 z.2.2 + c z.1)))).sum =
        -(D.map fun z ↦ log (sigmoid (r z.1 z.2.1 - r z.1 z.2.2))).sum) ∧
    (∀ pol, IsCondPolicy pol →
      calValue ρ π_ref π_cal β (fun x y ↦ r x y + c x) pol = calValue ρ π_ref π_cal β r pol) ∧
    optCalValue ρ π_ref π_cal β (fun x y ↦ r x y + c x) = optCalValue ρ π_ref π_cal β r ∧
    sSup {v | ∃ pol, IsCondPolicy pol ∧
        ∑ x, ρ x * (∑ y, pol x y * (r x y + c x) - β * klDiv (pol x) (π_ref x)) = v} =
      sSup {v | ∃ pol, IsCondPolicy pol ∧
        ∑ x, ρ x * (∑ y, pol x y * r x y - β * klDiv (pol x) (π_ref x)) = v} + ∑ x, ρ x * c x := by
  have hcv : ∀ pol, IsCondPolicy pol →
      calValue ρ π_ref π_cal β (fun x y ↦ r x y + c x) pol = calValue ρ π_ref π_cal β r pol := by
    intro pol hπ
    unfold calValue
    have h1 : ∀ (p : X → Y → ℝ), (∀ x, ∑ y, p x y = 1) → ∀ x,
        ∑ y, p x y * (r x y + c x) = ∑ y, p x y * r x y + c x := by
      intro p hp x
      simp only [mul_add, sum_add_distrib]
      rw [← sum_mul, hp x, one_mul]
    simp only [h1 pol hπ.2, h1 π_cal hcal.2]
    have e : ∀ x, ρ x * (∑ y, pol x y * r x y + c x - β * klDiv (pol x) (π_ref x)) =
        ρ x * (∑ y, pol x y * r x y - β * klDiv (pol x) (π_ref x)) + ρ x * c x := fun x ↦ by ring
    have e' : ∀ x, ρ x * (∑ y, π_cal x y * r x y + c x) =
        ρ x * ∑ y, π_cal x y * r x y + ρ x * c x := fun x ↦ by ring
    simp only [e, e', sum_add_distrib]
    ring
  refine ⟨fun x y₁ y₂ ↦ by ring, fun D ↦ ?_, hcv, ?_, ?_⟩
  · simp only [add_sub_add_right_eq_sub]
  · unfold optCalValue
    congr 1
    ext v
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨pol, hπ, rfl⟩; exact ⟨pol, hπ, (hcv pol hπ).symm⟩
    · rintro ⟨pol, hπ, rfl⟩; exact ⟨pol, hπ, hcv pol hπ⟩
  · have e := sSup_klValue_eq ρ hρ href hβ (fun x y ↦ r x y + c x)
    simp only at e
    rw [e, sSup_klValue_eq ρ hρ href hβ r]
    simp_rw [log_partitionFn_shift href r c β]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun x _ ↦ ?_
    field_simp
    ring

end Displays

end StatisticalRL.Ch7Rest.Rlhf
