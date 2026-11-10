import Formalization.RLHF.VPO.Gibbs

/-!
# Corrected Theorem 7.12: calibration gap, local-curvature bound, existence of minimizers

Proof steps L4 and L5, and step 1 of the local-curvature argument
(per-round regret of a Gibbs policy is at most `e^{4R/β}/(4β)` times the pair dispersion).
-/

namespace StatisticalRL.Ch7Rest.Rlhf

open Finset Real

set_option linter.unusedSectionVars false

section Rows

variable {Y : Type} [Fintype Y]

/-- `Var_p g = ½ ∑∑ p(y) p(y') (g(y) − g(y'))²`. -/
theorem var_eq_half_pair (p g : Y → ℝ) (hp1 : ∑ y, p y = 1) :
    ∑ y, p y * (g y - ∑ y', p y' * g y') ^ 2 =
      (1 / 2) * ∑ y, ∑ y', p y * p y' * (g y - g y') ^ 2 := by
  set m := ∑ y', p y' * g y'
  have hz : ∑ y, p y * (g y - m) = 0 := by
    have : ∀ y, p y * (g y - m) = p y * g y - p y * m := fun y ↦ by ring
    rw [sum_congr rfl fun y _ ↦ this y, sum_sub_distrib, ← sum_mul, hp1, one_mul, sub_self]
  have hterm : ∀ y y', p y * p y' * (g y - g y') ^ 2 =
      p y * (g y - m) ^ 2 * p y' + p y' * (g y' - m) ^ 2 * p y -
        2 * (p y * (g y - m)) * (p y' * (g y' - m)) := fun y y' ↦ by ring
  have hrow : ∀ y, ∑ y', p y * p y' * (g y - g y') ^ 2 =
      p y * (g y - m) ^ 2 + (∑ y', p y' * (g y' - m) ^ 2) * p y -
        2 * (p y * (g y - m)) * 0 := by
    intro y
    rw [sum_congr rfl fun y' _ ↦ hterm y y', sum_sub_distrib, sum_add_distrib, ← mul_sum,
      hp1, mul_one, ← sum_mul, ← mul_sum, hz]
  rw [sum_congr rfl fun y _ ↦ hrow y]
  simp only [mul_zero, sub_zero]
  rw [sum_add_distrib, ← mul_sum, hp1, mul_one]
  ring

/-- Row calibration gap (L5): if `c ≤ K p` pointwise, then
`(E_p g − E_c g)² ≤ K Var_p g`. -/
theorem row_cal_gap (p c g : Y → ℝ) (hc0 : ∀ y, 0 ≤ c y) (hc1 : ∑ y, c y = 1) (K : ℝ)
    (hK : ∀ y, c y ≤ K * p y) :
    (∑ y, p y * g y - ∑ y, c y * g y) ^ 2 ≤
      K * ∑ y, p y * (g y - ∑ y', p y' * g y') ^ 2 := by
  set m := ∑ y', p y' * g y'
  have heq : ∑ y, p y * g y - ∑ y, c y * g y = -∑ y, c y * (g y - m) := by
    have : ∀ y, c y * (g y - m) = c y * g y - c y * m := fun y ↦ by ring
    rw [sum_congr rfl fun y _ ↦ this y, sum_sub_distrib, ← sum_mul, hc1, one_mul]
    ring
  rw [heq, neg_sq]
  calc (∑ y, c y * (g y - m)) ^ 2 ≤ ∑ y, c y * (g y - m) ^ 2 :=
        sq_wsum_le univ c (fun y ↦ g y - m) (fun y _ ↦ hc0 y) hc1
    _ ≤ ∑ y, K * p y * (g y - m) ^ 2 :=
        sum_le_sum fun y _ ↦ mul_le_mul_of_nonneg_right (hK y) (sq_nonneg _)
    _ = _ := by rw [mul_sum]; refine sum_congr rfl fun y _ ↦ by ring

/-- Row local-curvature bound. With `π = π_r` the Gibbs row of `(q, r)`, `g = r − s` and
`|g| ≤ G`: `β log Z_s − (E_π s − β KL(π‖q)) ≤ e^{2G/β}/(2β) Var_π g`. -/
theorem row_local_bound (q r s : Y → ℝ) {β G : ℝ} (hβ : 0 < β) (hq : ∀ y, 0 < q y)
    (hq1 : ∑ y, q y = 1) (hg : ∀ y, |r y - s y| ≤ G) :
    let Zr := ∑ y, q y * exp (r y / β)
    let pol := fun y ↦ q y * exp (r y / β) / Zr
    β * log (∑ y, q y * exp (s y / β)) -
        (∑ y, pol y * s y - β * ∑ y, pol y * log (pol y / q y)) ≤
      exp (2 * G / β) / (2 * β) *
        ∑ y, pol y * ((r y - s y) - ∑ y', pol y' * (r y' - s y')) ^ 2 := by
  intro Zr pol
  have hne : (univ : Finset Y).Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty.1 h, sum_empty] at hq1
    exact zero_ne_one hq1
  have hZr : 0 < Zr := sum_pos (fun y _ ↦ mul_pos (hq y) (exp_pos _)) hne
  have hpol0 : ∀ y, 0 < pol y := fun y ↦ div_pos (mul_pos (hq y) (exp_pos _)) hZr
  have hpol1 : ∑ y, pol y = 1 := by
    show ∑ y, q y * exp (r y / β) / Zr = 1
    rw [← sum_div, div_self hZr.ne']
  set g : Y → ℝ := fun y ↦ r y - s y with hgdef
  set m := ∑ y', pol y' * g y' with hm
  set h : Y → ℝ := fun y ↦ (g y - m) / β with hhdef
  set S := ∑ y, pol y * exp (-h y) with hSdef
  have hG0 : 0 ≤ G := le_trans (abs_nonneg _) (hg (hne.choose))
  -- |m| ≤ G, |g − m| ≤ 2G
  have hmG : |m| ≤ G := by
    calc |m| ≤ ∑ y', |pol y' * g y'| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ y', pol y' * G := sum_le_sum fun y _ ↦ by
          rw [abs_mul, abs_of_pos (hpol0 y)]
          exact mul_le_mul_of_nonneg_left (hg y) (hpol0 y).le
      _ = G := by rw [← sum_mul, hpol1, one_mul]
  have hh : ∀ y, |h y| ≤ 2 * G / β := by
    intro y
    simp only [hhdef, abs_div, abs_of_pos hβ]
    refine div_le_div_of_nonneg_right ?_ hβ.le
    calc |g y - m| ≤ |g y| + |m| := abs_sub _ _
      _ ≤ G + G := add_le_add (hg y) hmG
      _ = 2 * G := by ring
  -- partition identity
  have hZs : ∑ y, q y * exp (s y / β) = Zr * exp (-m / β) * S := by
    rw [hSdef, mul_sum]
    refine sum_congr rfl fun y _ ↦ ?_
    show q y * exp (s y / β) = Zr * exp (-m / β) *
      (q y * exp (r y / β) / Zr * exp (-((r y - s y - m) / β)))
    have he : exp (-m / β) * exp (r y / β) * exp (-((r y - s y - m) / β)) = exp (s y / β) := by
      rw [← exp_add, ← exp_add]; congr 1; ring
    rw [← he]
    field_simp [hZr.ne']
  have hS0 : 0 < S := sum_pos (fun y _ ↦ mul_pos (hpol0 y) (exp_pos _)) hne
  -- KL term
  have hkl : ∑ y, pol y * log (pol y / q y) = (∑ y, pol y * r y) / β - log Zr := by
    have : ∀ y, pol y * log (pol y / q y) = pol y * r y / β - pol y * log Zr := by
      intro y
      have : pol y / q y = exp (r y / β) / Zr := by
        show q y * exp (r y / β) / Zr / q y = _
        field_simp [(hq y).ne']
      rw [this, log_div (exp_pos _).ne' hZr.ne', log_exp]
      ring
    rw [sum_congr rfl fun y _ ↦ this y, sum_sub_distrib, ← sum_div, ← sum_mul, hpol1, one_mul]
  have hmsum : m = ∑ y, pol y * r y - ∑ y, pol y * s y := by
    rw [hm, ← sum_sub_distrib]; refine sum_congr rfl fun y _ ↦ ?_; simp only [hgdef]; ring
  have hLHS : β * log (∑ y, q y * exp (s y / β)) -
      (∑ y, pol y * s y - β * ∑ y, pol y * log (pol y / q y)) = β * log S := by
    rw [hZs, hkl, log_mul (by positivity) hS0.ne', log_mul hZr.ne' (exp_pos _).ne', log_exp]
    field_simp
    rw [hmsum]
    ring
  rw [hLHS]
  -- `log S ≤ S − 1 ≤ ∑ π h² e^{2G/β}/2`
  have hsumh : ∑ y, pol y * h y = 0 := by
    simp only [hhdef]
    have : ∀ y, pol y * ((g y - m) / β) = (pol y * g y - pol y * m) / β := fun y ↦ by ring
    rw [sum_congr rfl fun y _ ↦ this y, ← sum_div, sum_sub_distrib, ← sum_mul, hpol1, one_mul,
      ← hm, sub_self, zero_div]
  have hS1 : S - 1 ≤ exp (2 * G / β) / 2 * ∑ y, pol y * h y ^ 2 := by
    have hpt : ∀ y, pol y * exp (-h y) ≤
        pol y * 1 - pol y * h y + exp (2 * G / β) / 2 * (pol y * h y ^ 2) := by
      intro y
      have h1 := exp_le_quadratic (-h y)
      have h2 : exp |(-h y)| ≤ exp (2 * G / β) := by rw [abs_neg]; exact exp_le_exp.2 (hh y)
      have h3 : exp (-h y) ≤ 1 - h y + h y ^ 2 / 2 * exp (2 * G / β) := by
        have : (-h y) ^ 2 = h y ^ 2 := by ring
        rw [this] at h1
        nlinarith [sq_nonneg (h y)]
      have := mul_le_mul_of_nonneg_left h3 (hpol0 y).le
      linarith
    have := sum_le_sum fun y (_ : y ∈ univ) ↦ hpt y
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, hsumh] at this
    simp only [mul_one] at this
    rw [hpol1] at this
    linarith
  have hlog := log_le_sub_one_of_pos hS0
  have hh2 : ∑ y, pol y * h y ^ 2 = (∑ y, pol y * (g y - m) ^ 2) / β ^ 2 := by
    rw [sum_div]; refine sum_congr rfl fun y _ ↦ ?_; simp only [hhdef]; field_simp
  rw [hh2] at hS1
  have : β * log S ≤ β * (exp (2 * G / β) / 2 * ((∑ y, pol y * (g y - m) ^ 2) / β ^ 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) hβ.le
  calc β * log S ≤ _ := this
    _ = _ := by field_simp; rfl

end Rows

section Global

variable {X Y : Type} [Fintype X] [Fintype Y]

/-- Pair dispersion `E_{x∼ρ} E_{y,y'∼π(·|x)} (g(x,y) − g(x,y'))²`. -/
noncomputable def pairDisp (ρ : X → ℝ) (pol g : X → Y → ℝ) : ℝ :=
  ∑ x, ρ x * ∑ y, ∑ y', pol x y * pol x y' * (g x y - g x y') ^ 2

theorem pairDisp_nonneg (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (pol g : X → Y → ℝ)
    (hpol : ∀ x y, 0 ≤ pol x y) : 0 ≤ pairDisp ρ pol g :=
  sum_nonneg fun x _ ↦ mul_nonneg (hρ x) (sum_nonneg fun y _ ↦ sum_nonneg fun y' _ ↦
    mul_nonneg (mul_nonneg (hpol x y) (hpol x y')) (sq_nonneg _))

/-- The calibrated values of two rewards at the same policy differ by the expected reward
difference (the KL terms cancel). -/
theorem calValue_sub (ρ : X → ℝ) (π_ref π_cal : X → Y → ℝ) (β : ℝ) (r s pol : X → Y → ℝ) :
    calValue ρ π_ref π_cal β r pol - calValue ρ π_ref π_cal β s pol =
      ∑ x, ρ x * (∑ y, pol x y * (r x y - s x y) - ∑ y, π_cal x y * (r x y - s x y)) := by
  unfold calValue
  simp only [mul_sub, sum_sub_distrib]
  ring

/-- L5 (calibration gap): if `π_cal ≤ K π` pointwise, then
`(J(r, π) − J(s, π))² ≤ (K/2) · pairDisp ρ π (r − s)`. -/
theorem calValue_sub_sq_le (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (hρ1 : ∑ x, ρ x = 1)
    (π_ref π_cal : X → Y → ℝ) (hcal : IsCondPolicy π_cal) (β : ℝ) (r s pol : X → Y → ℝ)
    (hpol : IsCondPolicy pol) (K : ℝ) (hK : ∀ x y, π_cal x y ≤ K * pol x y) :
    (calValue ρ π_ref π_cal β r pol - calValue ρ π_ref π_cal β s pol) ^ 2 ≤
      K / 2 * pairDisp ρ pol (fun x y ↦ r x y - s x y) := by
  rw [calValue_sub]
  calc _ ≤ ∑ x, ρ x * (∑ y, pol x y * (r x y - s x y) - ∑ y, π_cal x y * (r x y - s x y)) ^ 2 :=
        sq_wsum_le univ ρ _ (fun x _ ↦ hρ x) hρ1
    _ ≤ ∑ x, ρ x * (K * ∑ y, pol x y * ((r x y - s x y) -
          ∑ y', pol x y' * (r x y' - s x y')) ^ 2) :=
        sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left
          (row_cal_gap (pol x) (π_cal x) (fun y ↦ r x y - s x y) (hcal.1 x) (hcal.2 x) K (hK x))
          (hρ x)
    _ = _ := by
        unfold pairDisp
        rw [mul_sum]
        refine sum_congr rfl fun x _ ↦ ?_
        rw [var_eq_half_pair (pol x) (fun y ↦ r x y - s x y) (hpol.2 x)]
        ring

/-- Local-curvature bound (step 1 of the local-curvature argument): for `|r − s| ≤ G`,
`J⋆(s) − J(s, π_r) ≤ e^{2G/β}/(4β) · pairDisp ρ π_r (r − s)`. -/
theorem optClosed_sub_calValue_le (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) {π_ref : X → Y → ℝ}
    (href : IsPositivePolicy π_ref) (π_cal : X → Y → ℝ) {β G : ℝ} (hβ : 0 < β)
    (r s : X → Y → ℝ) (hg : ∀ x y, |r x y - s x y| ≤ G) :
    optClosed ρ π_ref π_cal β s - calValue ρ π_ref π_cal β s (gibbsPolicy π_ref r β) ≤
      exp (2 * G / β) / (4 * β) *
        pairDisp ρ (gibbsPolicy π_ref r β) (fun x y ↦ r x y - s x y) := by
  unfold optClosed calValue pairDisp klDiv
  have hrow : ∀ x, β * log (partitionFn π_ref s β x) -
      (∑ y, gibbsPolicy π_ref r β x y * s x y - β * ∑ y, gibbsPolicy π_ref r β x y *
        log (gibbsPolicy π_ref r β x y / π_ref x y)) ≤
      exp (2 * G / β) / (4 * β) * ∑ y, ∑ y', gibbsPolicy π_ref r β x y *
        gibbsPolicy π_ref r β x y' * (r x y - s x y - (r x y' - s x y')) ^ 2 := by
    intro x
    have h := row_local_bound (π_ref x) (r x) (s x) hβ (href.1 x) (href.2 x) (hg x)
    simp only at h
    have hv := var_eq_half_pair (gibbsPolicy π_ref r β x) (fun y ↦ r x y - s x y)
      (gibbsPolicy_sum href r β x)
    simp only [gibbsPolicy_eq] at hv ⊢
    unfold partitionFn at hv ⊢
    rw [hv] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  have : ∀ x, ρ x * (β * log (partitionFn π_ref s β x)) -
      ρ x * (∑ y, gibbsPolicy π_ref r β x y * s x y - β * ∑ y, gibbsPolicy π_ref r β x y *
        log (gibbsPolicy π_ref r β x y / π_ref x y)) ≤
      exp (2 * G / β) / (4 * β) * (ρ x * ∑ y, ∑ y', gibbsPolicy π_ref r β x y *
        gibbsPolicy π_ref r β x y' * (r x y - s x y - (r x y' - s x y')) ^ 2) := by
    intro x
    have := mul_le_mul_of_nonneg_left (hrow x) (hρ x)
    nlinarith
  have hsum := sum_le_sum fun x (_ : x ∈ univ) ↦ this x
  rw [sum_sub_distrib, ← mul_sum] at hsum
  linarith

/-- The calibrated value gap of two rewards with `|r − s| ≤ G` is at most `2G`. -/
theorem calValue_sub_le (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (hρ1 : ∑ x, ρ x = 1)
    (π_ref π_cal : X → Y → ℝ) (hcal : IsCondPolicy π_cal) (β : ℝ) (r s pol : X → Y → ℝ)
    (hpol : IsCondPolicy pol) {G : ℝ} (hg : ∀ x y, |r x y - s x y| ≤ G) :
    calValue ρ π_ref π_cal β r pol - calValue ρ π_ref π_cal β s pol ≤ 2 * G := by
  rw [calValue_sub]
  have hrow : ∀ (c : X → Y → ℝ), IsCondPolicy c → ∀ x, |∑ y, c x y * (r x y - s x y)| ≤ G := by
    intro c hc x
    calc |∑ y, c x y * (r x y - s x y)| ≤ ∑ y, |c x y * (r x y - s x y)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, c x y * G := sum_le_sum fun y _ ↦ by
          rw [abs_mul, abs_of_nonneg (hc.1 x y)]
          exact mul_le_mul_of_nonneg_left (hg x y) (hc.1 x y)
      _ = G := by rw [← sum_mul, hc.2 x, one_mul]
  calc _ ≤ ∑ x, ρ x * (2 * G) := sum_le_sum fun x _ ↦ by
        refine mul_le_mul_of_nonneg_left ?_ (hρ x)
        have h1 := abs_le.1 (hrow pol hpol x)
        have h2 := abs_le.1 (hrow π_cal hcal x)
        linarith [h1.2, h2.1]
    _ = 2 * G := by rw [← sum_mul, hρ1, one_mul]

/-- L4: a ball-constrained selection rule exists. -/
theorem exists_ballSelection {d : ℕ} (ρ : X → ℝ) {π_ref : X → Y → ℝ}
    (href : IsPositivePolicy π_ref) (π_cal : X → Y → ℝ) (hcal : ∀ x, ∑ y, π_cal x y = 1)
    (φ : X → Y → EuclideanSpace ℝ (Fin d)) (α : ℝ) {β R : ℝ} (hβ : 0 < β) (hR : 0 ≤ R) :
    ∃ sel, IsBallSelection ρ π_ref π_cal φ α β R sel := by
  have key : ∀ D : List (X × Y × Y), ∃ θ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) R,
      IsMinOn (fun θ ↦ vpoObjective ρ π_ref π_cal α β D (gibbsPolicy π_ref (linReward φ θ) β))
        (Metric.closedBall 0 R) θ := by
    intro D
    refine (isCompact_closedBall _ _).exists_isMinOn ⟨0, Metric.mem_closedBall_self hR⟩ ?_
    refine Continuous.continuousOn ?_
    simp_rw [vpoObjective_gibbs ρ href π_cal hcal α hβ]
    have hlin : ∀ x y, Continuous fun θ : EuclideanSpace ℝ (Fin d) ↦ linReward φ θ x y :=
      fun x y ↦ continuous_const.inner continuous_id
    unfold nll optClosed partitionFn
    refine Continuous.sub (Continuous.neg ?_) (continuous_const.mul ?_)
    · refine continuous_list_sum _ fun z _ ↦ ?_
      exact (continuous_sigmoid.comp ((hlin _ _).sub (hlin _ _))).log
        fun θ ↦ (sigmoid_pos _).ne'
    · refine Continuous.sub (continuous_finset_sum _ fun x _ ↦ continuous_const.mul
        (continuous_const.mul ?_)) (continuous_finset_sum _ fun x _ ↦ continuous_const.mul
        (continuous_finset_sum _ fun y _ ↦ continuous_const.mul (hlin x y)))
      refine Continuous.log (continuous_finset_sum _ fun y _ ↦ continuous_const.mul
        (continuous_exp.comp ((hlin x y).div_const β))) fun θ ↦ ?_
      exact (partitionFn_pos href (linReward φ θ) β x).ne'
  choose sel hsel hmin using key
  refine ⟨sel, fun D ↦ ⟨?_, fun θ hθ ↦ ?_⟩⟩
  · simpa using hsel D
  · exact hmin D (by simpa using hθ)

end Global

end StatisticalRL.Ch7Rest.Rlhf
