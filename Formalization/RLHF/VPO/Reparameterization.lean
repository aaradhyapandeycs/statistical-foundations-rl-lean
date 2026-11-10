import Formalization.RLHF.VPO.Gibbs

/-!
# DPO and VPO reparameterizations (`eq:DPO`, `eq:policy_RBMLE`, `eq:online_RBMLE`)

Source: `chapters/RLHF.tex`. Gibbs closed form :52–59, reward–policy correspondence
`eq:reward-policy-eq` :63–66, `eq:DPO` :67–74, prompt-shift non-identifiability :90,
`eq:RBMLE` :107–113, `eq:Jstar` :116–124, `eq:policy_RBMLE` :125–141, online steps :158–177,
`eq:online_RBMLE` :194–198.

Results.
* `dpoLoss_gibbs`: the DPO loss of `π_r` is the Bradley–Terry NLL of `r` (`Z` cancels).
* `exists_gibbsPolicy_eq`: every full-support policy is `π_r` for `r = β log(π/π_ref)`.
* `gibbsPolicy_eq_iff`: `π_r = π_{r'}` iff `r − r'` depends on the prompt only.
* `isMin_iff_of_gibbs`: generic argmin transfer from rewards to full-support policies.
* `dpo_argmin_iff`, `vpo_argmin_iff`: the DPO and VPO argmin correspondences.
* `calShift_eq_neg_kl`, `vpoObjective_calSwap`: the `π_cal` swap and the KL identity (:137–140).
* `klValue_le_gibbs`, `online_vpo_step`: the online combination claim (:177).

Everything is over full-support policies (`IsPositivePolicy`), because `log π` is a real number
exactly there; see the docstrings of the statement-index entries.
-/

namespace StatisticalRL.Ch7Rest.Rlhf

open Finset Real

set_option linter.unusedSectionVars false

variable {X Y : Type} [Fintype X] [Fintype Y]

/-- The printed DPO loss of `eq:DPO` (`RLHF.tex:69–72`). -/
noncomputable def dpoLoss (π_ref : X → Y → ℝ) (β : ℝ) (D : List (X × Y × Y))
    (pol : X → Y → ℝ) : ℝ :=
  -(D.map fun z ↦ log (sigmoid
      (β * (log (pol z.1 z.2.1 / π_ref z.1 z.2.1) - log (pol z.1 z.2.2 / π_ref z.1 z.2.2))))).sum

variable {π_ref : X → Y → ℝ}

/-- `eq:DPO` (i): the DPO loss of the Gibbs policy `π_r` is `ℓ(r, D)`; `Z(r, x)` cancels (:74). -/
theorem dpoLoss_gibbs (href : IsPositivePolicy π_ref) {β : ℝ} (hβ : β ≠ 0) (r : X → Y → ℝ)
    (D : List (X × Y × Y)) : dpoLoss π_ref β D (gibbsPolicy π_ref r β) = nll r D := by
  unfold dpoLoss nll
  congr 2
  refine List.map_congr_left fun z _ ↦ ?_
  rw [log_gibbs_div href, log_gibbs_div href]
  congr 2
  field_simp
  ring

/-- `eq:reward-policy-eq` (:63–66): every full-support policy is the Gibbs policy of
`r = β log(π/π_ref)`. -/
theorem exists_gibbsPolicy_eq (href : IsPositivePolicy π_ref) {β : ℝ} (hβ : β ≠ 0)
    {pol : X → Y → ℝ} (hpol : IsPositivePolicy pol) : ∃ r, pol = gibbsPolicy π_ref r β := by
  refine ⟨fun x y ↦ β * log (pol x y / π_ref x y), ?_⟩
  have hexp : ∀ x y, π_ref x y * exp (β * log (pol x y / π_ref x y) / β) = pol x y := by
    intro x y
    rw [mul_div_cancel_left₀ _ hβ, exp_log (div_pos (hpol.1 x y) (href.1 x y))]
    field_simp [(href.1 x y).ne']
  funext x y
  rw [gibbsPolicy_eq, partitionFn]
  simp only [hexp, hpol.2 x, div_one]

/-- Prompt-shift non-identifiability (:90) and its converse: `π_r = π_{r'}` iff `r − r'` is a
function of the prompt only. -/
theorem gibbsPolicy_eq_iff (href : IsPositivePolicy π_ref) {β : ℝ} (hβ : β ≠ 0)
    (r r' : X → Y → ℝ) :
    gibbsPolicy π_ref r β = gibbsPolicy π_ref r' β ↔
      ∃ c : X → ℝ, ∀ x y, r x y = r' x y + c x := by
  constructor
  · intro h
    refine ⟨fun x ↦ β * (log (partitionFn π_ref r β x) - log (partitionFn π_ref r' β x)), ?_⟩
    intro x y
    have h1 := log_gibbs_div href r β x y
    have h2 := log_gibbs_div href r' β x y
    rw [h] at h1
    have h3 : r x y / β = r' x y / β +
        (log (partitionFn π_ref r β x) - log (partitionFn π_ref r' β x)) := by linarith
    field_simp at h3
    linarith
  · rintro ⟨c, hc⟩
    have hZ : ∀ x, partitionFn π_ref r β x = exp (c x / β) * partitionFn π_ref r' β x := by
      intro x
      unfold partitionFn
      rw [mul_sum]
      refine sum_congr rfl fun y _ ↦ ?_
      rw [hc x y, add_div, exp_add]
      ring
    funext x y
    rw [gibbsPolicy_eq, gibbsPolicy_eq, hZ x, hc x y, add_div, exp_add]
    have := exp_pos (c x / β)
    have := partitionFn_pos href r' β x
    field_simp

/-- Generic argmin transfer: if `G r = F (π_r)` for every reward and every full-support policy is
some `π_r`, then a full-support `π` minimizes `F` over full-support policies iff it is `π_r` for a
minimizer `r` of `G`. -/
theorem isMin_iff_of_gibbs (href : IsPositivePolicy π_ref) {β : ℝ} (hβ : β ≠ 0)
    (F : (X → Y → ℝ) → ℝ) (G : (X → Y → ℝ) → ℝ)
    (hFG : ∀ r, F (gibbsPolicy π_ref r β) = G r) {pol : X → Y → ℝ} (hpol : IsPositivePolicy pol) :
    (∀ pol', IsPositivePolicy pol' → F pol ≤ F pol') ↔
      ∃ r, pol = gibbsPolicy π_ref r β ∧ ∀ r', G r ≤ G r' := by
  constructor
  · intro hmin
    obtain ⟨r, rfl⟩ := exists_gibbsPolicy_eq href hβ hpol
    refine ⟨r, rfl, fun r' ↦ ?_⟩
    rw [← hFG, ← hFG]
    exact hmin _ (gibbsPolicy_isPositive href r' β)
  · rintro ⟨r, rfl, hr⟩ pol' hpol'
    obtain ⟨r', rfl⟩ := exists_gibbsPolicy_eq href hβ hpol'
    rw [hFG, hFG]
    exact hr r'

/-- `eq:DPO` (iv): DPO minimizers over full-support policies are the Gibbs policies of NLL
minimizers. -/
theorem dpo_argmin_iff (href : IsPositivePolicy π_ref) {β : ℝ} (hβ : β ≠ 0)
    (D : List (X × Y × Y)) {pol : X → Y → ℝ} (hpol : IsPositivePolicy pol) :
    (∀ pol', IsPositivePolicy pol' → dpoLoss π_ref β D pol ≤ dpoLoss π_ref β D pol') ↔
      ∃ r, pol = gibbsPolicy π_ref r β ∧ ∀ r', nll r D ≤ nll r' D :=
  isMin_iff_of_gibbs href hβ (dpoLoss π_ref β D) (fun r ↦ nll r D)
    (fun r ↦ dpoLoss_gibbs href hβ r D) hpol

/-- `eq:policy_RBMLE` (i): for any coefficient `a` (the source's `sign·α`), the VPO objective at
`π_r` is `ℓ(r, D) − a J⋆(r; π_cal)`. -/
theorem vpoObjective_gibbs_optCal (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x)
    (href : IsPositivePolicy π_ref) (π_cal : X → Y → ℝ) (hcal : IsCondPolicy π_cal) (a : ℝ)
    {β : ℝ} (hβ : 0 < β) (r : X → Y → ℝ) (D : List (X × Y × Y)) :
    vpoObjective ρ π_ref π_cal a β D (gibbsPolicy π_ref r β) =
      nll r D - a * optCalValue ρ π_ref π_cal β r := by
  rw [vpoObjective_gibbs ρ href π_cal hcal.2 a hβ r D, optCalValue_eq ρ hρ href π_cal hβ r]

/-- `eq:policy_RBMLE` (ii): VPO minimizers over full-support policies are the Gibbs policies of
minimizers of `ℓ(r, D) − a J⋆(r; π_cal)`. -/
theorem vpo_argmin_iff (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (href : IsPositivePolicy π_ref)
    (π_cal : X → Y → ℝ) (hcal : IsCondPolicy π_cal) (a : ℝ) {β : ℝ} (hβ : 0 < β)
    (D : List (X × Y × Y)) {pol : X → Y → ℝ} (hpol : IsPositivePolicy pol) :
    (∀ pol', IsPositivePolicy pol' →
        vpoObjective ρ π_ref π_cal a β D pol ≤ vpoObjective ρ π_ref π_cal a β D pol') ↔
      ∃ r, pol = gibbsPolicy π_ref r β ∧
        ∀ r', nll r D - a * optCalValue ρ π_ref π_cal β r ≤
          nll r' D - a * optCalValue ρ π_ref π_cal β r' :=
  isMin_iff_of_gibbs href hβ.ne' (vpoObjective ρ π_ref π_cal a β D)
    (fun r ↦ nll r D - a * optCalValue ρ π_ref π_cal β r)
    (fun r ↦ vpoObjective_gibbs_optCal ρ hρ href π_cal hcal a hβ r D) hpol

/-- KL identity (:138–140): `E_{ρ,π_cal}[log π − log π_cal] = −E_ρ KL(π_cal‖π)` for full-support
`π` and nonnegative `π_cal` (terms with `π_cal = 0` vanish on both sides). -/
theorem calShift_eq_neg_kl (ρ : X → ℝ) {π_cal pol : X → Y → ℝ} (hcal : ∀ x y, 0 ≤ π_cal x y)
    (hpol : ∀ x y, 0 < pol x y) :
    ∑ x, ρ x * ∑ y, π_cal x y * (log (pol x y) - log (π_cal x y)) =
      -∑ x, ρ x * klDiv (π_cal x) (pol x) := by
  unfold klDiv
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [← mul_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun y _ ↦ ?_
  rcases (hcal x y).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · rw [log_div hpos.ne' (hpol x y).ne']
    ring

/-- The `π_ref → π_cal` swap in the last term (:137): it shifts the VPO objective by a constant
independent of the policy (an identity for every `pol`, with Lean's `log`). -/
theorem vpoObjective_calSwap (ρ : X → ℝ) (π_cal : X → Y → ℝ) (a β : ℝ)
    (D : List (X × Y × Y)) (pol : X → Y → ℝ) :
    vpoObjective ρ π_ref π_cal a β D pol =
      (-(D.map fun z ↦ log (sigmoid
          (β * log (pol z.1 z.2.1 / π_ref z.1 z.2.1) -
            β * log (pol z.1 z.2.2 / π_ref z.1 z.2.2)))).sum +
        a * β * ∑ x, ρ x * ∑ y, π_cal x y * (log (pol x y) - log (π_cal x y))) +
      a * β * ∑ x, ρ x * ∑ y, π_cal x y * (log (π_cal x y) - log (π_ref x y)) := by
  unfold vpoObjective
  have : ∑ x, ρ x * ∑ y, π_cal x y * (log (pol x y) - log (π_ref x y)) =
      ∑ x, ρ x * ∑ y, π_cal x y * (log (pol x y) - log (π_cal x y)) +
        ∑ x, ρ x * ∑ y, π_cal x y * (log (π_cal x y) - log (π_ref x y)) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun x _ ↦ ?_
    rw [← mul_add, ← sum_add_distrib]
    congr 1
    refine sum_congr rfl fun y _ ↦ ?_
    ring
  rw [this]
  ring

/-- Policy-learning step `eq:RLHF-policy` (:172–175): the Gibbs policy `π_r` maximizes the printed
KL-regularized value `J(r, π)` of `eq:KL_reward` over all conditional policies. -/
theorem klValue_le_gibbs (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (href : IsPositivePolicy π_ref)
    {β : ℝ} (hβ : 0 < β) (r : X → Y → ℝ) {pol : X → Y → ℝ} (hpol : IsCondPolicy pol) :
    ∑ x, ρ x * (∑ y, pol x y * r x y - β * klDiv (pol x) (π_ref x)) ≤
      ∑ x, ρ x * (∑ y, gibbsPolicy π_ref r β x y * r x y -
        β * klDiv (gibbsPolicy π_ref r β x) (π_ref x)) := by
  -- `calValue` differs from `J(r, ·)` by the policy-independent `E_{ρ,π_cal} r`; take `π_cal = 0`.
  have h1 := calValue_le_optClosed ρ hρ href (fun _ _ ↦ (0 : ℝ)) hβ r pol hpol
  have h2 := calValue_gibbs ρ href (fun _ _ ↦ (0 : ℝ)) hβ r
  unfold calValue at h1 h2
  simp only [zero_mul, sum_const_zero, mul_zero, sub_zero] at h1 h2
  rw [h2]
  exact h1

/-- The online combination claim (:177): for every minimizer `r` of `ℓ(r, D) − α J⋆(r; π_cal)`,
the Gibbs policy `π_r` solves the policy-learning step and minimizes the online VPO objective over
full-support policies. -/
theorem online_vpo_step (ρ : X → ℝ) (hρ : ∀ x, 0 ≤ ρ x) (href : IsPositivePolicy π_ref)
    (π_cal : X → Y → ℝ) (hcal : IsCondPolicy π_cal) (α : ℝ) {β : ℝ} (hβ : 0 < β)
    (D : List (X × Y × Y)) (r : X → Y → ℝ)
    (hr : ∀ r', nll r D - α * optCalValue ρ π_ref π_cal β r ≤
      nll r' D - α * optCalValue ρ π_ref π_cal β r') :
    (∀ pol, IsCondPolicy pol →
      ∑ x, ρ x * (∑ y, pol x y * r x y - β * klDiv (pol x) (π_ref x)) ≤
        ∑ x, ρ x * (∑ y, gibbsPolicy π_ref r β x y * r x y -
          β * klDiv (gibbsPolicy π_ref r β x) (π_ref x))) ∧
      IsVPOMinimizer ρ π_ref π_cal α β D (gibbsPolicy π_ref r β) := by
  refine ⟨fun pol hpol ↦ klValue_le_gibbs ρ hρ href hβ r hpol,
    gibbsPolicy_isPositive href r β, ?_⟩
  exact (vpo_argmin_iff ρ hρ href π_cal hcal α hβ D (gibbsPolicy_isPositive href r β)).2
    ⟨r, rfl, hr⟩

end StatisticalRL.Ch7Rest.Rlhf
