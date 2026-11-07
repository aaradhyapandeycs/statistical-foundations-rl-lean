import Formalization.Ch7Rest.RlhfPrinted712

/-!
# Theorem 7.12 is ill-posed (SOURCE-ISSUES C44)

1. At `T = 1` the printed formula for `α` (`RLHF.tex:214`) divides by
   `κ · min{d log 1, 1} = 0`, so it is undefined. The Lean transcription evaluates
   to the junk value `0` of `x / 0`; this records the undefinedness, not a value
   of `α` (the source requires `α > 0`, `RLHF.tex:113`).
2. The online VPO update (`RLHF.tex:194–198`) can have no minimizer. Instance:
   one prompt, two answers `y₁ = 0, y₂ = 1`, `π_ref = π_cal` uniform, any
   `α, β > 0`, and `n ≥ 0` comparisons `y₁ ≻ y₂` (including none, which is the
   dataset of the very first update `t = 0`). Along `π_p = (1-p, p)` with
   `p → 0` the objective tends to `-∞`; hence no full-support policy minimizes
   it. With `d = 1`, `φ(y₁) = 1`, `φ(y₂) = 0` (`‖φ‖ ≤ 1`) these `π_p` are exactly
   the Gibbs policies `π_θ`, so no parameter `θ ∈ ℝ` gives a minimizer either.
Boundary-policy disclosure. The argmin is taken over full-support policies, the
policies `π_r` induced by real rewards (`RLHF.tex:126–133`), i.e. the Gibbs class
`π_θ`. Over the closed simplex with the extended-real conventions `log 0 = -∞`,
`σ(+∞) = 1`, the infimum `-∞` of the instance below is attained at the boundary
policy `(1, 0)` (for `n = 0` also at `(0, 1)`). No real reward and no real `θ`
induces that policy, so the hypothesis `‖θ^{(t)}‖ ≤ r_max` (`RLHF.tex:209`) fails.
Under either reading the status is "Theorem 7.12 is ill-posed or vacuous", never
"Theorem 7.12 is false". The regret bound of Theorem 7.12 itself is neither
transcribed nor refuted.
-/

namespace StatisticalRL.Ch7Rest.Rlhf

/-! ### The step size at `T = 1` -/

/-- At `T = 1` the denominator `κ · min{d log T, T}` of the printed `α` is `0`. -/
theorem vpoAlpha_denominator_T_one (κ : ℝ) (d : ℕ) :
    κ * min ((d : ℝ) * Real.log ((1 : ℕ) : ℝ)) ((1 : ℕ) : ℝ) = 0 := by
  simp

/-- At `T = 1` the transcribed `α` is the junk value `0` of Lean's `x / 0`
(the printed formula is undefined there). -/
theorem vpoAlpha_T_one (r_max β κ : ℝ) (d : ℕ) : vpoAlpha r_max β κ d 1 = 0 := by
  simp [vpoAlpha]

/-- **C44 (i).** At `T = 1` the printed formula for `α` divides by
`κ · min{d log 1, 1} = 0` and is undefined; the Lean transcription evaluates to
the junk value `0` of `x / 0`, which is not positive. This records the
undefinedness of the printed formula, not a value of `α`. -/
theorem not_vpoAlpha_T_one_pos (r_max β κ : ℝ) (d : ℕ) : ¬ 0 < vpoAlpha r_max β κ d 1 := by
  rw [vpoAlpha_T_one]
  exact lt_irrefl 0

/-! ### The two-answer instance -/

/-- Uniform policy on two answers (used as `π_ref = π_cal`). -/
noncomputable def uniform2 : Unit → Fin 2 → ℝ := fun _ _ ↦ 1 / 2

/-- `π_p = (1 - p, p)`. -/
noncomputable def pol2 (p : ℝ) : Unit → Fin 2 → ℝ := fun _ y ↦ if y = 0 then 1 - p else p

/-- `n` comparisons `y₁ ≻ y₂`. -/
def data2 (n : ℕ) : List (Unit × Fin 2 × Fin 2) := List.replicate n ((), 0, 1)

theorem uniform2_positive : IsPositivePolicy uniform2 :=
  ⟨fun _ _ ↦ by norm_num [uniform2], fun _ ↦ by norm_num [uniform2, Fin.sum_univ_two]⟩

theorem pol2_positive {p : ℝ} (h0 : 0 < p) (h1 : p < 1) : IsPositivePolicy (pol2 p) := by
  refine ⟨fun _ y ↦ ?_, fun _ ↦ ?_⟩
  · fin_cases y <;> simp [pol2] <;> linarith
  · simp [pol2, Fin.sum_univ_two]

/-- Closed form of the objective along `π_p`. -/
theorem vpoObjective_pol2 (α β p : ℝ) (n : ℕ) :
    vpoObjective (fun _ ↦ 1) uniform2 uniform2 α β (data2 n) (pol2 p) =
      -(n * Real.log (Real.sigmoid (β * Real.log ((1 - p) / (1 / 2)) -
        β * Real.log (p / (1 / 2))))) +
      α * β * (1 / 2 * (Real.log (1 - p) - Real.log (1 / 2)) +
        1 / 2 * (Real.log p - Real.log (1 / 2))) := by
  simp [vpoObjective, data2, uniform2, pol2, Fin.sum_univ_two, List.map_replicate,
    List.sum_replicate]

/-- Upper bound along `π_p` for `0 < p ≤ 1/2`. -/
theorem vpoObjective_pol2_le (α β p : ℝ) (n : ℕ) (hα : 0 < α) (hβ : 0 < β)
    (h0 : 0 < p) (h1 : p ≤ 1 / 2) :
    vpoObjective (fun _ ↦ 1) uniform2 uniform2 α β (data2 n) (pol2 p) ≤
      n * Real.log 2 + α * β * (Real.log 2 + 1 / 2 * Real.log p) := by
  rw [vpoObjective_pol2]
  have hlog2 : Real.log (1 / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  -- the likelihood term is at most `n log 2`
  have hz : 0 ≤ β * Real.log ((1 - p) / (1 / 2)) - β * Real.log (p / (1 / 2)) := by
    have : Real.log (p / (1 / 2)) ≤ Real.log ((1 - p) / (1 / 2)) :=
      Real.log_le_log (by positivity) (by linarith)
    nlinarith
  have hσ : 1 / 2 ≤ Real.sigmoid (β * Real.log ((1 - p) / (1 / 2)) -
      β * Real.log (p / (1 / 2))) := by
    have := Real.sigmoid_le hz
    rwa [Real.sigmoid_zero, ← one_div] at this
  have hlogσ : -Real.log 2 ≤ Real.log (Real.sigmoid (β * Real.log ((1 - p) / (1 / 2)) -
      β * Real.log (p / (1 / 2)))) := by
    rw [← hlog2]
    exact Real.log_le_log (by norm_num) hσ
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hterm1 : -(n * Real.log (Real.sigmoid (β * Real.log ((1 - p) / (1 / 2)) -
      β * Real.log (p / (1 / 2))))) ≤ n * Real.log 2 := by
    nlinarith
  -- the calibration term
  have hl1 : Real.log (1 - p) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
  have hterm2 : α * β * (1 / 2 * (Real.log (1 - p) - Real.log (1 / 2)) +
      1 / 2 * (Real.log p - Real.log (1 / 2))) ≤
      α * β * (Real.log 2 + 1 / 2 * Real.log p) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [hlog2]
    linarith
  linarith

/-- **C44 (ii).** Along the policies `π_p`, `p ∈ (0, 1/2]`, the online VPO
objective of the two-answer instance is unbounded below, for every `α, β > 0`
and every number `n` of comparisons `y₁ ≻ y₂`. -/
theorem vpoObjective_pol2_unbounded (α β : ℝ) (n : ℕ) (hα : 0 < α) (hβ : 0 < β) (M : ℝ) :
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 / 2 ∧
      vpoObjective (fun _ ↦ 1) uniform2 uniform2 α β (data2 n) (pol2 p) < M := by
  have hαβ : 0 < α * β := mul_pos hα hβ
  set L : ℝ := min (-Real.log 2) (2 * ((M - n * Real.log 2) / (α * β) - Real.log 2) - 1)
    with hL
  refine ⟨Real.exp L, Real.exp_pos L, ?_, ?_⟩
  · calc Real.exp L ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (min_le_left _ _)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]
  · have hp : Real.exp L ≤ 1 / 2 := by
      calc Real.exp L ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.mpr (min_le_left _ _)
        _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]
    have hle := vpoObjective_pol2_le α β (Real.exp L) n hα hβ (Real.exp_pos L) hp
    rw [Real.log_exp] at hle
    have hL2 : L ≤ 2 * ((M - n * Real.log 2) / (α * β) - Real.log 2) - 1 := min_le_right _ _
    have hmul : α * β * (L / 2) ≤
        α * β * (((M - n * Real.log 2) / (α * β) - Real.log 2) - 1 / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hαβ.le
    have e : α * β * ((M - n * Real.log 2) / (α * β)) = M - n * Real.log 2 :=
      mul_div_cancel₀ _ (ne_of_gt hαβ)
    have e2 : α * β * (((M - n * Real.log 2) / (α * β) - Real.log 2) - 1 / 2) =
        α * β * ((M - n * Real.log 2) / (α * β)) - α * β * Real.log 2 - α * β / 2 := by ring
    nlinarith

/-- **C44 (ii).** The two-answer instance has no VPO minimizer among full-support
policies, for every `α, β > 0` and every number `n ≥ 0` of comparisons `y₁ ≻ y₂`. -/
theorem no_vpoMinimizer (α β : ℝ) (n : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    ¬ ∃ πstar, IsVPOMinimizer (fun _ ↦ 1) uniform2 uniform2 α β (data2 n) πstar := by
  rintro ⟨πstar, -, hmin⟩
  obtain ⟨p, hp0, hp1, hlt⟩ := vpoObjective_pol2_unbounded α β n hα hβ
    (vpoObjective (fun _ ↦ 1) uniform2 uniform2 α β (data2 n) πstar)
  exact absurd (hmin _ (pol2_positive hp0 (by linarith))) (not_le.mpr hlt)

/-- **C44 (ii).** The online VPO update is not always defined. -/
theorem not_vpoUpdate_exists_printed : ¬ VPOUpdate_exists_printed := by
  intro h
  exact no_vpoMinimizer 1 1 0 one_pos one_pos
    (h Unit (Fin 2) (fun _ ↦ 1) uniform2 uniform2 1 1 (data2 0) one_pos one_pos
      (fun _ ↦ zero_le_one) (by simp) uniform2_positive uniform2_positive)

/-- **C44 (ii).** Even the first online update `π^{(1)}` (empty dataset) can fail
to exist, for every `α, β > 0`. -/
theorem not_vpoFirstUpdate_exists_printed : ¬ VPOFirstUpdate_exists_printed := by
  intro h
  exact no_vpoMinimizer 1 1 0 one_pos one_pos
    (h Unit (Fin 2) (fun _ ↦ 1) uniform2 uniform2 1 1 one_pos one_pos
      (fun _ ↦ zero_le_one) (by simp) uniform2_positive uniform2_positive)

/-! ### Gibbs (linear-reward) parametrization, `d = 1` -/

/-- The Gibbs policy `π_θ(y) ∝ π_ref(y) exp(φ(y) θ / β)` of `RLHF.tex:51–59` for
the linear reward `r_θ(y) = φ(y) θ` with `d = 1`, `φ(y₁) = 1`, `φ(y₂) = 0`
(`RLHF.tex:146–152`) and uniform `π_ref`. -/
noncomputable def gibbs2 (β θ : ℝ) : Unit → Fin 2 → ℝ := fun _ y ↦
  uniform2 () y * Real.exp ((if y = 0 then θ else 0) / β) /
    (uniform2 () 0 * Real.exp (θ / β) + uniform2 () 1 * Real.exp (0 / β))

/-- Every `π_p`, `0 < p < 1`, is a Gibbs policy. -/
theorem gibbs2_eq_pol2 (β p : ℝ) (hβ : 0 < β) (h0 : 0 < p) (h1 : p < 1) :
    gibbs2 β (β * Real.log ((1 - p) / p)) = pol2 p := by
  have hq : 0 < (1 - p) / p := div_pos (by linarith) h0
  have he : Real.exp (β * Real.log ((1 - p) / p) / β) = (1 - p) / p := by
    rw [mul_div_cancel_left₀ _ (ne_of_gt hβ), Real.exp_log hq]
  have hp : p ≠ 0 := ne_of_gt h0
  funext x y
  fin_cases y
  · show (1 / 2 : ℝ) * Real.exp ((if (0 : Fin 2) = 0 then β * Real.log ((1 - p) / p)
          else 0) / β) / ((1 / 2) * Real.exp (β * Real.log ((1 - p) / p) / β) +
          (1 / 2) * Real.exp (0 / β)) = if (0 : Fin 2) = 0 then 1 - p else p
    rw [if_pos rfl, if_pos rfl, he, zero_div, Real.exp_zero]
    field_simp
    ring
  · simp only [gibbs2, uniform2, pol2, he, zero_div, Real.exp_zero]
    simp only [Fin.mk_one, one_ne_zero, if_false, zero_div, Real.exp_zero]
    field_simp
    ring

/-- **C44 (ii), Gibbs form.** No parameter `θ ∈ ℝ` minimizes the VPO objective
over the Gibbs policies `π_θ` of the two-answer, `d = 1` instance, for every
`α, β > 0` and `n ≥ 0` comparisons `y₁ ≻ y₂`. -/
theorem no_vpoMinimizer_gibbs (α β : ℝ) (n : ℕ) (hα : 0 < α) (hβ : 0 < β) :
    ¬ ∃ θstar : ℝ, ∀ θ : ℝ,
      vpoObjective (fun _ ↦ 1) uniform2 uniform2 α β (data2 n) (gibbs2 β θstar) ≤
        vpoObjective (fun _ ↦ 1) uniform2 uniform2 α β (data2 n) (gibbs2 β θ) := by
  rintro ⟨θstar, hmin⟩
  obtain ⟨p, hp0, hp1, hlt⟩ := vpoObjective_pol2_unbounded α β n hα hβ
    (vpoObjective (fun _ ↦ 1) uniform2 uniform2 α β (data2 n) (gibbs2 β θstar))
  have h := hmin (β * Real.log ((1 - p) / p))
  rw [gibbs2_eq_pol2 β p hβ hp0 (by linarith)] at h
  exact absurd h (not_le.mpr hlt)

end StatisticalRL.Ch7Rest.Rlhf
