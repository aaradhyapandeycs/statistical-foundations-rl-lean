import Formalization.OfflineRL.LowerBoundFamilyDefinitions
import Formalization.MDP.OptimalTrajectoryValue
import Formalization.MDP.FixedPoint
import Formalization.Generative.PolicyLearningPerformanceTransfer

/-!
# Values and optimal policies of the offline hard family (`lemma:value-policy-LB-inf`)

`chapters/offlineRL.tex:2544–2583`, proof `:5502–5679`. For every `θ ∈ {0,1}^{S-1}`:
the closed forms of `V⋆_θ(0)` and `V⋆_θ(s)`, `s > 0`; the optimal actions (for `ε > 0`); and the
upper bound on `V^π_θ(s)` for every stationary randomized policy, with equality at `π⋆`.

The proof verifies that an explicit candidate Q-function is the fixed point of the Bellman
optimality operator (so it is `Q⋆`), and bounds `V^π` through its Bellman equation and
`V^π ≤ V⋆`. The final step of the source proof (attainment of the bound at `π⋆`) is supplied by
the same fixed-point identity.
-/

open scoped BigOperators
namespace StatisticalRL.OfflineRL.LowerBound
open StatisticalRL.DiscountedMDP

/-- `V⋆(0) = 4/(7(1-γ))`. -/
noncomputable def lbVz (γ : ℝ) : ℝ := 4 / (7 * (1 - γ))

/-- `1 - γ(p + (1-p)/C)`. -/
noncomputable def lbD (γ ε C : ℝ) : ℝ := 1 - γ * (lbP γ ε + (1 - lbP γ ε) / C)

/-- The closed form of `V⋆(s)` for `s > 0`. -/
noncomputable def lbVs (γ ε C : ℝ) : ℝ :=
  (1 + γ * (1 - lbP γ ε) * (1 - 1 / C) * lbVz γ) / lbD γ ε C

/-- `∑ μ V⋆ = (1 - 1/C) V⋆(0) + V⋆(s)/C`. -/
noncomputable def lbW (γ ε C : ℝ) : ℝ := (1 - 1 / C) * lbVz γ + lbVs γ ε C / C

section Scalar

variable {γ ε C : ℝ}

theorem lbGap_nonneg (hγ : 2 / 3 ≤ γ) (hε : 0 ≤ ε) : 0 ≤ lbGap γ ε := by
  unfold lbGap
  exact div_nonneg (by positivity) (by linarith)

theorem lbGap_le (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1) (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) :
    lbGap γ ε ≤ (1 - γ) / 2 := by
  have h : lbGap γ ε = (1 - γ) * (224 * (1 - γ) * ε / γ) := by unfold lbGap; ring
  rw [h]
  have := mul_le_mul_of_nonneg_left hεmax (by linarith : (0 : ℝ) ≤ 1 - γ)
  linarith

/-- The scalar facts used by the fixed-point verification. -/
theorem lb_scalar (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1) (hε : 0 ≤ ε)
    (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C) :
    0 < lbD γ ε C ∧
    lbVz γ = 4 / 7 + γ * lbVz γ ∧
    lbVs γ ε C = 1 + γ * (lbP γ ε * lbVs γ ε C + (1 - lbP γ ε) * lbW γ ε C) ∧
    lbW γ ε C < lbVs γ ε C ∧
    γ * ((2 * γ - 1) * lbVz γ + (1 - (2 * γ - 1)) * lbW γ ε C) < lbVz γ := by
  have hγ0 : 0 < γ := by linarith
  have h1γ : 0 < 1 - γ := by linarith
  have hC0 : 0 < C := by linarith
  have hg0 := lbGap_nonneg hγ hε
  have hg1 := lbGap_le hγ hγ1 hεmax
  set p := lbP γ ε with hp
  have hp1 : p ≤ 1 := by rw [hp]; unfold lbP; linarith
  have hiC : 1 / C < 1 := by rw [div_lt_one hC0]; linarith
  have hiC0 : 0 < 1 / C := by positivity
  set Vz := lbVz γ with hVzdef
  set D := lbD γ ε C with hDdef
  set Vs := lbVs γ ε C with hVsdef
  set W := lbW γ ε C with hWdef
  have hD : D = 1 - γ * p - γ * (1 - p) * (1 / C) := by rw [hDdef]; unfold lbD; ring
  have hDge : 1 - γ ≤ D := by
    rw [hD]
    have : 0 ≤ γ * (1 - p) * (1 - 1 / C) :=
      mul_nonneg (mul_nonneg hγ0.le (by linarith)) (by linarith)
    nlinarith
  have hDpos : 0 < D := lt_of_lt_of_le h1γ hDge
  have hVz : Vz * (1 - γ) = 4 / 7 := by
    rw [hVzdef]; unfold lbVz; field_simp
  have hVsD : Vs * D = 1 + γ * (1 - p) * (1 - 1 / C) * Vz := by
    rw [hVsdef]; unfold lbVs; rw [← hDdef, ← hVzdef, ← hp]; field_simp
  have hW : W = (1 - 1 / C) * Vz + Vs * (1 / C) := by
    rw [hWdef]; unfold lbW; rw [← hVzdef, ← hVsdef]; ring
  have hdiff : (Vs - Vz) * D = 3 / 7 := by
    rw [hD] at hVsD ⊢
    linear_combination hVsD - hVz
  have hpos : 0 < Vs - Vz := by
    by_contra h
    push_neg at h
    have : (Vs - Vz) * D ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hDpos.le
    linarith
  have ht : (1 - γ) * (Vs - Vz) ≤ 3 / 7 := by
    have := mul_le_mul_of_nonneg_left hDge hpos.le
    nlinarith
  refine ⟨hDpos, ?_, ?_, ?_, ?_⟩
  · linarith
  · rw [hW]
    rw [hD] at hVsD
    linear_combination hVsD
  · rw [hW]
    have : (1 - 1 / C) * Vz + Vs * (1 / C) - Vs = (1 - 1 / C) * (Vz - Vs) := by ring
    have h2 : (1 - 1 / C) * (Vz - Vs) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    linarith
  · have hid : γ * ((2 * γ - 1) * Vz + (1 - (2 * γ - 1)) * W) =
        γ * Vz + 2 * γ * ((1 - γ) * (Vs - Vz)) * (1 / C) := by
      rw [hW]; ring
    rw [hid]
    have h1 : 2 * γ * ((1 - γ) * (Vs - Vz)) * (1 / C) ≤ 2 * γ * (3 / 7) * (1 / C) := by
      have := mul_le_mul_of_nonneg_left ht (by linarith : (0 : ℝ) ≤ 2 * γ)
      exact mul_le_mul_of_nonneg_right this hiC0.le
    have h2 : 2 * γ * (3 / 7) * (1 / C) < 4 / 7 := by
      rw [show 2 * γ * (3 / 7) * (1 / C) = (6 * γ / 7) / C by ring, div_lt_iff₀ hC0]
      nlinarith
    linarith

end Scalar

section MDP

variable {m : ℕ} {hm : 1 ≤ m} {γ ε C : ℝ} {hγ : 2 / 3 ≤ γ} {hγ1 : γ < 1} {hε : 0 ≤ ε}
  {hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2} {hC : 2 < C}

/-- Expectation under a mixed row. -/
theorem lbRow_expectation (o : Option (Fin m)) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (V : Option (Fin m) → ℝ) :
    (lbRow C m hC hm o x hx0 hx1).expectation V =
      x * V o + (1 - x) * ∑ t, lbMu C m t * V t := by
  simp only [FiniteDistribution.expectation, lbRow, add_mul, Finset.sum_add_distrib]
  congr 1
  · simp [mul_assoc]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    ring

/-- The candidate value vector. -/
noncomputable def lbValue (γ ε C : ℝ) : Option (Fin m) → ℝ
  | none => lbVz γ
  | some _ => lbVs γ ε C

theorem lbMu_sum_value (hm : 1 ≤ m) (hC : 2 < C) :
    ∑ t, lbMu C m t * (lbValue γ ε C : Option (Fin m) → ℝ) t = lbW γ ε C := by
  have hmR : (m : ℝ) ≠ 0 := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    exact this.ne'
  have hC0 : C ≠ 0 := by intro h; rw [h] at hC; norm_num at hC
  simp only [Fintype.sum_option, lbMu, lbValue, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, lbW]
  field_simp

/-- Weighted sums under `μ` are monotone. -/
theorem lbMu_sum_mono (hm : 1 ≤ m) (hC : 2 < C) (U V : Option (Fin m) → ℝ)
    (h : ∀ t, U t ≤ V t) : ∑ t, lbMu C m t * U t ≤ ∑ t, lbMu C m t * V t := by
  refine Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (h t) ?_)
  cases t with
  | none =>
    simp only [lbMu]
    have : 1 / C ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  | some _ =>
    simp only [lbMu]
    have : (0 : ℝ) < m := by exact_mod_cast hm
    have : (0 : ℝ) < C := by linarith
    positivity

end MDP

/-- `actionMaximum` over `Bool` equals a dominating value. -/
theorem actionMaximum_bool_eq (f : Bool → ℝ) (a : Bool) (h : ∀ b, f b ≤ f a) :
    actionMaximum f = f a :=
  le_antisymm (Finset.sup'_le _ _ (fun b _ => h b)) (le_actionMaximum f a)

/-- The candidate Q-function `r + γ P V`. -/
noncomputable def lbQfun (m : ℕ) (hm : 1 ≤ m) (γ ε C : ℝ) (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 ≤ ε) (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C) (θ : Fin m → Bool)
    (o : Option (Fin m)) (a : Bool) : ℝ :=
  (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).reward o a +
    γ * ((lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).transition o a).expectation (lbValue γ ε C)

/-- Explicit values of the candidate Q-function. -/
theorem lbQfun_values (m : ℕ) (hm : 1 ≤ m) (γ ε C : ℝ) (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 ≤ ε) (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C) (θ : Fin m → Bool) :
    let Q := lbQfun m hm γ ε C hγ hγ1 hε hεmax hC θ
    Q none false = lbVz γ ∧
    Q none true = γ * ((2 * γ - 1) * lbVz γ + (1 - (2 * γ - 1)) * lbW γ ε C) ∧
    ∀ i a, Q (some i) a = 1 + γ * ((if a = θ i then lbP γ ε else lbQ γ ε) * lbVs γ ε C +
      (1 - (if a = θ i then lbP γ ε else lbQ γ ε)) * lbW γ ε C) := by
  obtain ⟨_, hVz, _, _, _⟩ := lb_scalar hγ hγ1 hε hεmax hC
  have hsum := lbMu_sum_value (γ := γ) (ε := ε) hm hC
  refine ⟨?_, ?_, ?_⟩
  · simp only [lbQfun, lbMDP, Bool.false_eq_true, if_false]
    rw [lbRow_expectation, hsum]
    simp only [lbValue]
    linarith
  · simp only [lbQfun, lbMDP, if_true]
    rw [lbRow_expectation, hsum]
    simp only [lbValue]
    ring
  · intro i a
    by_cases ha : a = θ i
    · simp only [lbQfun, lbMDP, ha, if_true]
      rw [lbRow_expectation, hsum]
      simp only [lbValue]
    · simp only [lbQfun, lbMDP, ha, if_false]
      rw [lbRow_expectation, hsum]
      simp only [lbValue]

/-- Summing over `Bool` splits at any chosen action. -/
theorem sum_bool_split (f : Bool → ℝ) (c : Bool) : ∑ b, f b = f c + f (!c) := by
  cases c <;> simp [Fintype.sum_bool, add_comm]

/-- The candidate is the optimality fixed point, so it is `Q⋆`. -/
theorem lb_optimalityFixedPoint (m : ℕ) (hm : 1 ≤ m) (γ ε C : ℝ) (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 ≤ ε) (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C) (θ : Fin m → Bool) :
    (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalityFixedPoint =
        lbQfun m hm γ ε C hγ hγ1 hε hεmax hC θ ∧
      ∀ t, actionMaximum (lbQfun m hm γ ε C hγ hγ1 hε hεmax hC θ t) = lbValue γ ε C t := by
  obtain ⟨_, _, hVs, hWVs, hz⟩ := lb_scalar hγ hγ1 hε hεmax hC
  obtain ⟨hQ0f, hQ0t, hQs⟩ := lbQfun_values m hm γ ε C hγ hγ1 hε hεmax hC θ
  set M := lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ with hM
  set Q := lbQfun m hm γ ε C hγ hγ1 hε hεmax hC θ with hQ
  have hgap := lbGap_nonneg hγ hε
  have hγ0 : 0 ≤ γ := by linarith
  have hmax : ∀ t, actionMaximum (Q t) = lbValue γ ε C t := by
    intro t
    cases t with
    | none =>
      rw [actionMaximum_bool_eq _ false]
      · simpa [lbValue] using hQ0f
      · intro b
        cases b
        · exact le_rfl
        · rw [hQ0t, hQ0f]; exact hz.le
    | some i =>
      rw [actionMaximum_bool_eq _ (θ i)]
      · rw [hQs i (θ i)]; simp only [if_true, lbValue]; exact hVs.symm
      · intro b
        rw [hQs i b, hQs i (θ i)]
        simp only [if_true]
        by_cases hb : b = θ i
        · simp [hb]
        · simp only [hb, if_false]
          have hpq : lbQ γ ε ≤ lbP γ ε := by unfold lbQ lbP; linarith
          have h1 : 0 ≤ (lbP γ ε - lbQ γ ε) * (lbVs γ ε C - lbW γ ε C) :=
            mul_nonneg (by linarith) (by linarith)
          nlinarith
  have hfix : M.qOptimality Q = Q := by
    funext o a
    simp only [qOptimality]
    have : (fun t => actionMaximum (Q t)) = lbValue γ ε C := funext hmax
    rw [this]
    rfl
  exact ⟨((M.optimalityFixedPoint_characterization Q).mp hfix).symm, hmax⟩

/-- The optimal value is the closed form `lbValue`. -/
theorem lb_optimalValue (m : ℕ) (hm : 1 ≤ m) (γ ε C : ℝ) (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 ≤ ε) (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C) (θ : Fin m → Bool)
    (t : Option (Fin m)) :
    (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).trajectoryExpectedValue
        (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyPolicy t = lbValue γ ε C t := by
  set M := lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ
  obtain ⟨hfp, hmax⟩ := lb_optimalityFixedPoint m hm γ ε C hγ hγ1 hε hεmax hC θ
  rw [M.trajectoryExpectedValue_eq_policyAverageQ]
  change (EnvironmentStage.pointMass (M.optimalGreedyAction t)).expectation
    (M.trajectoryExpectedQ M.optimalGreedyPolicy t) = _
  rw [EnvironmentStage.expectation_pointMass, M.optimalGreedy_trajectoryQ, M.optimalGreedyAction_max]
  rw [hfp]
  exact hmax t

/-- The optimal greedy action at state 0 is `0`, for every `ε ≥ 0`. -/
theorem lb_optimalGreedyAction_none (m : ℕ) (hm : 1 ≤ m) (γ ε C : ℝ) (hγ : 2 / 3 ≤ γ)
    (hγ1 : γ < 1) (hε : 0 ≤ ε) (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C)
    (θ : Fin m → Bool) :
    (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyAction none = false := by
  obtain ⟨_, _, _, _, hz⟩ := lb_scalar hγ hγ1 hε hεmax hC
  obtain ⟨_, hQ0t, _⟩ := lbQfun_values m hm γ ε C hγ hγ1 hε hεmax hC θ
  obtain ⟨hfp, hmax⟩ := lb_optimalityFixedPoint m hm γ ε C hγ hγ1 hε hεmax hC θ
  set M := lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ
  have h : lbQfun m hm γ ε C hγ hγ1 hε hεmax hC θ none (M.optimalGreedyAction none) =
      (lbValue γ ε C : Option (Fin m) → ℝ) none := by
    have h := M.optimalGreedyAction_max none
    rw [hfp] at h
    rw [h]
    exact hmax none
  cases hg : M.optimalGreedyAction none
  · rfl
  · rw [hg, hQ0t] at h
    simp only [lbValue] at h
    linarith

/-- For `ε > 0` the optimal greedy actions are `π⋆(0) = 0` and `π⋆(s) = θ_s`. -/
theorem lb_optimalGreedyAction (m : ℕ) (hm : 1 ≤ m) (γ ε C : ℝ) (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 ≤ ε) (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C) (θ : Fin m → Bool)
    (hεpos : 0 < ε) :
    (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyAction none = false ∧
      ∀ i, (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).optimalGreedyAction (some i) = θ i := by
  obtain ⟨_, _, hVs, hWVs, hz⟩ := lb_scalar hγ hγ1 hε hεmax hC
  obtain ⟨hQ0f, hQ0t, hQs⟩ := lbQfun_values m hm γ ε C hγ hγ1 hε hεmax hC θ
  obtain ⟨hfp, hmax⟩ := lb_optimalityFixedPoint m hm γ ε C hγ hγ1 hε hεmax hC θ
  set M := lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ
  have hgreedy : ∀ t, lbQfun m hm γ ε C hγ hγ1 hε hεmax hC θ t (M.optimalGreedyAction t) =
      lbValue γ ε C t := by
    intro t
    have h := M.optimalGreedyAction_max t
    rw [hfp] at h
    rw [h]
    exact hmax t
  have hγ0 : 0 < γ := by linarith
  have hgap : 0 < lbGap γ ε := by
    unfold lbGap
    have : 0 < 1 - γ := by linarith
    positivity
  refine ⟨?_, fun i => ?_⟩
  · have h := hgreedy none
    cases hg : M.optimalGreedyAction none
    · rfl
    · rw [hg, hQ0t] at h
      simp only [lbValue] at h
      linarith
  · have h := hgreedy (some i)
    by_contra hne
    rw [hQs i _, if_neg hne] at h
    simp only [lbValue] at h
    have hpq : lbQ γ ε < lbP γ ε := by unfold lbQ lbP; linarith
    have h1 : 0 < (lbP γ ε - lbQ γ ε) * (lbVs γ ε C - lbW γ ε C) :=
      mul_pos (by linarith) (by linarith)
    nlinarith

/-- Upper bound on `V^π(s)`, `s > 0`, for every stationary randomized policy. -/
theorem lb_policy_value_le (m : ℕ) (hm : 1 ≤ m) (γ ε C : ℝ) (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 ≤ ε) (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C) (θ : Fin m → Bool)
    (π : StationaryPolicy (Option (Fin m)) Bool) (i : Fin m) :
    let x := lbP γ ε * (π (some i)).prob (θ i) + lbQ γ ε * (π (some i)).prob (!θ i)
    (lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ).trajectoryExpectedValue π (some i) ≤
      (1 + γ * (1 - x) * lbW γ ε C) / (1 - γ * x) := by
  intro x
  set M := lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ
  have hg0 := lbGap_nonneg hγ hε
  have hg1 := lbGap_le hγ hγ1 hεmax
  have hp0 : 0 ≤ lbP γ ε := by unfold lbP; linarith
  have hp1 : lbP γ ε < 1 := by unfold lbP; linarith
  have hq0 : 0 ≤ lbQ γ ε := by unfold lbQ; linarith
  have hq1 : lbQ γ ε < 1 := by unfold lbQ; linarith
  set a := (π (some i)).prob (θ i)
  set b := (π (some i)).prob (!θ i)
  have ha0 : 0 ≤ a := (π (some i)).prob_nonneg _
  have hb0 : 0 ≤ b := (π (some i)).prob_nonneg _
  have hab : a + b = 1 := by
    have := (π (some i)).sum_prob
    rwa [sum_bool_split _ (θ i)] at this
  set V := M.trajectoryExpectedValue π with hVdef
  have hVle : ∀ t, V t ≤ lbValue γ ε C t := fun t =>
    (M.trajectoryValue_le_optimalGreedy π t).trans
      (le_of_eq (lb_optimalValue m hm γ ε C hγ hγ1 hε hεmax hC θ t))
  have hS : ∑ t, lbMu C m t * V t ≤ lbW γ ε C :=
    (lbMu_sum_mono hm hC V _ hVle).trans (le_of_eq (lbMu_sum_value hm hC))
  have hγ0 : 0 ≤ γ := by linarith
  have hQb : ∀ c : Bool, M.trajectoryExpectedQ π (some i) c ≤
      1 + γ * ((if c = θ i then lbP γ ε else lbQ γ ε) * V (some i) +
        (1 - (if c = θ i then lbP γ ε else lbQ γ ε)) * lbW γ ε C) := by
    intro c
    rw [M.trajectoryQ_eq_reward_add_trajectoryValue, ← hVdef]
    by_cases hc : c = θ i
    · simp only [M, lbMDP, hc, if_true]
      rw [lbRow_expectation]
      have : (1 - lbP γ ε) * ∑ t, lbMu C m t * V t ≤ (1 - lbP γ ε) * lbW γ ε C :=
        mul_le_mul_of_nonneg_left hS (by linarith)
      nlinarith
    · simp only [M, lbMDP, hc, if_false]
      rw [lbRow_expectation]
      have : (1 - lbQ γ ε) * ∑ t, lbMu C m t * V t ≤ (1 - lbQ γ ε) * lbW γ ε C :=
        mul_le_mul_of_nonneg_left hS (by linarith)
      nlinarith
  have hV : V (some i) = a * M.trajectoryExpectedQ π (some i) (θ i) +
      b * M.trajectoryExpectedQ π (some i) (!θ i) := by
    change M.trajectoryExpectedValue π (some i) = _
    rw [M.trajectoryExpectedValue_eq_policyAverageQ]
    simp only [FiniteDistribution.expectation]
    rw [sum_bool_split _ (θ i)]
  have h1 := mul_le_mul_of_nonneg_left (hQb (θ i)) ha0
  have h2 := mul_le_mul_of_nonneg_left (hQb (!θ i)) hb0
  simp only [if_true, Bool.not_eq_self, if_false] at h1 h2
  have hx1 : x < 1 := by
    change lbP γ ε * a + lbQ γ ε * b < 1
    have e1 := mul_le_mul_of_nonneg_right (le_max_left (lbP γ ε) (lbQ γ ε)) ha0
    have e2 := mul_le_mul_of_nonneg_right (le_max_right (lbP γ ε) (lbQ γ ε)) hb0
    have hm1 : max (lbP γ ε) (lbQ γ ε) < 1 := max_lt hp1 hq1
    have e3 : max (lbP γ ε) (lbQ γ ε) * a + max (lbP γ ε) (lbQ γ ε) * b =
        max (lbP γ ε) (lbQ γ ε) := by rw [← mul_add, hab, mul_one]
    linarith
  have hden : 0 < 1 - γ * x := by
    have hx0 : 0 ≤ x := by change 0 ≤ lbP γ ε * a + lbQ γ ε * b; positivity
    nlinarith
  rw [le_div_iff₀ hden]
  change V (some i) * (1 - γ * (lbP γ ε * a + lbQ γ ε * b)) ≤
    1 + γ * (1 - (lbP γ ε * a + lbQ γ ε * b)) * lbW γ ε C
  have hb : b = 1 - a := by linarith
  rw [hb] at h2 hV ⊢
  nlinarith [h1, h2, hV]

/-- `lemma:value-policy-LB-inf` for every `θ`: the policy upper bound with equality at `π⋆`,
the optimal actions (for `ε > 0`) and the closed-form optimal values. -/
theorem lb_value_policy (m : ℕ) (hm : 1 ≤ m) (γ ε C : ℝ) (hγ : 2 / 3 ≤ γ) (hγ1 : γ < 1)
    (hε : 0 ≤ ε) (hεmax : 224 * (1 - γ) * ε / γ ≤ 1 / 2) (hC : 2 < C) (θ : Fin m → Bool) :
    let M := lbMDP m hm γ ε C hγ hγ1 hε hεmax hC θ
    let Vs := M.trajectoryExpectedValue M.optimalGreedyPolicy
    let p := lbP γ ε
    let q := lbQ γ ε
    (∀ (π : StationaryPolicy (Option (Fin m)) Bool) (i : Fin m),
      let x := p * (π (some i)).prob (θ i) + q * (π (some i)).prob (!θ i)
      M.trajectoryExpectedValue π (some i) ≤
        (1 + γ * (1 - x) * (C⁻¹ * Vs (some i) + (1 - C⁻¹) * Vs none)) / (1 - γ * x)) ∧
    (∀ i : Fin m,
      let x := p * (M.optimalGreedyPolicy (some i)).prob (θ i) +
        q * (M.optimalGreedyPolicy (some i)).prob (!θ i)
      Vs (some i) =
        (1 + γ * (1 - x) * (C⁻¹ * Vs (some i) + (1 - C⁻¹) * Vs none)) / (1 - γ * x)) ∧
    (M.optimalGreedyPolicy none).prob false = 1 ∧
    (0 < ε → ∀ i, (M.optimalGreedyPolicy (some i)).prob (θ i) = 1) ∧
    Vs none = 4 / (7 * (1 - γ)) ∧
    ∀ i, Vs (some i) = (1 + γ * (1 - p) * (1 - C⁻¹) * Vs none) / (1 - γ * (p + (1 - p) * C⁻¹)) := by
  intro M Vs p q
  have hV : ∀ t, Vs t = lbValue γ ε C t := lb_optimalValue m hm γ ε C hγ hγ1 hε hεmax hC θ
  have hWid : ∀ i : Fin m, C⁻¹ * Vs (some i) + (1 - C⁻¹) * Vs none = lbW γ ε C := by
    intro i
    rw [hV, hV]
    simp only [lbValue, lbW]
    ring
  obtain ⟨hD, _, hVs, hWVs, _⟩ := lb_scalar hγ hγ1 hε hεmax hC
  obtain ⟨_, _, hQs⟩ := lbQfun_values m hm γ ε C hγ hγ1 hε hεmax hC θ
  obtain ⟨hfp, hmax⟩ := lb_optimalityFixedPoint m hm γ ε C hγ hγ1 hε hεmax hC θ
  have hg0 := lbGap_nonneg hγ hε
  have hg1 := lbGap_le hγ hγ1 hεmax
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro π i
    rw [hWid i]
    exact lb_policy_value_le m hm γ ε C hγ hγ1 hε hεmax hC θ π i
  · intro i
    rw [hWid i]
    have hgreedy : lbQfun m hm γ ε C hγ hγ1 hε hεmax hC θ (some i) (M.optimalGreedyAction (some i)) =
        lbValue γ ε C (some i) := by
      have h := M.optimalGreedyAction_max (some i)
      rw [hfp] at h
      rw [h]
      exact hmax (some i)
    rw [hQs] at hgreedy
    simp only [lbValue] at hgreedy
    have hprob : ∀ c, (M.optimalGreedyPolicy (some i)).prob c =
        if c = M.optimalGreedyAction (some i) then 1 else 0 := by
      intro c
      simp [DiscountedMDP.optimalGreedyPolicy, EnvironmentStage.pointMass]
    rw [hprob, hprob, hV]
    simp only [lbValue]
    set g := M.optimalGreedyAction (some i)
    have hx : ∀ y : ℝ, y < 1 → 0 < 1 - γ * y := by intro y hy; nlinarith
    have hp1 : lbP γ ε < 1 := by unfold lbP; linarith
    have hq1 : lbQ γ ε < 1 := by unfold lbQ; linarith
    cases hgθ : g == θ i with
    | true =>
      have hgeq : g = θ i := by simpa using hgθ
      rw [if_pos hgeq] at hgreedy
      have hne : (!θ i) ≠ g := by rw [hgeq]; cases θ i <;> simp
      rw [if_pos hgeq.symm, if_neg hne]
      simp only [mul_one, mul_zero, add_zero]
      rw [eq_div_iff (by have := hx _ hp1; exact this.ne')]
      linarith
    | false =>
      have hgne : g ≠ θ i := by simpa using hgθ
      rw [if_neg hgne] at hgreedy
      have hbool : ∀ x y : Bool, x ≠ y → x = !y := by decide
      have hgeq : g = !θ i := hbool _ _ hgne
      rw [if_neg (Ne.symm hgne), if_pos hgeq.symm]
      simp only [mul_one, mul_zero, zero_add]
      rw [eq_div_iff (by have := hx _ hq1; exact this.ne')]
      linarith
  · have h0 := lb_optimalGreedyAction_none m hm γ ε C hγ hγ1 hε hεmax hC θ
    simp [DiscountedMDP.optimalGreedyPolicy, EnvironmentStage.pointMass]
    exact h0
  · intro hεpos i
    obtain ⟨_, hs⟩ := lb_optimalGreedyAction m hm γ ε C hγ hγ1 hε hεmax hC θ hεpos
    simp [DiscountedMDP.optimalGreedyPolicy, EnvironmentStage.pointMass]
    exact (hs i).symm
  · rw [hV]; rfl
  · intro i
    rw [hV, hV]
    simp only [lbValue, lbVs, lbD, one_div]
    rfl

end StatisticalRL.OfflineRL.LowerBound
