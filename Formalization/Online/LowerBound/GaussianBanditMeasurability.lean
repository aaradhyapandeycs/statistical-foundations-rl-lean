import Formalization.Online.Bandit.UCBDefinitions

/-!
# Gaussian bandit histories: causality and measurability (Remark 5.12)
-/

open MeasureTheory Finset

noncomputable section

namespace StatisticalRL.GaussianBanditLB

variable {A : ℕ} {Seed : Type*}

section causal

variable (arm : (t : ℕ) → Seed → (Fin t → Fin A × ℝ) → Fin A) (μ : Fin A → ℝ) (σ : Seed)

/-- The history of the first `t` rounds reads only the noise rows `s < t`. -/
theorem history_congr {ζ ζ' : ℕ → Fin A → ℝ} :
    ∀ t, (∀ s, s < t → ζ s = ζ' s) → history arm μ σ ζ t = history arm μ σ ζ' t
  | 0, _ => rfl
  | t + 1, h => by
    have ih := history_congr t (fun s hs => h s (Nat.lt_succ_of_lt hs))
    simp only [history]
    rw [ih, h t (Nat.lt_succ_self t)]

theorem history_succ_of_lt (ζ : ℕ → Fin A → ℝ) (t i : ℕ) (hi : i < t) :
    history arm μ σ ζ (t + 1) ⟨i, Nat.lt_succ_of_lt hi⟩ = history arm μ σ ζ t ⟨i, hi⟩ := by
  simp only [history, Fin.snoc, hi, dif_pos]
  rfl

/-- Histories are prefixes of later histories. -/
theorem history_of_le (ζ : ℕ → Fin A → ℝ) (t : ℕ) :
    ∀ d i (hi : i < t), history arm μ σ ζ (t + d) ⟨i, Nat.lt_add_right d hi⟩ =
      history arm μ σ ζ t ⟨i, hi⟩
  | 0, _, _ => rfl
  | d + 1, i, hi => by
    rw [← history_of_le ζ t d i hi]
    exact history_succ_of_lt arm μ σ ζ (t + d) i (Nat.lt_add_right d hi)

/-- The restriction of the history at horizon `T` to its first `s` entries is the history at `s`. -/
theorem history_restrict (ζ : ℕ → Fin A → ℝ) {s T : ℕ} (hsT : s ≤ T) :
    (fun i : Fin s => history arm μ σ ζ T (Fin.castLE hsT i)) = history arm μ σ ζ s := by
  funext i
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hsT
  exact history_of_le arm μ σ ζ s d i.val i.isLt

end causal

section measurability

variable [MeasurableSpace Seed] {arm : (t : ℕ) → Seed → (Fin t → Fin A × ℝ) → Fin A}
  (μ : Fin A → ℝ)

theorem measurable_evalArm {X : Type*} [MeasurableSpace X] {ζ : X → ℕ → Fin A → ℝ}
    (hζ : Measurable ζ) {a : X → Fin A} (ha : Measurable a) (t : ℕ) :
    Measurable fun x => ζ x t (a x) := by
  have h1 : Measurable fun q : Fin A × X => ζ q.2 t q.1 := by
    apply measurable_from_prod_countable_right
    intro b
    exact (measurable_pi_apply b).comp ((measurable_pi_apply t).comp hζ)
  exact h1.comp (ha.prodMk measurable_id)

theorem measurable_history (harm : ∀ t, Measurable (Function.uncurry (arm t)))
    {X : Type*} [MeasurableSpace X] {σ : X → Seed} (hσ : Measurable σ)
    {ζ : X → ℕ → Fin A → ℝ} (hζ : Measurable ζ) :
    ∀ t, Measurable fun x => history arm μ (σ x) (ζ x) t
  | 0 => measurable_pi_lambda _ fun i => i.elim0
  | t + 1 => by
    have ih := measurable_history harm hσ hζ t
    have ha : Measurable fun x => arm t (σ x) (history arm μ (σ x) (ζ x) t) :=
      (harm t).comp (hσ.prodMk ih)
    have hp : Measurable fun x => (arm t (σ x) (history arm μ (σ x) (ζ x) t),
        μ (arm t (σ x) (history arm μ (σ x) (ζ x) t))
          + ζ x t (arm t (σ x) (history arm μ (σ x) (ζ x) t))) :=
      ha.prodMk ((measurable_of_countable μ).comp ha |>.add (measurable_evalArm hζ ha t))
    simp only [history]
    refine measurable_pi_lambda _ fun i => ?_
    induction i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using hp
    | cast j => simpa only [Fin.snoc_castSucc] using (measurable_pi_apply j).comp ih

theorem measurable_armAt (harm : ∀ t, Measurable (Function.uncurry (arm t)))
    {X : Type*} [MeasurableSpace X] {σ : X → Seed} (hσ : Measurable σ)
    {ζ : X → ℕ → Fin A → ℝ} (hζ : Measurable ζ) (t : ℕ) :
    Measurable fun x => armAt arm μ (σ x) (ζ x) t :=
  (harm t).comp (hσ.prodMk (measurable_history μ harm hσ hζ t))

theorem measurable_extendNoise (T : ℕ) :
    Measurable fun z : Fin T → Fin A → ℝ => Bandit.extendNoise z := by
  refine measurable_pi_lambda _ fun t => ?_
  by_cases h : t < T
  · simp only [Bandit.extendNoise, h, dif_pos]
    exact measurable_pi_apply _
  · simp only [Bandit.extendNoise, h, dif_neg, not_false_eq_true]
    exact measurable_const

theorem measurable_regret (harm : ∀ t, Measurable (Function.uncurry (arm t))) (T : ℕ) :
    Measurable fun ω : Seed × (Fin T → Fin A → ℝ) => regret arm μ T ω.1 ω.2 := by
  unfold regret
  refine measurable_const.sub (Finset.measurable_sum _ fun s _ => ?_)
  exact (measurable_of_countable μ).comp (measurable_armAt μ harm measurable_fst
    ((measurable_extendNoise T).comp measurable_snd) s)

/-- The pseudo-regret is integrable (it is measurable and bounded). -/
theorem integrable_regret (harm : ∀ t, Measurable (Function.uncurry (arm t))) (T : ℕ)
    (P : Measure (Seed × (Fin T → Fin A → ℝ))) [IsFiniteMeasure P] :
    Integrable (fun ω : Seed × (Fin T → Fin A → ℝ) => regret arm μ T ω.1 ω.2) P := by
  refine Integrable.of_bound (measurable_regret μ harm T).aestronglyMeasurable
    ((T : ℝ) * |⨆ a, μ a| + T * ∑ b, |μ b|) (Filter.Eventually.of_forall fun ω => ?_)
  unfold regret
  rw [Real.norm_eq_abs]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, Nat.abs_cast]
  · refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ s : Fin T, |μ (armAt arm μ ω.1 (Bandit.extendNoise ω.2) s)|
        ≤ ∑ _s : Fin T, ∑ b, |μ b| := Finset.sum_le_sum fun s _ =>
          Finset.single_le_sum (f := fun b => |μ b|) (fun b _ => abs_nonneg _) (mem_univ _)
      _ = T * ∑ b, |μ b| := by simp

end measurability

end StatisticalRL.GaussianBanditLB
