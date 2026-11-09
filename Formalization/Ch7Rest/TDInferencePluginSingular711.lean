import Formalization.Ch7Rest.TDInferencePlugin711
import Mathlib.LinearAlgebra.Matrix.Gershgorin

/-!
# `Ā_T` is singular exactly when a state is unsampled (SOURCE-ISSUES C47(4))

Source: `chapters/inference.tex:166–182` (`Ā_T`, `eq:defn-hat-Lambda` :180–182). C47(4): row `s`
of `Ā_T` vanishes when state `s` is unsampled, so the printed `Λ̂_T = Ā_T⁻¹Γ̂_TĀ_T⁻ᵀ` is undefined
on that event, which has positive probability whenever `S ≥ 2`.

* `aBar_apply` gives row `s` as `T⁻¹(1[j=s] n_s − γ m_{sj})`. If every state is sampled, then
  `diag − ∑|offdiag| = T⁻¹(1−γ)n_s > 0` in every row, and Mathlib's Gershgorin lemma
  `det_ne_zero_of_sum_row_lt_diag` gives `det Ā_T ≠ 0` (`aBar_det_ne_zero_of_sampled`).
  An unsampled state gives a zero row (`aBar_det_eq_zero_of_unsampled`). Hence
  `aBar_det_ne_zero_iff` (no hypothesis on `T`; at `T = 0` every state is unsampled).
* Under the i.i.d. law, `P(state s unsampled) = (1 − μ(s))^T` (`pathProb_unsampled`), so
  `(1 − μ(s))^T ≤ P(Ā_T singular) ≤ ∑_s (1 − μ(s))^T`, and `P(Ā_T singular) > 0` for every `T`
  when two distinct states have positive sampling probability (`pathProb_aBar_singular_pos`).
* Junk value: on that event Lean's `lambdaHat = 0` (`lambdaHat_eq_zero_of_det_eq_zero`); the
  printed `Λ̂_T` is undefined there.
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.TDInference

variable {State Action : Type} [Fintype State] [Fintype Action] [DecidableEq State]

omit [Fintype State] [Fintype Action] in
theorem pluginVisitCount_nonneg {T : ℕ} (ω : Fin T → Tuple State Action) (s : State) :
    0 ≤ pluginVisitCount ω s :=
  Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num

omit [Fintype State] [Fintype Action] in
theorem pluginTransCount_nonneg {T : ℕ} (ω : Fin T → Tuple State Action) (s j : State) :
    0 ≤ pluginTransCount ω s j :=
  Finset.sum_nonneg fun _ _ ↦ by split_ifs <;> norm_num

omit [Fintype Action] in
theorem sum_pluginTransCount {T : ℕ} (ω : Fin T → Tuple State Action) (s : State) :
    ∑ j, pluginTransCount ω s j = pluginVisitCount ω s := by
  simp only [pluginTransCount, pluginVisitCount]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  by_cases h : (ω t).1 = s <;> simp [h]

omit [Fintype State] [Fintype Action] in
theorem pluginVisitCount_pos_of_mem {T : ℕ} {ω : Fin T → Tuple State Action} {s : State} {t : Fin T}
    (ht : (ω t).1 = s) : 0 < pluginVisitCount ω s := by
  unfold pluginVisitCount
  refine lt_of_lt_of_le zero_lt_one ?_
  calc (1 : ℝ) = (if (ω t).1 = s then 1 else 0) := by rw [if_pos ht]
    _ ≤ ∑ u, (if (ω u).1 = s then (1 : ℝ) else 0) :=
      Finset.single_le_sum (f := fun u ↦ if (ω u).1 = s then (1 : ℝ) else 0)
        (fun u _ ↦ by dsimp only; split_ifs <;> norm_num) (Finset.mem_univ t)

/-- If every state is sampled, `Ā_T` is strictly diagonally dominant, hence invertible. -/
theorem aBar_det_ne_zero_of_sampled (M : DiscountedMDP State Action) {T : ℕ}
    (ω : Fin T → Tuple State Action) (h : ∀ s, ∃ t, (ω t).1 = s) : (aBar M ω).det ≠ 0 := by
  refine det_ne_zero_of_sum_row_lt_diag fun k ↦ ?_
  obtain ⟨t, ht⟩ := h k
  have hT : (0 : ℝ) < (T : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast t.pos)
  have hn : 0 < pluginVisitCount ω k := pluginVisitCount_pos_of_mem ht
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  have hoff : ∀ j ∈ Finset.univ.erase k,
      ‖aBar M ω k j‖ = (T : ℝ)⁻¹ * M.discount * pluginTransCount ω k j := by
    intro j hj
    have hc := pluginTransCount_nonneg ω k j
    rw [aBar_apply, if_neg (Finset.ne_of_mem_erase hj), Real.norm_eq_abs, zero_sub, mul_neg,
      abs_neg, abs_of_nonneg (by positivity)]
    ring
  rw [Finset.sum_congr rfl hoff, ← Finset.mul_sum, Finset.sum_erase_eq_sub (Finset.mem_univ k),
    sum_pluginTransCount, aBar_apply, if_pos rfl, Real.norm_eq_abs]
  refine lt_of_lt_of_le ?_ (le_abs_self _)
  have hkey : (T : ℝ)⁻¹ * (pluginVisitCount ω k - M.discount * pluginTransCount ω k k) -
      (T : ℝ)⁻¹ * M.discount * (pluginVisitCount ω k - pluginTransCount ω k k) =
      (T : ℝ)⁻¹ * ((1 - M.discount) * pluginVisitCount ω k) := by ring
  have hpos : 0 < (T : ℝ)⁻¹ * ((1 - M.discount) * pluginVisitCount ω k) :=
    mul_pos hT (mul_pos (sub_pos.2 hγ1) hn)
  linarith

/-- If state `s` is unsampled, row `s` of `Ā_T` is zero, so `det Ā_T = 0`. -/
theorem aBar_det_eq_zero_of_unsampled (M : DiscountedMDP State Action) {T : ℕ}
    (ω : Fin T → Tuple State Action) {s : State} (h : ∀ t, (ω t).1 ≠ s) :
    (aBar M ω).det = 0 := by
  refine Matrix.det_eq_zero_of_row_eq_zero s fun j ↦ ?_
  have hv : pluginVisitCount ω s = 0 := Finset.sum_eq_zero fun t _ ↦ if_neg (h t)
  have hm : pluginTransCount ω s j = 0 := Finset.sum_eq_zero fun t _ ↦ if_neg fun h' ↦ h t h'.1
  rw [aBar_apply, hv, hm]
  simp

/-- **C2.** `Ā_T` is invertible iff every state is sampled (C47(4)). -/
theorem aBar_det_ne_zero_iff (M : DiscountedMDP State Action) {T : ℕ}
    (ω : Fin T → Tuple State Action) : (aBar M ω).det ≠ 0 ↔ ∀ s, ∃ t, (ω t).1 = s := by
  refine ⟨fun hdet s ↦ ?_, aBar_det_ne_zero_of_sampled M ω⟩
  by_contra hs
  push_neg at hs
  exact hdet (aBar_det_eq_zero_of_unsampled M ω hs)

theorem setOf_aBar_det_eq_zero (M : DiscountedMDP State Action) (T : ℕ) :
    {ω : Fin T → Tuple State Action | (aBar M ω).det = 0} =
      {ω | ∃ s, ∀ t, (ω t).1 ≠ s} := by
  ext ω
  have h := aBar_det_ne_zero_iff M ω
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hdet
    by_contra hs
    push_neg at hs
    exact (h.2 hs) hdet
  · rintro ⟨s, hs⟩
    exact aBar_det_eq_zero_of_unsampled M ω hs

/-- On the sampled event `Ā_T⁻¹` is a genuine inverse (no junk value). -/
theorem aBar_mul_inv_of_sampled (M : DiscountedMDP State Action) {T : ℕ}
    (ω : Fin T → Tuple State Action) (h : ∀ s, ∃ t, (ω t).1 = s) :
    aBar M ω * (aBar M ω)⁻¹ = 1 :=
  Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (aBar_det_ne_zero_of_sampled M ω h))

/-! ## Probability of the singular event -/

/-- `∑_{x : x.1 = s} μ(s)π(a|s)P(s'|s,a) = μ(s)`. -/
theorem sum_tupleProb_fst_eq (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (s : State) :
    ∑ x : Tuple State Action, (if x.1 = s then tupleProb M π μ x else 0) = μ.prob s := by
  simp only [Fintype.sum_prod_type]
  have h : ∀ s₀ : State, ∑ a : Action, ∑ s' : State,
      (if s₀ = s then tupleProb M π μ (s₀, a, s') else 0) = if s₀ = s then μ.prob s₀ else 0 := by
    intro s₀
    split_ifs
    · simp only [tupleProb]
      simp_rw [← Finset.mul_sum, (M.transition _ _).sum_prob, mul_one, ← Finset.mul_sum,
        (π s₀).sum_prob, mul_one]
    · simp
  simp_rw [h]
  simp

/-- `P(∀ t, ω t ∈ B) = (∑_{x ∈ B} p(x))^T` under the i.i.d. law. -/
theorem pathProb_forall_mem (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (T : ℕ) (B : Finset (Tuple State Action)) :
    pathProb M π μ T {ω | ∀ t, ω t ∈ B} = (∑ x ∈ B, tupleProb M π μ x) ^ T := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin T ↦ B) (fun _ x ↦ tupleProb M π μ x)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have hpt : ∀ ω : Fin T → Tuple State Action,
      pathWeight M π μ ω * ({ω | ∀ t, ω t ∈ B} : Set _).indicator (fun _ ↦ (1 : ℝ)) ω =
        if ω ∈ Fintype.piFinset (fun _ : Fin T ↦ B) then ∏ t, tupleProb M π μ (ω t) else 0 := by
    intro ω
    by_cases hω : ∀ t, ω t ∈ B
    · rw [Set.indicator_of_mem (show ω ∈ {ω | ∀ t, ω t ∈ B} from hω),
        if_pos (Fintype.mem_piFinset.2 hω), mul_one]
      rfl
    · rw [Set.indicator_of_notMem (show ω ∉ {ω | ∀ t, ω t ∈ B} from hω),
        if_neg (fun h ↦ hω (Fintype.mem_piFinset.1 h)), mul_zero]
  rw [pathProb, Finset.sum_congr rfl fun ω _ ↦ hpt ω, Finset.sum_ite_mem, Finset.univ_inter, h]

/-- `P(state s unsampled in T draws) = (1 − μ(s))^T`. -/
theorem pathProb_unsampled (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (μ : FiniteDistribution State) (T : ℕ) (s : State) :
    pathProb M π μ T {ω | ∀ t, (ω t).1 ≠ s} = (1 - μ.prob s) ^ T := by
  have hset : {ω : Fin T → Tuple State Action | ∀ t, (ω t).1 ≠ s} =
      {ω | ∀ t, ω t ∈ Finset.univ.filter (fun x : Tuple State Action ↦ x.1 ≠ s)} := by
    ext ω; simp
  rw [hset, pathProb_forall_mem, Finset.sum_filter]
  congr 1
  rw [← sum_tupleProb_fst_eq M π μ s, ← sum_tupleProb M π μ, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  by_cases h : x.1 = s <;> simp [h]

omit [DecidableEq State] in
/-- Union bound for path events. -/
theorem pathProb_exists_le {ι : Type*} [Fintype ι] (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (T : ℕ)
    (E : ι → Set (Fin T → Tuple State Action)) :
    pathProb M π μ T {ω | ∃ i, ω ∈ E i} ≤ ∑ i, pathProb M π μ T (E i) := by
  simp only [pathProb]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun ω _ ↦ ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (pathWeight_nonneg M π μ ω)
  by_cases h : ∃ i, ω ∈ E i
  · obtain ⟨i, hi⟩ := h
    rw [Set.indicator_of_mem (show ω ∈ {ω | ∃ i, ω ∈ E i} from ⟨i, hi⟩)]
    calc (1 : ℝ) = (E i).indicator (fun _ ↦ (1 : ℝ)) ω := (Set.indicator_of_mem hi (fun _ ↦ (1 : ℝ))).symm
      _ ≤ ∑ j, (E j).indicator (fun _ ↦ (1 : ℝ)) ω :=
        Finset.single_le_sum (fun j _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)
          (Finset.mem_univ i)
  · rw [Set.indicator_of_notMem (show ω ∉ {ω | ∃ i, ω ∈ E i} from h)]
    exact Finset.sum_nonneg fun j _ ↦ Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _

/-- Lower bound: `(1 − μ(s))^T ≤ P(Ā_T singular)` for every state `s` (C47(4)). -/
theorem pathProb_aBar_singular_ge (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (T : ℕ) (s : State) :
    (1 - μ.prob s) ^ T ≤ pathProb M π μ T {ω | (aBar M ω).det = 0} := by
  rw [← pathProb_unsampled M π μ T s, setOf_aBar_det_eq_zero]
  exact pathProb_mono M π μ T fun ω hω ↦ ⟨s, hω⟩

/-- Upper bound: `P(Ā_T singular) ≤ ∑_s (1 − μ(s))^T` (C47(4)). -/
theorem pathProb_aBar_singular_le (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (T : ℕ) :
    pathProb M π μ T {ω | (aBar M ω).det = 0} ≤ ∑ s, (1 - μ.prob s) ^ T := by
  rw [setOf_aBar_det_eq_zero]
  have h := pathProb_exists_le M π μ T fun s : State ↦ {ω : Fin T → Tuple State Action |
    ∀ t, (ω t).1 ≠ s}
  simp only [Set.mem_setOf_eq, pathProb_unsampled] at h
  exact h

/-- If another state `s'` has positive sampling probability then `1 − μ(s) > 0`. -/
theorem one_sub_prob_pos (μ : FiniteDistribution State) {s s' : State} (hss : s ≠ s')
    (hs' : 0 < μ.prob s') : 0 < 1 - μ.prob s := by
  have h : ∑ x ∈ ({s, s'} : Finset State), μ.prob x ≤ ∑ x, μ.prob x :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ ↦ μ.prob_nonneg x
  rw [Finset.sum_pair hss, μ.sum_prob] at h
  linarith

/-- **C47(4) (E3).** With two distinct states of positive sampling probability, `Ā_T` is singular
with positive probability for every `T`, and on that event Lean's `lambdaHat` is the junk `0`. -/
theorem pathProb_aBar_singular_pos (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) {s s' : State}
    (hss : s ≠ s') (hs' : 0 < μ.prob s') (T : ℕ) :
    0 < pathProb M π μ T {ω | (aBar M ω).det = 0} :=
  lt_of_lt_of_le (pow_pos (one_sub_prob_pos μ hss hs') T) (pathProb_aBar_singular_ge M π μ T s)

/-- The junk event `{lambdaHat = 0}` contains the singular event, so it has probability at least
`(1 − μ(s))^T` for every `s`. -/
theorem pathProb_lambdaHat_eq_zero_ge (M : DiscountedMDP State Action)
    (π : StationaryPolicy State Action) (μ : FiniteDistribution State) (η₀ : ℝ) (V₀ : State → ℝ)
    (T : ℕ) (s : State) :
    (1 - μ.prob s) ^ T ≤ pathProb M π μ T {ω | lambdaHat M η₀ V₀ ω = 0} :=
  (pathProb_aBar_singular_ge M π μ T s).trans
    (pathProb_mono M π μ T fun _ hω ↦ lambdaHat_eq_zero_of_det_eq_zero M η₀ V₀ hω)

end StatisticalRL.Ch7Rest.TDInference
