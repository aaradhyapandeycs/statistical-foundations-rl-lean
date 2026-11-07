import Formalization.Online.Bandit.UCBChernoff

/-!
# UCB: expected pull count of a suboptimal arm

Step 2 of the proof of Theorem 5.1 (`chapters/bandits.tex:432–451`) with the repaired Step 1:
for a suboptimal arm `a`, `E N_T(a) ≤ 8 L / Δ(a)² + 2`, the printed
`eq:instance-dependent-ub-Na-proof-bandit`. The per-round bad event is a union over the
counts `k ∈ [1, t]` of the adaptive fixed-count tails, so the error term is
`Σ_{t<T} 2 t δ / T² ≤ δ ≤ 1`.
-/

open MeasureTheory ProbabilityTheory Finset

noncomputable section

namespace StatisticalRL.Bandit

variable {A : ℕ} (tie : ℕ → Finset (Fin A) → Fin A) (r : Fin A → ℝ)

theorem measurable_count_real {T : ℕ} (L : ℝ) (t : ℕ) (c : Fin A) :
    Measurable fun z : Fin T → Fin A → ℝ => (ucbCount tie L r (extendNoise z) t c : ℝ) :=
  measurable_from_nat.comp
    (measurable_ucbCount tie L r (fun z => extendNoise z) (fun t => measurable_extendNoise t) t c)

theorem integrable_count_real {T : ℕ} (L : ℝ) (t : ℕ) (c : Fin A) :
    Integrable (fun z : Fin T → Fin A → ℝ => (ucbCount tie L r (extendNoise z) t c : ℝ))
      (gaussianNoiseTable T A) := by
  refine Integrable.of_bound (measurable_count_real tie r L t c).aestronglyMeasurable t
    (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast ucbCount_le tie L r _ t c

/-- Expected pull count of a suboptimal arm (repaired Step 1 + Step 2,
`chapters/bandits.tex:400–451`): `E N_T(a) ≤ 8 L / Δ² + 2` with `L = log (T² / δ)` and
`Δ = r a⋆ - r a > 0` (`a⋆` any arm with larger mean).

At each 0-indexed round `t < T` the bad event is the union over counts `1 ≤ k ≤ t` (the count
before round `t` is at most `t`) of the two adaptive fixed-count tails for `a` and `a⋆`, each of
probability at most `δ / T²`. Hence `E N_T(a) ≤ ⌊m⌋ + 1 + β` with
`β = Σ_{t<T} 2 t δ / T² = δ (T - 1) / T ≤ δ ≤ 1` and `m = 8 L / Δ²`. The initialization bound
`N_t ≤ t - A + 1` is not used. See `docs/SOURCE-ISSUES.md#C36`. -/
theorem ucb_expected_count_le [NeZero A] (htie : ∀ t s, s.Nonempty → tie t s ∈ s)
    {T : ℕ} (hT : 1 ≤ T) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (a astar : Fin A) (hΔ : 0 < r astar - r a) :
    ∫ z, (ucbCount tie (Real.log ((T : ℝ) ^ 2 / δ)) r (extendNoise z) T a : ℝ)
        ∂gaussianNoiseTable T A
      ≤ 8 * Real.log ((T : ℝ) ^ 2 / δ) / (r astar - r a) ^ 2 + 2 := by
  classical
  set L := Real.log ((T : ℝ) ^ 2 / δ) with hLdef
  set μ := gaussianNoiseTable T A
  set Δ := r astar - r a with hΔdef
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hT2 : (1 : ℝ) ≤ (T : ℝ) ^ 2 / δ := by
    rw [le_div_iff₀ hδ0]
    have : (1 : ℝ) ≤ T := by exact_mod_cast hT
    nlinarith
  have hL : 0 ≤ L := Real.log_nonneg hT2
  have hexpL : Real.exp (-L) = δ / (T : ℝ) ^ 2 := by
    rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  set m := 8 * L / Δ ^ 2 with hmdef
  have hm0 : 0 ≤ m := by positivity
  set n := ⌊m⌋₊ + 1 with hndef
  have hζ : ∀ t, Measurable fun z : Fin T → Fin A → ℝ => extendNoise z t :=
    fun t => measurable_extendNoise t
  let cnt : ℕ → Fin A → (Fin T → Fin A → ℝ) → ℕ := fun t c z => ucbCount tie L r (extendNoise z) t c
  let Y : ℕ → Fin A → (Fin T → Fin A → ℝ) → ℝ := fun k c z =>
    ucbNoiseSum tie L r (extendNoise z) T k c
  let Ep : ℕ → Set (Fin T → Fin A → ℝ) := fun k =>
    {z | k ≤ cnt T a z ∧ (k : ℝ) * Real.sqrt (2 * L / k) ≤ 1 * Y k a z}
  let Em : ℕ → Set (Fin T → Fin A → ℝ) := fun k =>
    {z | k ≤ cnt T astar z ∧ (k : ℝ) * Real.sqrt (2 * L / k) ≤ (-1) * Y k astar z}
  have hmeasE : ∀ (k : ℕ) (c : Fin A) (σ : ℝ), MeasurableSet
      {z : Fin T → Fin A → ℝ | k ≤ cnt T c z ∧ (k : ℝ) * Real.sqrt (2 * L / k) ≤ σ * Y k c z} := by
    intro k c σ
    have h1 : MeasurableSet {z : Fin T → Fin A → ℝ | k ≤ cnt T c z} :=
      measurable_ucbCount tie L r (fun z => extendNoise z) hζ T c
        (MeasurableSet.of_discrete (s := {n : ℕ | k ≤ n}))
    have h2 : MeasurableSet {z : Fin T → Fin A → ℝ |
        (k : ℝ) * Real.sqrt (2 * L / k) ≤ σ * Y k c z} :=
      measurableSet_le measurable_const
        ((measurable_ucbNoiseSum tie L r (fun z => extendNoise z) hζ T k c).const_mul σ)
    exact h1.inter h2
  have hEp : ∀ k, MeasurableSet (Ep k) := fun k => hmeasE k a 1
  have hEm : ∀ k, MeasurableSet (Em k) := fun k => hmeasE k astar (-1)
  -- pathwise count bound
  let ind : Set (Fin T → Fin A → ℝ) → (Fin T → Fin A → ℝ) → ℝ := fun E z => E.indicator 1 z
  have hind0 : ∀ E z, 0 ≤ ind E z := fun E z => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  let rhs : (Fin T → Fin A → ℝ) → ℝ := fun z =>
    (n : ℝ) + ∑ s ∈ range T, ∑ k ∈ Icc 1 s, (ind (Ep k) z + ind (Em k) z)
  have hpath : ∀ z, (cnt T a z : ℝ) ≤ rhs z := by
    intro z
    have hsplit : (cnt T a z : ℝ) = (∑ s ∈ range T,
        if ucbArm tie L r (extendNoise z) s = a ∧ cnt s a z < n then (1 : ℝ) else 0)
        + ∑ s ∈ range T,
          if ucbArm tie L r (extendNoise z) s = a ∧ n ≤ cnt s a z then (1 : ℝ) else 0 := by
      simp only [cnt]
      rw [ucbCount_eq_sum, ← sum_add_distrib]
      push_cast
      apply sum_congr rfl
      intro s _
      by_cases h1 : ucbArm tie L r (extendNoise z) s = a
      · by_cases h2 : ucbCount tie L r (extendNoise z) s a < n
        · simp [h1, h2, not_le.mpr h2]
        · simp [h1, h2, le_of_not_gt h2]
      · simp [h1]
    have hfirst : (∑ s ∈ range T,
        if ucbArm tie L r (extendNoise z) s = a ∧ cnt s a z < n then (1 : ℝ) else 0) ≤ n := by
      have := sum_pull_below_real tie L r (extendNoise z) n T a
      simp only [cnt]
      rw [this]
      exact_mod_cast min_le_left _ _
    rw [hsplit]
    simp only [rhs]
    apply add_le_add hfirst
    apply sum_le_sum
    intro s hs
    have hsT : s ≤ T := (mem_range.mp hs).le
    split_ifs with hcond
    · obtain ⟨hpull, hn⟩ := hcond
      have hmlt : m < (ucbCount tie L r (extendNoise z) s a : ℝ) := by
        have h1 : m < (n : ℝ) := by
          simp only [n]; push_cast; exact Nat.lt_floor_add_one m
        have h2 : (n : ℝ) ≤ cnt s a z := by exact_mod_cast hn
        exact lt_of_lt_of_le h1 h2
      rcases step1_pathwise tie L r (extendNoise z) htie hL hsT a astar hΔ hpull hmlt with
        ⟨hk1, hks, hY⟩ | ⟨hk1, hks, hY⟩
      · have hmemk : ucbCount tie L r (extendNoise z) s a ∈ Icc 1 s := mem_Icc.mpr ⟨hk1, hks⟩
        have hzE : z ∈ Ep (ucbCount tie L r (extendNoise z) s a) :=
          ⟨ucbCount_mono tie L r (extendNoise z) a hsT, by rw [one_mul]; exact hY.le⟩
        calc (1 : ℝ) = ind (Ep (ucbCount tie L r (extendNoise z) s a)) z := by
              simp [ind, Set.indicator_of_mem hzE]
          _ ≤ ind (Ep (ucbCount tie L r (extendNoise z) s a)) z
              + ind (Em (ucbCount tie L r (extendNoise z) s a)) z :=
              le_add_of_nonneg_right (hind0 _ _)
          _ ≤ ∑ k ∈ Icc 1 s, (ind (Ep k) z + ind (Em k) z) :=
              single_le_sum (f := fun k => ind (Ep k) z + ind (Em k) z)
                (fun k _ => add_nonneg (hind0 _ _) (hind0 _ _)) hmemk
      · have hmemk : ucbCount tie L r (extendNoise z) s astar ∈ Icc 1 s :=
          mem_Icc.mpr ⟨hk1, hks⟩
        have hzE : z ∈ Em (ucbCount tie L r (extendNoise z) s astar) :=
          ⟨ucbCount_mono tie L r (extendNoise z) astar hsT, by
            simp only [Y]; linarith⟩
        calc (1 : ℝ) = ind (Em (ucbCount tie L r (extendNoise z) s astar)) z := by
              simp [ind, Set.indicator_of_mem hzE]
          _ ≤ ind (Ep (ucbCount tie L r (extendNoise z) s astar)) z
              + ind (Em (ucbCount tie L r (extendNoise z) s astar)) z :=
              le_add_of_nonneg_left (hind0 _ _)
          _ ≤ ∑ k ∈ Icc 1 s, (ind (Ep k) z + ind (Em k) z) :=
              single_le_sum (f := fun k => ind (Ep k) z + ind (Em k) z)
                (fun k _ => add_nonneg (hind0 _ _) (hind0 _ _)) hmemk
    · exact sum_nonneg (fun k _ => add_nonneg (hind0 _ _) (hind0 _ _))
  -- integrate
  have hindint : ∀ E, MeasurableSet E → Integrable (ind E) μ := fun E hE =>
    (integrable_const (1 : ℝ)).indicator hE
  have hint_inner : ∀ s, Integrable (fun z => ∑ k ∈ Icc 1 s, (ind (Ep k) z + ind (Em k) z)) μ :=
    fun s => integrable_finset_sum _ (fun k _ => (hindint _ (hEp k)).add (hindint _ (hEm k)))
  have hint_sum : Integrable
      (fun z => ∑ s ∈ range T, ∑ k ∈ Icc 1 s, (ind (Ep k) z + ind (Em k) z)) μ :=
    integrable_finset_sum _ (fun s _ => hint_inner s)
  have hint_rhs : Integrable rhs μ := (integrable_const _).add hint_sum
  have hrhs : ∫ z, rhs z ∂μ
      = n + ∑ s ∈ range T, ∑ k ∈ Icc 1 s, (μ.real (Ep k) + μ.real (Em k)) := by
    simp only [rhs]
    rw [integral_add (integrable_const _) hint_sum, integral_const, smul_eq_mul,
      probReal_univ, one_mul, integral_finset_sum _ (fun s _ => hint_inner s)]
    congr 1
    apply sum_congr rfl; intro s _
    rw [integral_finset_sum (f := fun k z => ind (Ep k) z + ind (Em k) z) _
      (fun k _ => ((hindint _ (hEp k)).add (hindint _ (hEm k))))]
    apply sum_congr rfl; intro k _
    rw [integral_add (hindint _ (hEp k)) (hindint _ (hEm k))]
    simp only [ind]
    rw [integral_indicator_one (hEp k), integral_indicator_one (hEm k)]
  have hbound : ∀ s ∈ range T, ∑ k ∈ Icc 1 s, (μ.real (Ep k) + μ.real (Em k))
      ≤ s * (2 * (δ / (T : ℝ) ^ 2)) := by
    intro s _
    have : ∀ k ∈ Icc 1 s, μ.real (Ep k) + μ.real (Em k) ≤ 2 * (δ / (T : ℝ) ^ 2) := by
      intro k hk
      have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
      have h1 := ucb_first_noise_tail tie L r a k hk1 1 (by norm_num) L hL (T := T)
      have h2 := ucb_first_noise_tail tie L r astar k hk1 (-1) (by norm_num) L hL (T := T)
      rw [hexpL] at h1 h2
      have e1 : μ.real (Ep k) ≤ δ / (T : ℝ) ^ 2 := h1
      have e2 : μ.real (Em k) ≤ δ / (T : ℝ) ^ 2 := h2
      linarith
    calc ∑ k ∈ Icc 1 s, (μ.real (Ep k) + μ.real (Em k))
        ≤ ∑ k ∈ Icc 1 s, 2 * (δ / (T : ℝ) ^ 2) := sum_le_sum this
      _ = s * (2 * (δ / (T : ℝ) ^ 2)) := by
        rw [sum_const, Nat.card_Icc, nsmul_eq_mul]; simp
  have hsumid : (∑ s ∈ range T, (s : ℝ)) * 2 ≤ (T : ℝ) ^ 2 := by
    have h := Finset.sum_range_id_mul_two T
    have h' : (∑ i ∈ range T, i) * 2 ≤ T * T := by
      rw [h]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have : ((∑ i ∈ range T, i) * 2 : ℕ) ≤ (T * T : ℕ) := h'
    calc (∑ s ∈ range T, (s : ℝ)) * 2 = (((∑ i ∈ range T, i) * 2 : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((T * T : ℕ) : ℝ) := by exact_mod_cast this
      _ = (T : ℝ) ^ 2 := by push_cast; ring
  have hfinal : ∑ s ∈ range T, ∑ k ∈ Icc 1 s, (μ.real (Ep k) + μ.real (Em k)) ≤ δ := by
    calc ∑ s ∈ range T, ∑ k ∈ Icc 1 s, (μ.real (Ep k) + μ.real (Em k))
        ≤ ∑ s ∈ range T, (s : ℝ) * (2 * (δ / (T : ℝ) ^ 2)) := sum_le_sum hbound
      _ = (∑ s ∈ range T, (s : ℝ)) * 2 * (δ / (T : ℝ) ^ 2) := by rw [← sum_mul]; ring
      _ ≤ (T : ℝ) ^ 2 * (δ / (T : ℝ) ^ 2) := by gcongr
      _ = δ := by field_simp
  have hnm : (n : ℝ) ≤ m + 1 := by
    simp only [n]; push_cast; linarith [Nat.floor_le hm0]
  calc ∫ z, (ucbCount tie L r (extendNoise z) T a : ℝ) ∂μ ≤ ∫ z, rhs z ∂μ :=
        integral_mono (integrable_count_real tie r L T a) hint_rhs hpath
    _ = n + ∑ s ∈ range T, ∑ k ∈ Icc 1 s, (μ.real (Ep k) + μ.real (Em k)) := hrhs
    _ ≤ m + 1 + δ := by linarith
    _ ≤ m + 2 := by linarith

end StatisticalRL.Bandit
