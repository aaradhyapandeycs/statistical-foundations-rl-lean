import Formalization.Ch7Rest.LowerBound710
import Formalization.MDP.FixedPoint
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Theorem 7.10 under the reading "for some `c₀`" inside the hypothesis is false (SOURCE-ISSUES C42)

Under this reading the hypothesis `∃ c₀ > 0, C_round ≤ c₀ / ((1-γ) log² N)` always holds
(`log N > 0` for `N ≥ 16`). Take `γ = 5/6`, `S = 4`, `A = 2`, `B = 1`, the constant rate
`η = 1/2`, and synchronization at every iteration (`𝒞 = {1,…,T}`). For every MDP, pathwise,
with `ρ = 1 - η(1-γ)` and `E_t = max_{k,s,a} |Q_t^k(s,a) - Q⋆(s,a)|`,
`E_t ≤ ρ E_{t-1} + ηγ ∑_{s,a} |noise_t(s,a)|`, where
`noise_t(s,a) = (1/K) ∑_k (V⋆(s_t^k(s,a)) - P(·|s,a)V⋆)` involves only the *fixed* `V⋆`.
The noise terms are averages of `K` independent centred variables bounded by `1/(1-γ)`, so
`E|noise| ≤ (a/(K(1-γ)²) + 1/a)/2` for every `a > 0`. Hence
`E‖Q̂ - Q⋆‖_∞ ≤ ρ^T/(1-γ) + ηγ T S A (a/(K(1-γ)²) + 1/a)/2`. Choosing `T` large (the first term
decays geometrically, the printed bound only polynomially), then `a`, then `K`, the printed
bound fails for every `C_γ`, for every MDP instance.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace StatisticalRL.Ch7Rest.FedGeneric

open StatisticalRL.Ch7Rest.Fed (greedyValue)

variable {State Action : Type} [Fintype State] [Fintype Action]

local instance fedInnerStateMeasurable : MeasurableSpace State := ⊤

section Pathwise

variable [Nonempty State] [Nonempty Action]

omit [Fintype State] [Nonempty State] in
theorem greedyValue_sub_le (Q Q' : State → Action → ℝ) (x : State) (d : ℝ)
    (h : ∀ a, |Q x a - Q' x a| ≤ d) : |greedyValue Q x - greedyValue Q' x| ≤ d := by
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    apply ciSup_le
    intro a
    have h1 := (abs_sub_le_iff.mp (h a)).1
    have h2 : Q' x a ≤ greedyValue Q' x := le_ciSup (Finite.bddAbove_range _) a
    linarith
  · rw [sub_le_iff_le_add]
    apply ciSup_le
    intro a
    have h1 := (abs_sub_le_iff.mp (h a)).2
    have h2 : Q x a ≤ greedyValue Q x := le_ciSup (Finite.bddAbove_range _) a
    linarith

/-- `V⋆ = max_a Q⋆(·,a)`. -/
noncomputable def vStar (M : DiscountedMDP State Action) : State → ℝ :=
  greedyValue M.optimalityFixedPoint

omit [Nonempty State] in
theorem optimalityFixedPoint_bellman (M : DiscountedMDP State Action) (s : State) (a : Action) :
    M.optimalityFixedPoint s a =
      M.reward s a + M.discount * (M.transition s a).expectation (vStar M) := by
  have h := congrFun (congrFun M.optimalityFixedPoint_spec s) a
  rw [← h]
  simp only [DiscountedMDP.qOptimality, actionMaximum, Finset.sup'_univ_eq_ciSup, vStar]
  rfl

omit [Nonempty State] in
theorem vStar_bounds (M : DiscountedMDP State Action) (x : State) :
    0 ≤ vStar M x ∧ vStar M x ≤ 1 / (1 - M.discount) := by
  obtain ⟨a₀⟩ := (inferInstance : Nonempty Action)
  constructor
  · exact le_trans (M.optimalityFixedPoint_bounds x a₀).1
      (le_ciSup (Finite.bddAbove_range _) a₀)
  · exact ciSup_le fun a ↦ (M.optimalityFixedPoint_bounds x a).2

omit [Nonempty State] [Nonempty Action] in
theorem expectation_bounds (d : FiniteDistribution State) (f : State → ℝ) (lo hi : ℝ)
    (h : ∀ x, lo ≤ f x ∧ f x ≤ hi) : lo ≤ d.expectation f ∧ d.expectation f ≤ hi := by
  have hs := d.sum_prob
  constructor
  · calc lo = ∑ x, d.prob x * lo := by rw [← Finset.sum_mul, hs, one_mul]
      _ ≤ _ := Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (h x).1 (d.prob_nonneg x)
  · calc d.expectation f ≤ ∑ x, d.prob x * hi :=
          Finset.sum_le_sum fun x _ ↦ mul_le_mul_of_nonneg_left (h x).2 (d.prob_nonneg x)
      _ = hi := by rw [← Finset.sum_mul, hs, one_mul]

/-- Sup-norm error over all agents and state-action pairs at iteration `t` (`B = 1`). -/
noncomputable def runErr (M : DiscountedMDP State Action) (η : ℕ → ℝ) (K : ℕ) (𝒞 : Finset ℕ)
    (sm : ℕ → Fin K → State → Action → Fin 1 → State) (t : ℕ) : ℝ :=
  ⨆ p : Fin K × State × Action,
    |genericRun M η K 1 𝒞 sm t p.1 p.2.1 p.2.2 - M.optimalityFixedPoint p.2.1 p.2.2|

/-- Centred sampling noise of the fixed `V⋆` at iteration `t`. -/
noncomputable def fedNoise (M : DiscountedMDP State Action) (K : ℕ)
    (sm : ℕ → Fin K → State → Action → Fin 1 → State) (t : ℕ) (s : State) (a : Action) : ℝ :=
  (1 / (K : ℝ)) * ∑ j, (vStar M (sm t j s a 0) - (M.transition s a).expectation (vStar M))

/-- Sum of the absolute noise over state-action pairs. -/
noncomputable def noiseSum (M : DiscountedMDP State Action) (K : ℕ)
    (sm : ℕ → Fin K → State → Action → Fin 1 → State) (t : ℕ) : ℝ :=
  ∑ s, ∑ a, |fedNoise M K sm t s a|

omit [Nonempty State] [Nonempty Action] in
theorem le_runErr (M : DiscountedMDP State Action) (η : ℕ → ℝ) (K : ℕ) (𝒞 : Finset ℕ)
    (sm : ℕ → Fin K → State → Action → Fin 1 → State) (t : ℕ) (k : Fin K) (s : State)
    (a : Action) :
    |genericRun M η K 1 𝒞 sm t k s a - M.optimalityFixedPoint s a| ≤ runErr M η K 𝒞 sm t :=
  le_ciSup (f := fun p : Fin K × State × Action ↦
    |genericRun M η K 1 𝒞 sm t p.1 p.2.1 p.2.2 - M.optimalityFixedPoint p.2.1 p.2.2|)
    (Finite.bddAbove_range _) (k, s, a)

omit [Nonempty State] in
/-- One synchronized step: `|Q_{t+1}^k - Q⋆| ≤ ρ E_t + ηγ |noise_{t+1}|`. -/
theorem step_bound (M : DiscountedMDP State Action) (η : ℕ → ℝ) (K : ℕ) (hK : 1 ≤ K)
    (𝒞 : Finset ℕ) (sm : ℕ → Fin K → State → Action → Fin 1 → State) (t : ℕ)
    (ht : t + 1 ∈ 𝒞) (hη0 : 0 ≤ η (t + 1)) (hη1 : η (t + 1) ≤ 1) (k : Fin K) (s : State)
    (a : Action) :
    |genericRun M η K 1 𝒞 sm (t + 1) k s a - M.optimalityFixedPoint s a| ≤
      (1 - η (t + 1) + η (t + 1) * M.discount) * runErr M η K 𝒞 sm t +
        η (t + 1) * M.discount * |fedNoise M K sm (t + 1) s a| := by
  have hK' : (K : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  set e := η (t + 1)
  set E := runErr M η K 𝒞 sm t
  set Q := genericRun M η K 1 𝒞 sm t
  let x : Fin K → State := fun j ↦ sm (t + 1) j s a 0
  let A : Fin K → ℝ := fun j ↦ (1 - e) * (Q j s a - M.optimalityFixedPoint s a) +
    e * M.discount * (greedyValue (Q j) (x j) - vStar M (x j))
  have h1 : genericRun M η K 1 𝒞 sm (t + 1) k s a =
      (1 / (K : ℝ)) * ∑ j, ((1 - e) * Q j s a +
        e * (M.reward s a + M.discount * greedyValue (Q j) (x j))) := by
    simp only [genericRun, genericStep, if_pos ht, batchUpdate, Nat.cast_one, div_one,
      Fin.sum_univ_one, x, Q, e]
  have h2 : genericRun M η K 1 𝒞 sm (t + 1) k s a - M.optimalityFixedPoint s a =
      (1 / (K : ℝ)) * ∑ j, A j + e * M.discount * fedNoise M K sm (t + 1) s a := by
    rw [h1]
    have hb := optimalityFixedPoint_bellman M s a
    have hc : M.optimalityFixedPoint s a =
        (1 / (K : ℝ)) * ∑ _j : Fin K, M.optimalityFixedPoint s a := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hL : (1 / (K : ℝ)) * ∑ j, ((1 - e) * Q j s a +
          e * (M.reward s a + M.discount * greedyValue (Q j) (x j))) -
          M.optimalityFixedPoint s a =
        (1 / (K : ℝ)) * ∑ j, ((1 - e) * Q j s a +
          e * (M.reward s a + M.discount * greedyValue (Q j) (x j)) -
            M.optimalityFixedPoint s a) := by
      rw [Finset.sum_sub_distrib, mul_sub, ← hc]
    have hR : (1 / (K : ℝ)) * ∑ j, A j + e * M.discount * fedNoise M K sm (t + 1) s a =
        (1 / (K : ℝ)) * ∑ j, (A j + e * M.discount *
          (vStar M (sm (t + 1) j s a 0) - (M.transition s a).expectation (vStar M))) := by
      simp only [fedNoise, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hL, hR]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [A, x]
    rw [hb]
    ring
  have hA : ∀ j, |A j| ≤ (1 - e + e * M.discount) * E := by
    intro j
    have hq := le_runErr M η K 𝒞 sm t j s a
    have hv : |greedyValue (Q j) (x j) - vStar M (x j)| ≤ E :=
      greedyValue_sub_le _ _ _ _ fun a' ↦ le_runErr M η K 𝒞 sm t j (x j) a'
    have hγ0 : 0 ≤ M.discount := M.discount_nonneg
    calc |A j| ≤ |(1 - e) * (Q j s a - M.optimalityFixedPoint s a)| +
          |e * M.discount * (greedyValue (Q j) (x j) - vStar M (x j))| := abs_add_le _ _
      _ = (1 - e) * |Q j s a - M.optimalityFixedPoint s a| +
          e * M.discount * |greedyValue (Q j) (x j) - vStar M (x j)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - e),
            abs_of_nonneg (mul_nonneg hη0 hγ0)]
      _ ≤ (1 - e) * E + e * M.discount * E := by
          gcongr
          · linarith
      _ = (1 - e + e * M.discount) * E := by ring
  have hsum : |(1 / (K : ℝ)) * ∑ j, A j| ≤ (1 - e + e * M.discount) * E := by
    rw [abs_mul, abs_of_pos (by positivity)]
    calc 1 / (K : ℝ) * |∑ j, A j| ≤ 1 / (K : ℝ) * ∑ j, |A j| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ ≤ 1 / (K : ℝ) * ∑ _j : Fin K, (1 - e + e * M.discount) * E :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ ↦ hA j) (by positivity)
      _ = (1 - e + e * M.discount) * E := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  rw [h2]
  calc |(1 / (K : ℝ)) * ∑ j, A j + e * M.discount * fedNoise M K sm (t + 1) s a| ≤
        |(1 / (K : ℝ)) * ∑ j, A j| + |e * M.discount * fedNoise M K sm (t + 1) s a| :=
          abs_add_le _ _
    _ ≤ (1 - e + e * M.discount) * E + e * M.discount * |fedNoise M K sm (t + 1) s a| := by
        rw [abs_mul (e * M.discount), abs_of_nonneg (mul_nonneg hη0 M.discount_nonneg)]
        linarith

omit [Nonempty State] [Nonempty Action] in
theorem noise_le_noiseSum (M : DiscountedMDP State Action) (K : ℕ)
    (sm : ℕ → Fin K → State → Action → Fin 1 → State) (t : ℕ) (s : State) (a : Action) :
    |fedNoise M K sm t s a| ≤ noiseSum M K sm t := by
  unfold noiseSum
  calc |fedNoise M K sm t s a| ≤ ∑ a', |fedNoise M K sm t s a'| :=
        Finset.single_le_sum (f := fun a' ↦ |fedNoise M K sm t s a'|)
          (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ a)
    _ ≤ ∑ s', ∑ a', |fedNoise M K sm t s' a'| :=
        Finset.single_le_sum (f := fun s' ↦ ∑ a', |fedNoise M K sm t s' a'|)
          (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) (Finset.mem_univ s)

omit [Nonempty State] [Nonempty Action] in
theorem noiseSum_nonneg (M : DiscountedMDP State Action) (K : ℕ)
    (sm : ℕ → Fin K → State → Action → Fin 1 → State) (t : ℕ) : 0 ≤ noiseSum M K sm t :=
  Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ abs_nonneg _

/-- Unrolled bound with a constant rate `η ∈ [0,1]` and synchronization at every
iteration `1, …, T`. -/
theorem runErr_unroll (M : DiscountedMDP State Action) (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (K : ℕ) (hK : 1 ≤ K) (𝒞 : Finset ℕ) (T : ℕ) (h𝒞 : ∀ t, 1 ≤ t → t ≤ T → t ∈ 𝒞)
    (sm : ℕ → Fin K → State → Action → Fin 1 → State) (t : ℕ) (ht : t ≤ T) :
    runErr M (fun _ ↦ η) K 𝒞 sm t ≤
      (1 - η + η * M.discount) ^ t * (1 / (1 - M.discount)) +
        η * M.discount * ∑ u ∈ Finset.range t, noiseSum M K sm (u + 1) := by
  have hγ0 := M.discount_nonneg
  have hγ1 := M.discount_lt_one
  have hρ0 : 0 ≤ 1 - η + η * M.discount := by nlinarith
  have hρ1 : 1 - η + η * M.discount ≤ 1 := by nlinarith
  haveI : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  induction t with
  | zero =>
    simp only [pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, mul_zero, add_zero]
    apply ciSup_le
    intro p
    simp only [genericRun, zero_sub, abs_neg]
    rw [abs_of_nonneg (M.optimalityFixedPoint_bounds _ _).1]
    exact (M.optimalityFixedPoint_bounds _ _).2
  | succ t ih =>
    have ih := ih (by omega)
    have hstep : runErr M (fun _ ↦ η) K 𝒞 sm (t + 1) ≤
        (1 - η + η * M.discount) * runErr M (fun _ ↦ η) K 𝒞 sm t +
          η * M.discount * noiseSum M K sm (t + 1) := by
      apply ciSup_le
      intro p
      have h := step_bound M (fun _ ↦ η) K hK 𝒞 sm t (h𝒞 (t + 1) (by omega) ht) hη0 hη1
        p.1 p.2.1 p.2.2
      have hn := noise_le_noiseSum M K sm (t + 1) p.2.1 p.2.2
      have : η * M.discount * |fedNoise M K sm (t + 1) p.2.1 p.2.2| ≤
          η * M.discount * noiseSum M K sm (t + 1) :=
        mul_le_mul_of_nonneg_left hn (mul_nonneg hη0 hγ0)
      linarith
    have hS0 : 0 ≤ ∑ u ∈ Finset.range t, noiseSum M K sm (u + 1) :=
      Finset.sum_nonneg fun _ _ ↦ noiseSum_nonneg M K sm _
    have hX0 : 0 ≤ η * M.discount * ∑ u ∈ Finset.range t, noiseSum M K sm (u + 1) :=
      mul_nonneg (mul_nonneg hη0 hγ0) hS0
    rw [Finset.sum_range_succ, mul_add, pow_succ]
    calc runErr M (fun _ ↦ η) K 𝒞 sm (t + 1)
        ≤ (1 - η + η * M.discount) * runErr M (fun _ ↦ η) K 𝒞 sm t +
          η * M.discount * noiseSum M K sm (t + 1) := hstep
      _ ≤ (1 - η + η * M.discount) * ((1 - η + η * M.discount) ^ t * (1 / (1 - M.discount)) +
            η * M.discount * ∑ u ∈ Finset.range t, noiseSum M K sm (u + 1)) +
          η * M.discount * noiseSum M K sm (t + 1) := by gcongr
      _ ≤ _ := by nlinarith

/-- The output error is at most the agent-wise error. -/
theorem supError_output_le (M : DiscountedMDP State Action) (η : ℕ → ℝ) (K : ℕ) (hK : 1 ≤ K)
    (𝒞 : Finset ℕ) (sm : ℕ → Fin K → State → Action → Fin 1 → State) (T : ℕ) :
    supError (genericOutput M η K 1 𝒞 sm T) M.optimalityFixedPoint ≤ runErr M η K 𝒞 sm T := by
  have hK' : (K : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  apply ciSup_le
  intro s
  apply ciSup_le
  intro a
  have hc : M.optimalityFixedPoint s a =
      (1 / (K : ℝ)) * ∑ _k : Fin K, M.optimalityFixedPoint s a := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  simp only [genericOutput]
  rw [hc, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul, abs_of_pos (by positivity)]
  calc 1 / (K : ℝ) * |∑ k, (genericRun M η K 1 𝒞 sm T k s a - M.optimalityFixedPoint s a)|
      ≤ 1 / (K : ℝ) * ∑ k, |genericRun M η K 1 𝒞 sm T k s a - M.optimalityFixedPoint s a| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ 1 / (K : ℝ) * ∑ _k : Fin K, runErr M η K 𝒞 sm T :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦ le_runErr M η K 𝒞 sm T k s a)
          (by positivity)
    _ = runErr M η K 𝒞 sm T := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

end Pathwise

section Probability

variable (M : DiscountedMDP State Action) (T K : ℕ)

theorem fed_coord_integral (i : FedIndex State Action T K 1) (f : State → ℝ) :
    ∫ data, f (data i) ∂fedSamplingLaw M T K 1 = (M.transition i.2.1.1 i.2.1.2).expectation f := by
  have hmap : (fedSamplingLaw M T K 1).map (fun data ↦ data i) =
      (M.transition i.2.1.1 i.2.1.2).rowMeasure :=
    (measurePreserving_eval (fun i : FedIndex State Action T K 1 ↦
      (M.transition i.2.1.1 i.2.1.2).rowMeasure) i).map_eq
  rw [← FiniteDistribution.rowMeasure_integral, ← hmap,
    integral_map (measurable_pi_apply i).aemeasurable Integrable.of_finite.aestronglyMeasurable]

theorem fed_coord_indep_integral (i i' : FedIndex State Action T K 1) (h : i ≠ i')
    (f g : State → ℝ) :
    ∫ data, f (data i) * g (data i') ∂fedSamplingLaw M T K 1 =
      (∫ data, f (data i) ∂fedSamplingLaw M T K 1) *
        (∫ data, g (data i') ∂fedSamplingLaw M T K 1) := by
  have hind : iIndepFun (fun i (data : FedSamples State Action T K 1) ↦ data i)
      (fedSamplingLaw M T K 1) :=
    iIndepFun_pi (fun _ ↦ measurable_id.aemeasurable)
  have hp := (hind.indepFun h).comp (measurable_of_countable f) (measurable_of_countable g)
  exact hp.integral_mul_eq_mul_integral (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aestronglyMeasurable

variable [Nonempty State] [Nonempty Action]

omit [Nonempty State] [Nonempty Action] in
/-- The noise at iteration `t ∈ {1,…,T}` in terms of the sample coordinates. -/
theorem fedNoise_extend (data : FedSamples State Action T K 1) (t : ℕ) (ht : 0 < t ∧ t ≤ T)
    (s : State) (a : Action) :
    fedNoise M K (fedSamplesExtend M T K 1 data) t s a =
      (1 / (K : ℝ)) * ∑ j, (vStar M (data ((⟨t - 1, by omega⟩, j), (s, a), 0)) -
        (M.transition s a).expectation (vStar M)) := by
  simp only [fedNoise, fedSamplesExtend, dif_pos ht]

omit [Nonempty State] in
/-- `E|noise_t(s,a)| ≤ (a/(K(1-γ)²) + 1/a)/2` for every `a > 0`. -/
theorem fedNoise_abs_integral_le (hK : 1 ≤ K) (t : ℕ) (ht : 0 < t ∧ t ≤ T) (s : State)
    (a : Action) (w : ℝ) (hw : 0 < w) :
    ∫ data, |fedNoise M K (fedSamplesExtend M T K 1 data) t s a| ∂fedSamplingLaw M T K 1 ≤
      (w * (1 / (1 - M.discount)) ^ 2 / K + 1 / w) / 2 := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have h1γ : 0 < 1 - M.discount := by linarith [M.discount_lt_one]
  set m := (M.transition s a).expectation (vStar M)
  set Bd := 1 / (1 - M.discount)
  let idx : Fin K → FedIndex State Action T K 1 := fun j ↦ ((⟨t - 1, by omega⟩, j), (s, a), 0)
  let f : State → ℝ := fun x ↦ vStar M x - m
  have hm := expectation_bounds (M.transition s a) (vStar M) 0 Bd (vStar_bounds M)
  have hf : ∀ x, |f x| ≤ Bd := by
    intro x
    have := vStar_bounds M x
    rw [abs_le]
    constructor <;> simp only [f] <;> linarith [hm.1, hm.2]
  have hf0 : (M.transition s a).expectation f = 0 := by
    simp only [f, FiniteDistribution.expectation, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, (M.transition s a).sum_prob, one_mul, m]
    ring
  have hf2 : (M.transition s a).expectation (fun x ↦ f x * f x) ≤ Bd ^ 2 := by
    refine (expectation_bounds _ _ (-(Bd ^ 2)) (Bd ^ 2) fun x ↦ ?_).2
    have := hf x
    have h0 : 0 ≤ |f x| := abs_nonneg _
    constructor
    · nlinarith [mul_self_nonneg (f x)]
    · rw [← abs_mul_abs_self (f x), sq]
      exact mul_le_mul this this h0 (le_trans h0 this)
  -- second moment of the sum
  have hsq : ∫ data, (∑ j, f (data (idx j))) ^ 2 ∂fedSamplingLaw M T K 1 ≤ K * Bd ^ 2 := by
    have hexp : (fun data : FedSamples State Action T K 1 ↦ (∑ j, f (data (idx j))) ^ 2) =
        fun data ↦ ∑ j, ∑ l, f (data (idx j)) * f (data (idx l)) := by
      funext data
      rw [sq, Finset.sum_mul_sum]
    rw [hexp, integral_finset_sum _ (fun _ _ ↦ Integrable.of_finite)]
    have hdiag : ∀ j, ∫ data, ∑ l, f (data (idx j)) * f (data (idx l)) ∂fedSamplingLaw M T K 1 =
        (M.transition s a).expectation (fun x ↦ f x * f x) := by
      intro j
      rw [integral_finset_sum _ (fun _ _ ↦ Integrable.of_finite)]
      rw [Finset.sum_eq_single j]
      · exact fed_coord_integral M T K (idx j) (fun x ↦ f x * f x)
      · intro l _ hlj
        have hne : idx j ≠ idx l := by
          intro he
          apply hlj
          have := congrArg (fun i : FedIndex State Action T K 1 ↦ i.1.2) he
          exact this.symm
        rw [fed_coord_indep_integral M T K _ _ hne f f, fed_coord_integral M T K (idx l) f, hf0,
          mul_zero]
      · intro hj
        exact absurd (Finset.mem_univ j) hj
    simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_left hf2 hKpos.le
  -- pointwise AM-GM bound
  have hpt : ∀ data : FedSamples State Action T K 1,
      |fedNoise M K (fedSamplesExtend M T K 1 data) t s a| ≤
        w / (2 * (K : ℝ) ^ 2) * (∑ j, f (data (idx j))) ^ 2 + 1 / (2 * w) := by
    intro data
    rw [fedNoise_extend M T K data t ht s a]
    set z := ∑ j, f (data (idx j))
    have hz : (1 / (K : ℝ)) * ∑ j, (vStar M (data ((⟨t - 1, by omega⟩, j), (s, a), 0)) - m) =
        z / K := by
      simp only [z, f, idx]
      ring
    rw [hz]
    have key : 2 * |z / K| ≤ w * (z / K) ^ 2 + 1 / w := by
      have h1 : 0 ≤ (w * |z / K| - 1) ^ 2 := sq_nonneg _
      have h2 : (z / K) ^ 2 = |z / K| ^ 2 := (sq_abs _).symm
      rw [h2]
      have h3 : w * |z / K| ^ 2 + 1 / w - 2 * |z / K| = (w * |z / K| - 1) ^ 2 / w := by
        field_simp
        ring
      have h4 : 0 ≤ (w * |z / K| - 1) ^ 2 / w := div_nonneg h1 hw.le
      linarith
    have h5 : w * (z / K) ^ 2 = w / (K : ℝ) ^ 2 * z ^ 2 := by
      field_simp
    have h6 : 1 / (2 * w) = (1 / w) / 2 := by ring
    have h7 : w / (2 * (K : ℝ) ^ 2) * z ^ 2 = (w / (K : ℝ) ^ 2 * z ^ 2) / 2 := by ring
    rw [h6, h7, ← h5]
    linarith
  calc ∫ data, |fedNoise M K (fedSamplesExtend M T K 1 data) t s a| ∂fedSamplingLaw M T K 1
      ≤ ∫ data, (w / (2 * (K : ℝ) ^ 2) * (∑ j, f (data (idx j))) ^ 2 + 1 / (2 * w))
          ∂fedSamplingLaw M T K 1 :=
        integral_mono Integrable.of_finite Integrable.of_finite hpt
    _ = w / (2 * (K : ℝ) ^ 2) * ∫ data, (∑ j, f (data (idx j))) ^ 2 ∂fedSamplingLaw M T K 1 +
          1 / (2 * w) := by
        rw [integral_add Integrable.of_finite (integrable_const _), integral_const_mul,
          integral_const, probReal_univ, one_smul]
    _ ≤ w / (2 * (K : ℝ) ^ 2) * (K * Bd ^ 2) + 1 / (2 * w) := by
        gcongr
    _ = (w * Bd ^ 2 / K + 1 / w) / 2 := by
        field_simp

/-- Expected error of full synchronization with a constant rate. -/
theorem expected_error_le (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hK : 1 ≤ K)
    (𝒞 : Finset ℕ) (h𝒞 : ∀ t, 1 ≤ t → t ≤ T → t ∈ 𝒞) (w : ℝ) (hw : 0 < w) :
    ∫ data, supError (genericOutput M (fun _ ↦ η) K 1 𝒞 (fedSamplesExtend M T K 1 data) T)
        M.optimalityFixedPoint ∂fedSamplingLaw M T K 1 ≤
      (1 - η + η * M.discount) ^ T * (1 / (1 - M.discount)) +
        η * M.discount * (T * (Fintype.card State * Fintype.card Action *
          ((w * (1 / (1 - M.discount)) ^ 2 / K + 1 / w) / 2))) := by
  set β := (w * (1 / (1 - M.discount)) ^ 2 / K + 1 / w) / 2
  have hpt : ∀ data : FedSamples State Action T K 1,
      supError (genericOutput M (fun _ ↦ η) K 1 𝒞 (fedSamplesExtend M T K 1 data) T)
        M.optimalityFixedPoint ≤
      (1 - η + η * M.discount) ^ T * (1 / (1 - M.discount)) +
        η * M.discount * ∑ u ∈ Finset.range T,
          noiseSum M K (fedSamplesExtend M T K 1 data) (u + 1) := fun data ↦
    le_trans (supError_output_le M _ K hK 𝒞 _ T)
      (runErr_unroll M η hη0 hη1 K hK 𝒞 T h𝒞 _ T le_rfl)
  refine le_trans (integral_mono Integrable.of_finite Integrable.of_finite hpt) ?_
  rw [integral_add (integrable_const _) Integrable.of_finite, integral_const, probReal_univ,
    one_smul, integral_const_mul]
  gcongr
  · exact mul_nonneg hη0 M.discount_nonneg
  rw [integral_finset_sum _ (fun _ _ ↦ Integrable.of_finite)]
  calc ∑ u ∈ Finset.range T, ∫ data, noiseSum M K (fedSamplesExtend M T K 1 data) (u + 1)
        ∂fedSamplingLaw M T K 1
      ≤ ∑ _u ∈ Finset.range T, (Fintype.card State * Fintype.card Action * β : ℝ) := by
        apply Finset.sum_le_sum
        intro u hu
        have hu' : 0 < u + 1 ∧ u + 1 ≤ T := ⟨by omega, by simp at hu; omega⟩
        simp only [noiseSum]
        rw [integral_finset_sum _ (fun _ _ ↦ Integrable.of_finite)]
        calc ∑ s, ∫ data, ∑ a, |fedNoise M K (fedSamplesExtend M T K 1 data) (u + 1) s a|
              ∂fedSamplingLaw M T K 1
            ≤ ∑ _s : State, ∑ _a : Action, β := by
              apply Finset.sum_le_sum
              intro s _
              rw [integral_finset_sum _ (fun _ _ ↦ Integrable.of_finite)]
              exact Finset.sum_le_sum fun a _ ↦
                fedNoise_abs_integral_le M T K hK (u + 1) hu' s a w hw
          _ = Fintype.card State * Fintype.card Action * β := by
              simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              ring
    _ = T * (Fintype.card State * Fintype.card Action * β) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end Probability

/-- **C42, alternative reading.** Theorem 7.10 with "for some `c₀ > 0`" inside the hypothesis is
false: for every `C_γ`, at `γ = 5/6`, `S = 4`, `A = 2`, `B = 1`, `η ≡ 1/2`, `𝒞 = {1,…,T}` and
`T` large, every MDP instance has some `K ≥ 2` with expected error below the printed bound. -/
theorem not_thm7_10_innerConstant : ¬ Thm7_10_innerConstant := by
  rintro ⟨Cγ, hC⟩
  obtain ⟨hpos, h⟩ := hC (5 / 6) le_rfl (by norm_num)
  set c := Cγ (5 / 6)
  have hlim := tendsto_pow_const_mul_const_pow_of_abs_lt_one 4 (r := (11 / 12 : ℝ))
    (by rw [abs_of_pos (by norm_num)]; norm_num)
  obtain ⟨T, hTs, hT16⟩ := ((hlim.eventually (gt_mem_nhds
    (show (0 : ℝ) < c / 18 by positivity))).and (eventually_ge_atTop 16)).exists
  have hTr : (16 : ℝ) ≤ T := by exact_mod_cast hT16
  have hlogpos : 0 < Real.log T := Real.log_pos (by linarith)
  have hL2 : 0 < (1 - 5 / 6 : ℝ) * Real.log (((1 : ℕ) : ℝ) * T) ^ 2 := by
    rw [Nat.cast_one, one_mul]
    exact mul_pos (by norm_num) (by positivity)
  obtain ⟨M, hM, hK⟩ := h (Fin 4) (Fin 2) (by simp) (by simp) T 1 (Finset.Icc 1 T)
    (fun _ ↦ 1 / 2) hT16 (by norm_num; linarith) le_rfl subset_rfl
    (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
    (Or.inr ⟨1 / 2, by norm_num, by norm_num, fun _ _ _ ↦ rfl⟩)
    ⟨((Finset.Icc 1 T).card : ℝ) * ((1 - 5 / 6 : ℝ) * Real.log (((1 : ℕ) : ℝ) * T) ^ 2) + 1,
      add_pos_of_nonneg_of_pos (mul_nonneg (Nat.cast_nonneg _) hL2.le) one_pos,
      by rw [le_div_iff₀ hL2]; linarith⟩
  simp only [Nat.cast_one, one_mul] at hK
  set D := Real.sqrt T * Real.log T ^ 3 with hD
  have hDpos : 0 < D := by
    have : 0 < Real.sqrt T := Real.sqrt_pos.mpr (by linarith)
    positivity
  set bnd := c / D with hbnd
  have hbndpos : 0 < bnd := div_pos hpos hDpos
  -- the geometric term
  have hsq : Real.sqrt T ≤ T := Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hlog : Real.log T ≤ T := by
    linarith [Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < T)]
  have hlog3 : Real.log T ^ 3 ≤ (T : ℝ) ^ 3 := pow_le_pow_left₀ hlogpos.le hlog 3
  have hprod : D ≤ (T : ℝ) ^ 4 := by
    calc D ≤ (T : ℝ) * (T : ℝ) ^ 3 :=
          mul_le_mul hsq hlog3 (by positivity) (by linarith)
      _ = (T : ℝ) ^ 4 := by ring
  have hr0 : (0 : ℝ) ≤ (11 / 12 : ℝ) ^ T := by positivity
  have t1 : (11 / 12 : ℝ) ^ T * 6 < bnd / 3 := by
    rw [hbnd, div_div, lt_div_iff₀ (by positivity)]
    calc (11 / 12 : ℝ) ^ T * 6 * (D * 3) = 18 * ((11 / 12 : ℝ) ^ T * D) := by ring
      _ ≤ 18 * ((11 / 12 : ℝ) ^ T * (T : ℝ) ^ 4) := by gcongr
      _ < c := by linarith
  -- choose the auxiliary weight and the number of agents
  set X : ℝ := 1 / 2 * (5 / 6) * (T * 8) with hX
  have hXpos : 0 < X := by positivity
  set w : ℝ := 3 * X / bnd with hw
  have hwpos : 0 < w := by positivity
  set K : ℕ := ⌈54 * X * w / bnd⌉₊ + 2 with hKdef
  have hK2 : 2 ≤ K := by omega
  have hKr : 54 * X * w / bnd < K := by
    have := Nat.le_ceil (54 * X * w / bnd)
    rw [hKdef]
    push_cast
    linarith
  have hKpos : (0 : ℝ) < K := by positivity
  have hE := expected_error_le M T K (1 / 2) (by norm_num) (by norm_num) (by omega)
    (Finset.Icc 1 T) (fun t h1 h2 ↦ Finset.mem_Icc.mpr ⟨h1, h2⟩) w hwpos
  rw [hM] at hE
  have hlow := hK K hK2
  have key : (1 - 1 / 2 + 1 / 2 * (5 / 6) : ℝ) ^ T * (1 / (1 - 5 / 6)) +
      1 / 2 * (5 / 6) * (T * (Fintype.card (Fin 4) * Fintype.card (Fin 2) *
        ((w * (1 / (1 - 5 / 6)) ^ 2 / K + 1 / w) / 2))) < bnd := by
    have e1 : (1 - 1 / 2 + 1 / 2 * (5 / 6) : ℝ) = 11 / 12 := by norm_num
    have e2 : (1 : ℝ) / (1 - 5 / 6) = 6 := by norm_num
    rw [e1, e2, Fintype.card_fin, Fintype.card_fin]
    have t2 : 1 / 2 * (5 / 6) * (T * ((4 : ℕ) * (2 : ℕ) * ((w * 6 ^ 2 / K + 1 / w) / 2))) =
        18 * X * w / K + X / (2 * w) := by
      rw [hX]
      push_cast
      field_simp
      ring
    have t3 : X / (2 * w) = bnd / 6 := by
      rw [hw]
      field_simp
      ring
    have t4 : 18 * X * w / K < bnd / 3 := by
      rw [div_lt_div_iff₀ hKpos (by norm_num)]
      rw [div_lt_iff₀ hbndpos] at hKr
      nlinarith
    rw [t2, t3]
    linarith
  linarith

end StatisticalRL.Ch7Rest.FedGeneric
