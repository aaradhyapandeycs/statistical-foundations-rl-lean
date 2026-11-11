import Formalization.Probability.StdGaussianPi
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Blocks of a standard Gaussian vector on `κ × ι`

Infrastructure for the all-convex route to Theorem 7.11 (`thm:Berry-Esseen-linear`,
`chapters/inference.tex:132–141`): the Gaussian block plumbing of the reservoir Lindeberg swap,
pass 1 (milestone M5a, section A of the M5a design). Planner/P0 construction; not from a cited
paper, and not a source result.

All Gaussian twins share one standard Gaussian vector `w : κ × ι → ℝ` with law
`stdGaussianPi (κ × ι)`; the twin of index `i` uses the block `blockOf w i = fun a ↦ w (i, a)`.

* `blockOf`, `blockPw`: the block `i` of `w`, and `w` with block `i` replaced by that of `w'`;
* `measurePreserving_piecewise_stdGaussianPi`: gluing two independent standard Gaussian vectors
  along any set of coordinates gives a standard Gaussian vector; `measurePreserving_blockPw`;
* `integral_blockPw`: `∫ g dγ = ∫ w', ∫ w, g (blockPw i w' w) dγ dγ` (fresh copy `w'` outer);
* `measurePreserving_blockOf`, `integral_comp_blockOf`: a block is standard Gaussian on `ι`;
* `integral_comp_blockOf_indep`: integrating out one block of `w` that the integrand otherwise
  ignores.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace StatisticalRL.Probability

variable {κ ι : Type*}

/-- D1. Block `i` of the twin vector `w : κ × ι → ℝ`. -/
def blockOf (w : κ × ι → ℝ) (i : κ) : ι → ℝ := fun a ↦ w (i, a)

/-- D2. Replace block `i` of `w` by that of `w'`. -/
def blockPw [DecidableEq κ] (i : κ) (w' w : κ × ι → ℝ) : κ × ι → ℝ :=
  fun c ↦ if c.1 = i then w' c else w c

@[simp] theorem blockOf_apply (w : κ × ι → ℝ) (i : κ) (a : ι) : blockOf w i a = w (i, a) := rfl

theorem blockPw_apply [DecidableEq κ] (i : κ) (w' w : κ × ι → ℝ) (c : κ × ι) :
    blockPw i w' w c = if c.1 = i then w' c else w c := rfl

/-- L6. The replaced block is the block of `w'`. -/
@[simp] theorem blockOf_blockPw_self [DecidableEq κ] (i : κ) (w' w : κ × ι → ℝ) :
    blockOf (blockPw i w' w) i = blockOf w' i := by
  ext a
  simp [blockPw]

/-- The other blocks are those of `w`. -/
@[simp] theorem blockOf_blockPw_of_ne [DecidableEq κ] {i j : κ} (h : j ≠ i) (w' w : κ × ι → ℝ) :
    blockOf (blockPw i w' w) j = blockOf w j := by
  ext a
  simp [blockPw, h]

/-! ## Measurability (L1) -/

theorem continuous_blockOf (i : κ) : Continuous (fun w : κ × ι → ℝ ↦ blockOf w i) :=
  continuous_pi fun a ↦ continuous_apply (i, a)

theorem measurable_blockOf (i : κ) : Measurable (fun w : κ × ι → ℝ ↦ blockOf w i) :=
  measurable_pi_lambda _ fun a ↦ measurable_pi_apply (i, a)

/-! ## Gluing two independent Gaussian vectors (L2, L3) -/

/-- L2. Gluing two independent standard Gaussian vectors along the coordinates where `P` holds
gives a standard Gaussian vector. -/
theorem measurePreserving_piecewise_stdGaussianPi {α : Type*} [Fintype α] (P : α → Prop)
    [DecidablePred P] :
    MeasurePreserving (fun q : (α → ℝ) × (α → ℝ) ↦ fun c ↦ if P c then q.1 c else q.2 c)
      ((stdGaussianPi α).prod (stdGaussianPi α)) (stdGaussianPi α) := by
  have hm : Measurable (fun q : (α → ℝ) × (α → ℝ) ↦ fun c ↦ if P c then q.1 c else q.2 c) := by
    refine measurable_pi_lambda _ fun c ↦ ?_
    by_cases h : P c
    · simpa [h] using (measurable_pi_apply c).comp measurable_fst
    · simpa [h] using (measurable_pi_apply c).comp measurable_snd
  refine ⟨hm, ?_⟩
  haveI : IsProbabilityMeasure (((stdGaussianPi α).prod (stdGaussianPi α)).map
      (fun q : (α → ℝ) × (α → ℝ) ↦ fun c ↦ if P c then q.1 c else q.2 c)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  symm
  refine Measure.pi_eq fun s hs ↦ ?_
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun q : (α → ℝ) × (α → ℝ) ↦ fun c ↦ if P c then q.1 c else q.2 c) ⁻¹'
      Set.univ.pi s =
      Set.univ.pi (fun c ↦ if P c then s c else Set.univ) ×ˢ
        Set.univ.pi (fun c ↦ if P c then Set.univ else s c) := by
    ext q
    simp only [Set.mem_preimage, Set.mem_univ_pi, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun c ↦ ?_, fun c ↦ ?_⟩
      · by_cases hc : P c
        · simpa [hc] using h c
        · simp [hc]
      · by_cases hc : P c
        · simp [hc]
        · simpa [hc] using h c
    · rintro ⟨h1, h2⟩ c
      by_cases hc : P c
      · simpa [hc] using h1 c
      · simpa [hc] using h2 c
  rw [hpre, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ ↦ ?_
  by_cases hc : P c <;> simp [hc]

/-- L2 for blocks: resampling block `i` of a standard Gaussian vector on `κ × ι` by an
independent copy keeps the law. -/
theorem measurePreserving_blockPw [Fintype κ] [Fintype ι] [DecidableEq κ] (i : κ) :
    MeasurePreserving (fun q : (κ × ι → ℝ) × (κ × ι → ℝ) ↦ blockPw i q.1 q.2)
      ((stdGaussianPi (κ × ι)).prod (stdGaussianPi (κ × ι))) (stdGaussianPi (κ × ι)) :=
  measurePreserving_piecewise_stdGaussianPi (fun c : κ × ι ↦ c.1 = i)

/-- L3. Integrals over `stdGaussianPi (κ × ι)` as iterated integrals, the fresh copy `w'` of block
`i` being the outer variable. -/
theorem integral_blockPw [Fintype κ] [Fintype ι] [DecidableEq κ] (i : κ)
    {g : (κ × ι → ℝ) → ℝ} (hg : Integrable g (stdGaussianPi (κ × ι))) :
    ∫ w, g w ∂stdGaussianPi (κ × ι) =
      ∫ w', ∫ w, g (blockPw i w' w) ∂stdGaussianPi (κ × ι) ∂stdGaussianPi (κ × ι) := by
  have hmp := measurePreserving_blockPw (κ := κ) (ι := ι) i
  have h1 : ∫ q, g (blockPw i q.1 q.2)
      ∂((stdGaussianPi (κ × ι)).prod (stdGaussianPi (κ × ι))) =
      ∫ w, g w ∂stdGaussianPi (κ × ι) := by
    rw [← integral_map hmp.measurable.aemeasurable
      (by rw [hmp.map_eq]; exact hg.aestronglyMeasurable), hmp.map_eq]
  have hint : Integrable (fun q : (κ × ι → ℝ) × (κ × ι → ℝ) ↦ g (blockPw i q.1 q.2))
      ((stdGaussianPi (κ × ι)).prod (stdGaussianPi (κ × ι))) :=
    hmp.integrable_comp_of_integrable hg
  rw [← h1, integral_prod _ hint]

/-! ## One block is standard Gaussian (L4, L5) -/

/-- L4. Block `i` of a standard Gaussian vector on `κ × ι` is standard Gaussian on `ι`. -/
theorem measurePreserving_blockOf [Fintype κ] [Fintype ι] (i : κ) :
    MeasurePreserving (fun w : κ × ι → ℝ ↦ blockOf w i) (stdGaussianPi (κ × ι))
      (stdGaussianPi ι) := by
  classical
  refine ⟨measurable_blockOf i, ?_⟩
  haveI : IsProbabilityMeasure ((stdGaussianPi (κ × ι)).map
      (fun w : κ × ι → ℝ ↦ blockOf w i)) :=
    Measure.isProbabilityMeasure_map (measurable_blockOf i).aemeasurable
  symm
  refine Measure.pi_eq fun s hs ↦ ?_
  rw [Measure.map_apply (measurable_blockOf i) (MeasurableSet.univ_pi hs)]
  have hpre : (fun w : κ × ι → ℝ ↦ blockOf w i) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun c : κ × ι ↦ if c.1 = i then s c.2 else Set.univ) := by
    ext w
    simp only [Set.mem_preimage, Set.mem_univ_pi, blockOf]
    constructor
    · rintro h ⟨c1, c2⟩
      by_cases hc : c1 = i
      · subst hc
        simpa using h c2
      · simp [hc]
    · intro h a
      simpa using h (i, a)
  rw [hpre, Measure.pi_pi, Fintype.prod_prod_type, Finset.prod_eq_single i]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- L5. Integrating a function of block `i`. -/
theorem integral_comp_blockOf [Fintype κ] [Fintype ι] (i : κ) {g : (ι → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (stdGaussianPi ι)) :
    ∫ w, g (blockOf w i) ∂stdGaussianPi (κ × ι) = ∫ z, g z ∂stdGaussianPi ι := by
  have hmp := measurePreserving_blockOf (κ := κ) (ι := ι) i
  rw [← hmp.map_eq] at hg ⊢
  exact (integral_map (measurable_blockOf i).aemeasurable hg).symm

/-! ## Integrating out one block -/

/-- Integrating out one Gaussian block: if `G z w` ignores block `i` of `w`, then
`∫ G (blockOf w i) w dγ = ∫ z, ∫ w, G z w dγ dν`. -/
theorem integral_comp_blockOf_indep [Fintype κ] [Fintype ι] [DecidableEq κ] (i : κ)
    {G : (ι → ℝ) → (κ × ι → ℝ) → ℝ}
    (hG : Continuous (Function.uncurry G)) {C : ℝ} (hGb : ∀ z w, |G z w| ≤ C)
    (hind : ∀ z w w', G z (blockPw i w' w) = G z w) :
    ∫ w, G (blockOf w i) w ∂stdGaussianPi (κ × ι) =
      ∫ z, ∫ w, G z w ∂stdGaussianPi (κ × ι) ∂stdGaussianPi ι := by
  have hcont : Continuous (fun w : κ × ι → ℝ ↦ G (blockOf w i) w) :=
    hG.comp ((continuous_blockOf i).prodMk continuous_id)
  have hint : Integrable (fun w : κ × ι → ℝ ↦ G (blockOf w i) w) (stdGaussianPi (κ × ι)) :=
    Integrable.of_bound hcont.aestronglyMeasurable C
      (ae_of_all _ fun w ↦ by rw [Real.norm_eq_abs]; exact hGb _ _)
  have hinner : Continuous (fun z : ι → ℝ ↦ ∫ w, G z w ∂stdGaussianPi (κ × ι)) := by
    refine continuous_of_dominated (bound := fun _ ↦ C)
      (fun z ↦ (hG.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
      (fun z ↦ ae_of_all _ fun w ↦ by rw [Real.norm_eq_abs]; exact hGb _ _)
      (integrable_const C)
      (ae_of_all _ fun w ↦ hG.comp (continuous_id.prodMk continuous_const))
  rw [integral_blockPw i hint]
  have hrw : ∀ w' w : κ × ι → ℝ, G (blockOf (blockPw i w' w) i) (blockPw i w' w) =
      G (blockOf w' i) w := by
    intro w' w
    rw [blockOf_blockPw_self, hind]
  simp_rw [hrw]
  exact integral_comp_blockOf i (g := fun z ↦ ∫ w, G z w ∂stdGaussianPi (κ × ι))
    hinner.aestronglyMeasurable

end StatisticalRL.Probability
