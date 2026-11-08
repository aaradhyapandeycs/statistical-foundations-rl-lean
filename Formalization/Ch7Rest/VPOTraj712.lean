import Formalization.Ch7Rest.VPOGibbsBounds712
import Formalization.Ch7Rest.VPOAdaptive712

/-!
# Corrected Theorem 7.12: the trajectory law of online VPO

Kernel properties (dependence on the past only, total mass one), the negative log-likelihood of
the dataset `vpoData h k` as a sum over the rounds `j < k`, and index conversions.
-/

namespace StatisticalRL.Ch7Rest.Rlhf

open Finset Real

set_option linter.unusedSectionVars false

variable {X Y : Type} [Fintype X] [Fintype Y] {d : ℕ}

theorem sum_omega (f : X × Y × Y × Bool → ℝ) :
    ∑ ω, f ω = ∑ x, ∑ y1, ∑ y2, (f (x, y1, y2, true) + f (x, y1, y2, false)) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]

theorem prefProb_true (r : X → Y → ℝ) (x : X) (y1 y2 : Y) :
    prefProb r (x, y1, y2, true) = sigmoid (r x y1 - r x y2) := by
  simp [prefProb, compRecord]

theorem prefProb_false (r : X → Y → ℝ) (x : X) (y1 y2 : Y) :
    prefProb r (x, y1, y2, false) = 1 - sigmoid (r x y1 - r x y2) := by
  simp only [prefProb, compRecord, Bool.false_eq_true, if_false]
  rw [← sigmoid_neg]; ring_nf

theorem prefProb_add (r : X → Y → ℝ) (x : X) (y1 y2 : Y) :
    prefProb r (x, y1, y2, true) + prefProb r (x, y1, y2, false) = 1 := by
  rw [prefProb_true, prefProb_false]; ring

theorem prefProb_pos (r : X → Y → ℝ) (ω : X × Y × Y × Bool) : 0 < prefProb r ω :=
  sigmoid_pos _

theorem vpoData_congr {T : ℕ} (h h' : Fin T → X × Y × Y × Bool) (k : Fin T)
    (hag : ∀ j, j < k → h j = h' j) : vpoData h k = vpoData h' k := by
  unfold vpoData
  refine List.map_congr_left fun j hj ↦ ?_
  simp only [List.mem_filter, decide_eq_true_eq] at hj
  rw [hag j hj.2]

variable (ρ : X → ℝ) (π_ref π_cal : X → Y → ℝ) (φ : X → Y → EuclideanSpace ℝ (Fin d))
  (θstar : EuclideanSpace ℝ (Fin d)) (β : ℝ) (sel : List (X × Y × Y) → EuclideanSpace ℝ (Fin d))

theorem roundPolicy_congr {T : ℕ} (h h' : Fin T → X × Y × Y × Bool) (k : Fin T)
    (hag : ∀ j, j < k → h j = h' j) :
    roundPolicy π_ref φ β sel h k = roundPolicy π_ref φ β sel h' k := by
  unfold roundPolicy; rw [vpoData_congr h h' k hag]

theorem roundKernel_congr {T : ℕ} (k : Fin T) (h h' : Fin T → X × Y × Y × Bool)
    (hag : ∀ j, j < k → h j = h' j) :
    roundKernel ρ π_ref φ θstar β sel k h = roundKernel ρ π_ref φ θstar β sel k h' := by
  funext ω; unfold roundKernel; rw [roundPolicy_congr π_ref φ β sel h h' k hag]

theorem roundKernel_nonneg (hρ : ∀ x, 0 ≤ ρ x) (href : IsPositivePolicy π_ref) {T : ℕ}
    (k : Fin T) (h : Fin T → X × Y × Y × Bool) (ω : X × Y × Y × Bool) :
    0 ≤ roundKernel ρ π_ref φ θstar β sel k h ω := by
  unfold roundKernel roundPolicy
  have := gibbsPolicy_pos href (linReward φ (sel (vpoData h k))) β
  exact mul_nonneg (mul_nonneg (mul_nonneg (hρ _) (this _ _).le) (this _ _).le)
    (prefProb_pos _ _).le

/-- Expectation of `f` under the round kernel. -/
theorem roundKernel_sum_mul {T : ℕ} (k : Fin T) (h : Fin T → X × Y × Y × Bool)
    (f : X × Y × Y × Bool → ℝ) :
    ∑ ω, roundKernel ρ π_ref φ θstar β sel k h ω * f ω =
      ∑ x, ρ x * ∑ y1, ∑ y2, roundPolicy π_ref φ β sel h k x y1 *
        roundPolicy π_ref φ β sel h k x y2 *
        (prefProb (linReward φ θstar) (x, y1, y2, true) * f (x, y1, y2, true) +
          prefProb (linReward φ θstar) (x, y1, y2, false) * f (x, y1, y2, false)) := by
  rw [sum_omega]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun y1 _ ↦ ?_
  rw [mul_sum]
  refine sum_congr rfl fun y2 _ ↦ ?_
  unfold roundKernel
  ring

theorem roundKernel_sum (hρ1 : ∑ x, ρ x = 1) (href : IsPositivePolicy π_ref) {T : ℕ}
    (k : Fin T) (h : Fin T → X × Y × Y × Bool) :
    ∑ ω, roundKernel ρ π_ref φ θstar β sel k h ω = 1 := by
  have := roundKernel_sum_mul ρ π_ref φ θstar β sel k h (fun _ ↦ 1)
  simp only [mul_one, prefProb_add] at this
  rw [this]
  have hp := gibbsPolicy_sum href (linReward φ (sel (vpoData h k))) β
  simp only [roundPolicy, ← mul_sum, hp, mul_one, hρ1] at *

theorem vpoTrajWeight_nonneg (hρ : ∀ x, 0 ≤ ρ x) (href : IsPositivePolicy π_ref) {T : ℕ}
    (h : Fin T → X × Y × Y × Bool) : 0 ≤ vpoTrajWeight ρ π_ref φ θstar β sel h :=
  prod_nonneg fun k _ ↦ roundKernel_nonneg ρ π_ref φ θstar β sel hρ href k h (h k)

theorem vpoTrajWeight_sum (hρ1 : ∑ x, ρ x = 1) (href : IsPositivePolicy π_ref) (T : ℕ) :
    ∑ h : Fin T → X × Y × Y × Bool, vpoTrajWeight ρ π_ref φ θstar β sel h = 1 := by
  have hX : Nonempty X := by
    by_contra hX
    rw [not_nonempty_iff] at hX
    simp at hρ1
  obtain ⟨x₀⟩ := hX
  obtain ⟨y₀, -⟩ := univ_nonempty_of_pos href x₀
  haveI : Nonempty (X × Y × Y × Bool) := ⟨(x₀, y₀, y₀, true)⟩
  exact adaptive_prod_sum_eq_one T (fun k h ω ↦ roundKernel ρ π_ref φ θstar β sel k h ω)
    (fun k h h' hag ↦ roundKernel_congr ρ π_ref φ θstar β sel k h h' hag)
    (fun k h ↦ roundKernel_sum ρ π_ref φ θstar β sel hρ1 href k h)

/-- Negative log-likelihood of the dataset of the rounds `j < k`. -/
theorem nll_vpoData (r : X → Y → ℝ) {T : ℕ} (h : Fin T → X × Y × Y × Bool) (k : Fin T) :
    nll r (vpoData h k) = -∑ j ∈ univ.filter (fun j ↦ j < k), log (prefProb r (h j)) := by
  unfold nll vpoData
  rw [List.map_map]
  congr 1

/-- Index conversion `∑_{j : Fin T, j < k} f j = ∑_{n < k} f n`. -/
theorem sum_filter_lt_eq_sum_range {T : ℕ} (k : Fin T) (f : ℕ → ℝ) :
    ∑ j ∈ univ.filter (fun j : Fin T ↦ j < k), f j = ∑ n ∈ range k, f n := by
  rw [sum_filter]
  have : ∀ j : Fin T, (if j < k then f j else 0) = (fun n : ℕ ↦ if n < k.val then f n else 0) j :=
    fun j ↦ by simp only [Fin.lt_def]
  rw [sum_congr rfl fun j _ ↦ this j, Fin.sum_univ_eq_sum_range (fun n ↦ if n < k.val then f n else 0),
    ← sum_filter]
  congr 1
  ext n; simp only [mem_filter, mem_range]; omega

end StatisticalRL.Ch7Rest.Rlhf
