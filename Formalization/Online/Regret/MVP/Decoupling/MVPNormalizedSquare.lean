import Formalization.ModelFree.TDVariancePairwise
import Formalization.Generative.PolicyEvaluationGeneralForcing

/-! deterministic normalization for a second application of the same
horizon-H concentration event. No probabilistic premise is hidden here. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {State : Type*}

noncomputable def mvp_normalizedSquare (H : ℝ) (V : State → ℝ) : State → ℝ :=
  fun s => V s ^ 2 / H

noncomputable def mvp_normalizedSquareFamily (H : ℝ)
    (family : Finset (State → ℝ)) : Finset (State → ℝ) := by
  classical
  exact family.image (mvp_normalizedSquare H)

theorem mvp_normalizedSquare_zero (H : ℝ) :
    mvp_normalizedSquare H (0 : State → ℝ) = 0 := by
  ext s
  simp [mvp_normalizedSquare]

theorem mvp_normalizedSquare_bounds (H : ℝ) (hH : 0 < H)
    (V : State → ℝ) (hV : ∀ s, 0 ≤ V s ∧ V s ≤ H) :
    ∀ s, 0 ≤ mvp_normalizedSquare H V s ∧ mvp_normalizedSquare H V s ≤ H := by
  intro s
  dsimp [mvp_normalizedSquare]
  refine ⟨div_nonneg (sq_nonneg _) hH.le, (div_le_iff₀ hH).2 ?_⟩
  nlinarith [hV s, mul_nonneg (hV s).1 (sub_nonneg.mpr (hV s).2)]

theorem mvp_normalizedSquareFamily_mem (H : ℝ) (family : Finset (State → ℝ))
    (V : State → ℝ) (hV : V ∈ family) :
    mvp_normalizedSquare H V ∈ mvp_normalizedSquareFamily H family := by
  classical
  exact Finset.mem_image.mpr ⟨V, hV, rfl⟩

theorem mvp_normalizedSquareFamily_zero (H : ℝ) (family : Finset (State → ℝ))
    (hzero : 0 ∈ family) : 0 ∈ mvp_normalizedSquareFamily H family := by
  simpa only [mvp_normalizedSquare_zero] using
    mvp_normalizedSquareFamily_mem H family 0 hzero

theorem mvp_normalizedSquareFamily_card (H : ℝ) (family : Finset (State → ℝ)) :
    (mvp_normalizedSquareFamily H family).card ≤ family.card := by
  classical
  exact Finset.card_image_le

theorem mvp_normalizedSquareFamily_bounds (H : ℝ) (hH : 0 < H)
    (family : Finset (State → ℝ))
    (hfamily : ∀ V ∈ family, ∀ s, 0 ≤ V s ∧ V s ≤ H) :
    ∀ W ∈ mvp_normalizedSquareFamily H family, ∀ s, 0 ≤ W s ∧ W s ≤ H := by
  classical
  intro W hW
  obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hW
  exact mvp_normalizedSquare_bounds H hH V (hfamily V hV)

variable [Fintype State]

theorem mvp_normalizedSquare_variance (p : FiniteDistribution State)
    (H : ℝ) (hH : 0 < H) (V : State → ℝ)
    (hV : ∀ s, 0 ≤ V s ∧ V s ≤ H) :
    p.variance (mvp_normalizedSquare H V) ≤ 4 * p.variance V := by
  have heq : mvp_normalizedSquare H V = fun s => (1/H) * V s ^ 2 := by
    ext s
    simp only [mvp_normalizedSquare, div_eq_mul_inv, one_mul]
    ring
  rw [heq, DiscountedMDP.forcing_variance_const_mul]
  have hs := p.variance_sq_le_four_mul_sq V hH.le hV
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (1/H))
  have hc : (1/H)^2 * (4*H^2*p.variance V) = 4*p.variance V := by
    field_simp
  exact hc ▸ hm

theorem mvp_normalizedSquare_expectation (p : FiniteDistribution State)
    (H : ℝ) (hH : 0 < H) (V : State → ℝ) :
    p.expectation (fun s => V s^2) = H*p.expectation (mvp_normalizedSquare H V) := by
  rw [← p.expectation_mul]
  congr 1
  ext s
  dsimp [mvp_normalizedSquare]
  field_simp

theorem mvp_normalizedSquare_error (p q : FiniteDistribution State)
    (H : ℝ) (hH : 0 < H) (V : State → ℝ) :
    q.expectation (fun s => V s^2) - p.expectation (fun s => V s^2) =
      H*(q.expectation (mvp_normalizedSquare H V) -
        p.expectation (mvp_normalizedSquare H V)) := by
  rw [mvp_normalizedSquare_expectation p H hH,
    mvp_normalizedSquare_expectation q H hH]
  ring

theorem mvp_normalizedSquare_positive_error (p q : FiniteDistribution State)
    (H : ℝ) (hH : 0 < H) (V : State → ℝ) :
    max (q.expectation (fun s => V s^2) - p.expectation (fun s => V s^2)) 0 =
      H*max (q.expectation (mvp_normalizedSquare H V) -
        p.expectation (mvp_normalizedSquare H V)) 0 := by
  rw [mvp_normalizedSquare_error p q H hH]
  by_cases he : 0 ≤ q.expectation (mvp_normalizedSquare H V) -
      p.expectation (mvp_normalizedSquare H V)
  · rw [max_eq_left he, max_eq_left (mul_nonneg hH.le he)]
  · have hn := le_of_not_ge he
    rw [max_eq_right hn, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hH.le hn), mul_zero]

end StatisticalRL.OnlineRL
