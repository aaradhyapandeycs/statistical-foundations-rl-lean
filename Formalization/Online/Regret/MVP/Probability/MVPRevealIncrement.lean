import Formalization.Online.Regret.MVP.Probability.MVPPredictableSum

/-! Padded finite-product increments: range, centering and reveal measurability. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {Index Outcome : Type*} [Fintype Index] [Fintype Outcome]
local instance : MeasurableSpace Outcome := ⊤

theorem mvp_paddedRevealIncrement_centered {M : ℕ} (order : Fin M → Index)
    (hinj : Function.Injective order) (d : Index → FiniteDistribution Outcome)
    (F : (j : Fin M) → ((i : mvpRevealedPrefix order j.val) → Outcome) → Outcome → ℝ)
    (k : ℕ) :
    (onlineStackProductLaw d)[mvpPaddedRevealIncrement order d F k |
      mvpRevealFiltration (Outcome := Outcome) order k] =ᵐ[onlineStackProductLaw d] 0 := by
  classical
  by_cases hk : k < M
  · let j : Fin M := ⟨k,hk⟩
    have h := (mvp_prefix_centered_moments order hinj d j (F j)).1
    have heq : mvpPaddedRevealIncrement order d F k = (fun data =>
        F j (onlineRevealedCode (mvpRevealedPrefix order k) data) (data (order j)) -
        (d (order j)).expectation (F j (onlineRevealedCode (mvpRevealedPrefix order k) data))) := by
      funext data
      simp [mvpPaddedRevealIncrement, hk, j]
    rw [heq]
    exact h
  · have heq : mvpPaddedRevealIncrement order d F k = 0 := by
      funext data
      simp [mvpPaddedRevealIncrement, hk]
    rw [heq]
    simp

theorem mvp_paddedRevealIncrement_bound {M : ℕ} (order : Fin M → Index)
    (d : Index → FiniteDistribution Outcome)
    (F : (j : Fin M) → ((i : mvpRevealedPrefix order j.val) → Outcome) → Outcome → ℝ)
    (C : ℝ) (hC : 0 ≤ C)
    (hF : ∀ j code x, 0 ≤ F j code x ∧ F j code x ≤ C)
    (k : ℕ) (data : Index → Outcome) : |mvpPaddedRevealIncrement order d F k data| ≤ C := by
  classical
  by_cases hk : k < M
  · let j : Fin M := ⟨k,hk⟩
    let code := onlineRevealedCode (mvpRevealedPrefix order k) data
    have hlow : 0 ≤ (d (order j)).expectation (F j code) :=
      (d (order j)).expectation_nonneg (fun x => (hF j code x).1)
    have hhigh : (d (order j)).expectation (F j code) ≤ C :=
      (d (order j)).expectation_le_const (fun x => (hF j code x).2)
    have hv := hF j code (data (order j))
    simp only [mvpPaddedRevealIncrement, dif_pos hk]
    change |F j code (data (order j)) - (d (order j)).expectation (F j code)| ≤ C
    rw [abs_le]
    constructor <;> linarith
  · simp [mvpPaddedRevealIncrement, hk, hC]

/-- The current coordinate has joined the reveal set at the next step. -/
theorem mvp_order_mem_next_prefix {M : ℕ} (order : Fin M → Index) (j : Fin M) :
    order j ∈ mvpRevealedPrefix order (j.val + 1) := by
  classical
  simp only [mvpRevealedPrefix, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨⟨j,rfl⟩, j, Nat.lt_succ_self _, rfl⟩

/-- The padded increment is measurable once its sampled coordinate is revealed. -/
theorem mvp_paddedRevealIncrement_adapted {M : ℕ} (order : Fin M → Index)
    (d : Index → FiniteDistribution Outcome)
    (F : (j : Fin M) → ((i : mvpRevealedPrefix order j.val) → Outcome) → Outcome → ℝ)
    (k : ℕ) : StronglyMeasurable[mvpRevealFiltration (Outcome := Outcome) order (k+1)]
      (mvpPaddedRevealIncrement order d F k) := by
  classical
  by_cases hk : k < M
  · let j : Fin M := ⟨k,hk⟩
    let next := mvpRevealedPrefix order (k+1)
    have hsub : mvpRevealedPrefix order k ⊆ next := mvpRevealedPrefix_mono order (Nat.le_succ k)
    have hmem : order j ∈ next := mvp_order_mem_next_prefix order j
    let eval : ((i : next) → Outcome) → ℝ := fun code =>
      let old : ((i : mvpRevealedPrefix order k) → Outcome) := fun i => code ⟨i.val,hsub i.property⟩
      F j old (code ⟨order j,hmem⟩) - (d (order j)).expectation (F j old)
    have heval : Measurable eval := measurable_of_countable _
    have heq : mvpPaddedRevealIncrement order d F k =
        eval ∘ onlineRevealedCode next := by
      funext data
      simp [mvpPaddedRevealIncrement, hk, eval, onlineRevealedCode, j]
      rfl
    rw [heq]
    exact (heval.comp (comap_measurable _)).stronglyMeasurable
  · have heq : mvpPaddedRevealIncrement order d F k = 0 := by
      funext data
      simp [mvpPaddedRevealIncrement, hk]
    rw [heq]
    exact stronglyMeasurable_const
end StatisticalRL.OnlineRL
