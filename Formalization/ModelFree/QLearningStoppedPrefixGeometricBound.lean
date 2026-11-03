import Formalization.ModelFree.QLearningStoppedPrefixKLMixtureIdentity
import Formalization.ModelFree.QLearningFiniteLogSumPinsker
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Geometric normalization and the expected-horizon KL bound. -/

open scoped BigOperators
namespace StatisticalRL.QLearning.CountablePinsker

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The source geometric stopping weights sum to one. The zero-discount
branch is an explicit point mass at zero and never evaluates `0 ^ 0`. -/
theorem qGeometricStopWeight_hasSum_one (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    HasSum (qGeometricStopWeight γ) 1 := by
  by_cases hγ0 : γ = 0
  · subst γ
    have hfun : qGeometricStopWeight 0 = fun k : ℕ ↦ if k = 0 then 1 else 0 := by
      funext k
      exact qGeometricStopWeight_zero k
    rw [hfun]
    simpa using (hasSum_ite_eq 0 (1 : ℝ))
  · have hgeom : HasSum (fun k : ℕ ↦ γ ^ k) ((1 - γ)⁻¹) :=
      hasSum_geometric_of_lt_one hγ hγ1
    have hscale : HasSum (fun k : ℕ ↦ (1 - γ) * γ ^ k)
        ((1 - γ) * (1 - γ)⁻¹) := hgeom.mul_left (1 - γ)
    have hweight : qGeometricStopWeight γ = fun k ↦ (1 - γ) * γ ^ k := by
      funext k
      simp [qGeometricStopWeight, hγ0]
    rw [hweight]
    convert hscale using 1
    exact (mul_inv_cancel₀ (by linarith : 1 - γ ≠ 0)).symm

/-- Every finite forced-prefix fiber is the actual normalized law, so its
finite sum is exactly one. This equality retains the fixed initial action and
the `k=0` unit-law boundary. -/
theorem qForcedPrefixWeight_sum_one
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (s : State) (a : Action) (k : ℕ) :
    ∑ path : QForcedPrefix (State := State) (Action := Action) k,
      qForcedPrefixWeight M π s a k path = 1 :=
  (qForcedPrefixLaw M π s a k).sum_prob

/-- The actual dependent-sum stopped-prefix mass is normalized. Regrouping is
performed only after establishing nonnegative summability; the inner finite
law has mass one, and the outer actual stop weights have mass one. -/
theorem qActualStoppedPrefixMass_hasSum_one
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (γ : ℝ) (s : State) (a : Action)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    HasSum (qActualStoppedPrefixMass M π γ s a) 1 := by
  have hnonneg : ∀ z : qStoppedPrefixAbsCarrier (State := State) (Action := Action),
      0 ≤ qActualStoppedPrefixMass M π γ s a z := by
    intro z
    cases z with
    | mk k path =>
        exact mul_nonneg (qGeometricStopWeight_nonneg γ k hγ hγ1)
          ((qForcedPrefixLaw M π s a k).prob_nonneg path)
  have hweightSummable : Summable (qGeometricStopWeight γ) :=
    (qGeometricStopWeight_hasSum_one γ hγ hγ1).summable
  have hsigma := (summable_sigma_of_nonneg hnonneg).2
  have hfibers : ∀ k : ℕ,
      Summable (fun path : QForcedPrefix (State := State) (Action := Action) k ↦
        qActualStoppedPrefixMass M π γ s a ⟨k, path⟩) := by
    intro k
    exact Summable.of_finite
  have houter : Summable (fun k : ℕ ↦
      ∑' path : QForcedPrefix (State := State) (Action := Action) k,
        qActualStoppedPrefixMass M π γ s a ⟨k, path⟩) := by
    have heq : (fun k : ℕ ↦
        ∑' path : QForcedPrefix (State := State) (Action := Action) k,
          qActualStoppedPrefixMass M π γ s a ⟨k, path⟩) =
        qGeometricStopWeight γ := by
      funext k
      rw [tsum_fintype]
      change (∑ path, qGeometricStopWeight γ k *
        qForcedPrefixWeight M π s a k path) = qGeometricStopWeight γ k
      rw [← Finset.mul_sum, qForcedPrefixWeight_sum_one]
      ring
    rw [heq]
    exact hweightSummable
  have hsigmaSummable : Summable
      (qActualStoppedPrefixMass M π γ s a) :=
    (summable_sigma_of_nonneg hnonneg).2 ⟨hfibers, houter⟩
  have htsum := hsigmaSummable.tsum_sigma
  have htotal : (∑' z : qStoppedPrefixAbsCarrier (State := State) (Action := Action),
      qActualStoppedPrefixMass M π γ s a z) = 1 := by
    rw [htsum]
    have heq : (fun k : ℕ ↦
        ∑' path : QForcedPrefix (State := State) (Action := Action) k,
          qActualStoppedPrefixMass M π γ s a ⟨k, path⟩) =
        qGeometricStopWeight γ := by
      funext k
      rw [tsum_fintype]
      change (∑ path, qGeometricStopWeight γ k *
        qForcedPrefixWeight M π s a k path) = qGeometricStopWeight γ k
      rw [← Finset.mul_sum, qForcedPrefixWeight_sum_one]
      ring
    rw [heq, (qGeometricStopWeight_hasSum_one γ hγ hγ1).tsum_eq]
  exact hsigmaSummable.hasSum_iff.mpr htotal

/-- Exact first moment of the independent geometric stop. In particular the
factor is `γ/(1-γ)`, not a horizon-shifted variant. -/
theorem qGeometricStopWeight_firstMoment (γ : ℝ)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    (∑' k : ℕ, qGeometricStopWeight γ k * (k : ℝ)) =
      γ / (1 - γ) := by
  by_cases hγ0 : γ = 0
  · subst γ
    have hfun : (fun k : ℕ ↦ qGeometricStopWeight 0 k * (k : ℝ)) =
        fun _ ↦ 0 := by
      funext k
      by_cases hk : k = 0
      · simp [qGeometricStopWeight_zero, hk]
      · simp [qGeometricStopWeight_zero, hk]
    rw [hfun]
    simp
  · have hnorm : ‖γ‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hγ]
      exact hγ1
    have hmoment := tsum_coe_mul_geometric_of_norm_lt_one hnorm
    have hgeom : (∑' k : ℕ, qGeometricStopWeight γ k * (k : ℝ)) =
        (1 - γ) * (∑' k : ℕ, (k : ℝ) * γ ^ k) := by
      calc
        _ = ∑' k : ℕ, ((1 - γ) * γ ^ k) * (k : ℝ) := by
          apply tsum_congr
          intro k
          simp [qGeometricStopWeight, hγ0]
        _ = (1 - γ) * (∑' k : ℕ, (k : ℝ) * γ ^ k) := by
          calc
            _ = ∑' k : ℕ, (1 - γ) * ((k : ℝ) * γ ^ k) := by
              apply tsum_congr
              intro k
              ring
            _ = _ := by rw [tsum_mul_left]
    rw [hgeom, hmoment]
    have hden : 1 - γ ≠ 0 := by linarith
    field_simp [hden]

/-- The actual stopped-prefix KL is bounded by the exact expected number of
transitions times the worst row KL. The numerator/reference orientation is
the source `KL(M' || M)`. The row support and row KL hypotheses are exposed;
there is no target-shaped trajectory premise. -/
theorem qActualStoppedPrefixKL_le_geometric_bound
    (M M' : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (γ ρ : ℝ) (s : State) (a : Action)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hρ : 0 ≤ ρ)
    (hrowSupport : ∀ x b y, (M'.transition x b).prob y ≠ 0 →
      (M.transition x b).prob y ≠ 0)
    (hrowKL : ∀ x b,
      StatisticalRL.GenerativeLowerBound.finiteKLExpression
        (fun y ↦ (M'.transition x b).prob y)
        (fun y ↦ (M.transition x b).prob y) ≤ ρ) :
    (∑' z : qStoppedPrefixAbsCarrier (State := State) (Action := Action),
      qStoppedPrefixKLAtom (qActualStoppedPrefixMass M' π γ s a z)
        (qActualStoppedPrefixMass M π γ s a z)) ≤ ρ * γ / (1 - γ) := by
  rw [qActualStoppedPrefixKL_mixture_eq_rec M M' π γ ρ s a
    hγ hγ1 hρ hrowSupport hrowKL]
  let term : ℕ → ℝ := fun k ↦ qGeometricStopWeight γ k *
    qForcedPrefixKLRec M M' π s a k
  let major : ℕ → ℝ := fun k ↦ qGeometricStopWeight γ k * ((k : ℝ) * ρ)
  have hmajorant := qGeometricStopWeight_weighted_linear_summable γ ρ hγ hγ1
  have hrecNonneg (k : ℕ) : 0 ≤ qForcedPrefixKLRec M M' π s a k := by
    have hfinite := qForcedPrefixLaw_finiteKL_eq_rec M M' π k hrowSupport s a
    rw [← hfinite]
    have hsumA : (∑ path, (qForcedPrefixLaw M' π s a k).prob path) = 1 :=
      (qForcedPrefixLaw M' π s a k).sum_prob
    have hsumB : (∑ path, (qForcedPrefixLaw M π s a k).prob path) = 1 :=
      (qForcedPrefixLaw M π s a k).sum_prob
    have heq : qFiniteKLOn Finset.univ
        (fun path ↦ (qForcedPrefixLaw M' π s a k).prob path)
        (fun path ↦ (qForcedPrefixLaw M π s a k).prob path) =
      StatisticalRL.GenerativeLowerBound.finiteKLExpression
        (fun path ↦ (qForcedPrefixLaw M' π s a k).prob path)
        (fun path ↦ (qForcedPrefixLaw M π s a k).prob path) := by
      unfold qFiniteKLOn StatisticalRL.GenerativeLowerBound.finiteKLExpression
      apply Finset.sum_congr rfl
      intro path _
      by_cases hzero : (qForcedPrefixLaw M' π s a k).prob path = 0
      · simp [qFiniteKLTerm, hzero]
      · simp [qFiniteKLTerm, hzero]
    rw [← heq]
    apply qFiniteKLOn_nonneg (s := Finset.univ)
    · intro path _
      exact (qForcedPrefixLaw M' π s a k).prob_nonneg path
    · intro path _
      exact (qForcedPrefixLaw M π s a k).prob_nonneg path
    · simpa using hsumA
    · simpa using hsumB
    · intro path _ hp
      exact qForcedPrefixWeight_support M M' π s a k hrowSupport path hp
  have htermSummable : Summable term := by
    apply Summable.of_nonneg_of_le
      (fun k ↦ mul_nonneg (qGeometricStopWeight_nonneg γ k hγ hγ1)
        (hrecNonneg k))
      (fun k ↦ by
        have hrec := qForcedPrefixKLRec_le M M' π ρ k hrowKL s a
        exact mul_le_mul_of_nonneg_left
          (by linarith : qForcedPrefixKLRec M M' π s a k ≤ (k : ℝ) * ρ + 2)
          (qGeometricStopWeight_nonneg γ k hγ hγ1)) hmajorant
  have hmajorSummable : Summable (fun k : ℕ ↦
      qGeometricStopWeight γ k * ((k : ℝ) * ρ)) := by
    apply Summable.of_nonneg_of_le
      (fun k ↦ mul_nonneg (qGeometricStopWeight_nonneg γ k hγ hγ1)
        (mul_nonneg (Nat.cast_nonneg k) hρ))
      (fun k ↦ by
        exact mul_le_mul_of_nonneg_left (by linarith :
          (k : ℝ) * ρ ≤ (k : ℝ) * ρ + 2)
          (qGeometricStopWeight_nonneg γ k hγ hγ1)) hmajorant
  have hpointwise (k : ℕ) : term k ≤ major k := by
    dsimp [term]
    exact mul_le_mul_of_nonneg_left
      (qForcedPrefixKLRec_le M M' π ρ k hrowKL s a)
      (qGeometricStopWeight_nonneg γ k hγ hγ1)
  have hsum := htermSummable.tsum_le_tsum hpointwise hmajorSummable
  calc
    (∑' k : ℕ, qGeometricStopWeight γ k * qForcedPrefixKLRec M M' π s a k)
        ≤ ∑' k : ℕ, major k := by
          change (∑' k, term k) ≤ ∑' k, major k
          exact hsum
    _ = ρ * γ / (1 - γ) := by
      dsimp [major]
      calc
    _ = ρ * (∑' k : ℕ, qGeometricStopWeight γ k * (k : ℝ)) := by
          rw [← tsum_mul_left]
          apply tsum_congr
          intro k
          ring
        _ = ρ * (γ / (1 - γ)) := by rw [qGeometricStopWeight_firstMoment γ hγ hγ1]
        _ = ρ * γ / (1 - γ) := by ring

end StatisticalRL.QLearning.CountablePinsker
