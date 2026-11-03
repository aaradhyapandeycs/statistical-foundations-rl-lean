import Formalization.ModelFree.QLearningTrajectoryKLPathInduction
import Formalization.ModelFree.QLearningGeometricKLAtom
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! Absolute summability of the actual geometrically stopped prefix KL series. -/

open scoped BigOperators
namespace StatisticalRL.QLearning.CountablePinsker

/-- A zero-safe KL atom cannot have negative part larger in magnitude than
its reference mass. A crude constant `1` (rather than the sharper `1/e`) is
sufficient for summability and leaves the source's final KL constants intact. -/
theorem qStoppedPrefixKLAtom_neg_le_reference (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsupport : a ≠ 0 → b ≠ 0) :
    -qStoppedPrefixKLAtom a b ≤ b := by
  by_cases ha0 : a = 0
  · simp [qStoppedPrefixKLAtom, ha0, hb]
  have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb0 := hsupport ha0
  have hbPos : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  by_cases hba : b ≤ a
  · have hratio : 1 ≤ a / b := (one_le_div₀ hbPos).2 hba
    have hlog : 0 ≤ Real.log (a / b) := Real.log_nonneg hratio
    have hterm : 0 ≤ a * Real.log (a / b) := mul_nonneg haPos.le hlog
    simp [qStoppedPrefixKLAtom, ha0]
    linarith
  · have hab : a ≤ b := le_of_not_ge hba
    have hratio : a / b ≤ 1 := (div_le_one₀ hbPos).2 hab
    have hratioPos : 0 < a / b := div_pos haPos hbPos
    have hcurv := Real.abs_log_mul_self_lt (a / b) hratioPos hratio
    have habs : |(a / b) * Real.log (a / b)| ≤ 1 := by
      simpa [mul_comm] using hcurv.le
    have hneg : -((a / b) * Real.log (a / b)) ≤ 1 := by
      rw [abs_le] at habs
      linarith
    have hidentity : a * Real.log (a / b) = b * ((a / b) * Real.log (a / b)) := by
      field_simp [ne_of_gt hbPos]
    simp [qStoppedPrefixKLAtom, ha0]
    rw [hidentity]
    nlinarith [mul_le_mul_of_nonneg_left hneg hbPos.le]

/-- Pointwise absolute-value domination by the signed atom plus twice the
reference mass. Summing this bounds the absolute KL series by KL plus `2`. -/
theorem abs_qStoppedPrefixKLAtom_le_signed_add_two_reference (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hsupport : a ≠ 0 → b ≠ 0) :
    |qStoppedPrefixKLAtom a b| ≤ qStoppedPrefixKLAtom a b + 2 * b := by
  have hneg := qStoppedPrefixKLAtom_neg_le_reference a b ha hb hsupport
  by_cases hterm : 0 ≤ qStoppedPrefixKLAtom a b
  · rw [abs_of_nonneg hterm]
    linarith
  · rw [abs_of_neg (lt_of_not_ge hterm)]
    linarith

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Countable carrier of actual forced-initial-action prefixes tagged by the
number of transitions. -/
abbrev qStoppedPrefixAbsCarrier :=
  Σ k : ℕ, QForcedPrefix (State := State) (Action := Action) k

/-- Actual stopped-prefix mass: one common source geometric stop weight times
the actual finite transition-policy prefix law. The initial action is fixed
outside the carrier, and fiber `k` contains exactly `k` transition draws. -/
noncomputable def qActualStoppedPrefixMass
    (M : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (γ : ℝ) (s : State) (a : Action) :
    qStoppedPrefixAbsCarrier (State := State) (Action := Action) → ℝ
  | ⟨k, path⟩ => qGeometricStopWeight γ k * qForcedPrefixWeight M π s a k path

/-- The crude linear fiber majorant is summable under the source geometric
stop. The zero-discount case is a finitely supported sequence and is handled
before invoking any positive-geometric-weight theorem. -/
theorem qGeometricStopWeight_weighted_linear_summable
    (γ ρ : ℝ) (hγ : 0 ≤ γ) (hγ1 : γ < 1) :
    Summable (fun k : ℕ ↦
      qGeometricStopWeight γ k * ((k : ℝ) * ρ + 2)) := by
  by_cases hγ0 : γ = 0
  · have heq : (fun k : ℕ ↦
        qGeometricStopWeight γ k * ((k : ℝ) * ρ + 2)) =
      fun k ↦ if k = 0 then 2 else 0 := by
      funext k
      rw [hγ0, qGeometricStopWeight_zero]
      split_ifs with hk
      · subst k
        simp
      · simp
    rw [heq]
    refine summable_of_finite_support ((Set.finite_singleton 0).subset (by
      intro k hk
      have hk0 : k = 0 := by simpa using hk
      subst k
      simp))
  · have hgeom : Summable (fun k : ℕ ↦ γ ^ k) :=
      summable_geometric_of_lt_one hγ hγ1
    have hnorm : ‖γ‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg hγ]
      exact hγ1
    have hgeomLinear : Summable (fun k : ℕ ↦ (k : ℝ) * γ ^ k) := by
      simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
    have hmajor : Summable (fun k : ℕ ↦
        ((1 - γ) * ρ) * ((k : ℝ) * γ ^ k) +
          (2 * (1 - γ)) * γ ^ k) :=
      (hgeomLinear.mul_left ((1 - γ) * ρ)).add
        (hgeom.mul_left (2 * (1 - γ)))
    apply hmajor.congr
    intro k
    rw [qGeometricStopWeight, if_neg hγ0]
    ring

/-- The atomic KL series of the two actual stopped-prefix laws is absolutely
summable when each actual fixed-action prefix KL is bounded by `kρ` and the
corresponding geometric weighted linear majorant is summable. The majorant
premise is the isolated geometric first-moment obligation; it includes the
explicit `γ=0` weight definition, where only the `k=0` fiber survives. -/
theorem qActualStoppedPrefixKL_abs_summable
    (M M' : DiscountedMDP State Action) (π : StationaryPolicy State Action)
    (γ ρ : ℝ) (s : State) (a : Action)
    (hγ : 0 ≤ γ) (hγ1 : γ < 1) (hρ : 0 ≤ ρ)
    (hrowSupport : ∀ x b y, (M'.transition x b).prob y ≠ 0 →
      (M.transition x b).prob y ≠ 0)
    (hrowKL : ∀ x b,
      StatisticalRL.GenerativeLowerBound.finiteKLExpression
        (fun y ↦ (M'.transition x b).prob y)
        (fun y ↦ (M.transition x b).prob y) ≤ ρ) :
    Summable (fun z : qStoppedPrefixAbsCarrier (State := State) (Action := Action) ↦
      |qStoppedPrefixKLAtom (qActualStoppedPrefixMass M' π γ s a z)
        (qActualStoppedPrefixMass M π γ s a z)|) := by
  let p : qStoppedPrefixAbsCarrier (State := State) (Action := Action) → ℝ :=
    qActualStoppedPrefixMass M' π γ s a
  let q : qStoppedPrefixAbsCarrier (State := State) (Action := Action) → ℝ :=
    qActualStoppedPrefixMass M π γ s a
  have hw (k : ℕ) : 0 ≤ qGeometricStopWeight γ k :=
    qGeometricStopWeight_nonneg γ k hγ hγ1
  have hWeightedMajorant :=
    qGeometricStopWeight_weighted_linear_summable γ ρ hγ hγ1
  have hfiberKL (k : ℕ) :
      StatisticalRL.GenerativeLowerBound.finiteKLExpression
        (fun path ↦ (qForcedPrefixLaw M' π s a k).prob path)
        (fun path ↦ (qForcedPrefixLaw M π s a k).prob path) ≤ (k : ℝ) * ρ := by
    rw [qForcedPrefixLaw_finiteKL_eq_rec M M' π k hrowSupport]
    exact qForcedPrefixKLRec_le M M' π ρ k hrowKL s a
  have hfiberAtomEq (k : ℕ) :
      StatisticalRL.GenerativeLowerBound.finiteKLExpression
          (fun path ↦ (qForcedPrefixLaw M' π s a k).prob path)
          (fun path ↦ (qForcedPrefixLaw M π s a k).prob path) =
        ∑ path, qStoppedPrefixKLAtom ((qForcedPrefixLaw M' π s a k).prob path)
          ((qForcedPrefixLaw M π s a k).prob path) := by
    unfold StatisticalRL.GenerativeLowerBound.finiteKLExpression
    apply Finset.sum_congr rfl
    intro path _
    by_cases hzero : (qForcedPrefixLaw M' π s a k).prob path = 0
    · simp [qStoppedPrefixKLAtom, hzero]
    · simp [qStoppedPrefixKLAtom, hzero]
  have hfiberAbs (k : ℕ) :
      (∑ path, |qStoppedPrefixKLAtom ((qForcedPrefixLaw M' π s a k).prob path)
        ((qForcedPrefixLaw M π s a k).prob path)|) ≤ (k : ℝ) * ρ + 2 := by
    have hsupport (path) :
        (qForcedPrefixLaw M' π s a k).prob path ≠ 0 →
          (qForcedPrefixLaw M π s a k).prob path ≠ 0 :=
      qForcedPrefixWeight_support M M' π s a k hrowSupport path
    have hdom (path) := abs_qStoppedPrefixKLAtom_le_signed_add_two_reference
      ((qForcedPrefixLaw M' π s a k).prob path)
      ((qForcedPrefixLaw M π s a k).prob path)
      ((qForcedPrefixLaw M' π s a k).prob_nonneg path)
      ((qForcedPrefixLaw M π s a k).prob_nonneg path) (hsupport path)
    calc
      _ ≤ ∑ path, (qStoppedPrefixKLAtom ((qForcedPrefixLaw M' π s a k).prob path)
            ((qForcedPrefixLaw M π s a k).prob path) +
          2 * (qForcedPrefixLaw M π s a k).prob path) :=
        Finset.sum_le_sum fun path _ ↦ hdom path
      _ = StatisticalRL.GenerativeLowerBound.finiteKLExpression
            (fun path ↦ (qForcedPrefixLaw M' π s a k).prob path)
            (fun path ↦ (qForcedPrefixLaw M π s a k).prob path) + 2 := by
        rw [Finset.sum_add_distrib, hfiberAtomEq]
        rw [← Finset.mul_sum, (qForcedPrefixLaw M π s a k).sum_prob]
        ring
      _ ≤ (k : ℝ) * ρ + 2 := by linarith [hfiberKL k]
  have hscale (k : ℕ) (path : QForcedPrefix (State := State) (Action := Action) k) :
      qStoppedPrefixKLAtom (p ⟨k, path⟩) (q ⟨k, path⟩) =
        qGeometricStopWeight γ k * qStoppedPrefixKLAtom
          ((qForcedPrefixLaw M' π s a k).prob path)
          ((qForcedPrefixLaw M π s a k).prob path) := by
    dsimp [p, q, qActualStoppedPrefixMass]
    exact qStoppedPrefixKLAtom_geometric_scale γ k _ _ hγ hγ1
      ((qForcedPrefixLaw M' π s a k).prob_nonneg path)
      ((qForcedPrefixLaw M π s a k).prob_nonneg path)
      (qForcedPrefixWeight_support M M' π s a k hrowSupport path)
  let g : qStoppedPrefixAbsCarrier (State := State) (Action := Action) → ℝ :=
    fun z ↦ |qStoppedPrefixKLAtom (p z) (q z)|
  have hgNonneg : ∀ z, 0 ≤ g z := fun z ↦ abs_nonneg _
  have hSigma := summable_sigma_of_nonneg hgNonneg
  apply hSigma.2
  constructor
  · intro k
    exact Summable.of_finite
  · have houter : ∀ k : ℕ,
        (∑' path : QForcedPrefix (State := State) (Action := Action) k,
          g ⟨k, path⟩) ≤
          qGeometricStopWeight γ k * ((k : ℝ) * ρ + 2) := by
      intro k
      rw [tsum_fintype]
      calc
        _ ≤ ∑ path, qGeometricStopWeight γ k *
            |qStoppedPrefixKLAtom ((qForcedPrefixLaw M' π s a k).prob path)
              ((qForcedPrefixLaw M π s a k).prob path)| := by
          apply Finset.sum_le_sum
          intro path _
          rw [show g ⟨k, path⟩ =
            |qGeometricStopWeight γ k * qStoppedPrefixKLAtom
              ((qForcedPrefixLaw M' π s a k).prob path)
              ((qForcedPrefixLaw M π s a k).prob path)| by
                dsimp [g]
                rw [hscale]]
          rw [abs_mul, abs_of_nonneg (hw k)]
        _ = qGeometricStopWeight γ k *
              (∑ path, |qStoppedPrefixKLAtom ((qForcedPrefixLaw M' π s a k).prob path)
                ((qForcedPrefixLaw M π s a k).prob path)|) := by
          rw [Finset.mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (hfiberAbs k) (hw k)
    exact Summable.of_nonneg_of_le
      (fun k ↦ tsum_nonneg fun path ↦ hgNonneg ⟨k, path⟩)
      houter hWeightedMajorant

end StatisticalRL.QLearning.CountablePinsker
