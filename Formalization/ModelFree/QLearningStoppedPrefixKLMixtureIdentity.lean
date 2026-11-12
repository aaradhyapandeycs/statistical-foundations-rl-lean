import Formalization.ModelFree.QLearningStoppedPrefixKLAbsSummable

/-! Geometric stopped-prefix atomic KL mixture identity. -/

open scoped BigOperators
namespace StatisticalRL.QLearning.CountablePinsker

variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- The common geometric stopped-prefix atom series equals the geometric
mixture of the actual finite forced-prefix KLs. The numerator is the primed
model, the reference is the nominal model, and each fiber has exactly the
source's `k` transitions after the fixed initial state/action. The row support
and KL assumptions are the same ones used by the preceding absolute
summability theorem, which justifies exchanging the dependent `Σ k` sum and
its fiber series. -/
theorem qActualStoppedPrefixKL_mixture_identity
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
        (qActualStoppedPrefixMass M π γ s a z)) =
      ∑' k : ℕ, qGeometricStopWeight γ k *
        StatisticalRL.GenerativeLowerBound.finiteKLExpression
          (fun path ↦ (qForcedPrefixLaw M' π s a k).prob path)
          (fun path ↦ (qForcedPrefixLaw M π s a k).prob path) := by
  let f : qStoppedPrefixAbsCarrier (State := State) (Action := Action) → ℝ :=
    fun z ↦ qStoppedPrefixKLAtom (qActualStoppedPrefixMass M' π γ s a z)
      (qActualStoppedPrefixMass M π γ s a z)
  have habs := qActualStoppedPrefixKL_abs_summable
    M M' π γ ρ s a hγ hγ1 hρ hrowSupport hrowKL
  have hsum : Summable f := by
    apply habs.of_abs.congr
    intro z
    rfl
  have hfiberAtoms (k : ℕ) :
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
  have hscale (k : ℕ) (path : QForcedPrefix (State := State) (Action := Action) k) :
      f ⟨k, path⟩ = qGeometricStopWeight γ k *
        qStoppedPrefixKLAtom ((qForcedPrefixLaw M' π s a k).prob path)
          ((qForcedPrefixLaw M π s a k).prob path) := by
    change qStoppedPrefixKLAtom
        (qGeometricStopWeight γ k * qForcedPrefixWeight M' π s a k path)
        (qGeometricStopWeight γ k * qForcedPrefixWeight M π s a k path) =
      qGeometricStopWeight γ k * qStoppedPrefixKLAtom
        (qForcedPrefixWeight M' π s a k path)
        (qForcedPrefixWeight M π s a k path)
    exact qStoppedPrefixKLAtom_geometric_scale γ k _ _ hγ hγ1
      ((qForcedPrefixLaw M' π s a k).prob_nonneg path)
      ((qForcedPrefixLaw M π s a k).prob_nonneg path)
      (qForcedPrefixWeight_support M M' π s a k hrowSupport path)
  have hfiber (k : ℕ) :
      (∑' path : QForcedPrefix (State := State) (Action := Action) k,
        f ⟨k, path⟩) =
        qGeometricStopWeight γ k *
          StatisticalRL.GenerativeLowerBound.finiteKLExpression
            (fun path ↦ (qForcedPrefixLaw M' π s a k).prob path)
            (fun path ↦ (qForcedPrefixLaw M π s a k).prob path) := by
    rw [tsum_fintype]
    calc
      (∑ path, f ⟨k, path⟩) =
          ∑ path, qGeometricStopWeight γ k *
            qStoppedPrefixKLAtom ((qForcedPrefixLaw M' π s a k).prob path)
              ((qForcedPrefixLaw M π s a k).prob path) := by
        apply Finset.sum_congr rfl
        intro path _
        exact hscale k path
      _ = qGeometricStopWeight γ k *
          ∑ path, qStoppedPrefixKLAtom ((qForcedPrefixLaw M' π s a k).prob path)
            ((qForcedPrefixLaw M π s a k).prob path) := by
        rw [Finset.mul_sum]
      _ = qGeometricStopWeight γ k *
          StatisticalRL.GenerativeLowerBound.finiteKLExpression
            (fun path ↦ (qForcedPrefixLaw M' π s a k).prob path)
            (fun path ↦ (qForcedPrefixLaw M π s a k).prob path) := by
        rw [← hfiberAtoms k]
  change (∑' z, f z) = _
  calc
    (∑' z : qStoppedPrefixAbsCarrier (State := State) (Action := Action), f z) =
        ∑' k : ℕ, ∑' path : QForcedPrefix (State := State) (Action := Action) k,
          f ⟨k, path⟩ := hsum.tsum_sigma
    _ = ∑' k : ℕ, qGeometricStopWeight γ k *
          StatisticalRL.GenerativeLowerBound.finiteKLExpression
            (fun path ↦ (qForcedPrefixLaw M' π s a k).prob path)
            (fun path ↦ (qForcedPrefixLaw M π s a k).prob path) :=
      tsum_congr hfiber

/-- The same mixture identity with each actual finite prefix KL replaced by
the recursion cost already identified with that law. This version makes the
transition-row chain-rule consumer explicit. -/
theorem qActualStoppedPrefixKL_mixture_eq_rec
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
        (qActualStoppedPrefixMass M π γ s a z)) =
      ∑' k : ℕ, qGeometricStopWeight γ k *
        qForcedPrefixKLRec M M' π s a k := by
  rw [qActualStoppedPrefixKL_mixture_identity M M' π γ ρ s a
    hγ hγ1 hρ hrowSupport hrowKL]
  exact tsum_congr fun k ↦ congrArg (fun x : ℝ ↦ qGeometricStopWeight γ k * x)
    (qForcedPrefixLaw_finiteKL_eq_rec M M' π k hrowSupport s a)

end StatisticalRL.QLearning.CountablePinsker
