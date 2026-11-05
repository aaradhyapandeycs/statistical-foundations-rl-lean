import Mathlib
import Formalization.OfflineRL.RankedPair

/-! Projection from the source's finite transition stacks to the emitted
next-state observations. The index map is proved injective; the fixed-label law
and iid-label composition are handled by separate results. -/

open MeasureTheory ProbabilityTheory

namespace StatisticalRL.OfflineRL.StackProjection

/-- Selecting coordinates along an injective index map pushes a product of
probability measures to the product of the selected factors. -/
theorem pi_map_comp_injective {ι κ S : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace S] (ν : κ → Measure S) [∀ k, IsProbabilityMeasure (ν k)]
    (g : ι → κ) (hg : Function.Injective g) :
    (Measure.pi ν).map (fun ω : κ → S => fun i => ω (g i)) =
      Measure.pi (fun i => ν (g i)) := by
  classical
  have hmeas : Measurable (fun ω : κ → S => fun i => ω (g i)) :=
    measurable_pi_lambda _ fun i => measurable_pi_apply (g i)
  symm
  refine Measure.pi_eq fun s hs => ?_
  let t : κ → Set S := fun k => ⋂ (i : ι) (_ : g i = k), s i
  have ht : ∀ k, MeasurableSet (t k) := fun k =>
    MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => hs i
  have hpre : (fun ω : κ → S => fun i => ω (g i)) ⁻¹' Set.univ.pi s = Set.univ.pi t := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_univ_pi, t, Set.mem_iInter]
    constructor
    · intro h k i hik
      subst hik
      exact h i
    · intro h i
      exact h (g i) i rfl
  rw [Measure.map_apply hmeas (MeasurableSet.univ_pi hs), hpre, Measure.pi_pi]
  symm
  refine Fintype.prod_of_injective g hg _ _ ?_ ?_
  · intro k hk
    have : t k = Set.univ := by
      ext x
      simp only [t, Set.mem_iInter, Set.mem_univ, iff_true]
      intro i hik
      exact absurd ⟨i, hik⟩ hk
    rw [this, measure_univ]
  · intro i
    have : t (g i) = s i := by
      ext x
      simp only [t, Set.mem_iInter]
      constructor
      · intro h; exact h i rfl
      · intro hx j hj; rw [hg hj]; exact hx
    rw [this]

/-- Under a product of probability measures, the coordinates selected along an
injective index map are independent. -/
theorem iIndepFun_comp_injective {ι κ S : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace S] (ν : κ → Measure S) [∀ k, IsProbabilityMeasure (ν k)]
    (g : ι → κ) (hg : Function.Injective g) :
    iIndepFun (fun i (ω : κ → S) => ω (g i)) (Measure.pi ν) := by
  rw [iIndepFun_iff_map_fun_eq_pi_map fun i => (measurable_pi_apply (g i)).aemeasurable,
    pi_map_comp_injective ν g hg]
  congr 1
  funext i
  exact ((measurePreserving_eval ν (g i)).map_eq).symm

variable {Row S : Type*} [Fintype Row] [DecidableEq Row] [MeasurableSpace S] {n : ℕ}

/-- The (row, slot) stack law: coordinate `(r, k)` is an independent draw from
the actual transition law `P r` of row `r`. -/
noncomputable def stackLaw (P : Row → Measure S) (n : ℕ) : Measure (Row × Fin n → S) :=
  Measure.pi fun p : Row × Fin n => P p.1

/-- For a fixed label sequence, sample `i` reads the stack at its row and its
strict-past visit rank. -/
def selectByRank (l : Fin n → Row) (ω : Row × Fin n → S) : Fin n → S :=
  fun i => ω (l i, RankedPair.visitRankFin l i)

/-- Fixed-label stack projection law: the selected next states have exactly the
product of the actual row transition laws. -/
theorem stackLaw_map_selectByRank (P : Row → Measure S) [∀ r, IsProbabilityMeasure (P r)]
    (l : Fin n → Row) :
    (stackLaw P n).map (selectByRank l) = Measure.pi fun i => P (l i) :=
  pi_map_comp_injective (fun p : Row × Fin n => P p.1)
    (fun i => (l i, RankedPair.visitRankFin l i)) (RankedPair.rankedPairFin_injective l)

/-- The selected next states are independent under the stack law. -/
theorem iIndepFun_selectByRank (P : Row → Measure S) [∀ r, IsProbabilityMeasure (P r)]
    (l : Fin n → Row) :
    iIndepFun (fun i (ω : Row × Fin n → S) => selectByRank l ω i) (stackLaw P n) :=
  iIndepFun_comp_injective (fun p : Row × Fin n => P p.1)
    (fun i => (l i, RankedPair.visitRankFin l i)) (RankedPair.rankedPairFin_injective l)

/-- Each selected next state has the actual transition law of its row. -/
theorem stackLaw_map_selectByRank_apply (P : Row → Measure S)
    [∀ r, IsProbabilityMeasure (P r)] (l : Fin n → Row) (i : Fin n) :
    (stackLaw P n).map (fun ω => selectByRank l ω i) = P (l i) :=
  (measurePreserving_eval (fun p : Row × Fin n => P p.1)
    (l i, RankedPair.visitRankFin l i)).map_eq

end StatisticalRL.OfflineRL.StackProjection
