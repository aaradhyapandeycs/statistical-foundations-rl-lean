import Formalization.Online.SourceOptimism.FreshCoordinateSelection
import Formalization.Online.SourceOptimism.SourceBonusCompatibleBernstein

/-! A deterministic row-prefix projection of
the actual stack product has the actual iid row law; no random-count iid. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {Row State : Type*} [Fintype Row] [Fintype State]
local instance onlinePrefixMarginalStateMeasurable : MeasurableSpace State := ⊤

def onlineStackRowPrefix (K n : ℕ) (hn : n≤K) (r : Row)
    (data : Row × Fin K → State) : Fin n → State :=
  fun j => data (r,⟨j.val,j.isLt.trans_le hn⟩)

/-- A deterministic prefix of one pre-sampled row is exactly iid from that
true row. The entire other-row array remains in the same product experiment. -/
theorem onlineStackRowPrefix_map_law
    (d : Row → FiniteDistribution State) (K n : ℕ) (hn : n≤K) (r : Row) :
    (onlineStackProductLaw (fun i : Row × Fin K => d i.1)).map
      (onlineStackRowPrefix K n hn r)=(d r).sampleMeasure n := by
  let μ := onlineStackProductLaw (fun i : Row × Fin K => d i.1)
  let label := fun j : Fin n => (r,(⟨j.val,j.isLt.trans_le hn⟩ : Fin K))
  have hinj : Function.Injective label := by
    intro j k h
    apply Fin.ext
    exact congrArg (fun p : Row × Fin K => p.2.val) h
  have hall : iIndepFun (fun i (data : Row × Fin K → State) => data i) μ :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hprefix : iIndepFun (fun j (data : Row × Fin K → State) => data (label j)) μ :=
    hall.precomp hinj
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map
    (fun j => (measurable_pi_apply (label j)).aemeasurable)).mp hprefix
  change μ.map (fun data j => data (label j))=Measure.pi (fun _ : Fin n => (d r).rowMeasure)
  rw [hmap]
  congr 1
  funext j
  exact (measurePreserving_eval (fun i : Row × Fin K => (d i.1).rowMeasure) (label j)).map_eq

/-- Source-compatible fixed-V bonus confidence transferred to the common
actual row-stack law by the proved deterministic prefix marginal. -/
theorem onlineStackRowPrefix_bonus_confidence
    (d : Row → FiniteDistribution State) (V : State → ℝ)
    (K n : ℕ) (hn : n≤K) (hnpos : 0<n) (r : Row)
    (H δ c₁ c₂ : ℝ) (hH : 0<H) (hδ : 0<δ) (hδsmall : δ≤2/5)
    (hc₁ : 4≤c₁) (hc₂ : c₁^2≤c₂) (hV : ∀ s,V s∈Set.Icc 0 H) :
    1-2*δ ≤ (onlineStackProductLaw (fun i : Row × Fin K => d i.1)).real
      {data | ∀ U : State → ℝ, (∀ s,V s≤U s ∧ U s≤H) →
        (d r).expectation V≤
          (FiniteDistribution.empiricalRow n hnpos (onlineStackRowPrefix K n hn r data)).expectation U+
          c₁*Real.sqrt ((FiniteDistribution.empiricalRow n hnpos
            (onlineStackRowPrefix K n hn r data)).variance U*(Real.log (1/δ)/n))+
          c₂*H*(Real.log (1/δ)/n)} := by
  let good : Set (Fin n → State) := {data | ∀ U : State → ℝ,
    (∀ s,V s≤U s ∧ U s≤H) → (d r).expectation V≤
      (FiniteDistribution.empiricalRow n hnpos data).expectation U+
      c₁*Real.sqrt ((FiniteDistribution.empiricalRow n hnpos data).variance U*
        (Real.log (1/δ)/n))+c₂*H*(Real.log (1/δ)/n)}
  have h := onlineFixedPrefix_source_bonus_confidence (d r) V n hnpos H δ c₁ c₂
    hH hδ hδsmall hc₁ hc₂ hV
  have heq : (onlineStackProductLaw (fun i : Row × Fin K => d i.1)).real
      ((onlineStackRowPrefix K n hn r) ⁻¹' good)=((d r).sampleMeasure n).real good := by
    rw [measureReal_def,← Measure.map_apply (measurable_of_countable _)
      ((Set.to_countable good).measurableSet),onlineStackRowPrefix_map_law]
    rfl
  change 1-2*δ≤(onlineStackProductLaw (fun i : Row × Fin K => d i.1)).real
    ((onlineStackRowPrefix K n hn r) ⁻¹' good)
  rw [heq]
  exact h

end StatisticalRL.OnlineRL
