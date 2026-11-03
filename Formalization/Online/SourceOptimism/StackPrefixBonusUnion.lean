import Formalization.Online.SourceOptimism.StackPrefixMarginal
import Formalization.Online.SourceOptimism.VisitPrefixConcentrationUnion

/-! Actual common stack-law concentration for
all fixed row/count prefixes with printed factor2 and no random-count iid. -/
namespace StatisticalRL.OnlineRL
open MeasureTheory ProbabilityTheory
variable {Row State : Type*} [Fintype Row] [Nonempty Row] [Fintype State]
local instance onlineStackUnionStateMeasurable : MeasurableSpace State := ⊤

/-- Good source-compatible certificates at a fixed positive prefix; other
counts are intentionally unconstrained because their source branch is separate. -/
noncomputable def onlineStackPrefixBonusGood
    (d : Row → FiniteDistribution State) (V : Row → State → ℝ)
    (K : ℕ) (H δ c₁ c₂ : ℝ) (r : Row) (n : ℕ) : Set (Row × Fin K → State) :=
  if hn : 3≤n ∧ n<K then
    {data | ∀ U : State → ℝ, (∀ s,V r s≤U s ∧ U s≤H) →
      (d r).expectation (V r)≤
        (FiniteDistribution.empiricalRow n (by omega)
          (onlineStackRowPrefix K n (by omega) r data)).expectation U+
        c₁*Real.sqrt ((FiniteDistribution.empiricalRow n (by omega)
          (onlineStackRowPrefix K n (by omega) r data)).variance U*(Real.log (1/δ)/n))+
        c₂*H*(Real.log (1/δ)/n)}
  else Set.univ

/-- One actual product experiment supplies every row and deterministic prefix
certificate with strict probability exceeding1−2 R K δ. The certificates are
uniform over every optimistic continuation, allowing same-data postselection. -/
theorem onlineStack_allPrefixes_sourceBonus_strict
    (d : Row → FiniteDistribution State) (V : Row → State → ℝ)
    (K : ℕ) (hK : 0<K) (H δ c₁ c₂ : ℝ)
    (hH : 0<H) (hδ : 0<δ) (hδsmall : δ≤2/5)
    (hc₁ : 4≤c₁) (hc₂ : c₁^2≤c₂) (hV : ∀ r s,V r s∈Set.Icc 0 H) :
    1-2*(Fintype.card Row : ℝ)*K*δ <
      (onlineStackProductLaw (fun i : Row × Fin K => d i.1)).real
        {data | ∀ r n,3≤n → n<K →
          data∈onlineStackPrefixBonusGood d V K H δ c₁ c₂ r n} := by
  classical
  apply onlineFixedPrefix_union_strict _ K hK δ hδ
    (onlineStackPrefixBonusGood d V K H δ c₁ c₂)
  intro r n hn hnK
  have hgood := onlineStackRowPrefix_bonus_confidence d (V r) K n (by omega)
    (by omega) r H δ c₁ c₂ hH hδ hδsmall hc₁ hc₂ (hV r)
  have hcomp := measureReal_compl
    (μ := onlineStackProductLaw (fun i : Row × Fin K => d i.1))
    ((Set.to_countable (onlineStackPrefixBonusGood d V K H δ c₁ c₂ r n)).measurableSet)
  rw [probReal_univ] at hcomp
  have hbounds : 3 ≤ n ∧ n < K := ⟨hn, hnK⟩
  simp only [onlineStackPrefixBonusGood,dif_pos hbounds] at hcomp ⊢
  linarith

end StatisticalRL.OnlineRL
