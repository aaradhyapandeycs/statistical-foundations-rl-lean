import Formalization.Ch7Rest.Marl76Main
import Formalization.Ch7Rest.Marl76Statement

/-!
# Theorem 7.6 (restricted): the three clauses

`thm7_6_restricted : Thm7_6_restricted` with `C₁ = 400`: (a) causal CCE oracles, (b) causal NE
oracles, (c) the printed joint conclusion. Each clause is `core` with two data-causal maps.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl76

open StatisticalRL StatisticalRL.Ch7Rest.Marl

theorem thm7_6_restricted : Thm7_6_restricted := by
  refine ⟨400, by norm_num, ?_⟩
  intro m S H A hS hA G hR N hN δ ε hδ hδ1 hε hεH hthr
  set Gh := empiricalGame G N hN
  have hfin : ∀ (Pol : Fin 2 → GameSamples m S H A N → JointPolicy m S A),
      (∀ o, DataCausal (Pol o)) → (∀ o data, IsCCE (Gh data) (Pol o data)) →
      1 - δ ≤ (gameSamplingLaw G hS hA N).real {data | ∀ o, gapJ G (Pol o data) ≤ ε} :=
    fun Pol hPol hcce => core G hR hS hA N hN δ ε hδ hδ1 hε hεH hthr Pol hPol hcce
  refine ⟨?_, ?_, ?_⟩
  · intro O hO hcce
    have h := hfin (fun _ data => O (Gh data)) (fun _ => hO.dataCausal G N hN)
      (fun _ data => hcce data)
    exact h.trans (measureReal_mono (fun data hd => hd 0) (measure_ne_top _ _))
  · intro O hO hne
    have h := hfin (fun _ data => toJoint (O (Gh data))) (fun _ => hO.toJoint.dataCausal G N hN)
      (fun _ data => (hne data).isCCE)
    refine h.trans (measureReal_mono (fun data hd => ?_) (measure_ne_top _ _))
    have := hd 0
    simp only [Set.mem_setOf_eq]
    rwa [← gapJ_toJoint]
  · intro One Occe hOne hOcce hne hcce
    let Pol : Fin 2 → GameSamples m S H A N → JointPolicy m S A := fun o data =>
      if (o : ℕ) = 0 then toJoint (One (Gh data)) else Occe (Gh data)
    have hPol : ∀ o, DataCausal (Pol o) := by
      intro o
      by_cases ho : (o : ℕ) = 0
      · simp only [Pol, ho, if_true]; exact hOne.toJoint.dataCausal G N hN
      · simp only [Pol, ho, if_false]; exact hOcce.dataCausal G N hN
    have hc : ∀ o data, IsCCE (Gh data) (Pol o data) := by
      intro o data
      by_cases ho : (o : ℕ) = 0
      · simp only [Pol, ho, if_true]; exact (hne data).isCCE
      · simp only [Pol, ho, if_false]; exact hcce data
    have h := hfin Pol hPol hc
    refine h.trans (measureReal_mono (fun data hd => ?_) (measure_ne_top _ _))
    have h0 := hd 0
    have h1 := hd 1
    simp only [Pol, Fin.val_zero, Fin.val_one, if_true, one_ne_zero, if_false] at h0 h1
    exact ⟨by rwa [← gapJ_toJoint], h1⟩

end StatisticalRL.Ch7Rest.Marl76
