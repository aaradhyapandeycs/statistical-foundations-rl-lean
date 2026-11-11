import Formalization.Online.Regret.MVP.Decoupling.MVPVisitValueLookup
import Formalization.Online.Regret.MVP.Decoupling.MVPSourceIotaEndpoints

/-! exact adaptive-value regrouping into the source dyadic slots. -/
namespace StatisticalRL.OnlineRL
open scoped BigOperators
variable {Row Value : Type*} [AddCommMonoid Value]

theorem mvp_adaptiveVisit_sum_dyadicSlots [DecidableEq Row]
    (rows : ℕ → Row) (K : ℕ) (r : Row) (V : Fin K → Value)
    (G : ℕ → Value → ℝ) (hG : ∀ u, G u 0 = 0) :
    (∑ k : Fin K, if rows k.val = r then
      G (onlineVisitCount rows k.val r) (V k) else 0) =
      G 0 (mvp_visitValueLookup rows K r 0 V) +
      G 1 (mvp_visitValueLookup rows K r 1 V) +
      ∑ j ∈ Finset.range (Nat.log2 K), ∑ i ∈ Finset.range (2*2^j),
        G (2*2^j+i) (mvp_visitValueLookup rows K r (2*2^j+i) V) := by
  rw [← mvp_visitValueLookup_sum rows K r V G hG]
  apply mvp_sum_sourceDyadicSlots_zeroExtended
  intro u hu
  rw [mvp_visitValueLookup_zero_of_ge rows K r u V hu, hG]

end StatisticalRL.OnlineRL
