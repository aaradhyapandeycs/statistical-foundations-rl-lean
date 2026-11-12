import Formalization.Online.Regret.MVP.MVPCountDefinitions
import Formalization.Online.Regret.W1.OnlineW1StageEpisodeCount
import Mathlib.Data.Nat.Log

/-! MVP count and deterministic visit-budget results. -/
namespace StatisticalRL.OnlineRL

/-- Finite diagnostic for the proof's proposed pointwise factor-two claim.
It is not a counterexample to the lemma's final summed inequality. -/
theorem onlineMVP_factor_two_pointwise_fails : 2 * onlineMVPStoredCount 3 < 3 := by
  decide

end StatisticalRL.OnlineRL
