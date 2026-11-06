import Formalization.Generative.FiniteHorizonSamplingDefinitions
import Formalization.Online.Regret.MVP.MVPProfileDefinitions
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-! Definition-only source objects for corrected MVP uniform concentration.
The family at current stage h denotes the source continuation family at h+1.
No terminal-zero condition is imposed on this generic family. -/
namespace StatisticalRL.OnlineRL.MVPUniformSource

variable {State Action : Type*} [Fintype State] [Fintype Action]
local instance : MeasurableSpace State := ⊤

/-- The monotone ceiling cover, including the manuscript's integer profiles
and every actual pre-episode profile (source issue C15). -/
abbrev Profiles (H K : ℕ) :=
  MVPProfile.MonotoneProfiles K (Fintype.card (Fin H × (State × Action)))
    (MVPProfile.profileLevelCap K)

/-- Exactly the expanded-sample coordinates at stages strictly later than h. -/
noncomputable def futureIndices {H : ℕ} (h : Fin H) (K : ℕ) :
    Finset (FiniteHorizonGenerative.SampleIndex State Action H K) :=
  Finset.univ.filter (fun i => h < i.1.1)

/-- A complete strictly-future data block; the source empirical summaries
are deterministic functions of this block. -/
abbrev FutureCode {H : ℕ} (h : Fin H) (K : ℕ) :=
  (i : futureIndices (State := State) (Action := Action) h K) → State

def futureData {H : ℕ} (h : Fin H) (K : ℕ)
    (data : FiniteHorizonGenerative.Samples State Action H K) :
    FutureCode (State := State) (Action := Action) h K := fun i => data i

/-- Source level l=j+2 uses the samples with zero-based positions
2^j,...,2^(j+1)-1. The finite level itself proves these positions fit. -/
def batchIndex {K : ℕ} (j : Fin (Nat.log2 K)) (i : Fin (2^j.val)) : Fin K := by
  have hK : 0 < K := by
    by_contra hn
    have hz : K = 0 := by omega
    have hj := j.isLt
    simp [hz] at hj
  have hp : 2^(j.val+1) ≤ 2^Nat.log2 K :=
    Nat.pow_le_pow_right (by decide) j.isLt
  have hc : 2^Nat.log2 K ≤ K := Nat.log2_self_le (Nat.ne_of_gt hK)
  have hfit : 2*(2^j.val) ≤ K := by
    calc
      2*(2^j.val) = 2^(j.val+1) := by simp [pow_succ, Nat.mul_comm]
      _ ≤ 2^Nat.log2 K := hp
      _ ≤ K := hc
  exact ⟨2^j.val+i.val, by have hi := i.isLt; omega⟩

/-- The source's noninitial empirical batch row, without an out-of-range
default branch. At K=1 there is no such level. -/
noncomputable def batchRow {H K : ℕ}
    (data : FiniteHorizonGenerative.Samples State Action H K)
    (j : Fin (Nat.log2 K)) (h : Fin H) (s : State) (a : Action) :
    FiniteDistribution State :=
  FiniteDistribution.empiricalRow (2^j.val) (by positivity)
    (fun i => data ((h,s,a),batchIndex j i))

end StatisticalRL.OnlineRL.MVPUniformSource
