import Formalization.Online.Regret.MVP.MVPCountDefinitions
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Nat.Log

/-! Source definitions for MVP total profiles and their finite row-table carrier. -/
namespace StatisticalRL.OnlineRL.MVPProfile

open StatisticalRL.OnlineRL
open scoped BigOperators

/-- A single row's nondecreasing profile sequence with levels `0` through `J`. -/
abbrev MonotoneRowProfile (K J : ℕ) :=
  { f : Fin K → Fin (J + 1) // Monotone f }

noncomputable instance instFintypeMonotoneRowProfile (K J : ℕ) :
    Fintype (MonotoneRowProfile K J) := Fintype.ofFinite _

/-- All rowwise monotone profiles, represented as a bounded function table. -/
abbrev MonotoneProfiles (K d J : ℕ) :=
  { p : Fin K → Fin d → Fin (J + 1) // ∀ r, Monotone (fun k => p k r) }

noncomputable instance instFintypeMonotoneProfiles (K d J : ℕ) :
    Fintype (MonotoneProfiles K d J) := Fintype.ofFinite _

/-- The source's real logarithm base two. -/
noncomputable def logTwoReal (K : ℕ) : ℝ :=
  Real.log (K : ℝ) / Real.log 2

/-- Safe integer ceiling for the source profile level. -/
def profileLevelCap (K : ℕ) : ℕ := Nat.log2 (K - 1) + 1

/-- A complete episode-by-stage row table. -/
abbrev EpisodeRowTable (H : ℕ) (Row : Type*) := ℕ → Fin H → Row

/-- Flatten an episode-by-stage table into the chronological stage-tagged row
sequence used by the operational counter fold. -/
noncomputable def sourceMVPFlattenRows {H : ℕ} {Row : Type*}
    (rows : EpisodeRowTable H Row) (hH : 0 < H) : ℕ → Fin H × Row :=
  fun t =>
    let h : Fin H := ⟨t % H, Nat.mod_lt _ hH⟩
    (h, rows (t / H) h)

/-- The source's integer threshold maximum: zero at zero count and
`floor(log₂ n)+1` at positive count. -/
def sourceMVPProfileIndex (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.log2 n + 1

/-- The literal pre-episode cumulative visit count for one stage and row. -/
noncomputable def sourceMVPVisitCount {H : ℕ} {Row : Type*}
    (rows : EpisodeRowTable H Row) (k : ℕ) (h : Fin H) (r : Row) : ℕ := by
  classical
  exact ((Finset.range k).filter (fun e => rows e h = r)).card

/-- Source total-profile entry: profile index of the cumulative count before
episode `k`. -/
noncomputable def sourceMVPActualProfile {K H : ℕ} {Row : Type*}
    (rows : EpisodeRowTable H Row) (k : Fin K)
    (h : Fin H) (r : Row) : ℕ :=
  sourceMVPProfileIndex (sourceMVPVisitCount rows k.val h r)

/-- The row table's profile, encoded in the finite monotone family. Its proof
fields express the direct count monotonicity and the count bound `N≤K−1`. -/
noncomputable def sourceMVPActualProfileTable {K H : ℕ} {Row : Type*}
    [Fintype Row] (rows : EpisodeRowTable H Row) :
    MonotoneProfiles K (Fintype.card (Fin H × Row)) (profileLevelCap K) := by
  classical
  letI : DecidableEq Row := Classical.decEq Row
  let e : (Fin H × Row) ≃ Fin (Fintype.card (Fin H × Row)) := Fintype.equivFin _
  refine ⟨fun k i => ⟨sourceMVPActualProfile rows k (e.symm i).1 (e.symm i).2, ?_⟩,
    ?_⟩
  · have hcount : sourceMVPVisitCount rows k.val (e.symm i).1 (e.symm i).2 ≤ k.val := by
      unfold sourceMVPVisitCount
      calc
        _ ≤ (Finset.range k.val).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = k.val := Finset.card_range _
    have hsource : sourceMVPVisitCount rows k.val (e.symm i).1 (e.symm i).2 ≤ K - 1 := by
      omega
    have hindex : sourceMVPProfileIndex
        (sourceMVPVisitCount rows k.val (e.symm i).1 (e.symm i).2) ≤ profileLevelCap K := by
      by_cases hz : sourceMVPVisitCount rows k.val (e.symm i).1 (e.symm i).2 = 0
      · simp [sourceMVPProfileIndex, profileLevelCap, hz]
      · have hlog : Nat.log2
            (sourceMVPVisitCount rows k.val (e.symm i).1 (e.symm i).2) ≤ Nat.log2 (K - 1) := by
          simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) hsource
        simp [sourceMVPProfileIndex, profileLevelCap, hz]
        omega
    exact Nat.lt_succ_of_le hindex
  · intro i k₁ k₂ hk
    have hcount : sourceMVPVisitCount rows k₁.val (e.symm i).1 (e.symm i).2 ≤
        sourceMVPVisitCount rows k₂.val (e.symm i).1 (e.symm i).2 := by
      unfold sourceMVPVisitCount
      apply Finset.card_le_card
      intro x hx
      have hx' := Finset.mem_filter.mp hx
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx'.1) hk), hx'.2⟩
    have hidx : sourceMVPProfileIndex
        (sourceMVPVisitCount rows k₁.val (e.symm i).1 (e.symm i).2) ≤
        sourceMVPProfileIndex (sourceMVPVisitCount rows k₂.val (e.symm i).1 (e.symm i).2) := by
      by_cases hz : sourceMVPVisitCount rows k₁.val (e.symm i).1 (e.symm i).2 = 0
      · simp [sourceMVPProfileIndex, hz]
      · have hz₂ : sourceMVPVisitCount rows k₂.val (e.symm i).1 (e.symm i).2 ≠ 0 := by omega
        simp [sourceMVPProfileIndex, hz, hz₂]
        simpa only [Nat.log2_eq_log_two] using Nat.log_mono_right (b := 2) hcount
    exact hidx

/-- Extend a finite K-episode row table; the arbitrary suffix is never used by
pre-episode source counts. -/
noncomputable def sourceMVPExtendFiniteRows {K H : ℕ} {Row : Type*}
    [Nonempty Row] (rows : Fin K → Fin H → Row) : EpisodeRowTable H Row := by
  classical
  exact fun e h => if he : e < K then rows ⟨e, he⟩ h else Classical.choice ‹Nonempty Row›

/-- Finite set of all source profiles generated by arbitrary K-episode row
tables. This covers every realized algorithm trajectory. -/
noncomputable def sourceMVPFinitePossibleProfiles {K H : ℕ} {Row : Type*}
    [Fintype Row] [Nonempty Row] :
    Finset (MonotoneProfiles K (Fintype.card (Fin H × Row)) (profileLevelCap K)) := by
  classical
  letI : DecidableEq Row := Classical.decEq Row
  exact Finset.univ.image fun rows : Fin K → Fin H → Row =>
    sourceMVPActualProfileTable (sourceMVPExtendFiniteRows rows)

/-- The operational per-row counter table after `k*H` actual chronological
row/successor records. -/
noncomputable def sourceMVPOperationalTablesAt {K H : ℕ} {Row Outcome : Type*}
    [Fintype Outcome] [DecidableEq Row] [DecidableEq Outcome]
    (rows : EpisodeRowTable H Row) (nextAt : ℕ → Outcome) (hH : 0 < H) (k : Fin K) :
    OnlineMVPCountTables (Fin H × Row) Outcome :=
  onlineMVPCountTablesRun (sourceMVPFlattenRows rows hH) nextAt (k.val * H)

end StatisticalRL.OnlineRL.MVPProfile
