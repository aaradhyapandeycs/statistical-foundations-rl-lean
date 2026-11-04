import Formalization.Online.Regret.MVP.MVPCountDefinitions
import Formalization.Online.Regret.MVP.MVPProfileDefinitions
import Formalization.Online.Regret.MVP.MVPProfileCardinality
import Formalization.Online.Regret.MVP.OnlineMVPOperationalCounters
import Formalization.Online.Regret.W1.OnlineW1StageEpisodeCount
import Formalization.Online.SourceOptimism.VisitCountFoundation

/-! Actual cumulative-count profiles and their inclusion in the finite family. -/
namespace StatisticalRL.OnlineRL.MVPProfile

open StatisticalRL.OnlineRL


theorem sourceMVPFlattenRows_stage {H : ℕ} {Row : Type*}
    (rows : EpisodeRowTable H Row) (hH : 0 < H) (t : ℕ) :
    (sourceMVPFlattenRows rows hH t).1.val = t % H := by
  simp [sourceMVPFlattenRows]

theorem sourceMVPFlattenRows_episode_stage {H : ℕ} {Row : Type*}
    (rows : EpisodeRowTable H Row) (hH : 0 < H) (e : ℕ) (h : Fin H) :
    sourceMVPFlattenRows rows hH (e * H + h.val) = (h, rows e h) := by
  apply Prod.ext
  · apply Fin.ext
    change (e * H + h.val) % H = h.val
    rw [Nat.add_comm, Nat.mul_comm e H, Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt h.isLt
  · change rows ((e * H + h.val) / H) ⟨(e * H + h.val) % H, _⟩ = rows e h
    have hmod : (e * H + h.val) % H = h.val := by
      rw [Nat.add_comm, Nat.mul_comm e H, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt h.isLt
    have hdiv : (e * H + h.val) / H = e := by
      rw [Nat.add_comm, Nat.mul_comm e H, Nat.add_mul_div_left _ _ hH,
        Nat.div_eq_of_lt h.isLt, Nat.zero_add]
    simp [hmod, hdiv]

theorem sourceMVP_visitCount_eq_episode_rows {H : ℕ} {Row : Type*}
    [DecidableEq Row] (rows : EpisodeRowTable H Row) (hH : 0 < H)
    (k : ℕ) (h : Fin H) (r : Row) :
    onlineVisitCount (sourceMVPFlattenRows rows hH) (k * H) (h, r) =
      onlineVisitCount (fun e => rows e h) k r := by
  classical
  rw [onlineVisitCount_stage_episode_eq (sourceMVPFlattenRows rows hH) h k hH
    (h, r) rfl (fun _ _ => sourceMVPFlattenRows_stage rows hH _)]
  rw [onlineVisitCount, onlineVisitCount]
  congr 1
  ext e
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨he, heq⟩
    rw [sourceMVPFlattenRows_episode_stage rows hH e h] at heq
    exact ⟨he, (Prod.mk.inj heq).2⟩
  · rintro ⟨he, heq⟩
    rw [sourceMVPFlattenRows_episode_stage rows hH e h]
    exact ⟨he, Prod.ext rfl heq⟩

theorem sourceMVP_operationalTotal_eq_episode_count
    {H K : ℕ} {Row Outcome : Type*} [Fintype Outcome]
    [DecidableEq Row] [DecidableEq Outcome]
    (rows : EpisodeRowTable H Row) (nextAt : ℕ → Outcome)
    (hH : 0 < H) (k : Fin K) (h : Fin H) (r : Row) :
    (onlineMVPCountTablesRun (sourceMVPFlattenRows rows hH) nextAt (k.val * H)).total
        (h, r) = onlineVisitCount (fun e => rows e h) k.val r := by
  rw [(onlineMVPCountTablesRun_row_invariant (sourceMVPFlattenRows rows hH)
    nextAt (k.val * H) (h, r)).1]
  exact sourceMVP_visitCount_eq_episode_rows rows hH k.val h r


theorem sourceMVPProfileIndex_eq_log_succ {n : ℕ} (hn : 0 < n) :
    sourceMVPProfileIndex n = Nat.log2 n + 1 := by
  simp [sourceMVPProfileIndex, Nat.ne_of_gt hn]

/-- The floor-log index is exactly the source's positive-count threshold:
`2^(index−1) ≤ n < 2^index`. -/
theorem sourceMVPProfileIndex_threshold {n : ℕ} (hn : 0 < n) :
    2 ^ (sourceMVPProfileIndex n - 1) ≤ n ∧
      n < 2 ^ sourceMVPProfileIndex n := by
  rw [sourceMVPProfileIndex_eq_log_succ hn]
  constructor
  · simpa only [Nat.log2_eq_log_two] using
      Nat.pow_log_le_self 2 (Nat.ne_of_gt hn)
  · simpa [Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self Nat.one_lt_two n

theorem sourceMVPProfileIndex_mono : Monotone sourceMVPProfileIndex := by
  intro m n hmn
  by_cases hm : m = 0
  · simp [sourceMVPProfileIndex, hm]
  · have hn : n ≠ 0 := by omega
    simp [sourceMVPProfileIndex, hm, hn]
    simpa only [Nat.log2_eq_log_two] using
      (Nat.log_mono_right (b := 2) hmn)

theorem onlineVisitCount_le_prefix {Row : Type*} (rows : ℕ → Row)
    (n : ℕ) (r : Row) : onlineVisitCount rows n r ≤ n := by
  classical
  unfold onlineVisitCount
  calc
    _ ≤ (Finset.range n).card := Finset.card_le_card (Finset.filter_subset _ _)
    _ = n := Finset.card_range n

theorem onlineVisitCount_mono {Row : Type*} (rows : ℕ → Row)
    {m n : ℕ} (hmn : m ≤ n) (r : Row) :
    onlineVisitCount rows m r ≤ onlineVisitCount rows n r := by
  classical
  unfold onlineVisitCount
  apply Finset.card_le_card
  intro x hx
  have hx' := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx'.1) hmn), hx'.2⟩

theorem sourceMVPProfileIndex_le_Kcap (K n : ℕ)
    (hn : n ≤ K - 1) : sourceMVPProfileIndex n ≤ profileLevelCap K := by
  by_cases hzero : n = 0
  · simp [sourceMVPProfileIndex, hzero, profileLevelCap]
  · have hmono : Nat.log2 n ≤ Nat.log2 (K - 1) := by
      simpa only [Nat.log2_eq_log_two] using
        (Nat.log_mono_right (b := 2) hn)
    simp [sourceMVPProfileIndex, hzero, profileLevelCap]
    omega


/-- Any actual episode-by-stage row table produces a member of the finite
monotone-profile family counted above. This is the path-to-family bridge;
the uniform cardinal bound is supplied by `monotoneProfiles_card_le_choose_pow`
and its real stars-and-bars estimate. -/
theorem sourceMVPActualProfileTable_mem {K H : ℕ} {Row : Type*}
    [Fintype Row] (rows : EpisodeRowTable H Row) :
    ∃ p : MonotoneProfiles K (Fintype.card (Fin H × Row)) (profileLevelCap K),
      p = sourceMVPActualProfileTable rows :=
  ⟨sourceMVPActualProfileTable rows, rfl⟩

end StatisticalRL.OnlineRL.MVPProfile

namespace StatisticalRL.OnlineRL.MVPProfile

/-- Full real-power cardinality bound for the family containing every actual
profile table. The source's large-sample premise is retained in the interface,
although the stars-and-bars estimate is stronger. -/
theorem sourceMVP_profileFamily_card_bound (K d : ℕ) (hK : 2 ≤ K)
    (hd : 1 ≤ d) (_hSourceBudget : (K : ℝ) ≥ (d : ℝ) * logTwoReal K) :
    (Fintype.card (MonotoneProfiles K d (profileLevelCap K)) : ℝ) ≤
      (4 * (d : ℝ) * K) ^ ((d : ℝ) * logTwoReal K + 1) := by
  classical
  let J := profileLevelCap K
  have hcardNat : Fintype.card (MonotoneProfiles K d J) ≤
      Fintype.card (Fin d → MonotoneRowProfile K J) :=
    Fintype.card_le_of_injective _ monotoneProfilesToRows_injective
  have hcardEq : Fintype.card (Fin d → MonotoneRowProfile K J) =
      (Fintype.card (MonotoneRowProfile K J)) ^ d := by simp
  have hcardReal : (Fintype.card (MonotoneProfiles K d J) : ℝ) ≤
      (Fintype.card (MonotoneRowProfile K J) : ℝ) ^ d := by
    exact_mod_cast hcardNat.trans_eq hcardEq
  have hrow := monotoneRowProfile_card_real_bound K hK
  have hLpos : 0 < logTwoReal K := by
    have := profileLevelCap_bounds K hK
    linarith [this.2.2.2]
  have hrowPow : (Fintype.card (MonotoneRowProfile K J) : ℝ) ^ d ≤
      ((4 * (K : ℝ)) ^ logTwoReal K) ^ d := by
    gcongr
  have hdCast : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hAB : 4 * (K : ℝ) ≤ 4 * (d : ℝ) * (K : ℝ) := by
    calc
      4 * (K : ℝ) = (4 * 1) * (K : ℝ) := by ring
      _ ≤ (4 * (d : ℝ)) * (K : ℝ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hdCast (by norm_num)) (by positivity)
      _ = 4 * (d : ℝ) * (K : ℝ) := by ring
  have hexp : logTwoReal K * (d : ℝ) ≤ (d : ℝ) * logTwoReal K + 1 := by
    have heq : logTwoReal K * (d : ℝ) = (d : ℝ) * logTwoReal K := by ring
    linarith
  have hfinalPow : ((4 * (K : ℝ)) ^ logTwoReal K) ^ d ≤
      (4 * (d : ℝ) * (K : ℝ)) ^ ((d : ℝ) * logTwoReal K + 1) := by
    have hbase : (1 : ℝ) ≤ 4 * (K : ℝ) := by
      have hKreal : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
      linarith
    calc
      ((4 * (K : ℝ)) ^ logTwoReal K) ^ d =
          (4 * (K : ℝ)) ^ (logTwoReal K * (d : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      _ ≤ (4 * (K : ℝ)) ^ ((d : ℝ) * logTwoReal K + 1) :=
        Real.rpow_le_rpow_of_exponent_le hbase hexp
      _ ≤ (4 * (d : ℝ) * (K : ℝ)) ^ ((d : ℝ) * logTwoReal K + 1) :=
        Real.rpow_le_rpow (by positivity) hAB (by positivity)
  calc
    (Fintype.card (MonotoneProfiles K d (profileLevelCap K)) : ℝ) ≤
        (Fintype.card (MonotoneRowProfile K J) : ℝ) ^ d := by
          simpa [J] using hcardReal
    _ ≤ ((4 * (K : ℝ)) ^ logTwoReal K) ^ d := hrowPow
    _ ≤ (4 * (d : ℝ) * K) ^ ((d : ℝ) * logTwoReal K + 1) := by
      simpa only [Nat.cast_ofNat] using hfinalPow

end StatisticalRL.OnlineRL.MVPProfile

namespace StatisticalRL.OnlineRL.MVPProfile


theorem sourceMVPFinitePossibleProfiles_card_le_family {K H : ℕ} {Row : Type*}
    [Fintype Row] [Nonempty Row] :
    (sourceMVPFinitePossibleProfiles (K := K) (H := H) (Row := Row)).card ≤
      Fintype.card (MonotoneProfiles K (Fintype.card (Fin H × Row)) (profileLevelCap K)) := by
  classical
  exact Finset.card_le_univ _

theorem sourceMVPFinitePossibleProfiles_card_bound {K H : ℕ} {Row : Type*}
    [Fintype Row] [Nonempty Row] (hK : 2 ≤ K) (hH : 0 < H)
    (hbudget : (K : ℝ) ≥ (Fintype.card (Fin H × Row) : ℝ) * logTwoReal K) :
    ((sourceMVPFinitePossibleProfiles (K := K) (H := H) (Row := Row)).card : ℝ) ≤
      (4 * (Fintype.card (Fin H × Row) : ℝ) * K) ^
        ((Fintype.card (Fin H × Row) : ℝ) * logTwoReal K + 1) := by
  have hDpos : 0 < Fintype.card (Fin H × Row) :=
    Fintype.card_pos_iff.mpr ⟨(⟨0, hH⟩, Classical.choice ‹Nonempty Row›)⟩
  have hfamily := sourceMVP_profileFamily_card_bound K
    (Fintype.card (Fin H × Row)) hK (Nat.succ_le_of_lt hDpos) hbudget
  have hsubset := sourceMVPFinitePossibleProfiles_card_le_family
    (K := K) (H := H) (Row := Row)
  have hsubsetR :
      ((sourceMVPFinitePossibleProfiles (K := K) (H := H) (Row := Row)).card : ℝ) ≤
        (Fintype.card (MonotoneProfiles K (Fintype.card (Fin H × Row))
          (profileLevelCap K)) : ℝ) := by exact_mod_cast hsubset
  exact hsubsetR.trans hfamily

theorem sourceMVPActualProfile_eq_operationalTotal
    {K H : ℕ} {Row Outcome : Type*} [Fintype Outcome]
    [DecidableEq Row] [DecidableEq Outcome] [Fintype Row]
    (rows : EpisodeRowTable H Row) (nextAt : ℕ → Outcome)
    (hH : 0 < H) (k : Fin K) (h : Fin H) (r : Row) :
    sourceMVPActualProfile rows k h r =
      sourceMVPProfileIndex
        ((onlineMVPCountTablesRun (sourceMVPFlattenRows rows hH) nextAt (k.val * H)).total
          (h, r)) := by
  change sourceMVPProfileIndex
      (onlineVisitCount (fun e => rows e h) k.val r) =
    sourceMVPProfileIndex
      ((onlineMVPCountTablesRun (sourceMVPFlattenRows rows hH) nextAt (k.val * H)).total
        (h, r))
  rw [sourceMVP_operationalTotal_eq_episode_count rows nextAt hH k h r]

end StatisticalRL.OnlineRL.MVPProfile

namespace StatisticalRL.OnlineRL.MVPProfile

/-- With one episode every pre-episode count is zero, so every row table
induces the all-zero profile. -/
theorem sourceMVPActualProfileTable_one {H : ℕ} {Row : Type*}
    [Fintype Row] (rows : EpisodeRowTable H Row) :
    sourceMVPActualProfileTable (K := 1) rows =
      (⟨fun _ _ => ⟨0, by simp [profileLevelCap]⟩,
        by intro i j k hij; exact le_rfl⟩ :
        MonotoneProfiles 1 (Fintype.card (Fin H × Row)) (profileLevelCap 1)) := by
  classical
  apply Subtype.ext
  funext k i
  fin_cases k
  simp [sourceMVPActualProfileTable, sourceMVPActualProfile,
    sourceMVPProfileIndex, sourceMVPVisitCount, onlineVisitCount, profileLevelCap]

theorem sourceMVPFinitePossibleProfiles_card_le_one {H : ℕ} {Row : Type*}
    [Fintype Row] [Nonempty Row] :
    (sourceMVPFinitePossibleProfiles (K := 1) (H := H) (Row := Row)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  rcases Finset.mem_image.mp hp with ⟨rows, _, rfl⟩
  rcases Finset.mem_image.mp hq with ⟨rows', _, rfl⟩
  rw [sourceMVPActualProfileTable_one, sourceMVPActualProfileTable_one]

theorem sourceMVPFinitePossibleProfiles_card_bound_all {K H : ℕ} {Row : Type*}
    [Fintype Row] [Nonempty Row] (hKpos : 1 ≤ K) (hH : 0 < H)
    (hbudget : (K : ℝ) ≥ (Fintype.card (Fin H × Row) : ℝ) * logTwoReal K) :
    ((sourceMVPFinitePossibleProfiles (K := K) (H := H) (Row := Row)).card : ℝ) ≤
      (4 * (Fintype.card (Fin H × Row) : ℝ) * K) ^
        ((Fintype.card (Fin H × Row) : ℝ) * logTwoReal K + 1) := by
  by_cases hK : 2 ≤ K
  · exact sourceMVPFinitePossibleProfiles_card_bound hK hH hbudget
  · have hKone : K = 1 := by omega
    subst K
    have hcard := sourceMVPFinitePossibleProfiles_card_le_one (H := H) (Row := Row)
    have hcardR :
        ((sourceMVPFinitePossibleProfiles (K := 1) (H := H) (Row := Row)).card : ℝ) ≤ 1 :=
      by exact_mod_cast hcard
    have hbase : 1 ≤ 4 * (Fintype.card (Fin H × Row) : ℝ) := by
      have hDpos : 0 < Fintype.card (Fin H × Row) :=
        Fintype.card_pos_iff.mpr ⟨(⟨0, hH⟩, Classical.choice ‹Nonempty Row›)⟩
      have hD : 1 ≤ (Fintype.card (Fin H × Row) : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt hDpos)
      linarith
    have hlog : logTwoReal 1 = 0 := by simp [logTwoReal]
    simpa [hlog, Real.rpow_one] using hcardR.trans hbase

end StatisticalRL.OnlineRL.MVPProfile
