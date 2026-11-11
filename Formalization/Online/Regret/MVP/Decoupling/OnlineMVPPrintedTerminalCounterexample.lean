import Formalization.Online.Regret.MVP.MVPModelDefinitions

/-! # Fixed-profile auxiliary MVP(I) with terminal value H (source issue C17)

The learner `alg:main-mvp` initializes `V_{H+1} ← 0` (`chapters/onlineRL.tex:1267`) and updates
by the capped Bernstein backup (`:1296–1308`, bonus `eq:bh-defn-Bernstein-ucbvi`, `:406–411`).
The auxiliary `MVP(I)` (`alg:main-fixed-profile`, `:4419–4440`) instead initializes
`V_{H+1}^{k,I} ← H` (`:4423`). The family `X_{h,I} = {V_h^{k,I} | 1 ≤ k ≤ K} ∪ {0}`
(`eq:X-I-ours`, `:4445–4449`) is then claimed to contain the learner's values,
`V_h^k = V_h^{k,I_true} ∈ X_{h,I_true}` (`eq:Vk-Itrue`, `:4467–4472`).

This file proves that at the last stage every auxiliary value is the constant `H`, for every
profile, every expanded sample set and every episode, and that the learner's last-stage value
in the instance `S = A = 1`, `H = K = 2`, zero rewards, is `min{2c₂L, 2} ∈ (0, 2)`. Hence
`eq:Vk-Itrue` fails. No refutation of the final MVP regret or decoupling conclusion is claimed. -/

namespace StatisticalRL.OnlineRL
open scoped BigOperators

section Auxiliary
variable {State Action : Type*} [Fintype State] [Fintype Action]

/-- Data of one stage of the auxiliary `MVP(I)` in one episode `k`: the reward `r_h(s,a)`, the
selected batch row `P̂^{(j)}_{s,a,h}` with `j = I^k_{s,a,h}`, and the count `n = 2^{j−2}`
entering the bonus. The row is an arbitrary finite distribution and the count an arbitrary
real number, so every profile `I` and every expanded sample set `D^expand` is covered, including
the printed `n = 2^{j−2} = 1/2` at `j = 1`. -/
structure PrintedFixedProfileStage (State Action : Type*) [Fintype State] [Fintype Action] where
  reward : State → Action → ℝ
  row : State → Action → FiniteDistribution State
  count : State → Action → ℝ

/-- The printed auxiliary update (`chapters/onlineRL.tex:4427–4431`):
`min{r + ⟨P̂, V_next⟩ + c₁√(Var_{P̂}(V_next)·L/max{n,1}) + c₂·H·L/max{n,1}, H}`, with
`L = log(1/δ′)`. -/
noncomputable def printedFixedProfileStageQ (H L c₁ c₂ r : ℝ) (P : FiniteDistribution State)
    (n : ℝ) (next : State → ℝ) : ℝ :=
  min (r + P.expectation next +
    (c₁ * Real.sqrt (P.variance next * L / max n 1) + c₂ * H * L / max n 1)) H

/-- Backward recursion of the printed `MVP(I)` in one episode, with the printed terminal value
`V_{H+1}^{k,I} = H` (`chapters/onlineRL.tex:4423`). For a list of `H` stages, index `h`
(0-based, `drop h`) is source stage `h + 1`. -/
noncomputable def printedFixedProfileValue [Nonempty Action] (H : ℕ) (L c₁ c₂ : ℝ) :
    List (PrintedFixedProfileStage State Action) → State → ℝ
  | [] => fun _ => (H : ℝ)
  | st :: sts => fun s => actionMaximum (fun a =>
      printedFixedProfileStageQ (H : ℝ) L c₁ c₂ (st.reward s a) (st.row s a) (st.count s a)
        (printedFixedProfileValue H L c₁ c₂ sts))

/-- The printed family `X_{h,I} = {V_h^{k,I} | 1 ≤ k ≤ K} ∪ {0}` (`eq:X-I-ours`), with the
episode data `stagesOf k` of a fixed profile `I`, at 0-based stage index `h`. -/
def printedFixedProfileFamily [Nonempty Action] (H : ℕ) (L c₁ c₂ : ℝ) (K : ℕ)
    (stagesOf : Fin K → List (PrintedFixedProfileStage State Action)) (h : ℕ) :
    Set (State → ℝ) :=
  {V | ∃ k : Fin K, V = printedFixedProfileValue H L c₁ c₂ ((stagesOf k).drop h)} ∪
    {fun _ => 0}

theorem finiteDistribution_expectation_const (P : FiniteDistribution State) (c : ℝ) :
    P.expectation (fun _ => c) = c :=
  FiniteDistribution.expectation_const P c

/-- Scalar core: against the continuation `H·1`, any nonnegative reward and any nonnegative
bonus clip to `H`, because `⟨P̂, H·1⟩ = H` for every probability vector `P̂`. -/
theorem printedFixedProfile_scalar_terminal (H r b : ℝ) (P : FiniteDistribution State)
    (hr : 0 ≤ r) (hb : 0 ≤ b) :
    min (r + P.expectation (fun _ => H) + b) H = H := by
  rw [finiteDistribution_expectation_const]
  exact min_eq_right (by linarith)

/-- The printed bonus is nonnegative for nonnegative constants and every real count `n`. -/
theorem printedFixedProfile_bonus_nonneg (H L c₁ c₂ n v : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    0 ≤ c₁ * Real.sqrt (v * L / max n 1) + c₂ * H * L / max n 1 := by
  have hn : 0 < max n 1 := lt_of_lt_of_le one_pos (le_max_right n 1)
  have h1 : 0 ≤ c₁ * Real.sqrt (v * L / max n 1) := mul_nonneg hc₁ (Real.sqrt_nonneg _)
  have h2 : 0 ≤ c₂ * H * L / max n 1 := div_nonneg (by positivity) hn.le
  linarith

theorem printedFixedProfileStageQ_terminal (H L c₁ c₂ r : ℝ) (P : FiniteDistribution State)
    (n : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hr : 0 ≤ r) :
    printedFixedProfileStageQ H L c₁ c₂ r P n (fun _ => H) = H :=
  printedFixedProfile_scalar_terminal H r _ P hr
    (printedFixedProfile_bonus_nonneg H L c₁ c₂ n _ hH hL hc₁ hc₂)

/-- **Last stage of the printed auxiliary.** For every episode's stage list of length `H ≥ 1`
with nonnegative rewards, arbitrary rows and arbitrary real counts, and nonnegative `c₁, c₂, L`,
the auxiliary stage-`H` value (0-based index `H − 1`) is the constant `H`. -/
theorem printedFixedProfile_lastStage_eq [Nonempty Action] (H : ℕ) (L c₁ c₂ : ℝ)
    (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂)
    (stages : List (PrintedFixedProfileStage State Action)) (hlen : stages.length = H)
    (hH : 1 ≤ H) (hr : ∀ st ∈ stages, ∀ s a, 0 ≤ st.reward s a) :
    printedFixedProfileValue H L c₁ c₂ (stages.drop (H - 1)) = fun _ => (H : ℝ) := by
  have hone : (stages.drop (H - 1)).length = 1 := by
    rw [List.length_drop]; omega
  obtain ⟨st, hst⟩ := List.length_eq_one_iff.mp hone
  have hmem : st ∈ stages := List.mem_of_mem_drop (i := H - 1) (by rw [hst]; simp)
  rw [hst]
  funext s
  simp only [printedFixedProfileValue]
  have hq : (fun a => printedFixedProfileStageQ (H : ℝ) L c₁ c₂ (st.reward s a) (st.row s a)
      (st.count s a) (fun _ => (H : ℝ))) = fun _ => (H : ℝ) := by
    funext a
    exact printedFixedProfileStageQ_terminal _ _ _ _ _ _ _ (Nat.cast_nonneg H) hL hc₁ hc₂
      (hr st hmem s a)
  rw [hq]
  exact Finset.sup'_const _ _

/-- **Printed stage-`H` family.** For every fixed profile (every choice of the per-episode
stage data), `X_{H,I} ⊆ {H·1, 0}`. -/
theorem printedFixedProfileFamily_lastStage_subset [Nonempty Action] (H : ℕ) (L c₁ c₂ : ℝ)
    (hL : 0 ≤ L) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (K : ℕ)
    (stagesOf : Fin K → List (PrintedFixedProfileStage State Action))
    (hlen : ∀ k, (stagesOf k).length = H) (hH : 1 ≤ H)
    (hr : ∀ k, ∀ st ∈ stagesOf k, ∀ s a, 0 ≤ st.reward s a) :
    printedFixedProfileFamily H L c₁ c₂ K stagesOf (H - 1) ⊆
      {fun _ => (H : ℝ), fun _ => 0} := by
  rintro V (⟨k, rfl⟩ | hV)
  · left
    exact printedFixedProfile_lastStage_eq H L c₁ c₂ hL hc₁ hc₂ _ (hlen k) hH (hr k)
  · right
    exact hV

end Auxiliary

section Learner

theorem finiteDistribution_unit_expectation (P : FiniteDistribution Unit) (f : Unit → ℝ) :
    P.expectation f = f () := by
  have hp : P.prob () = 1 := by simpa using P.sum_prob
  simp [FiniteDistribution.expectation, hp]

theorem finiteDistribution_unit_variance (P : FiniteDistribution Unit) (f : Unit → ℝ) :
    P.variance f = 0 := by
  simp [FiniteDistribution.variance, finiteDistribution_unit_expectation]

theorem actionMaximum_unit [Nonempty Unit] (f : Unit → ℝ) : actionMaximum f = f () := by
  unfold actionMaximum
  exact Finset.sup'_singleton (f := f) (b := ())

/-- The forced first-episode transcript for `S = A = 1`, `H = 2`: stage-1 row then stage-2 row,
each with the sole successor. -/
def onlineMVPUnitFirstEpisode : List (OnlineMDPRow Unit Unit 2 × Unit) :=
  [((0, ((), ())), ()), ((1, ((), ())), ())]

/-- **Learner, `S = A = 1`, `H = K = 2`, zero rewards.** The value of the actual Lean learner at
source stage 2 before episode 2 (`V_2^2`, computed from the forced first-episode transcript) is
`min{2c₂L, 2}`. This is the C8/C13-corrected learner consumed by `MVP_regret_corrected`; on this
instance both corrections are inactive: the queried row has count `1` (so the zero-count branch
is not taken), and both the literal and the dyadic trigger fire at count `1`, so the batch is the
single recorded sample. The update is therefore exactly the printed
`min{r + ⟨P̂, V₃⟩ + b, H}` with `V₃ = 0`, `P̂` the Dirac row, zero variance and
`b = c₂·H·L/1`. The transitions of `E` are arbitrary. -/
theorem onlineMVP_unit_secondEpisode_lastStage
    (E : Fin 2 → EnvironmentStage Unit Unit) (hE : ∀ h s a, (E h).reward s a = 0)
    (fallback : Unit) (L c₁ c₂ : ℝ) :
    onlineCappedBackwardValueAt ((2 : ℕ) : ℝ) L c₁ c₂
      (onlineMVPHistoryPlanningStages (by norm_num) E fallback onlineMVPUnitFirstEpisode) 1 =
      fun _ => min (2 * c₂ * L) 2 := by
  funext s
  have hlen : ((onlineMVPActualPlanningStage E
      (onlineMVPHistoryRowAt (by norm_num) E fallback onlineMVPUnitFirstEpisode)
      (onlineMVPHistoryNextAt fallback onlineMVPUnitFirstEpisode) 2 1).observations () ()).length
        = 1 := by
    simp [onlineMVPActualPlanningStage, onlineMVPSourceBatchList, onlineMVPSourceBatchStart,
      onlineMVPSourceBatchEnd, onlineMVPRowVisitList, onlineMVPHistoryRowAt,
      onlineMVPUnitFirstEpisode, List.range_succ]
  simp only [onlineCappedBackwardValueAt, onlineMVPHistoryPlanningStages, List.ofFn_succ,
    List.ofFn_zero, List.drop_succ_cons, List.drop_zero, onlineCappedBackwardValue]
  rw [actionMaximum_unit]
  simp only [onlineCappedStageQ, finiteDistribution_unit_expectation,
    finiteDistribution_unit_variance, onlineZeroCountSafeQUpdate]
  cases s
  rw [show onlineMVPUnitFirstEpisode.length = 2 from rfl,
    show (Fin.succ 0 : Fin 2) = 1 from rfl, hlen]
  have hr : (onlineMVPActualPlanningStage E
      (onlineMVPHistoryRowAt (by norm_num) E fallback onlineMVPUnitFirstEpisode)
      (onlineMVPHistoryNextAt fallback onlineMVPUnitFirstEpisode) 2 1).environment.reward () ()
        = 0 := hE 1 () ()
  rw [hr]
  norm_num
  ring_nf

/-- **C17, machine-checked.** Printed `eq:Vk-Itrue` (`chapters/onlineRL.tex:4467–4472`) fails.
Instance: `S = A = 1` (`State = Action = Unit`), `H = K = 2`, zero rewards, arbitrary
transitions. The Lean learner takes no `K` (only the one completed episode is used); the `K` bound
below is the auxiliary's episode count, so the auxiliary family is excluded for every `K`, and the
source instance is `K = 2`. Indexing: `V_h^k` is the learner's pre-episode value used in episode `k`, computed
from the transcript of episodes `1, …, k − 1`; the failure is at source stage `h = H = 2`
(0-based index `1`) and `k = 2`. (If `V_h^k` is read as the value computed after episode `k`,
the same number appears at `k = 1`, so the refutation does not depend on that reading.) With
one state and one action the first-episode transcript is forced.

For `0 ≤ c₁`, `0 < c₂`, `0 < L` and `c₂L < 1`, the learner value `min{2c₂L, 2} = 2c₂L ∈ (0,2)`
differs from the auxiliary value `V_2^{k,I}` for every episode `k` and lies outside the printed
family `X_{2,I}`, for every number of episodes `K`, every fixed profile `I` and every expanded
sample set (encoded by arbitrary per-episode stage data: nonnegative rewards, arbitrary rows,
arbitrary real counts, see `PrintedFixedProfileStage`). The auxiliary uses the same `c₁, c₂, L`
as the learner, as printed. The Lean learner is the C8/C13-corrected one; neither correction is
active here (see `onlineMVP_unit_secondEpisode_lastStage`). C16 is not involved: `L` is a free
parameter, linked to the printed allocation only by `onlineMVP_C17_sourceParameters`. -/
theorem not_eq_Vk_Itrue_printed
    (E : Fin 2 → EnvironmentStage Unit Unit) (hE : ∀ h s a, (E h).reward s a = 0)
    (fallback : Unit) (L c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 < c₂) (hL : 0 < L)
    (hc₂L : c₂ * L < 1) (K : ℕ)
    (stagesOf : Fin K → List (PrintedFixedProfileStage Unit Unit))
    (hlen : ∀ k, (stagesOf k).length = 2)
    (hr : ∀ k, ∀ st ∈ stagesOf k, ∀ s a, 0 ≤ st.reward s a) :
    let V := onlineCappedBackwardValueAt ((2 : ℕ) : ℝ) L c₁ c₂
      (onlineMVPHistoryPlanningStages (by norm_num) E fallback onlineMVPUnitFirstEpisode) 1
    (∀ k : Fin K, V ≠ printedFixedProfileValue 2 L c₁ c₂ ((stagesOf k).drop 1)) ∧
      V ∉ printedFixedProfileFamily 2 L c₁ c₂ K stagesOf 1 := by
  intro V
  have hV : V = fun _ => 2 * c₂ * L := by
    have h := onlineMVP_unit_secondEpisode_lastStage E hE fallback L c₁ c₂
    have hm : min (2 * c₂ * L) 2 = 2 * c₂ * L := min_eq_left (by nlinarith)
    simpa [V, hm] using h
  have hsub := printedFixedProfileFamily_lastStage_subset 2 L c₁ c₂ hL.le hc₁ hc₂.le K stagesOf
    hlen (by norm_num) hr
  have hnot : V ∉ printedFixedProfileFamily 2 L c₁ c₂ K stagesOf 1 := by
    intro hmem
    have h2 := hsub hmem
    rw [hV] at h2
    rcases h2 with h2 | h2
    · have := congrFun h2 ()
      norm_num at this
      nlinarith
    · have := congrFun h2 ()
      have hpos : 0 < c₂ * L := mul_pos hc₂ hL
      simp only at this
      nlinarith
  refine ⟨fun k hk => hnot (Or.inl ⟨k, hk⟩), hnot⟩

/-- Parameters of the C17 witness (`S = A = 1`, `H = K = 2`) for any `c₂ > 0`:
`q = min{1/(2c₂), 1/(80000 log 6)}`, `δ′ = e^{−q}`, `δ = (4/25)δ′`. Then `0 < δ < 1`, the printed
allocation `δ′ = 100δ/(S²A²H²K²)` holds, `L = log(1/δ′) = q`, `0 < c₂L ≤ 1/2 < 1`, and with
`ι = 40000 (log₂ K)³ log(3SAH) log(1/δ′)` both `K ≥ SAH·ι` and `K ≥ SAH log₂ K` hold. In fact
`SAH·ι = 2ι ≤ 1 < 2 = K`, so the instance also lies in the strict regime `K > SAH·ι` of the regret
proof; `eq:Vk-Itrue` is asserted unconditionally, so this does not affect the refutation. -/
theorem onlineMVP_C17_sourceParameters (c₂ : ℝ) (hc₂ : 0 < c₂) :
    let q := min (1 / (2 * c₂)) (1 / (80000 * Real.log 6))
    let δp := Real.exp (-q)
    let δ := 4 / 25 * δp
    0 < δ ∧ δ < 1 ∧
      100 * δ / ((1 : ℝ) ^ 2 * (1 : ℝ) ^ 2 * (2 : ℝ) ^ 2 * (2 : ℝ) ^ 2) = δp ∧
      Real.log (1 / δp) = q ∧ 0 < c₂ * Real.log (1 / δp) ∧ c₂ * Real.log (1 / δp) < 1 ∧
      (1 : ℝ) * 1 * 2 * (40000 * (Real.log 2 / Real.log 2) ^ 3 * Real.log (3 * 1 * 1 * 2) *
        Real.log (1 / δp)) ≤ 2 ∧
      (1 : ℝ) * 1 * 2 * (Real.log 2 / Real.log 2) ≤ 2 := by
  intro q δp δ
  have hlog6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hq1 : q ≤ 1 / (2 * c₂) := min_le_left _ _
  have hq2 : q ≤ 1 / (80000 * Real.log 6) := min_le_right _ _
  have hqpos : 0 < q := lt_min (by positivity) (by positivity)
  have hL : Real.log (1 / δp) = q := by
    simp [δp, Real.log_exp]
  have hδp : 0 < δp := Real.exp_pos _
  have hδp1 : δp < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hcq : c₂ * q ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hq1 hc₂.le
    calc c₂ * q ≤ c₂ * (1 / (2 * c₂)) := this
      _ = 1 / 2 := by field_simp
  have hiota : 40000 * Real.log 6 * q ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_left hq2 (by positivity : (0 : ℝ) ≤ 40000 * Real.log 6)
    calc 40000 * Real.log 6 * q ≤ 40000 * Real.log 6 * (1 / (80000 * Real.log 6)) := this
      _ = 1 / 2 := by field_simp; ring
  refine ⟨by positivity, by simp only [δ]; linarith, by simp only [δ]; ring, hL, ?_, ?_, ?_, ?_⟩
  · rw [hL]; positivity
  · rw [hL]; linarith
  · rw [hL, div_self hlog2]
    norm_num
    nlinarith
  · rw [div_self hlog2]; norm_num

/-- C17 witness at the source parameters: for any `c₁ ≥ 0`, `c₂ > 0`, with
`L = log(1/δ′)` from `onlineMVP_C17_sourceParameters`, `eq:Vk-Itrue` fails as in
`not_eq_Vk_Itrue_printed`. -/
theorem not_eq_Vk_Itrue_printed_sourceParameters
    (E : Fin 2 → EnvironmentStage Unit Unit) (hE : ∀ h s a, (E h).reward s a = 0)
    (fallback : Unit) (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 < c₂) (K : ℕ)
    (stagesOf : Fin K → List (PrintedFixedProfileStage Unit Unit))
    (hlen : ∀ k, (stagesOf k).length = 2)
    (hr : ∀ k, ∀ st ∈ stagesOf k, ∀ s a, 0 ≤ st.reward s a) :
    let L := Real.log (1 / Real.exp (-min (1 / (2 * c₂)) (1 / (80000 * Real.log 6))))
    let V := onlineCappedBackwardValueAt ((2 : ℕ) : ℝ) L c₁ c₂
      (onlineMVPHistoryPlanningStages (by norm_num) E fallback onlineMVPUnitFirstEpisode) 1
    (∀ k : Fin K, V ≠ printedFixedProfileValue 2 L c₁ c₂ ((stagesOf k).drop 1)) ∧
      V ∉ printedFixedProfileFamily 2 L c₁ c₂ K stagesOf 1 := by
  intro L
  obtain ⟨-, -, -, -, hpos, hlt, -, -⟩ := onlineMVP_C17_sourceParameters c₂ hc₂
  have hL : 0 < L := pos_of_mul_pos_right hpos hc₂.le
  exact not_eq_Vk_Itrue_printed E hE fallback L c₁ c₂ hc₁ hc₂ hL hlt K stagesOf hlen hr

end Learner

end StatisticalRL.OnlineRL
