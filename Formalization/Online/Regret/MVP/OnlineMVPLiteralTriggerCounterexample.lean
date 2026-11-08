import Formalization.Online.Regret.MVP.MVPCountDefinitions
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # Lemma 5.12 under the literal trigger set (source issue C13)

The MVP algorithm (`alg:main-mvp`, `chapters/onlineRL.tex:1264–1310`) commits a row's epoch
count when the updated total count satisfies `N^all_h(s,a) ∈ {1, 2, ⋯, 2^{log₂ K}}`
(`line:trigger-set-mvp`, `chapters/onlineRL.tex:1280`). Read literally this is every integer
from `1` to `2^{log₂ K}`. Under that reading the summed bound of `lem:sum-inv-Nhk-mvp`
(`chapters/onlineRL.tex:1570–1577`) fails. The dyadic reading is proved as
`Lemma5_12_powerOfTwo_corrected`; the pointwise factor-two diagnostic is the separate
`onlineMVP_factor_two_pointwise_fails`. -/

namespace StatisticalRL.OnlineRL
open scoped BigOperators

/-- Literal trigger set `{1, 2, ⋯, 2^{log₂ K}}` of `chapters/onlineRL.tex:1280`, read as
consecutive integers, with `log₂ K` read as `Nat.log 2 K`. For the witness `K = 32` below the
floor reading, the real reading `2^{log₂ 32} = 32` and the set `{1, …, K}` all coincide. -/
def onlineMVPLiteralRowTrigger (K n : ℕ) : Prop :=
  1 ≤ n ∧ n ≤ 2 ^ Nat.log 2 K

instance onlineMVPLiteralRowTriggerDecidable (K n : ℕ) :
    Decidable (onlineMVPLiteralRowTrigger K n) := by
  unfold onlineMVPLiteralRowTrigger
  infer_instance

/-- Verbatim copy of `onlineMVPCountTablesStep` with the literal trigger: increment the
total and the successor counter; on a trigger store the epoch count (sum of the row's pending
successor counters, `chapters/onlineRL.tex:1281–1282`) and reset that row's pending counters
(`:1287`). -/
def onlineMVPLiteralCountTablesStep (K : ℕ) {Row Outcome : Type*}
    [Fintype Outcome] [DecidableEq Row] [DecidableEq Outcome]
    (st : OnlineMVPCountTables Row Outcome) (r : Row) (x : Outcome) :
    OnlineMVPCountTables Row Outcome :=
  let nextTotal := st.total r + 1
  let pendingAfter := fun y => st.pending r y + if y = x then 1 else 0
  let commit := onlineMVPLiteralRowTrigger K nextTotal
  { total := Function.update st.total r nextTotal
    pending := Function.update st.pending r (if commit then fun _ => 0 else pendingAfter)
    stored := if commit then Function.update st.stored r (∑ y : Outcome, pendingAfter y)
      else st.stored }

/-- Verbatim copy of `onlineMVPCountTablesRun` with the literal trigger. -/
def onlineMVPLiteralCountTablesRun (K : ℕ) {Row Outcome : Type*}
    [Fintype Outcome] [DecidableEq Row] [DecidableEq Outcome]
    (rowAt : ℕ → Row) (nextAt : ℕ → Outcome) : ℕ → OnlineMVPCountTables Row Outcome
  | 0 => onlineMVPCountTablesInit Row Outcome
  | n+1 => onlineMVPLiteralCountTablesStep K
      (onlineMVPLiteralCountTablesRun K rowAt nextAt n) (rowAt n) (nextAt n)

/-- Printed `lem:sum-inv-Nhk-mvp` (`chapters/onlineRL.tex:1570–1577`) for the algorithm with
the literal trigger set of `:1280`, in exactly the shape of `Lemma5_12_powerOfTwo_corrected`:
`N_h^k` is the stored count after the first `k` episodes (`k·H` realized transitions), and
the bound is `4SAH log₂ K` for every `K ≥ 2`. -/
def Lemma5_12_literalTrigger_printed : Prop :=
  ∀ (State Action : Type*) [Fintype State] [DecidableEq State]
    [Fintype Action] [DecidableEq Action] (H K : ℕ) (hH : 0 < H), 2 ≤ K →
    ∀ (row : ℕ → State × Action) (next : ℕ → State),
    let rowAt : ℕ → Fin H × (State × Action) :=
      fun n => (⟨n % H, Nat.mod_lt n hH⟩, row n)
    (∑ k : Fin K, ∑ h : Fin H,
      (((max ((onlineMVPLiteralCountTablesRun K rowAt next (k.val * H)).stored
        (rowAt (k.val * H + h.val))) 1 : ℕ) : ℝ)⁻¹)) ≤
      4 * (Fintype.card State : ℝ) * Fintype.card Action * H * (Real.log K / Real.log 2)

/-- On a single row (any successor type), while the count stays inside the literal
trigger set every visit triggers and stores the epoch count `1`. -/
theorem onlineMVPLiteral_singleRow_run {Row Outcome : Type*} [DecidableEq Row] [Subsingleton Row]
    [Fintype Outcome] [DecidableEq Outcome]
    (K : ℕ) (rowAt : ℕ → Row) (nextAt : ℕ → Outcome) :
    ∀ n, n ≤ 2 ^ Nat.log 2 K → ∀ r : Row,
      (onlineMVPLiteralCountTablesRun K rowAt nextAt n).total r = n ∧
      (∀ y, (onlineMVPLiteralCountTablesRun K rowAt nextAt n).pending r y = 0) ∧
      (onlineMVPLiteralCountTablesRun K rowAt nextAt n).stored r = min n 1 := by
  intro n
  induction n with
  | zero =>
      intro _ r
      simp [onlineMVPLiteralCountTablesRun, onlineMVPCountTablesInit]
  | succ n ih =>
      intro hn r
      obtain ⟨htot, -, -⟩ := ih (by omega) r
      have hrow : rowAt n = r := Subsingleton.elim _ _
      have htrig : onlineMVPLiteralRowTrigger K
          ((onlineMVPLiteralCountTablesRun K rowAt nextAt n).total r + 1) := by
        rw [htot]
        exact ⟨by omega, hn⟩
      refine ⟨?_, ?_, ?_⟩
      · simp [onlineMVPLiteralCountTablesRun, onlineMVPLiteralCountTablesStep, hrow, htot]
      · intro y
        simp [onlineMVPLiteralCountTablesRun, onlineMVPLiteralCountTablesStep, htrig, hrow]
      · have hp := (ih (by omega) r).2.1
        simp [onlineMVPLiteralCountTablesRun, onlineMVPLiteralCountTablesStep, htrig, hrow, hp]

/-- **C13, machine-checked.** The printed Lemma 5.12 is false for the MVP algorithm with the
literal trigger set `{1, 2, ⋯, 2^{log₂ K}}` (read as `1 ≤ n ≤ 2^{Nat.log 2 K}`).
Witness: `S = A = H = 1` (`State = Action = Unit`) and `K = 32`. With one state and one action
there is exactly one row and one successor, so the realized trace is forced: the universally
quantified `row`/`next` are the algorithm's own trace, and the refutation is about every run of
the literal algorithm. Every visit `n ∈ {1, …, 32}` triggers and stores the epoch count `1`,
so each of the 32 summands equals `1` (the `k = 0` summand is `1/max{0,1}`), giving `32`, while
`4SAH log₂ K = 4 · 5 = 20`. Only the consecutive-integer reading is refuted here; the
power-of-two reading is `Lemma5_12_powerOfTwo_corrected`. -/
theorem not_Lemma5_12_literalTrigger_printed : ¬ Lemma5_12_literalTrigger_printed := by
  intro h
  have hK := h PUnit PUnit 1 32 Nat.one_pos (by norm_num) (fun _ => (PUnit.unit, PUnit.unit))
    (fun _ => PUnit.unit)
  simp only at hK
  have hbound : (2 : ℕ) ^ Nat.log 2 32 = 32 := by
    rw [show (32 : ℕ) = 2 ^ 5 by norm_num, Nat.log_pow (by norm_num)]
  have hterm : ∀ k : Fin 32,
      (((max ((onlineMVPLiteralCountTablesRun 32
          (fun n => ((⟨n % 1, Nat.mod_lt n Nat.one_pos⟩ : Fin 1),
            (PUnit.unit, PUnit.unit))) (fun _ => PUnit.unit)
          (k.val * 1)).stored
        ((⟨(k.val * 1 + 0) % 1, Nat.mod_lt _ Nat.one_pos⟩ : Fin 1),
          (PUnit.unit, PUnit.unit))) 1 : ℕ) : ℝ)⁻¹)
        = 1 := by
    intro k
    have hk : k.val * 1 ≤ 2 ^ Nat.log 2 32 := by rw [hbound]; omega
    rw [(onlineMVPLiteral_singleRow_run 32 _ _ (k.val * 1) hk _).2.2]
    have : max (min (k.val * 1) 1) 1 = 1 := by omega
    simp only [this, Nat.cast_one, inv_one]
  have hlog : Real.log (32 : ℕ) / Real.log 2 = 5 := by
    rw [show ((32 : ℕ) : ℝ) = (2 : ℝ) ^ 5 by norm_num, Real.log_pow]
    have : Real.log 2 ≠ 0 := by positivity
    field_simp
    norm_num
  have hsum : (∑ k : Fin 32, ∑ h : Fin 1,
      (((max ((onlineMVPLiteralCountTablesRun 32
          (fun n => ((⟨n % 1, Nat.mod_lt n Nat.one_pos⟩ : Fin 1),
            (PUnit.unit, PUnit.unit))) (fun _ => PUnit.unit)
          (k.val * 1)).stored
        ((⟨(k.val * 1 + h.val) % 1, Nat.mod_lt _ Nat.one_pos⟩ : Fin 1),
          (PUnit.unit, PUnit.unit))) 1 : ℕ) : ℝ)⁻¹))
      = 32 := by
    simp only [Fin.sum_univ_one, Fin.val_zero]
    rw [Finset.sum_congr rfl (fun k _ => hterm k)]
    simp
  rw [hsum, hlog] at hK
  norm_num at hK

end StatisticalRL.OnlineRL
