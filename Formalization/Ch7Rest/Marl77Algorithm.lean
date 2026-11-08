import Formalization.Online.Hedge.SecondOrderRegret
import Formalization.Ch7Rest.MarlNearSupersolution

/-!
# Theorem 7.7: the witness algorithm (optimistic Hedge with backward induction)

Reconstructed algorithm (plan §2; not the omitted Q-FTRL of `marl.tex:432`). Parameters: the known
reward table `rew`, the number of rounds `T ≥ 1`, the learning rate `η`, and a default history entry
`z₀` (used only to pad prefixes).

Stages `c = 0, …, H−1` process game steps `h = H − c` (backward induction). At stage `c`, for every
state `s`, `T` rounds are played; in round `t`, for every pair `(i, b)` (player `i`, action
`b ∈ 𝒜_i`) one generative query `(h, s, (b, a_{-i}))` is issued with `a ∼ ⊗_j π^t_j` drawn
afresh and `a_i` replaced by `b`. The gain is `q̂^t_i(b) = r_{i,h}(s, a) + V̄_{i,h+1}(s′)`.
`π^t_i` is Hedge on the cumulative gains. After the `T` rounds,

  `V̄_{i,h}(s) = min(H − h + 1, (1/T)∑_t ⟨π^t_i, q̂^t_i⟩ + log A_i/(ηT) + (η/T)∑_t Var_{π^t_i}(q̂^t_i))`

and the output stage policy is the average of the product policies `⊗_i π^t_i`.

The history is a tuple `x : Fin N → Query × Fin S`, `N = H·S·T·Σ_iA_i`, laid out
lexicographically in `(stage, state, round, pair)` via `slotEquiv`.
-/

open scoped BigOperators
open Finset

namespace StatisticalRL.Ch7Rest.Marl77

open StatisticalRL StatisticalRL.Ch7Rest.Marl StatisticalRL.Ch7Rest.Marl76
open StatisticalRL.Online.Hedge

variable {m S H : ℕ} {A : Fin m → ℕ}

/-! ### Elementary finite distributions -/

/-- The product law `⊗_i π_i` on joint actions. -/
noncomputable def prodDist (π : (i : Fin m) → FiniteDistribution (Fin (A i))) :
    FiniteDistribution (JointAction m A) where
  prob a := ∏ i, (π i).prob (a i)
  prob_nonneg a := prod_nonneg fun i _ => (π i).prob_nonneg (a i)
  sum_prob := by
    have hp := prod_univ_sum (fun i : Fin m => (univ : Finset (Fin (A i))))
      (fun i b => (π i).prob b)
    rw [Fintype.piFinset_univ] at hp
    rw [← hp]
    simp [(π _).sum_prob]

/-- The law of `update a' i b` with `a' ∼ μ` (the deviation to the fixed action `b`). -/
noncomputable def devDist (μ : FiniteDistribution (JointAction m A)) (i : Fin m) (b : Fin (A i)) :
    FiniteDistribution (JointAction m A) where
  prob a := ∑ a', μ.prob a' * (if Function.update a' i b = a then 1 else 0)
  prob_nonneg a := sum_nonneg fun a' _ => mul_nonneg (μ.prob_nonneg a') (by split_ifs <;> norm_num)
  sum_prob := by
    rw [sum_comm]
    simp_rw [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, if_true]
    exact μ.sum_prob

theorem devDist_sum (μ : FiniteDistribution (JointAction m A)) (i : Fin m) (b : Fin (A i))
    (g : JointAction m A → ℝ) :
    ∑ a, (devDist μ i b).prob a * g a = ∑ a', μ.prob a' * g (Function.update a' i b) := by
  simp only [devDist]
  simp_rw [sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun a' _ => ?_
  simp_rw [mul_assoc, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true]

/-- The average of `T ≥ 1` distributions. -/
noncomputable def avgDist {Ω : Type*} [Fintype Ω] {T : ℕ} (hT : 0 < T)
    (d : Fin T → FiniteDistribution Ω) : FiniteDistribution Ω where
  prob o := (∑ t, (d t).prob o) / T
  prob_nonneg o := div_nonneg (sum_nonneg fun t _ => (d t).prob_nonneg o) (Nat.cast_nonneg _)
  sum_prob := by
    rw [← sum_div, sum_comm]
    simp_rw [FiniteDistribution.sum_prob]
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact div_self (by exact_mod_cast hT.ne')

theorem avgDist_sum {Ω : Type*} [Fintype Ω] {T : ℕ} (hT : 0 < T)
    (d : Fin T → FiniteDistribution Ω) (g : Ω → ℝ) :
    ∑ o, (avgDist hT d).prob o * g o = (∑ t, ∑ o, (d t).prob o * g o) / T := by
  simp only [avgDist]
  simp_rw [div_mul_eq_mul_div, sum_mul]
  rw [← sum_div, sum_comm]

/-- The query law: step index `Fin.rev c` (game step `H − c`), state `s`, joint action `∼ μ`. -/
noncomputable def queryDist (c : Fin H) (s : Fin S) (μ : FiniteDistribution (JointAction m A)) :
    FiniteDistribution (Query m S H A) where
  prob q := if q.1 = c.rev ∧ q.2.1 = s then μ.prob q.2.2 else 0
  prob_nonneg q := by split_ifs <;> simp [μ.prob_nonneg]
  sum_prob := by
    rw [Fintype.sum_prod_type, sum_eq_single c.rev]
    · rw [Fintype.sum_prod_type, sum_eq_single s]
      · simp [μ.sum_prob]
      · intro s' _ hs'; simp [hs']
      · simp
    · intro h' _ hh'; simp [hh']
    · simp

theorem queryDist_sum (c : Fin H) (s : Fin S) (μ : FiniteDistribution (JointAction m A))
    (F : Query m S H A → ℝ) :
    ∑ q, (queryDist c s μ).prob q * F q = ∑ a, μ.prob a * F (c.rev, s, a) := by
  rw [Fintype.sum_prod_type, sum_eq_single c.rev]
  · rw [Fintype.sum_prod_type, sum_eq_single s]
    · simp [queryDist]
    · intro s' _ hs'; simp [queryDist, hs']
    · simp
  · intro h' _ hh'; simp [queryDist, hh']
  · simp

/-! ### Parameters, indices and slots -/

/-- Parameters of the witness algorithm. -/
structure Alg (m S H : ℕ) (A : Fin m → ℕ) where
  /-- the known reward table -/
  rew : Fin m → ℕ → Fin S → JointAction m A → ℝ
  /-- number of rounds per `(stage, state)` -/
  T : ℕ
  /-- Hedge learning rate -/
  η : ℝ
  hT : 0 < T
  hA : ∀ i, 0 < A i
  /-- default history entry (pads prefixes) -/
  z₀ : Query m S H A × Fin S

/-- Number of `(player, action)` pairs `Σ_i A_i`. -/
abbrev numPairs (A : Fin m → ℕ) : ℕ := ∑ i, A i

/-- `(i, b) ↦ j`. -/
abbrev pairEquiv (A : Fin m → ℕ) : (Σ i, Fin (A i)) ≃ Fin (numPairs A) := finSigmaFinEquiv

/-- Total number of queries. -/
abbrev Alg.N (al : Alg m S H A) : ℕ := H * S * al.T * numPairs A

/-- History entries. -/
abbrev Entry (m S H : ℕ) (A : Fin m → ℕ) := Query m S H A × Fin S

/-- Lexicographic slot layout `(stage, state, round, pair) ↦ index`. -/
def slotEquiv (H S T M : ℕ) : ((Fin H × Fin S) × Fin T) × Fin M ≃ Fin (H * S * T * M) :=
  ((finProdFinEquiv.prodCongr (Equiv.refl (Fin T))).trans finProdFinEquiv).prodCongr
    (Equiv.refl (Fin M)) |>.trans finProdFinEquiv

/-- The index of the query of pair `j` in round `t` of `(stage c, state s)`. -/
def Alg.slot (al : Alg m S H A) (c : Fin H) (s : Fin S) (t : Fin al.T) (j : Fin (numPairs A)) :
    Fin al.N :=
  slotEquiv H S al.T (numPairs A) (((c, s), t), j)

theorem slotEquiv_val (H S T M : ℕ) (c : Fin H) (s : Fin S) (t : Fin T) (j : Fin M) :
    (slotEquiv H S T M (((c, s), t), j)).val = j + M * (t + T * (s + S * c)) := by
  simp [slotEquiv, finProdFinEquiv]

theorem Alg.slot_val (al : Alg m S H A) (c : Fin H) (s : Fin S) (t : Fin al.T)
    (j : Fin (numPairs A)) :
    (al.slot c s t j).val = j + numPairs A * (t + al.T * (s + S * c)) :=
  slotEquiv_val _ _ _ _ _ _ _ _

/-! ### The algorithm's quantities as functions of the full history -/

/-- The gain of player `i` from an entry `z = ((h, s, a), s′)` at stage `c`, state `s`, with
continuation `V`: `r_{i,H−c}(s, a) + V_i(s′)`. -/
noncomputable def Alg.gz (al : Alg m S H A) (V : Fin m → Fin S → ℝ) (c : Fin H) (s : Fin S)
    (i : Fin m) (z : Entry m S H A) : ℝ :=
  al.rew i (H - c) s z.1.2.2 + V i z.2

/-- Gains `q̂^t_i(b)` of stage `c`, state `s` (zero for `t ≥ T`). -/
noncomputable def Alg.gain (al : Alg m S H A) (V : Fin m → Fin S → ℝ) (x : Fin al.N → Entry m S H A)
    (c : Fin H) (s : Fin S) (i : Fin m) : ℕ → Fin (A i) → ℝ := fun t b =>
  if ht : t < al.T then al.gz V c s i (x (al.slot c s ⟨t, ht⟩ (pairEquiv A ⟨i, b⟩))) else 0

/-- Hedge iterate `π^t_i` at stage `c`, state `s`. -/
noncomputable def Alg.hedge (al : Alg m S H A) (V : Fin m → Fin S → ℝ)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (i : Fin m) (t : ℕ) :
    FiniteDistribution (Fin (A i)) :=
  hedgeIter (al.hA i) al.η (al.gain V x c s i) t

/-- The bonus `β = log A_i/(ηT) + (η/T)∑_t Var_{π^t_i}(q̂^t_i)`. -/
noncomputable def Alg.bonus (al : Alg m S H A) (V : Fin m → Fin S → ℝ)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (i : Fin m) : ℝ :=
  Real.log (A i) / (al.η * al.T) +
    al.η / al.T * ∑ t ∈ range al.T, wvar (al.hedge V x c s i t) (al.gain V x c s i t)

/-- Unclipped optimistic value `U = (1/T)∑_t ⟨π^t_i, q̂^t_i⟩ + β`. -/
noncomputable def Alg.optU (al : Alg m S H A) (V : Fin m → Fin S → ℝ)
    (x : Fin al.N → Entry m S H A) (c : Fin H) (s : Fin S) (i : Fin m) : ℝ :=
  (∑ t ∈ range al.T, wmean (al.hedge V x c s i t) (al.gain V x c s i t)) / al.T +
    al.bonus V x c s i

/-- The new value `V̄_{i,H−c}(s) = min(c + 1, U)`. -/
noncomputable def Alg.stageV (al : Alg m S H A) (V : Fin m → Fin S → ℝ)
    (x : Fin al.N → Entry m S H A) (c : Fin H) : Fin m → Fin S → ℝ := fun i s =>
  min ((c : ℝ) + 1) (al.optU V x c s i)

/-- `vb x c = V̄_{H+1−c}`: `vb x 0 = 0`, `vb x (c+1) = stageV (vb x c) x c`. -/
noncomputable def Alg.vb (al : Alg m S H A) (x : Fin al.N → Entry m S H A) :
    ℕ → Fin m → Fin S → ℝ
  | 0 => fun _ _ => 0
  | c + 1 => if hc : c < H then al.stageV (al.vb x c) x ⟨c, hc⟩ else fun _ _ => 0

/-- Hedge iterate at stage `c` with the algorithm's own continuation `vb x c`. -/
noncomputable def Alg.hedgeAt (al : Alg m S H A) (x : Fin al.N → Entry m S H A) (c : Fin H)
    (s : Fin S) (i : Fin m) (t : ℕ) : FiniteDistribution (Fin (A i)) :=
  al.hedge (al.vb x c) x c s i t

/-- The product policy of round `t`. -/
noncomputable def Alg.stageProd (al : Alg m S H A) (x : Fin al.N → Entry m S H A) (c : Fin H)
    (s : Fin S) (t : ℕ) : FiniteDistribution (JointAction m A) :=
  prodDist fun i => al.hedgeAt x c s i t

/-- The output stage law: the average of the round products. -/
noncomputable def Alg.outStage (al : Alg m S H A) (x : Fin al.N → Entry m S H A) (c : Fin H)
    (s : Fin S) : FiniteDistribution (JointAction m A) :=
  avgDist al.hT fun t => al.stageProd x c s t

/-- The output joint Markov policy: at step `h ∈ [1, H]` the stage `H − h` law. -/
noncomputable def Alg.out (al : Alg m S H A) (x : Fin al.N → Entry m S H A) : JointPolicy m S A :=
  fun h s => if hc : H - h < H then al.outStage x ⟨H - h, hc⟩ s
    else prodDist fun i => hedgeDist (al.hA i) al.η 0

/-- The query law at index `k`, decoded as `(stage c, state s, round t, pair (i, b))`. -/
noncomputable def Alg.queryAt (al : Alg m S H A) (x : Fin al.N → Entry m S H A) (k : Fin al.N) :
    FiniteDistribution (Query m S H A) :=
  let d := (slotEquiv H S al.T (numPairs A)).symm k
  let σ := (pairEquiv A).symm d.2
  queryDist d.1.1.1 d.1.1.2 (devDist (al.stageProd x d.1.1.1 d.1.1.2 d.1.2) σ.1 σ.2)

/-- Pad a prefix to a full history. -/
noncomputable def Alg.ext (al : Alg m S H A) (k : ℕ) (p : Fin k → Entry m S H A) :
    Fin al.N → Entry m S H A :=
  fun n => if h : n.val < k then p ⟨n, h⟩ else al.z₀

/-- The adaptive query rule. -/
noncomputable def Alg.rule (al : Alg m S H A) (k : ℕ) (p : Fin k → Entry m S H A) :
    FiniteDistribution (Query m S H A) :=
  if hk : k < al.N then al.queryAt (al.ext k p) ⟨k, hk⟩ else EnvironmentStage.pointMass al.z₀.1

end StatisticalRL.Ch7Rest.Marl77
