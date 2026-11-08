import Formalization.Online.SourceOptimism.SequentialEpisodeDefinitions

/-! Start-state independence for the actual online episodic law
(`chapters/onlineRL.tex:17–41`, protocol (i)–(ii)): the episode-k initial state `s₁ᵏ` is
independent of the deployed policy `πᵏ = planner (history.take (k*H))`, so for every test
function `g`, `E[g(πᵏ, s₁ᵏ)] = E[ρ.expectation (g(πᵏ, ·))]`.

Route: (1) a recursive expectation functional `seqExp` for the causal outcome law and its
tower/prefix/congruence lemmas; (2) the length-`kH` prefix of the run reads the reset vector
only at indices `< k`; (3) an involution on `(Fin K → X) × X` that swaps coordinate `k` with an
independent fresh draw. -/

open scoped BigOperators
namespace StatisticalRL.OnlineRL.RegretToPAC

section SeqExp
variable {Row Outcome : Type*} [Fintype Outcome]

/-- Expectation of a history functional under the causal outcome law, by recursion. -/
noncomputable def seqExp (d : Row → FiniteDistribution Outcome)
    (choose : List (Row × Outcome) → Row) :
    ℕ → List (Row × Outcome) → (List (Row × Outcome) → ℝ) → ℝ
  | 0, h, G => G h
  | n + 1, h, G => ∑ o, (d (choose h)).prob o * seqExp d choose n (h ++ [(choose h, o)]) G

theorem sum_outcomeLaw_eq_seqExp (d : Row → FiniteDistribution Outcome)
    (choose : List (Row × Outcome) → Row) (G : List (Row × Outcome) → ℝ) :
    ∀ (n : ℕ) (h : List (Row × Outcome)),
    ∑ path, (onlineSequentialOutcomeLaw d choose n h).prob path *
        G (onlineSequentialPathHistory choose n h path) = seqExp d choose n h G := by
  intro n
  induction n with
  | zero =>
    intro h
    change ∑ path : PUnit, (EnvironmentStage.pointMass PUnit.unit).prob path * G h = G h
    rw [Fintype.sum_unique]
    simp [EnvironmentStage.pointMass]
  | succ n ih =>
    intro h
    change ∑ path : PUnit × Outcome × OnlineOutcomePath Outcome n,
        ((d (choose h)).prob path.2.1 *
          (onlineSequentialOutcomeLaw d choose n (h ++ [(choose h, path.2.1)])).prob path.2.2) *
        G (onlineSequentialPathHistory choose n (h ++ [(choose h, path.2.1)]) path.2.2) = _
    rw [Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_prod_type]
    simp only [seqExp]
    refine Finset.sum_congr rfl fun o _ ↦ ?_
    simp_rw [mul_assoc, ← Finset.mul_sum]
    rw [ih]

theorem seqExp_add (d : Row → FiniteDistribution Outcome)
    (choose : List (Row × Outcome) → Row) (G : List (Row × Outcome) → ℝ) (r : ℕ) :
    ∀ (j : ℕ) (h : List (Row × Outcome)),
    seqExp d choose (j + r) h G = seqExp d choose j h (fun h' ↦ seqExp d choose r h' G) := by
  intro j
  induction j with
  | zero => intro h; simp [seqExp]
  | succ j ih =>
    intro h
    rw [Nat.succ_add]
    simp only [seqExp, ih]

theorem seqExp_const (d : Row → FiniteDistribution Outcome)
    (choose : List (Row × Outcome) → Row) (G : List (Row × Outcome) → ℝ) (c : ℝ) :
    ∀ (n : ℕ) (h : List (Row × Outcome)), (∀ ext, G (h ++ ext) = c) →
    seqExp d choose n h G = c := by
  intro n
  induction n with
  | zero => intro h hG; simpa [seqExp] using hG []
  | succ n ih =>
    intro h hG
    simp only [seqExp]
    have hrec : ∀ o, seqExp d choose n (h ++ [(choose h, o)]) G = c := fun o ↦
      ih _ (fun ext ↦ by rw [List.append_assoc]; exact hG _)
    simp_rw [hrec, ← Finset.sum_mul, FiniteDistribution.sum_prob, one_mul]

theorem seqExp_congr (d : Row → FiniteDistribution Outcome)
    (c₁ c₂ : List (Row × Outcome) → Row) (G₁ G₂ : List (Row × Outcome) → ℝ) :
    ∀ (n : ℕ) (h : List (Row × Outcome)),
    (∀ h' : List (Row × Outcome), h.length ≤ h'.length → h'.length < h.length + n →
      c₁ h' = c₂ h') →
    (∀ h' : List (Row × Outcome), h'.length = h.length + n → G₁ h' = G₂ h') →
    seqExp d c₁ n h G₁ = seqExp d c₂ n h G₂ := by
  intro n
  induction n with
  | zero => intro h _ hG; exact hG h (by simp)
  | succ n ih =>
    intro h hc hG
    simp only [seqExp]
    have hch : c₁ h = c₂ h := hc h le_rfl (by omega)
    rw [hch]
    refine Finset.sum_congr rfl fun o _ ↦ ?_
    congr 1
    apply ih
    · intro h' h1 h2
      simp only [List.length_append, List.length_singleton] at h1 h2
      exact hc h' (by omega) (by omega)
    · intro h' h1
      simp only [List.length_append, List.length_singleton] at h1
      exact hG h' (by omega)

end SeqExp

section Swap
variable {X : Type*} [Fintype X]

/-- Replace coordinate `k` by a fresh value and return the old value. An involution. -/
def swapAt {K : ℕ} (k : Fin K) : (Fin K → X) × X ≃ (Fin K → X) × X :=
  Function.Involutive.toPerm (fun p ↦ (Function.update p.1 k p.2, p.1 k)) (by
    intro p
    ext
    · simp
    · simp)

theorem prod_update_mul {K : ℕ} (ρ : FiniteDistribution X) (k : Fin K)
    (init : Fin K → X) (s : X) :
    (∏ j, ρ.prob (Function.update init k s j)) * ρ.prob (init k) =
      (∏ j, ρ.prob (init j)) * ρ.prob s := by
  classical
  rw [Fintype.prod_eq_mul_prod_compl k, Fintype.prod_eq_mul_prod_compl k (fun j ↦ ρ.prob (init j))]
  have hrest : ∏ j ∈ ({k} : Finset (Fin K))ᶜ, ρ.prob (Function.update init k s j) =
      ∏ j ∈ ({k} : Finset (Fin K))ᶜ, ρ.prob (init j) := by
    refine Finset.prod_congr rfl fun j hj ↦ ?_
    have hjk : j ≠ k := by simpa using hj
    rw [Function.update_of_ne hjk]
  rw [hrest]
  simp only [Function.update_self]
  ring

/-- Fresh-draw identity for an i.i.d. vector: if `f init s` does not depend on coordinate
`k` of `init`, then evaluating at `s = init k` is the same as averaging `s` over `ρ`. -/
theorem sum_prod_eval_eq_sum_prod_avg {K : ℕ} (ρ : FiniteDistribution X) (k : Fin K)
    (f : (Fin K → X) → X → ℝ)
    (hf : ∀ init x s, f (Function.update init k x) s = f init s) :
    ∑ init : Fin K → X, (∏ j, ρ.prob (init j)) * f init (init k) =
      ∑ init : Fin K → X, (∏ j, ρ.prob (init j)) * ∑ s, ρ.prob s * f init s := by
  have hL : ∑ init : Fin K → X, (∏ j, ρ.prob (init j)) * f init (init k) =
      ∑ p : (Fin K → X) × X, (∏ j, ρ.prob (p.1 j)) * ρ.prob p.2 * f p.1 (p.1 k) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun init _ ↦ ?_
    simp_rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, FiniteDistribution.sum_prob, one_mul]
  have hR : ∑ init : Fin K → X, (∏ j, ρ.prob (init j)) * ∑ s, ρ.prob s * f init s =
      ∑ p : (Fin K → X) × X, (∏ j, ρ.prob (p.1 j)) * ρ.prob p.2 * f p.1 p.2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun init _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    ring
  rw [hL, hR]
  refine Fintype.sum_equiv (swapAt k) _ _ fun p ↦ ?_
  change _ = (∏ j, ρ.prob (Function.update p.1 k p.2 j)) * ρ.prob (p.1 k) *
    f (Function.update p.1 k p.2) (p.1 k)
  rw [prod_update_mul, hf]

end Swap

section Episodic
universe u v w
variable {State : Type u} {Action : Type v}

/-- Before the end of episode `k-1` the episodic selector does not read reset `k`. -/
theorem onlineEpisodicChoose_update_of_lt (H K : ℕ) (hH : 0 < H)
    (init : Fin K → State) (fallback : State) (planner : OnlineEpisodePlanner State Action H)
    (k : Fin K) (x : State) (h' : List (OnlineMDPRow State Action H × State))
    (hlen : h'.length < k.val * H) :
    onlineEpisodicChoose H K hH (Function.update init k x) fallback planner h' =
      onlineEpisodicChoose H K hH init fallback planner h' := by
  classical
  have hcur : onlineEpisodicCurrentState H K (Function.update init k x) fallback h' =
      onlineEpisodicCurrentState H K init fallback h' := by
    unfold onlineEpisodicCurrentState
    split_ifs with h1 h2
    · have hdiv : h'.length / H < k.val := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
      have hne : (⟨h'.length / H, h2⟩ : Fin K) ≠ k := by
        intro he; rw [← he] at hdiv; exact lt_irrefl _ hdiv
      rw [Function.update_of_ne hne]
    · rfl
    · rfl
  simp only [onlineEpisodicChoose, hcur]

/-- **Start-state independence.** Under the actual online law, for every test function
`g` of the episode-k deployed policy and a state,
`E[g(πᵏ, s₁ᵏ)] = E[ρ.expectation (g(πᵏ, ·))]`. -/
theorem onlineEpisode_startState_independent [Fintype State] [Fintype Action] (H K : ℕ) (hH : 0 < H)
    (E : Fin H → EnvironmentStage State Action) (ρ : FiniteDistribution State)
    (fallback : State) (planner : OnlineEpisodePlanner State Action H) (k : Fin K)
    (g : (Fin H → State → Action) → State → ℝ) :
    (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H) :
        FiniteDistribution ((Fin K → State) × OnlineOutcomePath.{u, w} State (K * H))).expectation
        (fun sample ↦ g (planner ((onlineSequentialPathHistory
          (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2).take
            (k.val * H))) (sample.1 k)) =
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H) :
        FiniteDistribution ((Fin K → State) × OnlineOutcomePath.{u, w} State (K * H))).expectation
        (fun sample ↦ ρ.expectation (g (planner ((onlineSequentialPathHistory
          (onlineEpisodicChoose H K hH sample.1 fallback planner) (K * H) [] sample.2).take
            (k.val * H))))) := by
  classical
  set d := onlineMDPSuccessorRowLaw E with hd
  let ch : (Fin K → State) → List (OnlineMDPRow State Action H × State) →
      OnlineMDPRow State Action H := fun init ↦ onlineEpisodicChoose H K hH init fallback planner
  let Ψ : (Fin K → State) → State → ℝ := fun init s ↦
    seqExp d (ch init) (k.val * H) [] (fun hist ↦ g (planner (hist.take (k.val * H))) s)
  -- (1) the full-run expectation of a prefix functional is the prefix expectation
  have hsplit : K * H = k.val * H + (K - k.val) * H := by
    rw [← Nat.add_mul, Nat.add_sub_cancel' k.isLt.le]
  have h1 : ∀ init s, ∑ path, (onlineSequentialOutcomeLaw d (ch init) (K * H) []).prob path *
      g (planner ((onlineSequentialPathHistory (ch init) (K * H) [] path).take (k.val * H))) s =
      Ψ init s := by
    intro init s
    rw [sum_outcomeLaw_eq_seqExp d (ch init)
      (fun hist ↦ g (planner (hist.take (k.val * H))) s) (K * H) []]
    rw [hsplit, seqExp_add]
    apply seqExp_congr d (ch init) (ch init)
    · intro _ _ _; rfl
    · intro h' hlen
      simp only [List.length_nil, zero_add] at hlen
      apply seqExp_const
      intro ext
      rw [List.take_left' hlen, List.take_of_length_le (le_of_eq hlen)]
  -- (2) the prefix expectation does not read reset `k`
  have h2 : ∀ init x s, Ψ (Function.update init k x) s = Ψ init s := by
    intro init x s
    apply seqExp_congr
    · intro h' _ hlt
      simp only [List.length_nil, zero_add] at hlt
      exact onlineEpisodicChoose_update_of_lt H K hH init fallback planner k x h' hlt
    · intro _ _; rfl
  -- (3) unfold the joint law and apply the fresh-draw identity
  have hexp : ∀ F : (Fin K → State) × OnlineOutcomePath.{u, w} State (K * H) → ℝ,
      (onlineSequentialEpisodeLaw H K hH E ρ fallback planner (K * H) :
        FiniteDistribution ((Fin K → State) × OnlineOutcomePath.{u, w} State (K * H))).expectation F =
        ∑ init : Fin K → State, (∏ j, ρ.prob (init j)) *
          ∑ path, (onlineSequentialOutcomeLaw d (ch init) (K * H) []).prob path *
            F (init, path) := by
    intro F
    simp only [FiniteDistribution.expectation, onlineSequentialEpisodeLaw, onlineInitialVectorLaw]
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun init _ ↦ ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun path _ ↦ ?_
    ring
  rw [hexp, hexp]
  dsimp only
  have hL : ∀ init : Fin K → State,
      ∑ path, (onlineSequentialOutcomeLaw d (ch init) (K * H) []).prob path *
        g (planner ((onlineSequentialPathHistory (ch init) (K * H) [] path).take (k.val * H)))
          (init k) = Ψ init (init k) := fun init ↦ h1 init (init k)
  have hR : ∀ init : Fin K → State,
      ∑ path, (onlineSequentialOutcomeLaw d (ch init) (K * H) []).prob path *
        ρ.expectation (g (planner
          ((onlineSequentialPathHistory (ch init) (K * H) [] path).take (k.val * H)))) =
        ∑ s, ρ.prob s * Ψ init s := by
    intro init
    simp_rw [← h1 init, FiniteDistribution.expectation, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ ↦ Finset.sum_congr rfl fun path _ ↦ ?_
    ring
  calc _ = ∑ init : Fin K → State, (∏ j, ρ.prob (init j)) * Ψ init (init k) :=
        Finset.sum_congr rfl fun init _ ↦ congrArg _ (hL init)
    _ = ∑ init : Fin K → State, (∏ j, ρ.prob (init j)) * ∑ s, ρ.prob s * Ψ init s :=
        sum_prod_eval_eq_sum_prod_avg ρ k Ψ h2
    _ = _ := Finset.sum_congr rfl fun init _ ↦ congrArg _ (hR init).symm

end Episodic
end StatisticalRL.OnlineRL.RegretToPAC
