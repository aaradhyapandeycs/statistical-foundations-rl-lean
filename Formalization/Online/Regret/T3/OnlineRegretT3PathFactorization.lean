import Formalization.Online.SourceOptimism.SequentialHistoryDensity

/-!
# Prefix/suffix factorization for the actual sequential online law

helper for the global T₃ filtration bridge. This file only factors
the already-defined recursive transition law into a revealed prePath and its
actual continuation law. No division by a prePath mass is used, so the identity
also holds on zero-probability histories. No conditional-expectation or tail
bound is claimed here.
-/

namespace StatisticalRL.OnlineRL

variable {Row Outcome : Type*} [Fintype Row] [Fintype Outcome]

/-- Chronological concatenation of direct outcome paths. The result length is
suffix length plus prePath length so the recursive equation is definitional. -/
def onlineSequentialPathAppend : (n m : ℕ) →
    OnlineOutcomePath Outcome n → OnlineOutcomePath Outcome m →
      OnlineOutcomePath Outcome (m + n)
  | 0, _, _, suffix => by simpa using suffix
  | n + 1, m, prePath, suffix =>
      (PUnit.unit, prePath.2.1, onlineSequentialPathAppend n m prePath.2.2 suffix)

/-- First `n` outcomes of a path of total length `m+n`. -/
def onlineSequentialPathPrefix : (n m : ℕ) →
    OnlineOutcomePath Outcome (m + n) → OnlineOutcomePath Outcome n
  | 0, _, _ => PUnit.unit
  | n + 1, m, path =>
      (PUnit.unit, path.2.1, onlineSequentialPathPrefix n m path.2.2)

/-- Remaining `m` outcomes after the first `n` outcomes of a path of length
`m+n`. -/
def onlineSequentialPathSuffix : (n m : ℕ) →
    OnlineOutcomePath Outcome (m + n) → OnlineOutcomePath Outcome m
  | 0, _, path => path
  | n + 1, m, path => onlineSequentialPathSuffix n m path.2.2

theorem onlineSequentialPathPrefix_append (n m : ℕ)
    (prePath : OnlineOutcomePath Outcome n) (suffix : OnlineOutcomePath Outcome m) :
    onlineSequentialPathPrefix n m (onlineSequentialPathAppend n m prePath suffix) = prePath := by
  induction n generalizing m with
  | zero => cases prePath; rfl
  | succ n ih =>
      rcases prePath with ⟨u, x, prefixTail⟩
      simp [onlineSequentialPathPrefix, onlineSequentialPathAppend, ih]

theorem onlineSequentialPathSuffix_append (n m : ℕ)
    (prePath : OnlineOutcomePath Outcome n) (suffix : OnlineOutcomePath Outcome m) :
    onlineSequentialPathSuffix n m (onlineSequentialPathAppend n m prePath suffix) = suffix := by
  induction n generalizing m with
  | zero => simp [onlineSequentialPathSuffix, onlineSequentialPathAppend]
  | succ n ih =>
      rcases prePath with ⟨u, x, prefixTail⟩
      simpa [onlineSequentialPathSuffix, onlineSequentialPathAppend] using ih m prefixTail suffix

theorem onlineSequentialPathAppend_prefix_suffix (n m : ℕ)
    (path : OnlineOutcomePath Outcome (m + n)) :
    onlineSequentialPathAppend n m (onlineSequentialPathPrefix n m path)
      (onlineSequentialPathSuffix n m path) = path := by
  induction n generalizing m with
  | zero =>
      simp [onlineSequentialPathPrefix, onlineSequentialPathSuffix,
        onlineSequentialPathAppend]
  | succ n ih =>
      rcases path with ⟨u, x, pathTail⟩
      cases u
      simp only [onlineSequentialPathPrefix, onlineSequentialPathSuffix,
        onlineSequentialPathAppend, Nat.add_succ]
      exact congrArg (fun tail => (PUnit.unit, x, tail)) (ih m pathTail)

/-- Finite path equivalence exposing the chronological prePath and continuation
without identifying their laws or assuming independence. -/
def onlineSequentialPathSplitEquiv (n m : ℕ) :
    OnlineOutcomePath Outcome (m + n) ≃
      OnlineOutcomePath Outcome n × OnlineOutcomePath Outcome m where
  toFun path :=
    (onlineSequentialPathPrefix n m path, onlineSequentialPathSuffix n m path)
  invFun paths := onlineSequentialPathAppend n m paths.1 paths.2
  left_inv := onlineSequentialPathAppend_prefix_suffix n m
  right_inv := by
    rintro ⟨prePath, suffix⟩
    simp only [Prod.mk.injEq]
    exact ⟨onlineSequentialPathPrefix_append n m prePath suffix,
      onlineSequentialPathSuffix_append n m prePath suffix⟩

/-- Reconstructing a concatenated path is exactly continuing from its revealed
prePath transcript. -/
theorem onlineSequentialPathHistory_append
    (choose : List (Row × Outcome) → Row) (n m : ℕ)
    (history : List (Row × Outcome))
    (prePath : OnlineOutcomePath Outcome n) (suffix : OnlineOutcomePath Outcome m) :
    onlineSequentialPathHistory choose (m + n) history
        (onlineSequentialPathAppend n m prePath suffix) =
      onlineSequentialPathHistory choose m
        (onlineSequentialPathHistory choose n history prePath) suffix := by
  induction n generalizing m history with
  | zero => simp [onlineSequentialPathAppend, onlineSequentialPathHistory]
  | succ n ih =>
      rcases prePath with ⟨u, x, prefixTail⟩
      simp only [onlineSequentialPathAppend, onlineSequentialPathHistory,
        Nat.add_succ]
      simpa [List.append_assoc] using
        ih m (history ++ [(choose history, x)]) prefixTail suffix

/-- Exact path-law factorization across a deterministic split. The chosen row
after the prePath is the same causal function evaluated on the reconstructed
prePath history. This identity is a product of actual recursive probabilities,
not an independence assertion and not a quotient by prePath mass. -/
theorem onlineSequentialOutcomeLaw_prob_append
    (d : Row → FiniteDistribution Outcome)
    (choose : List (Row × Outcome) → Row) (n m : ℕ)
    (history : List (Row × Outcome))
    (prePath : OnlineOutcomePath Outcome n) (suffix : OnlineOutcomePath Outcome m) :
    (onlineSequentialOutcomeLaw d choose (m + n) history).prob
        (onlineSequentialPathAppend n m prePath suffix) =
      (onlineSequentialOutcomeLaw d choose n history).prob prePath *
        (onlineSequentialOutcomeLaw d choose m
          (onlineSequentialPathHistory choose n history prePath)).prob suffix := by
  induction n generalizing m history with
  | zero =>
      letI : Subsingleton (OnlineOutcomePath Outcome 0) :=
        inferInstanceAs (Subsingleton PUnit)
      have hprob :
          (onlineSequentialOutcomeLaw d choose 0 history).prob prePath = 1 :=
        FiniteDistribution.prob_eq_one_of_subsingleton _ _
      cases prePath
      simp [onlineSequentialPathAppend, onlineSequentialPathHistory, hprob]
  | succ n ih =>
      rcases prePath with ⟨u, x, prefixTail⟩
      cases u
      change (d (choose history)).prob x *
          (onlineSequentialOutcomeLaw d choose (m + n)
            (history ++ [(choose history, x)] )).prob
            (onlineSequentialPathAppend n m prefixTail suffix) =
        ((d (choose history)).prob x *
          (onlineSequentialOutcomeLaw d choose n
            (history ++ [(choose history, x)] )).prob prefixTail) *
          (onlineSequentialOutcomeLaw d choose m
            (onlineSequentialPathHistory choose n
              (history ++ [(choose history, x)] ) prefixTail)).prob suffix
      rw [ih m (history ++ [(choose history, x)]) prefixTail suffix]
      ring

end StatisticalRL.OnlineRL
