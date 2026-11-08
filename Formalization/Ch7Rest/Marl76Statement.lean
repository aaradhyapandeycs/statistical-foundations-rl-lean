import Formalization.Ch7Rest.Marl76Defs

/-!
# Theorem 7.6: statement drafts (definitions only, no proofs)

`thm:sample-complexity-plug-in-marl`, `chapters/marl.tex:384–399`.

* `Thm7_6_printed`: the printed joint statement with the planning oracles left unspecified
  (any maps returning an NE, resp. a CCE, of every empirical game). It is refuted by
  `not_thm7_6_printed` (counterexample CE2, SOURCE-ISSUES C45). `0 < N` is part of the binder list
  (the empirical kernel needs it, an implicit convention as in `Thm3_2_positiveN`), so the
  refutation is of a statement that already contains that convention.
* `Thm7_6_restricted`: three clauses with one universal constant `C₁`:
  (a) every causal CCE oracle, (b) every causal NE oracle, (c) the printed joint form for a causal
  NE oracle together with a causal CCE oracle. The printed threshold (with `N` inside the
  logarithm), `δ ∈ (0,1)` and `0 < ε ≤ √H` are kept. Added: causal oracles (C45), `0 < N`
  (implicit convention), and the domain conditions `0 < S`, `∀ i, 0 < A_i` (needed for the
  sampling law to be defined).
-/

open scoped BigOperators

namespace StatisticalRL.Ch7Rest.Marl76

open StatisticalRL StatisticalRL.Ch7Rest.Marl

/-- Printed Theorem 7.6 (`thm:sample-complexity-plug-in-marl`, `marl.tex:384–399`), "any oracle"
reading (`docs/SOURCE-ISSUES.md#C45`). The planning step (`marl.tex:377`) only says that the oracle
returns an NE, resp. a CCE, of the empirical game, so the oracles are arbitrary deterministic maps
`One` (to product policies) and `Occe` (to joint policies) from Markov games to policies, applied to
the empirical game, subject only to: for every data set (`∀ data`, not merely almost surely) the
output is an NE (`eq:defn-Nash-E`, step 1 only, equality form), resp. a CCE (`eq:defn-CCE`), of the
empirical game. The NE gap is the product-policy `gap`, the CCE gap the joint-policy `gapJ`
(`eq:defn-NE-gap`). Universal constant `C₁` quantified first; printed threshold with `N` inside the
logarithm; `δ ∈ (0,1)`, `0 < ε ≤ √H`; rewards in `[0,1]` at steps `1..H`.

Binders added to the printed text (none weakens the refutation `not_thm7_6_printed`, which
refutes the statement with them):
* `0 < S` and `∀ i, 0 < A_i`: domain conditions needed for the sampling law to be defined;
* `0 < N`: implicit convention (the empirical kernel `P̂ = N⁻¹ ∑ …` needs it; with `N = 0` the
  printed condition is `0 ≥ C₁ … log 0`), as in `Thm3_2_positiveN`;
* the oracles are deterministic maps of the empirical game (randomized oracles are not modelled);
* the equilibrium hypotheses are required for every data set. -/
def Thm7_6_printed : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
  ∀ (m S H : ℕ) (A : Fin m → ℕ) (hS : 0 < S) (hA : ∀ i, 0 < A i) (G : MarkovGame m S H A),
    (∀ i h s a, 1 ≤ h → h ≤ H → 0 ≤ G.reward i h s a ∧ G.reward i h s a ≤ 1) →
  ∀ (N : ℕ) (hN : 0 < N) (δ ε : ℝ), 0 < δ → δ < 1 → 0 < ε → ε ≤ Real.sqrt H →
    C₁ * (H : ℝ) ^ 3 / ε ^ 2 *
        Real.log ((S : ℝ) * H * N * (∏ i, (A i : ℝ)) / δ) ≤ N →
  ∀ (One : MarkovGame m S H A → ProductPolicy m S A)
    (Occe : MarkovGame m S H A → JointPolicy m S A),
    (∀ data, IsNE (empiricalGame G N hN data) (One (empiricalGame G N hN data))) →
    (∀ data, IsCCE (empiricalGame G N hN data) (Occe (empiricalGame G N hN data))) →
    1 - δ ≤ (gameSamplingLaw G hS hA N).real
      {data | gap G (One (empiricalGame G N hN data)) ≤ ε ∧
        gapJ G (Occe (empiricalGame G N hN data)) ≤ ε}

/-- NE-only reading of printed Theorem 7.6 (same conventions as `Thm7_6_printed`, only the NE
clause). -/
def Thm7_6_printed_ne : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
  ∀ (m S H : ℕ) (A : Fin m → ℕ) (hS : 0 < S) (hA : ∀ i, 0 < A i) (G : MarkovGame m S H A),
    (∀ i h s a, 1 ≤ h → h ≤ H → 0 ≤ G.reward i h s a ∧ G.reward i h s a ≤ 1) →
  ∀ (N : ℕ) (hN : 0 < N) (δ ε : ℝ), 0 < δ → δ < 1 → 0 < ε → ε ≤ Real.sqrt H →
    C₁ * (H : ℝ) ^ 3 / ε ^ 2 *
        Real.log ((S : ℝ) * H * N * (∏ i, (A i : ℝ)) / δ) ≤ N →
  ∀ One : MarkovGame m S H A → ProductPolicy m S A,
    (∀ data, IsNE (empiricalGame G N hN data) (One (empiricalGame G N hN data))) →
    1 - δ ≤ (gameSamplingLaw G hS hA N).real
      {data | gap G (One (empiricalGame G N hN data)) ≤ ε}

/-- CCE-only reading of printed Theorem 7.6 (same conventions as `Thm7_6_printed`, only the CCE
clause). -/
def Thm7_6_printed_cce : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
  ∀ (m S H : ℕ) (A : Fin m → ℕ) (hS : 0 < S) (hA : ∀ i, 0 < A i) (G : MarkovGame m S H A),
    (∀ i h s a, 1 ≤ h → h ≤ H → 0 ≤ G.reward i h s a ∧ G.reward i h s a ≤ 1) →
  ∀ (N : ℕ) (hN : 0 < N) (δ ε : ℝ), 0 < δ → δ < 1 → 0 < ε → ε ≤ Real.sqrt H →
    C₁ * (H : ℝ) ^ 3 / ε ^ 2 *
        Real.log ((S : ℝ) * H * N * (∏ i, (A i : ℝ)) / δ) ≤ N →
  ∀ Occe : MarkovGame m S H A → JointPolicy m S A,
    (∀ data, IsCCE (empiricalGame G N hN data) (Occe (empiricalGame G N hN data))) →
    1 - δ ≤ (gameSamplingLaw G hS hA N).real
      {data | gapJ G (Occe (empiricalGame G N hN data)) ≤ ε}

/-- Restricted Theorem 7.6: causal planning oracles (C45), `0 < N`. -/
def Thm7_6_restricted : Prop :=
  ∃ C₁ : ℝ, 0 < C₁ ∧
  ∀ (m S H : ℕ) (A : Fin m → ℕ) (hS : 0 < S) (hA : ∀ i, 0 < A i) (G : MarkovGame m S H A),
    (∀ i h s a, 1 ≤ h → h ≤ H → 0 ≤ G.reward i h s a ∧ G.reward i h s a ≤ 1) →
  ∀ (N : ℕ) (hN : 0 < N) (δ ε : ℝ), 0 < δ → δ < 1 → 0 < ε → ε ≤ Real.sqrt H →
    C₁ * (H : ℝ) ^ 3 / ε ^ 2 *
        Real.log ((S : ℝ) * H * N * (∏ i, (A i : ℝ)) / δ) ≤ N →
    -- (a) CCE clause
    (∀ Occe : MarkovGame m S H A → JointPolicy m S A, CausalOracle Occe →
      (∀ data, IsCCE (empiricalGame G N hN data) (Occe (empiricalGame G N hN data))) →
      1 - δ ≤ (gameSamplingLaw G hS hA N).real
        {data | gapJ G (Occe (empiricalGame G N hN data)) ≤ ε}) ∧
    -- (b) NE clause
    (∀ One : MarkovGame m S H A → ProductPolicy m S A, CausalProductOracle One →
      (∀ data, IsNE (empiricalGame G N hN data) (One (empiricalGame G N hN data))) →
      1 - δ ≤ (gameSamplingLaw G hS hA N).real
        {data | gap G (One (empiricalGame G N hN data)) ≤ ε}) ∧
    -- (c) joint clause (the printed conclusion)
    (∀ (One : MarkovGame m S H A → ProductPolicy m S A)
        (Occe : MarkovGame m S H A → JointPolicy m S A),
      CausalProductOracle One → CausalOracle Occe →
      (∀ data, IsNE (empiricalGame G N hN data) (One (empiricalGame G N hN data))) →
      (∀ data, IsCCE (empiricalGame G N hN data) (Occe (empiricalGame G N hN data))) →
      1 - δ ≤ (gameSamplingLaw G hS hA N).real
        {data | gap G (One (empiricalGame G N hN data)) ≤ ε ∧
          gapJ G (Occe (empiricalGame G N hN data)) ≤ ε})

end StatisticalRL.Ch7Rest.Marl76
