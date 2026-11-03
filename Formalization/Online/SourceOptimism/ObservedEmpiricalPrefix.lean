import Formalization.Online.SourceOptimism.AdaptiveHistoryMass
import Formalization.Online.SourceOptimism.StackPrefixMarginal

/-! Same-data empirical row from actually
observed history equals its pre-sampled deterministic row prefix. No bonus
or empirical-row convention is defined at zero observed count. -/
namespace StatisticalRL.OnlineRL
variable {Row State : Type*} [Fintype Row] [DecidableEq Row] [Fintype State]

/-- The observed row data are the chronological successor list extracted from
actual records. The index type uses its actual count. -/
def onlineObservedRowData (history : List (Row × State)) (r : Row) :
    Fin (onlineRowOutcomes history r).length → State :=
  fun j => (onlineRowOutcomes history r).get j

/-- Stack prefix identity at the individual observed successor level, avoiding
an assumption that data selected by a random count are conditionally iid. -/
theorem onlineStackHistory_observedRowData
    (choose : List (Row × State) → Row) (stream : Row → ℕ → State)
    (n : ℕ) (r : Row)
    (j : Fin (onlineRowOutcomes (onlineStackHistory choose stream n) r).length) :
    onlineObservedRowData (onlineStackHistory choose stream n) r j=stream r j.val := by
  have hp := onlineStackHistory_row_prefix choose stream n r
  have h := congrArg (fun xs : List State => xs[j.val]?) hp
  have hs : some (onlineObservedRowData (onlineStackHistory choose stream n) r j)=
      some (stream r j.val) := by
    simpa [onlineObservedRowData,List.get_eq_getElem,j.isLt] using h
  exact Option.some.inj hs

/-- Actual observed data from a bounded finite stack equal the corresponding
fixed prefix vector, pointwise for every realization and every row. -/
theorem onlineFiniteStack_observedRowData_eq_prefix
    (choose : List (Row × State) → Row) (K n : ℕ) (fallback : State)
    (data : Row × Fin K → State) (r : Row)
    (hcount : (onlineRowOutcomes (onlineStackHistory choose
      (onlineFiniteStackExtend K fallback data) n) r).length≤K) :
    onlineObservedRowData (onlineStackHistory choose
      (onlineFiniteStackExtend K fallback data) n) r =
    onlineStackRowPrefix K
      (onlineRowOutcomes (onlineStackHistory choose
        (onlineFiniteStackExtend K fallback data) n) r).length hcount r data := by
  funext j
  rw [onlineStackHistory_observedRowData]
  have hj : j.val<K := j.isLt.trans_le hcount
  simp [onlineFiniteStackExtend,onlineStackRowPrefix,hj]

/-- The actual positive-count empirical frequency row is therefore exactly
the pre-sampled prefix empirical row; rewards and planning are not altered. -/
theorem onlineFiniteStack_empiricalRow_eq_prefix
    (choose : List (Row × State) → Row) (K n : ℕ) (fallback : State)
    (data : Row × Fin K → State) (r : Row)
    (hcount : (onlineRowOutcomes (onlineStackHistory choose
      (onlineFiniteStackExtend K fallback data) n) r).length≤K)
    (hpos : 0<(onlineRowOutcomes (onlineStackHistory choose
      (onlineFiniteStackExtend K fallback data) n) r).length) :
    FiniteDistribution.empiricalRow _ hpos
      (onlineObservedRowData (onlineStackHistory choose
        (onlineFiniteStackExtend K fallback data) n) r) =
    FiniteDistribution.empiricalRow _ hpos
      (onlineStackRowPrefix K
        (onlineRowOutcomes (onlineStackHistory choose
          (onlineFiniteStackExtend K fallback data) n) r).length hcount r data) := by
  rw [onlineFiniteStack_observedRowData_eq_prefix choose K n fallback data r hcount]

end StatisticalRL.OnlineRL
