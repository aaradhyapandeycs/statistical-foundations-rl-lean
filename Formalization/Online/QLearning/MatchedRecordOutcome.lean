import Formalization.Online.QLearning.ActualBonusRank
import Formalization.Online.QLearning.VisitCountNoise
import Mathlib.Data.List.GetD

/-! Deterministic ordered row outcomes at a matched chronological record. -/
namespace StatisticalRL.OnlineRL
variable {Row Outcome : Type*} [DecidableEq Row]

theorem qLearning_matchedRecord_rowOutcome
    (hist : List (Row × Outcome)) (r : Row) (j : ℕ) (hj : j < hist.length)
    (hr : hist[j].1 = r) (fallback : Outcome) :
    (onlineRowOutcomes hist r).getD (onlineRowOutcomes (hist.take j) r).length fallback = hist[j].2 := by
  have hsplit : hist = (hist.take j ++ [hist[j]]) ++ hist.drop (j+1) := by
    calc
      hist = hist.take (j+1) ++ hist.drop (j+1) := (List.take_append_drop (j+1) hist).symm
      _ = (hist.take j ++ [hist[j]]) ++ hist.drop (j+1) := by
        rw [← List.take_concat_get' hist j hj]
  have hrow : onlineRowOutcomes hist r = onlineRowOutcomes (hist.take j) r ++
      (hist[j].2 :: onlineRowOutcomes (hist.drop (j+1)) r) := by
    calc
      onlineRowOutcomes hist r = onlineRowOutcomes ((hist.take j ++ [hist[j]]) ++ hist.drop (j+1)) r :=
        congrArg (fun xs => onlineRowOutcomes xs r) hsplit
      _ = _ := by
        simp only [onlineRowOutcomes, List.filterMap_append, List.filterMap_cons,
          List.filterMap_nil, hr, ite_true, List.append_nil, List.append_assoc, List.singleton_append]
  rw [hrow, List.getD_append_right _ _ _ _ (le_refl _)]
  simp
end StatisticalRL.OnlineRL
