import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Basic

universe u v

namespace StatisticalRL

/-- All action/next-state paths of exactly the specified length. The current
state is supplied separately; each step stores its action and resulting state. -/
def FinitePath (State : Type u) (Action : Type v) : ℕ → Type (max u v)
  | 0 => PUnit
  | n + 1 => Action × State × FinitePath State Action n

namespace FinitePath

variable {State Action : Type*}

instance instFintype [Fintype State] [Fintype Action] :
    (n : ℕ) → Fintype (FinitePath State Action n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
    letI := instFintype n
    exact inferInstanceAs (Fintype (Action × State × FinitePath State Action n))

end FinitePath

end StatisticalRL

namespace StatisticalRL.OnlineRL

variable {Row Outcome : Type*} [Fintype Row] [Fintype Outcome]

/-- Dummy singleton actions merely reuse the established finite outcome-path
carrier; actual selected actions are recorded in the predictable row label. -/
abbrev OnlineOutcomePath (Outcome : Type*) (n : ℕ) := FinitePath Outcome PUnit n

/-- Realized history reconstructed from a direct sequential outcome path. -/
def onlineSequentialPathHistory
    (choose : List (Row × Outcome) → Row) :
    (n : ℕ) → List (Row × Outcome) → OnlineOutcomePath Outcome n → List (Row × Outcome)
  | 0, history, _ => history
  | n+1, history, path => onlineSequentialPathHistory choose n
      (history++[(choose history,path.2.1)]) path.2.2

end StatisticalRL.OnlineRL
