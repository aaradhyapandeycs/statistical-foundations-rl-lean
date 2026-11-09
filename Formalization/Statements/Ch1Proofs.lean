import Formalization.Probability.KLChiSquared
import Formalization.Statements.Ch1

namespace StatisticalRL.Statements

theorem Eq_KL_ub_chi2_holds : Eq_KL_ub_chi2 := by
  intro Ω _ P Q _ _ hPQ
  exact StatisticalRL.Probability.two_mul_sq_tv_le_klDiv_le_chiSquared P Q hPQ

end StatisticalRL.Statements
