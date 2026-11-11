# Critic report: TDInferenceC47Singular711.lean -- ACCEPT-WITH-FIXES (cosmetic)

Public copy, scrubbed (local paths, probe files and agent identifiers removed). Independent review of `Formalization/TDInference/Confidence/SingularConvention.lean` (convention on the singular event, C47(4)). Probes are local scratch files (`<local probe>`).

Integration note: verdict ACCEPT-WITH-FIXES (cosmetic); the finding 4 docstring fixes are applied, and the proposed C47(4) and COVERAGE wording is in `docs/SOURCE-ISSUES.md` and `docs/COVERAGE.md`. No statement entry (not a printed result); module imported from `Formalization.lean`.

Compile: copy at <local probe> (file + #print axioms) via scripts/lean-local.sh: no errors/warnings, 5.7s, all 8 exports depend only on [propext, Classical.choice, Quot.sound].

1. Singular event: setOf_aBar_det_eq_zero is a set EQUALITY {det=0} = {exists unsampled s}, proved using both directions of aBar_det_ne_zero_iff (the bound uses "unsampled => det=0" direction, i.e. the event {exists unsampled} is contained in/equal to singular; union bound via pathProb_exists_le + pathProb_unsampled). Correct, including T=0. In abs_pathProb_sub_le the indicator is of {det=0}; on det=0 the difference is <=1, off it 0 by hEF. Correct.
2. Rate lemma: rho (depends only on mu) is chosen before T, C1, C2, V; M, pi do not matter. Correct and strongest sensible order. rho=1-mu(s0)<1 by hmu; 0<=rho by mu<=1.
3. Corollary: hypotheses (h0,h1,V0,hmu,hGamma,Nonempty) are exactly those of plugin_coverage_tendsto; L arbitrary off {det!=0} (hL only on nonsingular). Uses .2.1 of the printed two-sided clause; the pathProb set matches definitionally (compiles). Note: only the two-sided clause is transferred (one-sided, rectangle D3 are not; transfer lemma tendsto_pathProb_of_eq_on_nonsingular applies to them verbatim). Convention concerns only Lambda-hat; V-bar_T (prAverage) and Gamma-hat are defined for all T.
4. Docstrings honest: defines nothing about the printed procedure; says C47(4) stays recorded. Minor fix: header says positive probability "when S>=2"; the cited pathProb_aBar_singular_pos needs two DISTINCT states of positive mu-mass -- reword. Also say the general-C result (abs_coverage_sub_le_*) is about arbitrary set-valued procedures, and eq:convex.Cdelta itself (Gaussian-mass condition) is NOT formalized here.
5. Not a printed result => no Statements entry needed (consistent with AGENTS.md); still must be imported in Formalization.lean for the audit.

## Proposed wording
SOURCE-ISSUES C47(4) append: "Quantified irrelevance of the convention (TDInferenceC47Singular711.lean): for any two confidence procedures agreeing whenever Abar_T is invertible, |P(V in C1)-P(V in C2)| <= P(Abar_T singular) <= sum_s (1-mu s)^T <= S rho^T (rho=max_s(1-mu s)<1 under full support). Hence for the plug-in two-sided interval, coverage -> 2Phi(z)-1 for every convention on the singular event (tendsto_coverage_twoSided_plugin_anyConvention). The printed procedure remains undefined on that event; the gap is not repaired, only shown asymptotically immaterial."
COVERAGE eq:defn-hat-Lambda Open: "Lambda-hat_T undefined when some state unsampled (C47(4)); asymptotic coverage independent of convention (C47Singular711); printed definition not repaired."
COVERAGE eq:convex.Cdelta Open: "Procedure with arbitrary C_alpha (Gaussian-mass >= 1-alpha) not formalized; only convention-independence of coverage for any set-valued procedure and for the plug-in two-sided interval; singular-event gap C47(4) as above."
