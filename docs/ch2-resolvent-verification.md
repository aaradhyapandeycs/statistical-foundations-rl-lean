# Chapter 2 policy-matrix resolvent verification

Source: `lem:basic-property-matrix-notation-inf`, `chapters/prelim.tex:544–574`.
Randomized policies are explicit in `prelim.tex:66`. The book defines its matrix
norm as maximum row-wise absolute sum in `chapters/intro.tex:204–209`.
The source export is `StatisticalRL.DiscountedMDP.policyMatrices_resolvent_properties`;
the index definitions are `StatisticalRL.Statements.Ch2.Lemma2_3` and `Lemma2_3_holds`.

For both policy matrices the result includes a genuine inverse, exact Neumann
expansion, all-ones action, row norm equality and nonnegative entries. Model fields
supply nonempty states/actions and `0≤discount<1`; no invertibility premise or
positive-discount restriction is added. The wrapper applies the stronger library
export and drops its explicit invertibility output.

Six qualified targets and their 14 actual exports passed standard-axiom checks.
The affected 837-module integration rebuilt 8 and verified 829 reused
modules; its whole-library audit covered 7,616 declarations. Manifest SHA-256:
`1103deecaf13b7286570f1b4c080cbaf301bf4cf0b949654bedda988ccc9ea6c`. The retained source/artifact ancestry has 20 edges through
the historical clean418 ancestor. Package guards record path/size/mtime metadata;
the historical clean418 run did not record OLean or package-byte hashes. This is
an affected rebuild with verified reuse, not a new clean 837-module build.
Independent source and consumption review is [here](critic-ch2-resolvent.md).
