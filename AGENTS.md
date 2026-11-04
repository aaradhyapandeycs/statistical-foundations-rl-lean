# Entire-monograph Lean formalization

The goal is the complete end-to-end formalization of arXiv:2610.41903v1, all chapters, appendices, stated results, algorithms and substantive mathematical claims. Keep the full goal open until coverage, Lean proof evidence, and independent source review establish it.

## Source and skills

- Pin the source with `source/provenance.json`. Restore raw inputs with `python3 scripts/fetch_source.py`. Treat upstream files as read-only. Cite exact source labels and ranges.
- Read `skills/lean/skills/lean-workflow/SKILL.md`, then relevant focused skills. The full collection index is `skills/lean/INDEX.md`.
- Source inventory is a checklist, not a source dependency graph or proof certification. An index of theorem environments does not cover prose claims, assumptions, algorithm semantics, or omitted arguments by itself.
- No author approval or frozen statement status may be inferred or fabricated. Follow the exact approval procedure if adopting frozen anchors. Ordinary proved infrastructure may be developed and audited without inventing a frozen manifest.

## Builder and critic teams

- Builders implement real definitions and proofs in assigned files; critics reconstruct source mathematics independently and attempt to refute the translation and its assumptions.
- Keep write sets disjoint and record ownership in `docs/PROGRESS.md`. A builder cannot certify its own source fidelity. The lead integrates after critic findings are addressed.
- Worker briefs include source locators, target scope, imports, owned files, validation command, and stop condition. Use the available worker slots for independent tasks (this session permits three plus the lead), and at most two concurrent Lean compilers.
- The user explicitly excludes Astra models. Use available Sol, Terra, or Luna models for agents and continuation work; do not select Astra as a fallback.
- Preserve theorem signatures during proof completion. No hidden hypotheses, unproved intermediate inputs, weakened conclusions, fallback definitions, custom axioms, `sorry`, or `admit` in library code.
- A source error is an open obligation. Record counterevidence and proposed corrections explicitly; never silently change the paper or call a corrected statement the original theorem.

## Statement index

- Every source result that `docs/COVERAGE.md` records as proved (fully, or as a disclosed corrected or restricted variant) also gets a statement entry in `Formalization/Statements/ChN.lean`, where N is the source chapter number. Add the entry in the same change that records the result as proved.
- An entry is a `Prop`-valued definition named after the source result, e.g. `def Thm3_2 : Prop := ...`. Its docstring cites the source label and the `.tex` line range. A corrected or restricted variant uses a suffix such as `Thm3_7_corrected`, and its docstring states how it differs from the printed result and points to the matching `docs/SOURCE-ISSUES.md` entry.
- The `Prop` must be the full, self-contained statement, with every quantifier and hypothesis written out, so a reader can check it against the book without opening proof files. Do not define it by referring to another theorem's type.
- `Formalization/Statements/ChN.lean` imports definition modules only and contains no proofs. A separate `Formalization/Statements/ChNProofs.lean` imports it together with the proof modules and proves each entry, e.g. `theorem Thm3_2_holds : Thm3_2 := ...`. The proof applies the existing library theorem; it must not restate the result or prove it a second time. Import both files from `Formalization.lean` so the axiom audit covers them.
- The index is a reading aid. Adding an entry never changes or weakens a library theorem signature.
- The entry states the printed result. When the library export implies it (for example, the export assumes less, such as rate bounds only on the prefix actually used, or concludes more), that is not a discrepancy: the `ChNProofs.lean` wrapper derives the printed statement from the export, for instance by restricting a global hypothesis to the needed range. Do not stop for this, and do not record it in `SOURCE-ISSUES.md`.
- Only when the export does not imply the printed result (it assumes more, concludes less, or concerns a different object) is it a source-fidelity finding. Then use a `_corrected` or `_restricted` entry that states exactly what is proved and points to a `SOURCE-ISSUES.md` entry, and continue with the other entries.

## Build and evidence

- Lean and Mathlib versions are pinned. Respect the module conventions supported by this version; no forced port to newer syntax.
- Search existing Mathlib APIs before proving. Use small compiler-guided steps and focused checks.
- Public setup: `lake exe cache get`, then `lake build` and `lake env lean Audit.lean`. Do not run `lake update` or `lake clean` during routine work.
- Local development may use ignored read-only dependency links and `scripts/lean-local.sh`; never write dependency artifacts or rebuild shared packages through those links. Only project artifacts go in this project's `.lake/build`.
- `python3 scripts/check.py` compiles the local import closure and runs the axiom audit without rebuilding dependencies. Report actual commands, source hashes, failures and skipped checks.
- Completion requires full source correspondence, meaningful definitions, completed prerequisites, compiled actual exports, and transitive axiom closure allowing only `propext`, `Classical.choice`, and `Quot.sound`.
- Performance claims require measurements. Public release checks include licenses, source provenance, explicit incomplete status, no private local paths, and no transient probes.

The user authorized a public maintained GitHub repository under `aaradhyapandeycs`. Public status must continue to distinguish infrastructure from completed source results and whole-paper completion.
