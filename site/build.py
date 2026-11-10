#!/usr/bin/env python3
"""Build the book-alongside-Lean reader into site/_build/.

    python3 scripts/fetch_source.py      # restore and verify the pinned arXiv TeX
    python3 site/build.py                # build from the pushed commit (origin/main)
    python3 site/build.py --rev HEAD     # or from another committed revision

Reads, never writes, project files. Lean files and ledgers are read with
`git show <rev>:<path>`, so uncommitted work is never shown and every Lean
link points at a commit that exists on GitHub. No Lean or Lake process runs.
"""

from __future__ import annotations

import argparse
import html
import re
import shutil
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))

from reader.book import Book  # noqa: E402
from reader.graph import GraphPages, gen_nodes  # noqa: E402
from reader.lean import REPO, Git, LeanIndex  # noqa: E402
from reader.links import repo_link_problems  # noqa: E402
from reader.render import Site  # noqa: E402


def default_rev(repo: Path) -> str:
    r = subprocess.run(["git", "-C", str(repo), "rev-parse", "--abbrev-ref", "@{upstream}"],
                       capture_output=True, text=True)
    return r.stdout.strip() if r.returncode == 0 and r.stdout.strip() else "HEAD"


COUNT_RE = re.compile(r'<span class="n" data-count="([^"]+)">([^<]*)</span>')


def check_counts(pages: dict, data: dict) -> list:
    """Every count shown is tagged with its summary path; each must equal nodes.json's summary, and the
    summary's label counts must equal a direct tally of the nodes' labels. Returns the problems."""
    s = data["summary"]
    problems = []
    nodes = data["nodes"]
    for cls in ("named", "prose"):
        for k in gen_nodes.SITE_LABEL_ORDER:
            direct = sum(1 for n in nodes if n["class"] == cls and n["site_label"] == k)
            if s[f"{cls}_by_label"][k] != direct:
                problems.append(f"summary {cls}_by_label.{k}={s[f'{cls}_by_label'][k]} but {direct} nodes have it")
        for mk, key in (("refuted", "refuted_marker"), ("fails-paper", "fails_paper_marker"),
                        ("boundary", "boundary_marker")):
            direct = sum(1 for n in nodes if n["class"] == cls and mk in n["site_markers"])
            if s[f"{cls}_{key}"] != direct:
                problems.append(f"summary {cls}_{key} disagrees with the nodes ({direct})")
    if sum(s["named_by_label"].values()) != s["named_results_in_inventory"]:
        problems.append("named_by_label does not add up to the numbered results in the inventory")
    seen = 0
    for pid, text in pages.items():
        for path, shown in COUNT_RE.findall(text):
            seen += 1
            v = s
            try:
                for k in html.unescape(path).split("."):
                    v = v[k]
            except (KeyError, TypeError):
                problems.append(f"{pid}.html: count path {path} is not in the summary")
                continue
            if str(v) != shown:
                problems.append(f"{pid}.html: {path} shows {shown}, summary has {v}")
    if not seen:
        problems.append("no tagged counts found on any page")
    return problems


def pinned_commit_warning(repo: Path, rev: str) -> str | None:
    """Best effort, no network: warn when the pinned commit is on no remote-tracking branch, so its GitHub
    links would 404 until it is pushed. Silent when the repository has no remote or git fails."""
    def git(*a):
        r = subprocess.run(["git", "-C", str(repo), *a], capture_output=True, text=True)
        return r.stdout.strip() if r.returncode == 0 else None
    remotes = git("remote")
    if not remotes:
        return None
    contains = git("branch", "-r", "--contains", rev)
    if contains is None or contains:
        return None
    return (f"WARNING: the pinned commit {rev[:12]} is not on any remote-tracking branch of "
            f"{', '.join(remotes.split())} (as of the last fetch). Every pinned GitHub link and the CI-status link "
            f"will return 404 until this commit is pushed; publish only a build of a pushed commit.")


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--rev", default=None, help="git revision for Lean files and ledgers (default: upstream branch)")
    ap.add_argument("--out", default=str(HERE / "_build"), help="output directory")
    ap.add_argument("--lean-repo", default=str(ROOT),
                    help="git repository to read Lean files and ledgers from (default: this checkout); "
                         "any clone of the project works, e.g. when local git objects are unavailable")
    ap.add_argument("--ci-run-url", default=None,
                    help="URL of the Lean CI run that gated this deploy (pages.yml passes it); omit for local builds")
    ap.add_argument("--audit-log", default=None,
                    help="file with the CI axiom-audit output; its 'Axiom audit passed ...' line is shown verbatim")
    args = ap.parse_args()

    final = Path(args.out).resolve()
    if final.exists() and not (final / ".sfrl-reader").exists():
        raise SystemExit(f"{final} exists and was not made by this builder; refusing to replace it")
    # Build next to the target and swap at the end, so a failed or interrupted
    # build never leaves the served site empty.
    out = final.with_name(final.name + ".new")
    if out.exists():
        shutil.rmtree(out)
    out.mkdir(parents=True)
    (out / ".sfrl-reader").write_text("generated by site/build.py\n")

    book = Book(ROOT, out)
    lean_repo = Path(args.lean_repo).resolve()
    git = Git(lean_repo, args.rev or default_rev(lean_repo))
    labels = {l["label"] for l in book.inventory["labels"]}
    lean = LeanIndex(git, labels)

    front, chapters, back = book.convert_all()
    pages = book.paginate(chapters)
    audit_line = None
    if args.audit_log:
        audit_line = next((l.strip() for l in Path(args.audit_log).read_text().splitlines()
                           if "Axiom audit passed for" in l), None)
        if audit_line is None:
            raise SystemExit(f"{args.audit_log}: no 'Axiom audit passed for' line")
    site = Site(book, lean, pages, front, back, ci_run_url=args.ci_run_url, audit_line=audit_line)
    bad = site.placement_problems()
    if bad:
        raise SystemExit("Lean cards not at their ledger item:\n  " + "\n  ".join(bad))

    html_pages = site.book_pages()
    html_pages["acknowledgements"] = site.ack_page()
    site.index_anchors(html_pages)  # anchors of book items, for links from the overview pages
    graph = GraphPages(site, html_pages)  # node graph from the ledgers at the same Lean revision
    html_pages["index"] = site.index_page()
    html_pages["results"] = site.results_page()
    html_pages["book"] = site.book_landing_page()
    html_pages["status"] = graph.status_page()
    html_pages["graph"] = graph.graph_page()
    html_pages["errata"] = graph.errata_page()
    html_pages["methodology"] = site.methodology_page()
    html_pages["credits"] = site.credits_page()
    html_pages["contribute"] = site.contribute_page()
    html_pages["about"] = site.about_page()
    html_pages["references"] = site.references_page()  # last: citations are collected above
    html_pages = site.resolve(html_pages)
    problems = check_counts(html_pages, graph.data)
    if problems:
        raise SystemExit("counts on the site disagree with the node-graph summary:\n  " + "\n  ".join(problems[:40]))
    link_problems = repo_link_problems(html_pages, REPO, git.rev, set(git.ls(".")), git.show)
    if link_problems:
        raise SystemExit("links into the repository with no target at the pinned commit:\n  "
                         + "\n  ".join(link_problems[:60]))

    for pid, text in html_pages.items():
        (out / f"{pid}.html").write_text(text)
    assets = out / "assets"
    assets.mkdir(exist_ok=True)
    for f in (HERE / "static").iterdir():
        shutil.copyfile(f, assets / f.name)
    (assets / "mathjax-config.js").write_text(site.mathjax_config())
    (out / "results.json").write_text(site.search_data())
    (out / "graph").mkdir(exist_ok=True)
    (out / "graph" / "nodes.json").write_text(graph.nodes_json())
    (out / "graph" / "graph.dot").write_text(graph.dot())
    (out / ".nojekyll").write_text("")

    old = final.with_name(final.name + ".old")
    if old.exists():
        shutil.rmtree(old)
    if final.exists():
        final.rename(old)
    out.rename(final)
    if old.exists():
        shutil.rmtree(old)
    out = final

    placed = len(lean.entries) - len(site.unplaced)
    print(f"Lean commit {git.rev}")
    warn = pinned_commit_warning(lean_repo, git.rev)
    if warn:
        print(warn)
    print(f"{len(html_pages)} pages, {len(pages)} book sections, {len(book.images)} figures")
    gs = graph.data["summary"]
    print("labels (numbered results): " + ", ".join(f"{gen_nodes.SITE_LABELS[k][0]}={gs['named_by_label'][k]}"
                                                    for k in gen_nodes.SITE_LABEL_ORDER)
          + f"; refuted in Lean={gs['named_refuted_marker']}, boundary case={gs['named_boundary_marker']}, "
            f"fails on paper={gs['named_fails_paper_marker']}")
    print("old status -> label: printed->proved as stated, corrected->proved with corrections, "
          "restricted->proved under restrictions, everything else->incomplete (explanatory: no label)")
    print(f"node graph: {len(graph.data['nodes'])} nodes, {gs['uses_edges']} unreviewed edges; "
          f"{gs['named_results_with_ledger_record']} of {gs['named_results_in_inventory']} numbered results "
          f"with a ledger record")
    print(f"{len(lean.entries)} statement entries, {placed} placed next to book text, {len(site.unplaced)} unplaced")
    if site.unplaced:
        print("  unplaced: " + ", ".join(e.name for e in site.unplaced))
    if book.unknown:
        top = sorted(book.unknown.items(), key=lambda x: -x[1])[:40]
        print("unhandled TeX commands (count): " + ", ".join(f"{k}={v}" for k, v in top))
    if site.missing_refs:
        print(f"unresolved references: {len(site.missing_refs)} labels, e.g. " + ", ".join(list(site.missing_refs)[:10]))
    for w in book.warnings[:40]:
        print("warning: " + w)
    if len(book.warnings) > 40:
        print(f"... {len(book.warnings) - 40} more warnings")
    print(f"wrote {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
