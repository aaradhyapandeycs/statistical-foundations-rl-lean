#!/usr/bin/env python3
"""Read-only loopback project dashboard. Run: python3 scripts/progress_dashboard.py."""
import argparse
from datetime import datetime, timezone
from functools import lru_cache
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
from urllib.parse import urlsplit

ROOT = Path(__file__).resolve().parents[1]
REPO_URL = 'https://github.com/aaradhyapandeycs/statistical-foundations-rl-lean'


def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args], stderr=subprocess.DEVNULL,
                                   timeout=10).decode('utf-8', errors='replace').strip()


def project_lean(path):
    p = PurePosixPath(path)
    return p.suffix == '.lean' and (len(p.parts) == 1 or p.parts[0] == 'Formalization')


@lru_cache(maxsize=4)
def published_snapshot(sha):
    tree = git('ls-tree', '-r', sha).splitlines()
    names = [line.split('\t', 1)[1] for line in tree
             if '\t' in line and not line.startswith('120000 ')
             and project_lean(line.split('\t', 1)[1])]
    lines = sum(len(subprocess.check_output(
        ['git', '-C', str(ROOT), 'show', f'{sha}:{p}'], stderr=subprocess.DEVNULL,
        timeout=10).splitlines()) for p in names)
    return {'available': True, 'reference': 'origin/main', 'sha': sha,
            'lean_lines': lines, 'lean_files': len(names),
            'commit_time': git('show', '-s', '--format=%cI', sha),
            'url': REPO_URL + '/commit/' + sha}


def staged_snapshot():
    config_path = ROOT / '.local/dashboard-staged.json'
    if not config_path.is_file():
        return {'available': False}
    try:
        config = json.loads(config_path.read_text())
        directory = (ROOT / config['verification_directory']).resolve()
        if ROOT not in directory.parents or not str(directory.relative_to(ROOT)).startswith('.local/'):
            raise ValueError('Invalid staged verification directory')
        freeze_bytes = (directory / 'source-freeze.json').read_bytes()
        if hashlib.sha256(freeze_bytes).hexdigest() != config['source_freeze_sha256']:
            raise ValueError('Staged source freeze changed')
        freeze = json.loads(freeze_bytes)
        state = json.loads((directory / 'state.json').read_text())
        progress = json.loads((directory / 'progress.json').read_text())
        candidate = Path(state['candidate']).resolve()
        sources = freeze['source_sha256']
        if sources != state['frozen_source_sha256']:
            raise ValueError('Staged source maps differ')
        lines = 0
        for relative, digest in sources.items():
            path = candidate / relative
            if not project_lean(relative) or candidate not in path.resolve().parents or path.is_symlink():
                raise ValueError('Invalid staged source path')
            content = path.read_bytes()
            if hashlib.sha256(content).hexdigest() != digest:
                raise ValueError('Staged source changed')
            lines += len(content.splitlines())
        completed, total = progress['completed_modules'], progress['total_modules']
        if not 0 <= completed <= total == len(sources):
            raise ValueError('Invalid staged progress')
        passed = progress['phase'] == 'complete' and state.get('check_exit') == 0
        return {'available': True, 'label': config['label'], 'lean_lines': lines,
                'lean_files': len(sources), 'completed_modules': completed, 'total_modules': total,
                'verification_status': 'passed' if passed else 'running' if (directory / 'RUNNING').exists() else 'recorded',
                'axiom_declarations': state.get('axiom_audit_declarations'),
                'updated_at': progress.get('updated_at')}
    except (OSError, ValueError, KeyError, TypeError):
        return {'available': False}


def status():
    paths = list(ROOT.glob('*.lean')) + list((ROOT / 'Formalization').rglob('*.lean'))
    paths = [p for p in paths if p.is_file() and not p.is_symlink()]
    current_lines = sum(len(p.read_bytes().splitlines()) for p in paths)
    inventory = json.loads((ROOT / 'docs/source-inventory.json').read_text())
    ledger = json.loads((ROOT / 'docs/named-result-status.json').read_text())
    kinds = inventory['counts']['by_kind']
    total = sum(kinds.get(k, 0) for k in ('theorem', 'lemma', 'claim'))
    certified = ledger['certified_named_results']
    source_entries = [e for e in inventory['entries'] if e.get('kind') in ('theorem', 'lemma', 'claim')]
    def matched_ids(records):
        result = []
        for record in records:
            source_id = record.get('source_inventory_id')
            label = record.get('source_label')
            matches = [e for e in source_entries
                       if (e['id'] == source_id if source_id else label in e.get('labels', []))
                       and (label is None or label in e.get('labels', []))
                       and any(r['file'].endswith('/' + record['source_file'])
                               for r in e.get('source_ranges', []))]
            if len(matches) != 1 or not (ROOT / record['evidence']).is_file() or not (ROOT / record['coverage']).is_file():
                raise ValueError('A reviewed result lacks a unique source entry or evidence file')
            result.append(matches[0]['id'])
        return result
    original_ids = matched_ids(certified)
    variants = ledger['proved_variants']
    variant_ids = matched_ids(variants)
    # Count unique source environments, never theorem declarations or proof components.
    reviewed = len(set(original_ids + variant_ids))
    if len(set(original_ids)) != len(certified) or reviewed > total:
        raise ValueError('Duplicate or excess certified named results')
    published = {'available': False, 'reference': 'origin/main'}
    try:
        sha = git('rev-parse', '--verify', 'refs/remotes/origin/main')
        published = published_snapshot(sha)
    except (subprocess.SubprocessError, OSError):
        pass
    return {'observed_at': datetime.now(timezone.utc).isoformat(),
            'current': {'lean_lines': current_lines, 'lean_files': len(paths)},
            'published': published, 'staged': staged_snapshot(),
            'inventory': {'named_results': total, 'algorithms': kinds['algorithm']},
            'original_result_count': len(certified), 'corrected_variant_count': len(variants),
            'reviewed_count': reviewed, 'conservative_named_result_percent': 100 * reviewed / total if total else 0,
            'ledger': ledger, 'github_url': REPO_URL, 'coverage_url': '/coverage'}


HTML = r'''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Lean formalization progress</title><style>
:root{color-scheme:light;--ink:#172c39;--muted:#566775;--teal:#087b74}*{box-sizing:border-box}body{margin:0;background:#f2f5f6;color:var(--ink);font:16px/1.6 system-ui,sans-serif}main{max-width:1120px;margin:auto;padding:40px 24px}header{display:flex;justify-content:space-between;gap:20px;align-items:start}h1{font-size:36px;line-height:1.2;margin:7px 0 12px;letter-spacing:-1px}.eyebrow{color:var(--teal);font-size:12px;font-weight:750;letter-spacing:2px;text-transform:uppercase}.sub{color:var(--muted);max-width:800px}a{color:#056962;text-underline-offset:4px}nav{display:flex;gap:18px;white-space:nowrap}.grid{display:grid;grid-template-columns:repeat(3,1fr);gap:18px;margin:28px 0}.card,.panel{background:white;border:1px solid #dce4e7;border-radius:16px;padding:24px}.panel{margin-top:18px}.label{font-size:14px;color:var(--muted)}.number{font-size:40px;font-weight:700;letter-spacing:-1px;margin:6px 0}.small{font-size:13px;color:var(--muted)}h2{font-size:27px;line-height:1.3;margin:10px 0}h3{font-size:17px;margin:8px 0}.meter{height:10px;background:#e9eff0;border-radius:6px;overflow:hidden;margin:20px 0 10px}.fill{width:0;height:100%;background:var(--teal)}.tag{display:inline-block;color:#07675f;background:#e3f4ef;padding:3px 10px;border-radius:6px;font-size:12px;font-weight:650}.row{display:flex;gap:32px;flex-wrap:wrap;margin:18px 0}.notice{background:#fff7e7;border-left:3px solid #bd8d32;padding:12px 16px;margin-top:18px;color:#634e29}footer{margin-top:24px;color:var(--muted);font-size:12px}#error{color:#9b352d}details{margin-top:18px}pre{white-space:pre-wrap;font:13px/1.6 system-ui,sans-serif}@media(max-width:760px){.grid{grid-template-columns:1fr}header{display:block}nav{margin-top:16px}h1{font-size:29px}}</style>
<main><header><div><div class="eyebrow">Statistical foundations of reinforcement learning</div><h1>Formalization progress</h1><div class="sub">The whole monograph remains incomplete. Code volume, verification, and reviewed source statements are tracked separately.</div></div><nav><a href="https://github.com/aaradhyapandeycs/statistical-foundations-rl-lean" rel="noreferrer">GitHub ↗</a><a href="/coverage">Coverage ledger</a></nav></header>
<div class="grid">
<section class="card"><div class="label">Main checkout · Lean lines</div><div class="number" id="current">…</div><div class="small" id="files"></div><div class="small">Current working files; includes comments and blank lines.</div></section>
<section class="card"><div class="label">Published snapshot · Lean lines</div><div class="number" id="published">…</div><div class="small" id="commit"></div><div class="small">Locally recorded origin/main; no network polling.</div></section>
<section class="card"><div class="label">Staged candidate · Lean lines</div><div class="number" id="staged">…</div><div class="small" id="staged-files"></div><div class="small">Separate candidate under verification; excludes other private drafts.</div></section>
</div>
<section class="panel"><div class="tag">Candidate verification</div><h2 id="build">…</h2><div class="sub" id="build-detail"></div><div class="small" id="build-time"></div></section>
<section class="panel"><div class="tag">Reviewed source statements</div><h2 id="fraction">…</h2><div class="row"><div><strong id="original-count">…</strong><div class="small">Original-result entries, including disclosed restrictions</div></div><div><strong id="corrected-count">…</strong><div class="small">Separately proved corrected variants</div></div></div><div class="sub">The combined count covers unique named source environments represented by either category. It is <strong>not a percentage of the entire monograph</strong>; definitions, algorithms, displayed claims and other mathematical work are outside this denominator.</div><div class="meter"><div class="fill" id="bar"></div></div><div class="small" id="percent"></div><div class="small" id="ledger-time"></div><div class="notice">A compiling helper or more lines of code does not certify a source result. Statement scope and corrections are recorded in the ledger and source-issues report. No complete chapter or monograph is certified.</div><details><summary>Original/restricted entries and corrected variants</summary><h3>Original-result entries</h3><div id="original-results"></div><h3>Corrected variants</h3><div id="corrected-results"></div></details><details><summary>Measurement scope and evidence</summary><pre id="policy"></pre><p class="small">Main and published line counts exclude Mathlib, dependencies, private drafts and symbolic links. Staged lines are counted from an explicitly selected, hash-checked source freeze. Source inventory: docs/source-inventory.json. Reviewed entries: docs/named-result-status.json.</p><div class="small" id="algorithms"></div></details></section>
<footer><span id="observed">Loading…</span> · Refreshes every 10 seconds · Loopback only · Read only <span id="error" role="status"></span></footer></main>
<script>
const text=(id,value)=>document.getElementById(id).textContent=value;
const describe=entries=>entries.map(x=>x.name+' · '+(x.source_label||x.source_inventory_id||'unlabeled')).join('; ');
async function refresh(){try{
 const r=await fetch('/api/status',{cache:'no-store'});if(!r.ok)throw Error('Status unavailable');const d=await r.json();
 text('current',d.current.lean_lines.toLocaleString());text('files',d.current.lean_files+' project Lean files');
 text('published',d.published.available?d.published.lean_lines.toLocaleString():'Unavailable');
 const c=document.getElementById('commit');c.replaceChildren();if(d.published.available){const a=document.createElement('a');a.href=d.published.url;a.rel='noreferrer';a.textContent=d.published.sha.slice(0,12);c.append(a,document.createTextNode(' · '+d.published.commit_time));}
 const s=d.staged;
 text('staged',s.available?s.lean_lines.toLocaleString():'No active candidate');
 text('staged-files',s.available?s.lean_files+' project Lean files':'No staged source freeze selected');
 text('build',s.available?s.completed_modules+' / '+s.total_modules+' modules checked':'No staged verification selected');
 text('build-detail',s.available?(s.verification_status==='passed'?'Fresh verification passed. '+(s.axiom_declarations||0).toLocaleString()+' declarations audited; release review and publication are tracked separately.':s.verification_status==='running'?'Verification is running. Staged code is not added to the reviewed-result count.':'Last recorded verification progress; no active run is confirmed.'):'Proof work can also exist in private drafts, which are excluded from these counts.');
 text('build-time',s.available&&s.updated_at?'Last verification update: '+new Date(s.updated_at).toLocaleString():'');
 text('fraction',d.reviewed_count+' / '+d.inventory.named_results+' named source environments with reviewed entries');
 text('original-count',d.original_result_count+' original/restricted entries');text('corrected-count',d.corrected_variant_count+' corrected variants');
 text('percent',d.conservative_named_result_percent.toFixed(2)+'% of named environments represented, including corrections and restrictions');document.getElementById('bar').style.width=Math.min(100,d.conservative_named_result_percent)+'%';
 text('original-results',describe(d.ledger.certified_named_results));text('corrected-results',describe(d.ledger.proved_variants));
 text('ledger-time','Ledger updated: '+d.ledger.updated_at);text('policy',d.ledger.policy+'\n\nSource: '+d.ledger.source);text('algorithms',d.inventory.algorithms+' algorithm environments are tracked separately.');
 text('observed','Observed '+new Date(d.observed_at).toLocaleString());text('error','');
}catch(e){text('error',' · Refresh failed; displayed data may be stale.');}}
refresh();setInterval(refresh,10000);
</script></html>'''


class Handler(BaseHTTPRequestHandler):
    def send(self, code, body, content_type):
        self.send_response(code)
        self.send_header('Content-Type', content_type)
        self.send_header('Content-Length', str(len(body)))
        self.send_header('Cache-Control', 'no-store')
        self.send_header('X-Content-Type-Options', 'nosniff')
        self.send_header('Referrer-Policy', 'no-referrer')
        self.send_header('Content-Security-Policy', "default-src 'none'; style-src 'unsafe-inline'; script-src 'unsafe-inline'; connect-src 'self'; frame-ancestors 'none'; base-uri 'none'")
        self.end_headers()
        self.wfile.write(body)

    def do_GET(self):
        route = urlsplit(self.path).path
        if route == '/':
            self.send(200, HTML.encode(), 'text/html; charset=utf-8')
        elif route == '/api/status':
            try:
                data = json.dumps(status()).encode()
                self.send(200, data, 'application/json; charset=utf-8')
            except (OSError, ValueError, KeyError, subprocess.SubprocessError):
                self.send(503, b'{"error":"Project status temporarily unavailable"}', 'application/json')
        elif route == '/coverage':
            self.send(200, (ROOT / 'docs/COVERAGE.md').read_bytes(), 'text/plain; charset=utf-8')
        else:
            self.send(404, b'Not found', 'text/plain')

    def log_message(self, *_args):
        pass


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--port', type=int, default=8765)
    args = parser.parse_args()
    if not 1 <= args.port <= 65535:
        parser.error('port must be between 1 and 65535')
    server = ThreadingHTTPServer(('127.0.0.1', args.port), Handler)
    print(f'Progress dashboard: http://127.0.0.1:{args.port}', flush=True)
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        pass
    finally:
        server.server_close()


if __name__ == '__main__':
    main()
