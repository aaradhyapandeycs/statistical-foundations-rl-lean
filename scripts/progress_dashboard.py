#!/usr/bin/env python3
"""Read-only loopback project dashboard. Run: python3 scripts/progress_dashboard.py."""
import argparse
from datetime import datetime, timezone
from functools import lru_cache
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
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
    for record in certified:
        matches = [e for e in source_entries if record['source_label'] in e.get('labels', [])
                   and any(r['file'].endswith('/' + record['source_file'])
                           for r in e.get('source_ranges', []))]
        if len(matches) != 1 or not (ROOT / record['evidence']).is_file() or not (ROOT / record['coverage']).is_file():
            raise ValueError('A certified result lacks a unique source entry or evidence file')
    # Count unique source environments, never theorem declarations or proof components.
    reviewed = len({(r['source_file'], r['source_label']) for r in certified})
    if reviewed != len(certified) or reviewed > total:
        raise ValueError('Duplicate or excess certified named results')
    published = {'available': False, 'reference': 'origin/main'}
    try:
        sha = git('rev-parse', '--verify', 'refs/remotes/origin/main')
        published = published_snapshot(sha)
    except (subprocess.SubprocessError, OSError):
        pass
    return {'observed_at': datetime.now(timezone.utc).isoformat(),
            'current': {'lean_lines': current_lines, 'lean_files': len(paths)},
            'published': published, 'inventory': {'named_results': total, 'algorithms': kinds['algorithm']},
            'reviewed_count': reviewed, 'conservative_named_result_percent': 100 * reviewed / total if total else 0,
            'ledger': ledger, 'github_url': REPO_URL, 'coverage_url': '/coverage'}


HTML = r'''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Formalization progress</title><style>
:root{color-scheme:light;--ink:#172c39;--muted:#566775;--teal:#087b74}*{box-sizing:border-box}body{margin:0;background:#f2f5f6;color:var(--ink);font:16px/1.6 system-ui,sans-serif}main{max-width:1100px;margin:auto;padding:48px 24px}header{display:flex;justify-content:space-between;gap:20px;align-items:start}h1{font-size:clamp(27px,4vw,40px);line-height:1.2;margin:7px 0 12px;letter-spacing:-1px}.eyebrow{color:var(--teal);font-size:12px;font-weight:750;letter-spacing:2px;text-transform:uppercase}.sub{color:var(--muted);max-width:730px}a{color:#056962;text-underline-offset:4px}nav{display:flex;gap:18px;white-space:nowrap}.grid{display:grid;grid-template-columns:repeat(3,1fr);gap:18px;margin:30px 0}.card,.panel{background:white;border:1px solid #dce4e7;border-radius:16px;padding:24px}.label{font-size:14px;color:var(--muted)}.number{font-size:40px;font-weight:700;letter-spacing:-1px;margin:6px 0}.small{font-size:13px;color:var(--muted)}.panel h2{font-size:20px;margin:0 0 9px}.meter{height:10px;background:#e9eff0;border-radius:6px;overflow:hidden;margin:22px 0 12px}.fill{width:0;height:100%;background:var(--teal)}.tag{display:inline-block;color:#07675f;background:#e3f4ef;padding:3px 10px;border-radius:6px;font-size:12px;font-weight:650}.row{display:flex;justify-content:space-between;gap:20px;margin:16px 0}.notice{background:#fff7e7;border-left:3px solid #bd8d32;padding:13px 17px;margin-top:22px;color:#634e29}footer{margin-top:24px;color:var(--muted);font-size:12px}code{overflow-wrap:anywhere}#error{color:#9b352d}details{margin-top:20px}pre{white-space:pre-wrap;font:13px/1.6 system-ui,sans-serif}@media(max-width:760px){.grid{grid-template-columns:1fr}header{display:block}nav{margin-top:16px}.row{display:block}}</style>
<main><header><div><div class="eyebrow">Statistical foundations of reinforcement learning</div><h1>Formalization progress</h1><div class="sub">A live local view of project Lean files and conservatively reviewed source results.</div></div><nav><a href="https://github.com/aaradhyapandeycs/statistical-foundations-rl-lean" rel="noreferrer">GitHub ↗</a><a href="/coverage">Coverage ledger</a></nav></header>
<div class="grid"><section class="card"><div class="label">Local project Lean files</div><div class="number" id="current">…</div><div class="small" id="files"></div><div class="small">Includes comments, blank lines, and files awaiting verification</div></section><section class="card"><div class="label">Published Git snapshot · origin/main</div><div class="number" id="published">…</div><div class="small" id="commit"></div><div class="small">Locally recorded remote branch; no network polling</div></section><section class="card"><div class="label">Source inventory</div><div class="number" id="inventory">…</div><div class="small">Named theorem / lemma / claim environments</div><div class="small" id="algorithms"></div></section></div>
<section class="panel"><div class="tag">Conservative reviewed-result measure</div><h2 style="margin-top:14px" id="percent">…</h2><div class="sub">Fully reviewed named-result environments only. This is <strong>not a percentage of the entire monograph</strong>; definitions, substantive prose, algorithms, dependencies and partial results are outside this denominator.</div><div class="meter"><div class="fill" id="bar"></div></div><div class="small" id="fraction"></div><div class="row"><div><strong>Certified in the ledger</strong><div id="results"></div></div><div class="small" id="ledger-time"></div></div><div class="notice">Certification changes require a human-reviewed ledger update. Compiling more code does not automatically certify a source result. Unlisted environments remain uncounted.</div><details><summary>Measurement scope and evidence</summary><pre id="policy"></pre><p class="small">Lean lines cover root project .lean files and Formalization/**/*.lean, excluding Mathlib, dependencies, staged .local files and symbolic links. Published lines use the same scope at the locally recorded origin/main commit. Source counts come from docs/source-inventory.json; certifications come from docs/named-result-status.json.</p></details></section><footer><span id="observed">Loading…</span> · Refreshes every 10 seconds · Loopback only · Read only · No tracking <span id="error" role="status"></span></footer></main>
<script>const text=(id,value)=>document.getElementById(id).textContent=value;async function refresh(){try{const r=await fetch('/api/status',{cache:'no-store'});if(!r.ok)throw Error('Status unavailable');const d=await r.json();text('current',d.current.lean_lines.toLocaleString());text('files',d.current.lean_files+' project files');text('inventory',d.inventory.named_results);text('algorithms',d.inventory.algorithms+' algorithm environments (not included above)');text('percent',d.conservative_named_result_percent.toFixed(2)+'% of named-result environments');text('fraction',d.reviewed_count+' fully reviewed / '+d.inventory.named_results+' inventoried');document.getElementById('bar').style.width=Math.min(100,d.conservative_named_result_percent)+'%';text('results',d.ledger.certified_named_results.map(x=>x.name+' · '+x.source_label).join(', '));text('ledger-time','Ledger updated: '+d.ledger.updated_at);text('policy',d.ledger.policy+'\n\nSource: '+d.ledger.source+'\nEvidence: '+d.ledger.certified_named_results.map(x=>x.evidence).join(', '));text('published',d.published.available?d.published.lean_lines.toLocaleString():'Unavailable');const c=document.getElementById('commit');c.replaceChildren();if(d.published.available){const a=document.createElement('a');a.href=d.published.url;a.rel='noreferrer';a.textContent=d.published.sha.slice(0,12);c.append(a,document.createTextNode(' · '+d.published.commit_time));}text('observed','Observed '+new Date(d.observed_at).toLocaleString());text('error','');}catch(e){text('error',' · Refresh failed; displayed data may be stale.');}}refresh();setInterval(refresh,10000);</script></html>'''


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
