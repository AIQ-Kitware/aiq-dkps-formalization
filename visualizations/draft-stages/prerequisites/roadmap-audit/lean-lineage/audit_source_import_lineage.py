#!/usr/bin/env python3
"""Audit LOCAL module imports and connect roadmap IDs to existing DKPS lineage records.

No Lean theorem-proof dependencies or line-by-line provenance claims are inferred.
Python 3.10+, standard library only.
"""
from __future__ import annotations
import argparse
import collections
import hashlib
import json
import re
from pathlib import Path

TARGETS = [
    'DavisKahan.Sources.DavisKahan1970.SineTheta.Presentation',
    'DavisKahan.Sources.DavisKahan1970.Sylvester.All',
    'DavisKahan.Sources.DavisKahan1970.TanTheta',
    'DavisKahan.Sources.DavisKahan1970.SinTwoThetaAmbientUnbounded',
    'DavisKahan.Sources.DavisKahan1970.TanTwoThetaUnboundedExact',
    'DavisKahan.Sources.DavisKahan1970.Section8.Theorem81',
    'DavisKahan.Sources.DavisKahan1970.Section8.Theorem82',
    'DavisKahan.Sources.DavisKahan1970.Section4DirectRotationSource',
    'DavisKahan.Sources.DavisKahan1970.Section9.All',
    'DavisKahan.Sources.DavisKahan1970.All',
]
ID_PATTERN = re.compile(r'\b(OG|PD|PA|MAJ|OI|SA|SSP|MSS)-([A-Z]?)(\d{2,3})(?:\s*[–-]\s*([A-Z]?\d{2,3}))?((?:/[A-Z]?\d{2,3})*)')


def canonical_id(prefix, section, number):
    return f'{prefix}-{section}{int(number):02d}'


def scope_ids(s):
    """Expand only explicit roadmap-code ranges, not donor-topic labels Txx."""
    found=set()
    for m in ID_PATTERN.finditer(s):
        p, sec, start, finish, suffix=m.groups()
        first=int(start)
        stop=first
        if finish:
            z=re.fullmatch(r'([A-Z]?)(\d{2,3})',finish)
            if z and (not z.group(1) or z.group(1)==sec):
                stop=int(z.group(2))
        if 0 <= stop-first <= 100:
            for n in range(first,stop+1):
                found.add(canonical_id(p,sec,n))
        else:
            found.add(canonical_id(p,sec,first))
        for part in suffix.split('/'):
            if not part:
                continue
            z=re.fullmatch(r'([A-Z]?)(\d{2,3})',part)
            if z and (not z.group(1) or z.group(1)==sec):
                found.add(canonical_id(p,sec,int(z.group(2))))
    return sorted(found)


def parse_explicit_census_rows(path):
    """Extract only the census's explicit DKPS-origin table; never read all PRs as D."""
    text=path.read_text(encoding='utf8').splitlines()
    started=False; in_table=False; out=[]
    for lineno,line in enumerate(text,1):
        if line.startswith('## A. PRs with explicit DKPS origin'):
            started=True
            continue
        if not started:
            continue
        if line.startswith('## '):
            break
        if line.startswith('| TauCeti PR |'):
            in_table=True
            continue
        if not in_table:
            continue
        if not line.startswith('|'):
            if out:
                break
            continue
        fields=[v.strip() for v in line.strip('|').split('|')]
        if len(fields)!=4 or fields[0].startswith('---'):
            continue
        pr=re.search(r'\[#(\d+)\]\((https://github.com/TauCetiProject/TauCeti/pull/\d+)\)',fields[0])
        if not pr:
            continue
        ids=scope_ids(fields[1])
        out.append({'pr':int(pr.group(1)),'url':pr.group(2),'scope':fields[1],
                    'donor_summary':fields[2], 'census_evidence':fields[3],
                    'census_line':lineno, 'explicit_roadmap_ids':ids,
                    'census_source':'dev/tauceti/dkps-upstream-contribution-census.md'})
    return out


def source_module(path):
    if not path.endswith('.lean'): raise ValueError(path)
    return path[:-5].replace('/','.')


def create_graph(imports):
    if not isinstance(imports,list): raise ValueError('Imports should be a list')
    by_name={}
    for x in imports:
        name=source_module(x['path'])
        if name in by_name: raise ValueError('Duplicate module: '+name)
        by_name[name]=x
    graph={name:sorted(m for m in x['imports'] if m in by_name) for name,x in by_name.items()}
    pending={}; topo=[]; stack=[]
    def visit(n):
        s=pending.get(n,0)
        if s==1: raise ValueError('Local import cycle: '+' -> '.join(stack+[n]))
        if s==2:return
        pending[n]=1; stack.append(n)
        for d in graph[n]:visit(d)
        stack.pop();pending[n]=2;topo.append(n)
    for n in sorted(graph):visit(n)
    return by_name,graph,topo


def closure_summary(root,by_name):
    todo=[root]; seen=set();external=set();direct=set()
    if root not in by_name:
        return {'module':root,'error':'not present in snapshot'}
    for imp in by_name[root]['imports']:
        if imp not in by_name:direct.add(imp)
    while todo:
        n=todo.pop()
        if n in seen: continue
        seen.add(n)
        for imp in by_name[n]['imports']:
            if imp in by_name:
                todo.append(imp)
            else:
                external.add(imp)
    return {
        'module':root,
        'local_modules_including_target':len(seen),
        'local_dkps_count':sum(x.startswith('DavisKahan.') for x in seen),
        'local_for_tauceti_count':sum(x.startswith('ForTauCeti.') for x in seen),
        'reachable_external_modules_count':len(external),
        'reachable_tauceti_imports':sorted(x for x in external if x.startswith('TauCeti.')),
        'reachable_mathlib_imports':sorted(x for x in external if x.startswith('Mathlib.')),
        'direct_external_imports':sorted(direct),
        'meaning':'All imports reachable THROUGH LOCAL MODULE IMPORTS ONLY. No TauCeti or Mathlib transitive closure and no term-level reference verification.'
    }


def analyze(import_path,pin_path,repo,obligations_path):
    source=json.loads(import_path.read_text(encoding='utf8'))
    pins=json.loads(pin_path.read_text(encoding='utf8'))
    by_name, graph, topo=create_graph(source)
    census=repo/'dev/tauceti/dkps-upstream-contribution-census.md'
    if not census.is_file(): raise FileNotFoundError(census)
    rows=parse_explicit_census_rows(census)
    all_ids=set()
    if obligations_path and obligations_path.is_file():
        j=json.loads(obligations_path.read_text(encoding='utf8'))
        all_ids={r['id'] for r in j['obligations']}
    indexed=collections.defaultdict(list)
    for row in rows:
        for oid in row['explicit_roadmap_ids']:
            indexed[oid].append({'pr':row['pr'], 'census_line':row['census_line'],
                                 'url':row['url'], 'census_evidence':row['census_evidence']})
    modules = [closure_summary(x,by_name) for x in TARGETS]
    all_direct={m for x in source for m in x['imports'] if m not in by_name}
    uniq=[m for m in all_direct if m.startswith('TauCeti.')]
    data={
      'metadata':{
        'schema':'dkps-staged-curriculum/lean-module-lineage-bridge-v1',
        'source_imports_sha256':hashlib.sha256(import_path.read_bytes()).hexdigest(),
        'pins_sha256':hashlib.sha256(pin_path.read_bytes()).hexdigest(),
        'repo_head_from_pins':pins.get('repo_head'),
        'lean_toolchain':pins.get('lean_toolchain'),
        'tauceti_pin':next((x['rev'] for x in pins.get('pins',[]) if x['name']=='TauCeti'),None),
        'source_census':str(census.relative_to(repo)),
        'evidence_limits':['Module imports are not proof-term dependencies',
           'A PR in a source census is not independently verified to be merged at the given pin',
           'Upstream roadmap delivery is not proof descent or exclusive authorship',
           'Historical lineage claims belong to the maintained source census'],
      },
      'counts':{
        'local_modules':len(by_name),
        'local_import_edges':sum(map(len,graph.values())),
        'direct_external_imports_distinct':len(all_direct),
        'direct_tauceti_modules_distinct':len(uniq),
        'direct_mathlib_modules_distinct':sum(x.startswith('Mathlib.') for x in all_direct),
        'census_explicit_origin_pr_rows':len(rows),
        'explicit_roadmap_ids_in_those_rows':len(indexed),
        'roadmap_ids_in_current_ledger':len(all_ids),
        'matched_explicit_origin_roadmap_ids':len(all_ids & indexed.keys()) if all_ids else None,
        'ids_not_in_current_ledger':sorted(indexed.keys()-all_ids) if all_ids else None,
      },
      'sample_course_targets':modules,
      'direct_tauceti_modules':sorted(uniq),
      'local_import_topological_order':topo,
      'census_explicit_origin_rows':rows,
      'roadmap_obligations_with_explicit_census_links':{k:v for k,v in sorted(indexed.items())},
      'unmatched_census_obligation_ids':sorted(indexed.keys()-all_ids) if all_ids else [],
    }
    return data


def make_report(x):
    C=x['counts']; P=x['metadata']
    lines=['# Lean import / DKPS lineage bridge: audited snapshot','',
       'This report is generated from the user-provided `pins.json` and `source-imports.json`,',
       'the existing DKPS contribution census, and (when available) the Operator Theory roadmap',
       'obligation ledger. It is an intermediate evidence layer, **not a completed theorem graph**.','',
       f"- Snapshot head in `pins.json`: `{P['repo_head_from_pins']}`",
       f"- TauCeti dependency revision: `{P['tauceti_pin']}`",
       f"- Lean toolchain: `{P['lean_toolchain']}`",
       f"- Local Lean modules: **{C['local_modules']}**; local module-import edges: **{C['local_import_edges']}**.",
       f"- Distinct directly imported TauCeti modules: **{C['direct_tauceti_modules_distinct']}**; Mathlib: **{C['direct_mathlib_modules_distinct']}**.",
       f"- Explicit-origin PR rows in maintained DKPS census: **{C['census_explicit_origin_pr_rows']}**.",
       f"- Explicit roadmap IDs referenced by those rows: **{C['explicit_roadmap_ids_in_those_rows']}**.",
       f"- IDs intersecting the supplied roadmap-obligation ledger: **{C['matched_explicit_origin_roadmap_ids']}**.",
       '',
       '## Example proof-facing module import boundaries','',
       '| Source module | Local modules in import closure | Reachable TauCeti modules | Reachable Mathlib modules |',
       '|---|---:|---:|---:|']
    for m in x['sample_course_targets']:
        if 'error' in m:continue
        lines.append(f"| `{m['module']}` | {m['local_modules_including_target']} | {len(m['reachable_tauceti_imports'])} | {len(m['reachable_mathlib_imports'])} |")
    lines +=['','The counts above describe imports reachable by following only **local** module imports.',
      'They do not include transitive imports within TauCeti or Mathlib, do not identify constants',
      'mentioned by proof terms, and are not proof complexity scores.','',
      '## Confirmed evidence categories','',
      'The maintained DKPS census has a table of upstream PRs with *explicit DKPS origin*.',
      'Its entries carry evidence codes and donor descriptions. The companion JSON records',
      'exact PR links and source line numbers. For example:','']
    for pr in [13599,17527,18917,19299,13331,13866]:
        row=next((x for x in x['census_explicit_origin_rows'] if x['pr']==pr),None)
        if row:
            lines.append(f"- [PR #{pr}]({row['url']}), {row['scope']} — census `{row['census_evidence']}`; "
                         f"`dev/tauceti/dkps-upstream-contribution-census.md:{row['census_line']}`.")
    lines += ['','**Interpretation:** even an explicit donor statement is not the same as a line-by-line',
      'proof comparison. The Courant–Fischer/Weyl family has a separate detailed audit at',
      '`papers/dk_formalization_journal/COURANT_FISCHER_LINEAGE_AUDIT.md`. The PVM port',
      'has layered Spectra ancestry, which must remain visible. Other items are not upgraded',
      'to proof-descent status merely because the same subject appears in both repositories.','',
      '## Not yet demonstrated','',
      '1. The exact constant-level dependencies of the 29 source-result endpoints.',
      '2. Which current TauCeti declarations (as opposed to modules) those endpoints use.',
      '3. Historical first-development evidence for every imported declaration.',
      '4. Which roadmap obligations have actually been **taught and proved** in TTS lectures.',
      '5. The complete transitive TauCeti / Mathlib term-level frontier.','',
      '## Next proof-dependency extraction','',
      'Run a Lean metaprogram against the **pinned compiled environment** that exports',
      '`{declaration, type_constants, proof_value_constants, module, defining_revision}`',
      'for each target theorem and transitively referenced declaration. Preserve the distinction',
      'between a theorem referenced in a *statement* and one referenced in its *proof*.',
      'Correlate declaration identities with historical donor commits using the **existing**',
      'DKPS census and archived donor history; do not infer mathematical authorship from imports.',
      '', '## Evidence sources', '',
      '- `dev/tauceti/dkps-upstream-contribution-census.md`',
      '- `dev/tauceti/extraction-manifest.json`',
      '- `dev/tauceti/spectra-provenance-map.md`',
      '- `dev/tauceti/proof-lineage/2026-10-20-canonical-spectrum-migration.md`',
      '- `papers/dk_formalization_journal/COURANT_FISCHER_LINEAGE_AUDIT.md`',
      '- User-provided `pins.json` and `source-imports.json` from 2026-11-07',
      '- Previously supplied roadmap obligations in `prerequisites/roadmap-audit/obligations.json`',
      '']
    return '\n'.join(lines)


def main():
    a=argparse.ArgumentParser(description=__doc__)
    a.add_argument('--source-imports',required=True,type=Path)
    a.add_argument('--pins',required=True,type=Path)
    a.add_argument('--repo',default=Path.cwd(),type=Path)
    a.add_argument('--obligations',type=Path,default=None)
    a.add_argument('--out',required=True,type=Path)
    args=a.parse_args()
    ob=args.obligations
    if ob is None:
        ob=args.repo/'visualizations/draft-stages/prerequisites/roadmap-audit/obligations.json'
    data=analyze(args.source_imports,args.pins,args.repo,ob)
    args.out.mkdir(parents=True,exist_ok=True)
    (args.out/'import-lineage-bridge.json').write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
    (args.out/'import-lineage-review.md').write_text(make_report(data)+'\n')
    print(f"local modules={data['counts']['local_modules']}, local import edges={data['counts']['local_import_edges']}, "
          f"census rows={data['counts']['census_explicit_origin_pr_rows']}, "
          f"roadmap matches={data['counts']['matched_explicit_origin_roadmap_ids']}")

if __name__=='__main__':main()
