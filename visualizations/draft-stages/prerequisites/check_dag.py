#!/usr/bin/env python3
"""Validate and render the human-curated DKPS mathematical prerequisite DAG.

No third-party Python packages, Lean toolchain, or Graphviz required for checks.
Use --write to regenerate DOT and the complete topological sequence.
"""
from __future__ import annotations
import argparse
from collections import Counter, defaultdict, deque
import heapq
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
OUTLINE = HERE.parent / 'outline.md'


def index_key(k: str, node: dict) -> tuple:
    if k == '000000':
        return (0, k)
    if node['status'] == 'gap':
        return (int(node['suggested_slot']), k)
    return (int(k), k)


def load_and_validate(path: Path):
    data = json.loads(path.read_text(encoding='utf-8'))
    nodes = {n['id']: n for n in data['nodes']}
    if len(nodes) != len(data['nodes']):
        raise ValueError('Duplicate node identifiers')
    edges = []
    for n in nodes.values():
        for p in n['requires']:
            if p not in nodes:
                raise ValueError(f"Missing node {p} required by {n['id']}")
            if p == n['id']:
                raise ValueError(f"Self-loop at {p}")
            edges.append((p,n['id']))
    if len(edges) != len(set(edges)):
        raise ValueError('Duplicate dependency edges')
    outgoing = defaultdict(set)
    incoming = defaultdict(set)
    for p, n in edges:
        outgoing[p].add(n)
        incoming[n].add(p)
    degrees = {k:len(incoming[k]) for k in nodes}
    heap = [(index_key(k,nodes[k]),k) for k in nodes if degrees[k]==0]
    heapq.heapify(heap)
    order=[]
    while heap:
        _, k = heapq.heappop(heap)
        order.append(k)
        for child in outgoing[k]:
            degrees[child]-=1
            if degrees[child]==0:
                heapq.heappush(heap,(index_key(child,nodes[child]),child))
    if len(order)!=len(nodes):
        blocked = sorted(set(nodes)-set(order))
        raise ValueError('Cycle or dependent on cycle: '+', '.join(blocked))
    positions={k:i for i,k in enumerate(order)}
    for p, n in edges:
        assert positions[p] < positions[n]
    gaps=[k for k in order if nodes[k]['status']=='gap']
    if len(gaps)==0:
        raise ValueError('Missing explicit gap review nodes')
    # This is a pedagogical input registry, not the Lean compiler dependency DAG.
    if not len(data.get('source_result_coverage',{})) == 29:
        raise ValueError('Source result crosswalk changed: expected 29 entries')
    for key, targets in data['source_result_coverage'].items():
        for k in targets:
            if k not in nodes:
                raise ValueError(f'Unknown source-result endpoint: {key} -> {k}')
    for name, ids in data['proof_targets'].items():
        for k in ids:
            if k not in nodes:
                raise ValueError(f'Unknown proof checkpoint: {name} -> {k}')
    return data,nodes,edges,order,incoming,outgoing


def ancestors(targets, incoming):
    visited=set(targets)
    frontier=list(targets)
    while frontier:
        k=frontier.pop()
        for parent in incoming[k]:
            if parent not in visited:
                visited.add(parent)
                frontier.append(parent)
    return visited


def minrank(k, nodes):
    return int(nodes[k].get('suggested_slot',k))


def generate_report(data, nodes, edges, order, incoming, outgoing):
    inversions=sorted([(p,n) for p,n in edges if minrank(p,nodes)>minrank(n,nodes)],key=lambda v:(minrank(v[1],nodes),minrank(v[0],nodes)))
    root_count=sum(not incoming[n] for n in nodes)
    sink_count=sum(not outgoing[n] for n in nodes)
    lines=[
        '# Topologically ordered draft course',
        '',
        '**Generated from `lesson-dag.json` by `check_dag.py --write`.**',
        'The edge semantics are **mathematical prerequisites for the intended proof depth**, not Lean imports or a mandated video schedule. The algorithm chooses the earliest original numeric slot whenever multiple nodes are ready.',
        '',
        f'- **{len(nodes)} vertices:** {len(nodes)-sum(n["status"]=="gap" for n in nodes.values())} outlined topics (including introduction), {sum(n["status"]=="gap" for n in nodes.values())} proposed prerequisite insertions.',
        f'- **{len(edges)} directed edges**; {root_count} roots and {sink_count} sinks; verified acyclic.',
        f'- **{len(inversions)} numerical-order violations** among direct prerequisite edges (including proposed insertion slots).',
        f'- **{len(data["source_result_coverage"])} original-paper endpoint entries** linked to outlined lectures, not a complete mathematical theorem dependency census.',
        '',
        '## Backward edges in the current numerical order',
        '',
        'These pairs mean that the current numbering introduces a claimed proof-level prerequisite *after* the topic that needs it. They are concrete reasons to edit the outline, split a lecture, or explicitly weaken an early lecture’s proof scope.',
        '',
        '| Required first | Dependent | Interpretation |',
        '| --- | --- | --- |',
    ]
    for p,n in inversions:
        lines.append(f'| `{p}` {nodes[p]["title"]} | `{n}` {nodes[n]["title"]} | Existing lesson order is reversed for this proof-level edge |')
    lines.extend(['', '## Proposed missing prerequisite lessons', '', '| Proposed ID | Topic | Suggested slot | Needed for |', '| --- | --- | --- | --- |'])
    for k in sorted((k for k,v in nodes.items() if v['status']=='gap'),key=lambda k:minrank(k,nodes)):
        node=nodes[k]; children=sorted(outgoing[k],key=lambda v:minrank(v,nodes))
        short=', '.join(f'`{x}`' for x in children)
        lines.append(f'| `{k}` | {node["title"]} | `{node["suggested_slot"]}` | {short} |')
    lines += ['', '## Proof target prerequisite closures', '', '| Target | Direct endpoints | Closure size | Gap nodes in closure |', '| --- | --- | ---: | --- |']
    for name,targets in data['proof_targets'].items():
        closure=ancestors(targets, incoming)
        g=[k for k in order if k in closure and nodes[k]['status']=='gap']
        lines.append(f'| `{name}` | '+', '.join(f'`{k}`' for k in targets)+f' | {len(closure)} | '+(', '.join(f'`{k}`' for k in g) or 'None')+' |')
    lines += ['', '## One valid topological order', '', 'The six-digit lecture IDs remain stable references. The schedule below may place a larger ID before a smaller one where the mathematical proof prerequisites require that. Proposed gaps are not yet authored lectures.', '', '| Step | ID | Topic |', '| ---: | --- | --- |']
    for i,k in enumerate(order,1):
        n=nodes[k]
        lines.append(f'| {i} | `{k}`'+ (' **(proposed)**' if n['status']=='gap' else '')+f' | {n["title"]} |')
    lines += ['', '## Reproducibility and limitations', '', '- Topological sorting checks consistency of **the edges we entered**. It cannot establish that our mathematical prerequisite review found every missing theorem.', '- The saved August 17, 2026 Lean dependency snapshot reflects project-local declarations at that snapshot; its compiler edges are not equivalent to mathematical proof prerequisites, and its TauCeti pin may differ from the current checkout.', '- `lesson-dag.json` is editable independently of the old Manim registry. Run `python3 visualizations/draft-stages/prerequisites/check_dag.py --write` after changing prerequisites.', '- Source-result endpoints and suggested insertion numbers are coverage and planning metadata, not assertion that those Lean files or lesson transcripts already exist.', '']
    return '\n'.join(lines), inversions


def dot_render(nodes,edges):
    lines=['digraph LecturePrerequisites {','  rankdir=LR;','  graph [fontname="DejaVu Sans", overlap=false, splines=true, nodesep=0.35, ranksep=0.6];','  node [shape=box,style="rounded,filled",color="#7e8b9a",fillcolor="#f8f9fa",fontname="DejaVu Sans",fontsize=10];','  edge [color="#a1a9b2",arrowsize=0.5];']
    for k,n in nodes.items():
        fill='#fff0dd' if n['status']=='gap' else ('#dbeafe' if 105000 <= int(k) <= 129000 else '#f8f9fa') if k.isdigit() else '#fff0dd'
        short=n['title'].replace('"','\\"')
        label=(k+'\\n'+short[:44]+ ('…' if len(short)>44 else ''))
        lines.append(f'  "{k}" [label="{label}",fillcolor="{fill}"];')
    for p,n in sorted(edges):
        lines.append(f'  "{p}" -> "{n}";')
    lines.append('}')
    return '\n'.join(lines)+'\n'


def check_outline(nodes):
    if not OUTLINE.exists():
        return None
    contents=OUTLINE.read_text(encoding='utf-8')
    old=set(re.findall(r'^\| `(\d{6})` \| \*\*',contents,re.M))
    modeled={k for k,v in nodes.items() if v['status']=='outlined' and k!='000000'}
    if old!=modeled:
        raise ValueError(f'Outline/graph drift: missing in DAG: {sorted(old-modeled)}, missing in outline: {sorted(modeled-old)}')
    return True


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='Regenerate derived order and full Graphviz DOT')
    parser.add_argument('--check-outline',action='store_true',help='Verify lesson registry against existing outline.md')
    args=parser.parse_args()
    data,nodes,edges,order,incoming,outgoing=load_and_validate(HERE/'lesson-dag.json')
    text,inversions=generate_report(data,nodes,edges,order,incoming,outgoing)
    if args.check_outline:
        result=check_outline(nodes)
        if result is None:
            raise SystemExit('Missing outline.md; pass --check-outline only where it is present')
    if args.write:
        (HERE/'topological-order.md').write_text(text,encoding='utf-8')
        (HERE/'lesson-dag.dot').write_text(dot_render(nodes,edges),encoding='utf-8')
    print(f'PASS: {len(nodes)} vertices, {len(edges)} prerequisite edges, '
          f'{len(inversions)} current-order inversions, '
          f'{sum(n["status"]=="gap" for n in nodes.values())} proposed gaps, '
          f'{len(data["source_result_coverage"])} source-result endpoints; graph acyclic')

if __name__=='__main__':
    main()
