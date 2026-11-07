#!/usr/bin/env python3
"""Validate the supplied roadmap obligation ledger and the proposed proof-node references."""
from pathlib import Path
import json,collections
p=Path(__file__).parent
ledger=json.loads((p/'obligations.json').read_text())
proposal=json.loads((p/'proposed-proof-nodes.json').read_text())
rows=ledger['obligations'];ids=[x['id'] for x in rows]
assert len(ids)==len(set(ids)), 'duplicate obligation labels'
assert len(ids)==899, f'unexpected roadmap ID count {len(ids)}'
assert len(ledger['toeplitz_stages'])==6
add={n['id'] for n in proposal['nodes']};assert len(add)==len(proposal['nodes'])
for o in rows:
 assert o['mapping'] in {'title_or_scope_overlap','unit_only','no_current_home','new_proof_node_needed'}
 assert o['new_proof_node'] is None or o['new_proof_node'] in add
 assert o['source_line']>0
for p0 in proposal['proof_spines']:
 for id in p0['roadmap_obligations']:assert id in ids,(p0['id'],id)
# Optional structural check against the prior installed baseline DAG.
prior=p.parent/'lesson-dag.json'
if prior.exists():
 old=json.loads(prior.read_text());available={n['id'] for n in old['nodes']}
 for o in rows:
  if o['existing_lecture_candidate'] is not None:
   assert o['existing_lecture_candidate'] in available,o['id']
 new={n['id'] for n in proposal['nodes']}
 assert not new & available
 for node in proposal['nodes']:
  for ref in node['requires']+node['feeds']:
   assert ref in available|new,(node['id'],ref)
 print(f'Baseline DAG linkage checked: {len(available)} nodes')
print(f"PASS: {len(ids)} uniquely numbered obligations, {len(ledger['toeplitz_stages'])} Toeplitz stages, {len(add)} proposed proof topics")
print('Mapping:',dict(collections.Counter(o['mapping'] for o in rows)))
print('Proposed combined DAG orderable:',proposal['combined_graph_topologically_orderable'])
