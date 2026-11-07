"""Standalone bridges from foundational geometry to the later proofs."""
from dkvis.deck_spec import DeckSpec, uses
from dkvis.lectures import lecture_path
from dkvis.quiz import quiz_uses


def bridge(name,key,prefix,core):
    module=f'dkvis.learning.{key}.scenes'
    return DeckSpec(name=name,description='Standalone prerequisite with geometric explanations, proof steps, and formal companions.',
        footer={'invariant_blocks':'Invariant subspaces and justified blocks','principal_angles':'Principal angles and perpendicular error',
                'trace_gradients':'Trace pairings and matrix derivatives','uniform_minima':'Uniform error and minimum values'}[key],
        narration=lecture_path(key),slides=uses(module,[prefix+'Title'])
        +uses('dkvis.learning.outcomes',['LectureOutcomes'])
        +uses('dkvis.learning.orientation',[prefix+'Setup'])+uses(module,core)
        +uses(module,[prefix+'Computation'],depth='*')+quiz_uses(count=4))

BRIDGES=(
 bridge('prereq-invariant-blocks','invariant_blocks','Ib',[
     'IbQuestion','IbBlocks','IbSymmetry','IbCommute','IbExample','IbSummary','IbFacts','IbLean','IbLeanSplit']),
 bridge('prereq-principal-angles','principal_angles','Pa',[
     'PaLines','PaSeveral','PaOverlap','PaError','PaBasis','PaSummary','PaFacts','PaLean','PaLeanSymmetry']),
 bridge('prereq-trace-gradients','trace_gradients','Tg',[
     'TgPairing','TgCyclic','TgDerivative','TgTests','TgSkew','TgSummary','TgFacts','TgLean','TgLeanPositive']),
 bridge('prereq-uniform-minima','uniform_minima','Um',[
     'UmBand','UmUpper','UmLower','UmDip','UmLocations','UmSummary','UmFacts','UmLean','UmLeanLower']),
)
