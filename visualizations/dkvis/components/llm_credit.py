"""Portable robot disclosure and recorded model names for lecture covers."""
from pathlib import Path

from manim import DOWN, RIGHT, SVGMobject, VGroup
from dkvis.presentation.provenance import source_provenance
from dkvis.slide_style import MUTED, para, tex


def credit_text(deck):
    provenance=source_provenance(deck)
    labels=[]
    uncertain=False
    for component in ['slides','transcript']:
        record=provenance.get(component,{})
        rows=[*record.get('initial_source_attribution',[]),*record.get('revisions',[])]
        models=list(dict.fromkeys(m for row in rows for m in row.get('models',[row.get('model','unknown')])))
        if not models:
            models=['unknown']
        shortened=[]
        for model in models:
            if 'undetermined' in model or 'unknown' in model.lower():
                uncertain=True
            shortened.append(model.replace('; exact model variant and weights/config undetermined',''))
        labels.append(('Slides' if component=='slides' else 'Transcript')+': '+', '.join(shortened))
    return ' / '.join(labels),uncertain


def llm_credit(deck):
    label,uncertain=credit_text(deck)
    # Use the same vector robot as the Kitware cover rather than depending on
    # the platform's emoji font or on TeX having a robot glyph.
    robot=SVGMobject(str(Path(__file__).resolve().parents[1]/'assets/robot.svg'),height=.38)
    heading=VGroup(robot,tex('LLM-generated',size=22,color=MUTED)).arrange(RIGHT,buff=.15)
    # Model identities are plain text, not LaTeX commands.
    for original,replacement in [('&',r'\&'),('_',r'\_'),('%',r'\%'),('#',r'\#'),('$',r'\$')]:
        label=label.replace(original,replacement)
    parts=[heading,para(label,width=12,size=20,color=MUTED)]
    if uncertain:
        parts.append(tex('Exact model variant/configuration not recorded.',size=17,color=MUTED))
    return VGroup(*parts).arrange(DOWN,buff=.13).move_to([0,-2.72,0])
