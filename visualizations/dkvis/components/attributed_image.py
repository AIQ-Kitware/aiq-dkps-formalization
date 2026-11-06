"""Display a reviewed external image together with visible attribution links."""
from manim import ImageMobject, VGroup
from dkvis.presentation.external_assets import catalog,require
from dkvis.slide_style import MUTED,para


def latex_plain(text):
    return ''.join({'\\':r'\textbackslash{}','&':r'\&','%':r'\%','_':r'\_','#':r'\#',
                    '$':r'\$','{':r'\{','}':r'\}'}.get(c,c) for c in text)


def add_attributed_image(scene,key,*,center=(-3.45,.72,0),width=4.2,height=3.05,credit_y=-1.45):
    """Aspect-preserving display; keep creator, source and licence on the slide."""
    row=catalog()[key]
    picture=ImageMobject(str(require(key)))
    picture.scale(min(width/picture.width,height/picture.height)).move_to(center)
    credit=' \\newline '.join(latex_plain(value) for value in [
        row['creator'],row['license']+'; scaled, no new crop.',
        row['short_source'],row['license_url'].removeprefix('https://').rstrip('/'),
    ])
    label=para(credit,width=5.1,size=16,color=MUTED).move_to([center[0],credit_y,0])
    if label.height>1.3:raise ValueError(f'Split the image credit for {key}')
    scene.add(picture,label)
    return picture,label
