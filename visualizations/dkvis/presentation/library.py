"""A deck is one library item; media, documents and voices are its variants."""
from pathlib import Path
import re
from urllib.parse import quote

from dkvis.presentation.captions import local_path, read_json

EXTENSIONS={'.mp4':'video','.webm':'video','.mov':'video','.m4v':'video',
            '.wav':'audio','.mp3':'audio','.ogg':'audio','.html':'slides','.htm':'slides','.pdf':'pdf'}


def unnumber(name):
    return re.sub(r'^\d{6}_','',name)


def identity(name):
    bare=unnumber(name)
    stem=bare.split('.')[0]
    return stem.removesuffix('-light'),'light' if stem.endswith('-light') else 'dark'


def asset(root,path,kind=None):
    safe=local_path(root,path)
    if safe is None or not safe.is_file():
        return None
    try:
        stat=safe.stat()
    except OSError:
        return None
    relative=path.relative_to(root).as_posix()
    metadata_path=local_path(root,str(path)+'.metadata.json')
    metadata=read_json(metadata_path,{}) if metadata_path else {}
    if not isinstance(metadata,dict):
        metadata={}
    return dict(path=relative,name=path.name,kind=kind or EXTENSIONS.get(path.suffix.lower()),
                url='/files/'+quote(relative,safe='/'),size=stat.st_size,
                modified=stat.st_mtime,version=str(stat.st_mtime_ns),
                generated_at=metadata.get('generated_at'),
                time_basis='recorded generation' if metadata.get('generated_at') else 'file modification',
                provenance=metadata.get('provenance'),render_settings=metadata.get('settings',{}),
                source_commit=metadata.get('source_commit'),source_dirty=metadata.get('source_dirty'),
                recorded_deck=metadata.get('deck'))


def catalog(root):
    from dkvis.decks import DECKS
    from dkvis.lectures import load_index,lecture_number
    from dkvis.presentation.provenance import source_provenance
    root=Path(root).resolve()
    indexed=load_index()
    titles={row['deck']:(i,row['title']) for i,row in enumerate(indexed.values())}
    groups={}

    def group(deck):
        if deck not in groups:
            order,title=titles.get(deck,(1000,deck.replace('-',' ')))
            number=lecture_number(deck)
            groups[deck]=dict(id=deck,title=f'{number} · {title}' if number else title,
                              order=order,kind='lecture',assets=[],modified=0,
                              provenance=source_provenance(deck) if deck in DECKS else dict(status='not recorded'))
        return groups[deck]

    # Indexed lectures remain visible even if no video has yet been generated.
    for deck in titles:
        row=group(deck)
        row['authored_transcript_url']='/api/source-transcript?deck='+quote(deck)
        spec=DECKS.get(deck)
        if spec and spec.narration:
            from dkvis.presentation.paths import ROOT
            source=ROOT/spec.narration
            sources=[source,source.with_name('quiz.yaml')]
            row['transcript_source_modified']=max((p.stat().st_mtime for p in sources if p.is_file()),default=None)

    try:
        children=list(root.iterdir())
    except OSError:
        children=[]
    for child in children:
        if child.name.startswith('.') or child.suffix.lower() not in EXTENSIONS:
            continue
        info=asset(root,child)
        if not info:
            continue
        deck,theme=identity(child.name)
        deck=info.get('recorded_deck') or deck
        # A loose preview or diagnostic render is not a registered lecture.
        if deck not in DECKS:
            continue
        theme=info['render_settings'].get('theme',theme)
        info['theme']=theme
        info['voice']=None
        if info['kind'] in {'video','audio'}:
            bare=unnumber(child.name)
            if bare.endswith('.narrated.mp4'):
                variant=bare.removesuffix('.narrated.mp4').partition('.')[2]
                info['preview']=variant.endswith('.preview')
                info['voice']=variant.removesuffix('.preview') or 'legacy'
            else:
                info['voice']=info['render_settings'].get('profile','original')
            info['label']=info['voice']+(' · preview' if info.get('preview') else '')
        elif info['kind']=='slides':
            info['label']='HTML slides'+(' · standalone' if '.standalone.' in child.name else '')
        else:
            info['label']='PDF handout' if '.handout.' in child.name else 'PDF slides'
        if theme=='light':
            info['label']+=' · light'
        row=group(deck);row['assets'].append(info)

    # Exported text is a deck resource, never another library entry. Narrator
    # subfolders retain the text exported for that particular video build.
    for folder in root.glob('*-narration'):
        if local_path(root,folder) is None or not folder.is_dir():
            continue
        deck,theme=identity(folder.name.removesuffix('-narration'))
        if deck not in DECKS:
            continue
        row=group(deck)
        for path in [folder/'presentation.txt',*folder.glob('*/presentation.txt')]:
            info=asset(root,path,'transcript')
            if not info:
                continue
            info.update(theme=theme,voice=None if path.parent==folder else path.parent.name,
                        label='Exported transcript'+(' · '+path.parent.name if path.parent!=folder else ''))
            row['assets'].append(info)
    for row in groups.values():
        row['assets'].sort(key=lambda a:(a['kind'],a.get('voice') or '',a['path']))
        row['modified']=max((a['modified'] for a in row['assets']),default=0)
    return sorted(groups.values(),key=lambda g:(g['order'],g['title']))
