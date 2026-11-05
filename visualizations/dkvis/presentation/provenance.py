"""Explicit source-model attribution and generation-time artifact snapshots."""
from datetime import datetime, timezone
from pathlib import Path
import json
import subprocess

import yaml

from dkvis.presentation.paths import ROOT


def source_provenance(deck):
    from dkvis.decks import get_deck
    spec=get_deck(deck)
    if not spec.narration:
        return dict(status='not recorded')
    path=(ROOT/spec.narration).with_name('provenance.yaml')
    try:
        data=yaml.safe_load(path.read_text())
        return data if isinstance(data,dict) else dict(status='not recorded')
    except (OSError,yaml.YAMLError):
        return dict(status='not recorded')


def snapshot(deck,component,**settings):
    try:
        commit=subprocess.run(['git','rev-parse','HEAD'],cwd=ROOT,check=True,
                              capture_output=True,text=True).stdout.strip()
        dirty=bool(subprocess.run(['git','status','--porcelain','--untracked-files=no'],cwd=ROOT,
                                  check=True,capture_output=True,text=True).stdout.strip())
    except (OSError,subprocess.SubprocessError):
        commit=None;dirty=None
    return dict(deck=deck,component=component,
                generated_at=datetime.now(timezone.utc).isoformat(),
                source_commit=commit,source_dirty=dirty,
                provenance=source_provenance(deck),settings=settings)


def record(path,deck,component,**settings):
    path=Path(path)
    metadata=snapshot(deck,component,**settings)
    path.with_name(path.name+'.metadata.json').write_text(json.dumps(metadata,indent=2)+'\n')
    return metadata
