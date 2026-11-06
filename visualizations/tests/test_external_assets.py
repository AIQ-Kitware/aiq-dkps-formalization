"""Portable media must retain the exact source record and reject damaged bytes."""
import hashlib,json,tarfile
from pathlib import Path
import pytest
from dkvis.presentation import external_assets as assets


@pytest.fixture
def tiny_store(tmp_path,monkeypatch):
    row={'file':'history/example.jpg','creator':'A photographer','license':'CC BY 4.0',
         'source_page':'https://example.org/photo','license_url':'https://creativecommons.org/licenses/by/4.0/'}
    monkeypatch.setattr(assets,'catalog',lambda:{'example':row})
    row['upstream_sha1']=hashlib.sha1(b'fixture image bytes').hexdigest()
    source=tmp_path/'source';path=source/row['file'];path.parent.mkdir(parents=True)
    path.write_bytes(b'fixture image bytes')
    assets.metadata_path(path).write_text(json.dumps(dict(source=row,sha1=hashlib.sha1(path.read_bytes()).hexdigest())))
    return source,row


def test_bundle_roundtrip_keeps_image_and_attribution(tiny_store,tmp_path):
    source,row=tiny_store;package=assets.bundle(tmp_path/'assets.tar.gz',root=source)
    dest=tmp_path/'destination';assets.import_bundle(package,root=dest)
    original=assets.require('example',source);restored=assets.require('example',dest)
    assert original.read_bytes()==restored.read_bytes()
    assert json.loads(assets.metadata_path(restored).read_text())['source']==row
    assets.import_bundle(package,root=dest)


def test_damage_and_changed_attribution_are_not_accepted(tiny_store):
    source,row=tiny_store;path=assets.require('example',source)
    path.write_bytes(b'wrong bytes')
    with pytest.raises(ValueError,match='Damaged'):assets.require('example',source)
    row['creator']='Another photographer'
    with pytest.raises(ValueError,match='Stale'):assets.require('example',source)


def test_uncatalogued_bundle_path_is_rejected(tiny_store,tmp_path):
    source,_=tiny_store;archive=tmp_path/'bad.tar.gz'
    with tarfile.open(archive,'w:gz') as tar:tar.add(assets.require('example',source),arcname='../outside.jpg')
    with pytest.raises(ValueError,match='Unrecognised'):assets.import_bundle(archive,root=tmp_path/'dest')
    assert not (tmp_path/'outside.jpg').exists()
