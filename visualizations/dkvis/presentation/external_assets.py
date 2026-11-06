"""Curated external images in a portable, attributed store outside Git.

python -m dkvis.presentation.external_assets fetch
python -m dkvis.presentation.external_assets bundle /tmp/dk-history-assets.tar.gz
python -m dkvis.presentation.external_assets import /tmp/dk-history-assets.tar.gz

Discovery/licence review is editorial work: the committed manifest records the
chosen file, attribution, licence and upstream revision. Rendering uses only
these reviewed entries. It never searches for a substitute photograph.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import tarfile
import time
import urllib.error
import urllib.request

import yaml
from dkvis.presentation.paths import ROOT

MANIFEST=ROOT/'dkvis/assets/history-images.yaml'


def store_root():
    return Path(os.environ.get('DKVIS_ASSET_DIR',ROOT/'asset-store')).expanduser().resolve()


def catalog():
    return yaml.safe_load(MANIFEST.read_text())['images']


def asset_path(key, root=None):
    row=catalog()[key]
    base=Path(root or store_root()).resolve()
    result=(base/row['file']).resolve()
    result.relative_to(base)
    return result


def metadata_path(path):
    return path.with_name(path.name+'.json')


def require(key, root=None):
    path=asset_path(key,root)
    sidecar=metadata_path(path)
    if not path.is_file() or not sidecar.is_file():
        raise FileNotFoundError(f'Missing image/attribution for {key}; run python -m dkvis.presentation.external_assets fetch')
    meta=json.loads(sidecar.read_text())
    if meta['source']!=catalog()[key]:
        raise ValueError(f'Stale image source record for {key}; fetch again before rendering')
    row=catalog()[key]
    expected=row.get('download_sha1',row['upstream_sha1'])
    if meta['sha1']!=expected or hashlib.sha1(path.read_bytes()).hexdigest()!=expected:
        raise ValueError(f'Damaged image {path}; restore it from a bundle or fetch again')
    return path


def fetch(keys=None, *, root=None, refresh=False):
    rows=catalog()
    for key in keys or rows:
        row=rows[key];path=asset_path(key,root);sidecar=metadata_path(path)
        if path.exists() and sidecar.exists() and not refresh:
            try:
                require(key,root)
                print(f'cached {key}',flush=True)
                continue
            except ValueError:
                pass
        start=time.monotonic()
        request=urllib.request.Request(row['url'],headers={'User-Agent':'DKPS-Lectures/0.1 (educational image attribution; Wikimedia Commons)'})
        for attempt in range(4):
            try:
                with urllib.request.urlopen(request,timeout=40) as response:
                    if not response.headers.get('Content-Type','').startswith('image/'):
                        raise ValueError(f'Not an image: {key}')
                    data=response.read()
                break
            except urllib.error.HTTPError as error:
                if error.code not in {429,502,503,504} or attempt==3:raise
                delay=min(45,max(3,float(error.headers.get('Retry-After',5*(attempt+1)))))
                time.sleep(delay)
        digest=hashlib.sha1(data).hexdigest()
        if digest!=row.get('download_sha1',row['upstream_sha1']):
            raise ValueError(f'Upstream image changed for {key}; review the new file before updating the manifest')
        path.parent.mkdir(parents=True,exist_ok=True)
        temporary=path.with_suffix(path.suffix+'.part')
        temporary.write_bytes(data);temporary.replace(path)
        metadata=dict(source=row,sha1=digest,bytes=len(data),
                      fetched_at=datetime.now(timezone.utc).isoformat(),download_seconds=round(time.monotonic()-start,3))
        sidecar.write_text(json.dumps(metadata,indent=2,ensure_ascii=False)+'\n')
        print(f'fetched {key} ({len(data):,} bytes)',flush=True)
        time.sleep(.4)


def bundle(output, keys=None, *, root=None):
    base=Path(root or store_root()).resolve()
    output=Path(output).expanduser().resolve();output.parent.mkdir(parents=True,exist_ok=True)
    with tarfile.open(output,'w:gz') as archive:
        for key in keys or catalog():
            path=require(key,base)
            for entry in [path,metadata_path(path)]:
                archive.add(entry,arcname=str(entry.relative_to(base)),recursive=False)
    return output


def import_bundle(source, *, root=None):
    base=Path(root or store_root()).resolve()
    allowed={str(asset_path(key,base).relative_to(base)) for key in catalog()}
    allowed|={name+'.json' for name in list(allowed)}
    # Read regular, catalogued files only. Never extract archive paths or links.
    with tarfile.open(source,'r:*') as archive:
        members=archive.getmembers()
        for member in members:
            if not member.isfile() or member.name not in allowed:
                raise ValueError(f'Unrecognised asset bundle member: {member.name}')
        pending=[]
        for member in members:
            path=base/member.name
            with archive.extractfile(member) as stream:data=stream.read()
            if path.exists() and path.read_bytes()!=data:
                if member.name.endswith('.json'):
                    old,new=json.loads(path.read_text()),json.loads(data)
                    if old['source']==new['source'] and old['sha1']==new['sha1']:continue
                raise ValueError(f'Asset conflict: {path}; import into a separate DKVIS_ASSET_DIR to inspect it')
            pending.append((path,data))
        for path,data in pending:
            path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
    for key in catalog():
        if asset_path(key,base).exists():require(key,base)


def main():
    parser=argparse.ArgumentParser(description=__doc__,formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--store',type=Path,help='override DKVIS_ASSET_DIR')
    subs=parser.add_subparsers(dest='command',required=True)
    download=subs.add_parser('fetch');download.add_argument('keys',nargs='*');download.add_argument('--refresh',action='store_true')
    pack=subs.add_parser('bundle');pack.add_argument('output',type=Path);pack.add_argument('keys',nargs='*')
    unpack=subs.add_parser('import');unpack.add_argument('archive',type=Path)
    subs.add_parser('status')
    args=parser.parse_args()
    if args.command=='fetch':fetch(args.keys,root=args.store,refresh=args.refresh)
    elif args.command=='bundle':print(bundle(args.output,args.keys,root=args.store))
    elif args.command=='import':import_bundle(args.archive,root=args.store)
    else:
        print(Path(args.store or store_root()))
        for key in catalog():
            try:require(key,args.store);state='ready'
            except (FileNotFoundError,ValueError) as e:state=str(e)
            print(f'{key}: {state}')


if __name__=='__main__':main()
