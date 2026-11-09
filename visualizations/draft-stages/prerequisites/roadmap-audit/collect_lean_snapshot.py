#!/usr/bin/env python3
"""Record reproducibility data and *source-level* direct imports for targeted DKPS modules.
This is not a Lean proof-term dependency exporter and never claims to be one.
"""
import argparse,json,subprocess,hashlib,re
from pathlib import Path

def run(cmd,base):
 try:
  p=subprocess.run(cmd,cwd=base,text=True,capture_output=True,timeout=20,check=False)
  return (p.stdout.strip() if p.returncode==0 else f"error: {p.stderr.strip()}")
 except (FileNotFoundError,subprocess.TimeoutExpired) as e:return f"unavailable: {e}"

def without_lean_comments(source):
 # Lightweight lexer for nested Lean block comments and line comments.
 # Suitable for locating import declarations, not for parsing Lean syntax.
 out=[];depth=0;i=0;length=len(source)
 while i<length:
  if source.startswith('/-',i):
   depth+=1;i+=2;continue
  if depth and source.startswith('-/',i):
   depth-=1;i+=2;continue
  if depth:
   if source[i]=='\n':out.append('\n')
   i+=1;continue
  if source.startswith('--',i):
   end=source.find('\n',i)
   if end==-1:break
   out.append('\n');i=end+1;continue
  out.append(source[i]);i+=1
 return ''.join(out)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',required=True);a=ap.parse_args()
 base=Path.cwd();out=Path(a.out);out.mkdir(parents=True,exist_ok=True)
 meta={'repo_path':str(base),'repo_head':run(['git','rev-parse','HEAD'],base),
       'repo_status':run(['git','status','--short'],base),
       'lean_toolchain':(base/'lean-toolchain').read_text().strip() if (base/'lean-toolchain').exists() else None,
       'lake_manifest_sha256':hashlib.sha256((base/'lake-manifest.json').read_bytes()).hexdigest() if (base/'lake-manifest.json').exists() else None,
       'pins':[]}
 if (base/'lake-manifest.json').exists():
  j=json.loads((base/'lake-manifest.json').read_text())
  for p in j.get('packages',[]):
   meta['pins'].append({'name':p.get('name'),'rev':p.get('rev'),'url':p.get('url')})
 paths=[]
 for prefix in ['DavisKahan','ForTauCeti','RoadmapBridge']:
  paths.extend(sorted((base/prefix).rglob('*.lean')) if (base/prefix).exists() else [])
 for prefix in ['DavisKahan.lean','ForTauCeti.lean']:
  if (base/prefix).exists():paths.append(base/prefix)
 rows=[]
 for p in paths:
  source=p.read_text(errors='replace')
  imports=[]
  for line in without_lean_comments(source).splitlines():
   m=re.match(r'^\s*(?:(?:public|private)\s+)?import\s+(.+?)\s*$',line)
   if m:imports.extend(m.group(1).split())
  rows.append({'path':str(p.relative_to(base)),'imports':imports})
 (out/'source-imports.json').write_text(json.dumps(rows,indent=2)+'\n')
 (out/'pins.json').write_text(json.dumps(meta,indent=2)+'\n')
 print('Recorded',len(rows),'local source modules in',out)
 print('This is SOURCE import data, not a declaration-level theorem dependency graph.')
if __name__=='__main__':main()
