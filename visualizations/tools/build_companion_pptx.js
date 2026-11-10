#!/usr/bin/env node
/** Export a G3 companion-slide source to a 16:9 PowerPoint with vector TeX.
 *
 * Run from visualizations/:
 *   node tools/build_companion_pptx.js companion-slides/dkps-fast-path.json /tmp/g3-fast.pptx
 * Editable prose and figures; equation glyphs are embedded SVG paths.
 */
'use strict';
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const {spawnSync} = require('node:child_process');
const pptxgen = require('pptxgenjs');
// Optional environment-specific layout helpers. PowerPoint export still works
// with only PptxGenJS installed (web slides do not require Node at all).
let helpers = {};
for (const name of [process.env.DKVIS_PPTX_HELPERS, 'pptxgenjs_helpers',
                    '/home/oai/skills/slides/pptxgenjs_helpers']) {
  if (!name) continue;
  try { helpers = require(name); break; } catch (error) {
    if (error.code !== 'MODULE_NOT_FOUND') throw error;
  }
}
const fitText = (content, font, opts) => helpers.autoFontSize
  ? helpers.autoFontSize(content, font, opts) : {fontSize: opts.fontSize};
const fitImage = (asset, x, y, w, h) => helpers.imageSizingContain
  ? helpers.imageSizingContain(asset, x, y, w, h) : {x, y, w, h};

async function main() {
  const [, , source, output] = process.argv;
  if (!source || !output) throw Error('Usage: node build_companion_pptx.js <source.json> <output.pptx>');
  const data = JSON.parse(fs.readFileSync(source, 'utf8'));
  if (data.schema_version !== 1 || !Array.isArray(data.slides)) throw Error('Invalid companion slide data');
  const visualizationsRoot = path.resolve(__dirname, '..');
  const work = fs.mkdtempSync(path.join(os.tmpdir(), 'dkps-companion-ppt-'));
  let mathAssets = {};
  let figureAssets = {};
  try {
    const py = process.env.PYTHON || 'python';
    const environment = {...process.env, PYTHONPATH: visualizationsRoot + (process.env.PYTHONPATH ? path.delimiter + process.env.PYTHONPATH : '')};
    if (data.slides.some(s => s.mathtex)) {
      const res = spawnSync(py, ['-m', 'dkvis.presentation.slide_math', path.resolve(source), work],
        {cwd: visualizationsRoot, env:environment, encoding:'utf8', maxBuffer:10*1024*1024});
      if (res.status !== 0) throw Error('Vector equation build failed: ' + (res.stderr || res.stdout));
      mathAssets = JSON.parse(res.stdout.trim().split('\n').at(-1));
    }
    const figureIds = [...new Set(data.slides.map(s => s.diagram).filter(Boolean))];
    if (figureIds.length) {
      const figureDir = path.join(work, 'figures');
      const res = spawnSync(py, ['-m', 'dkvis.presentation.companion_figures', '--output-dir', figureDir, ...figureIds],
        {cwd: visualizationsRoot, env:environment, encoding:'utf8', maxBuffer:10*1024*1024});
      if (res.status !== 0) throw Error('Vector figure build failed: ' + (res.stderr || res.stdout));
      figureAssets = JSON.parse(res.stdout.trim().split('\n').at(-1));
    }
    const pres = new pptxgen();
    pres.layout = 'LAYOUT_WIDE';
    pres.author = 'DKPS Lecture Project';
    pres.subject = 'Independent mathematical companion for a DKPS lecture';
    pres.title = data.title;
    pres.lang = 'en-US';
    pres.theme = {headFontFace:'Georgia', bodyFontFace:'Aptos', lang:'en-US'};
    const C = {bg:'102131', title:'F4F0E8', body:'DFE8EB', dim:'A4C1D0', aqua:'8EE1F2', gold:'F1C88C', edge:'385A71', pane:'182F40'};
    const SH = pres.ShapeType;
    for (const [index,row] of data.slides.entries()) {
      const slide = pres.addSlide(); slide.background = {color:C.bg};
      slide.addShape(SH.line,{x:.62,y:.22,w:12.1,h:0,line:{color:C.aqua,width:2.8}});
      slide.addText((row.eyebrow || data.title).toUpperCase(),{x:.67,y:.40,w:10.7,h:.30,fontFace:'Aptos',fontSize:10.3,bold:true,color:C.aqua,charSpacing:1.1,margin:0});
      const titleSize=fitText(row.title,'Georgia',{x:.67,y:.85,w:12.0,h:.67,fontSize:34,minFontSize:26,maxFontSize:34,mode:'shrink'});
      slide.addText(row.title,{x:.67,y:.85,w:12.0,h:.70,fontFace:'Georgia',fontSize:34,color:C.title,margin:0,...titleSize});
      const leadSize=fitText(row.lead,'Aptos',{x:.67,y:1.68,w:12.0,h:.55,fontSize:18,minFontSize:15,maxFontSize:18,mode:'shrink'});
      slide.addText(row.lead,{x:.67,y:1.70,w:12.0,h:.55,fontFace:'Aptos',color:'C3E2EF',margin:0,...leadSize});
      const hasFigure=Boolean(row.diagram);
      const hasMath=Boolean(mathAssets[String(index)]);
      if (hasMath) {
        const svg=fs.readFileSync(mathAssets[String(index)]);
        const dataUri='data:image/svg+xml;base64,'+svg.toString('base64');
        const box={x:.80,y:2.32,w:11.7,h:hasFigure?1.18:1.42};
        slide.addImage({data:dataUri, ...fitImage(dataUri,box.x,box.y,box.w,box.h)});
      } else if (row.formula) {
        slide.addText(row.formula,{x:.8,y:2.39,w:11.5,h:1.05,fontFace:'Georgia',fontSize:21,color:C.gold,margin:0,breakLine:false});
      }
      const startY=hasMath||row.formula?3.80:2.65;
      const bottom=6.52;
      const bodyW=hasFigure?6.2:11.75;
      const bodyParts=[...(row.body||[])];
      if (row.bullets?.length) bodyParts.push(row.bullets.map(x=>'• '+x).join('\n'));
      const prose=bodyParts.join('\n\n');
      const bodyOpts=fitText(prose,'Aptos',{
        x:.79,y:startY,w:bodyW,h:bottom-startY,fontSize:19,minFontSize:13.5,maxFontSize:19,mode:'shrink'});
      slide.addText(prose,{x:.79,y:startY,w:bodyW,h:bottom-startY,fontFace:'Aptos',color:C.body,margin:0,
        breakLine:false,valign:'top',paraSpaceAfterPt:10,...bodyOpts});
      if (hasFigure) {
        const figPath=figureAssets[row.diagram];
        slide.addShape(SH.rect,{x:7.25,y:startY-0.04,w:5.37,h:bottom-startY+.12,fill:{color:C.pane},line:{color:C.edge,width:.7}});
        if (fs.existsSync(figPath)) {
          slide.addImage({path:figPath,...fitImage(figPath,7.38,startY+.08,5.11,bottom-startY-.12)});
        }
      }
      if (row.takeaway) {
        slide.addShape(SH.line,{x:.68,y:6.72,w:11.9,h:0,line:{color:C.edge,width:.7}});
        const text='KEY POINT   '+row.takeaway;
        const opts=fitText(text,'Aptos',{x:.7,y:6.84,w:11.8,h:.30,fontSize:13,minFontSize:11,maxFontSize:13,mode:'shrink'});
        slide.addText(text,{x:.7,y:6.84,w:11.8,h:.32,fontFace:'Aptos',color:C.gold,margin:0,...opts});
      }
      slide.addText(`${index+1} / ${data.slides.length}`,{x:12.00,y:7.18,w:.64,h:.16,fontSize:9,align:'right',color:C.dim,margin:0});
      const sources = [];
      if (data.source_lecture) sources.push(`G3 lecture source: ${data.source_lecture}`);
      if (row.diagram) sources.push(`Drawing: generated from dkvis.presentation.companion_figures (${row.diagram})`);
      if (sources.length) slide.addNotes(`[Sources]\n${sources.join('\n')}\n[/Sources]`);
      if (helpers.warnIfSlideElementsOutOfBounds) helpers.warnIfSlideElementsOutOfBounds(slide,pres);
    }
    await pres.writeFile({fileName:output});
    console.log(`Saved ${output} (${data.slides.length} slides)`);
  } finally { fs.rmSync(work,{recursive:true,force:true}); }
}
main().catch(ex=>{ console.error(ex);process.exitCode=1; });
