#!/usr/bin/env node
/** Export a companion deck to PowerPoint using the same Manim-rendered frames
 * used by its standalone HTML viewer. No separate HTML/Pptx text composition.
 *
 * node tools/build_companion_pptx.js companion-slides/g2-091250-...json output.pptx
 *
 * For QA of the PowerPoint container without invoking Manim:
 * node tools/build_companion_pptx.js source.json output.pptx --frames-dir /tmp/frames
 */
'use strict';
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const {spawnSync} = require('node:child_process');
const pptxgen = require('pptxgenjs');
let helpers = {};
for (const name of [process.env.DKVIS_PPTX_HELPERS, 'pptxgenjs_helpers',
                    '/home/oai/skills/slides/pptxgenjs_helpers']) {
  if (!name) continue;
  try { helpers = require(name); break; }
  catch (error) { if (error.code !== 'MODULE_NOT_FOUND') throw error; }
}

async function main() {
  const [, , sourcePath, outputPath, option, value] = process.argv;
  if (!sourcePath || !outputPath || (option && (option !== '--frames-dir' || !value)))
    throw Error('Usage: build_companion_pptx.js <deck.json> <output.pptx> [--frames-dir <path>]');
  const source = path.resolve(sourcePath);
  const data = JSON.parse(fs.readFileSync(source, 'utf8'));
  if (data.schema_version !== 1 || !Array.isArray(data.slides)) throw Error('Invalid deck source');
  const work = fs.mkdtempSync(path.join(os.tmpdir(), 'dkps-companion-ppt-'));
  try {
    let frames;
    if (option === '--frames-dir') {
      const base = path.resolve(value);
      frames = data.slides.map((_, index) => path.join(base, `frame-${String(index+1).padStart(3,'0')}.png`));
    } else {
      const root = path.resolve(__dirname, '..');
      const py = process.env.PYTHON || 'python';
      const env = {...process.env, PYTHONPATH: root + (process.env.PYTHONPATH ? path.delimiter+process.env.PYTHONPATH : '')};
      const cmd = ['-m', 'dkvis.presentation.companion_export', source, work];
      const result = spawnSync(py, cmd, {cwd:root, env, encoding:'utf8', maxBuffer:16*1024*1024});
      if (result.status !== 0) throw Error('Manim slide export failed:\n' + (result.stderr || result.stdout));
      const record = JSON.parse(result.stdout.trim().split('\n').at(-1));
      if (record.rendered_count !== data.slides.length) throw Error('Manim emitted incomplete deck');
      frames = record.frames;
    }
    const pptx = new pptxgen();
    pptx.layout = 'LAYOUT_WIDE';
    pptx.author = 'DKPS Lecture Project';
    pptx.subject = 'Mathematical lecture companion rendered using Manim';
    pptx.title = data.title;
    pptx.lang = 'en-US';
    for (const [index, row] of data.slides.entries()) {
      const asset = frames[index];
      if (!fs.existsSync(asset)) throw Error(`Missing Manim frame ${index+1}: ${asset}`);
      const slide = pptx.addSlide();
      slide.background = {color:'0E1319'};
      // A 16:9 image fills the entire 16:9 canvas without rescaling text or geometry.
      slide.addImage({path:asset, x:0, y:0, w:40/3, h:7.5, altText:row.title});
      const sourceNotes = [];
      if (data.source_lecture) sourceNotes.push(`Lecture source: ${data.source_lecture}`);
      sourceNotes.push(`Slide ${index+1}: ${row.title}`);
      sourceNotes.push('Slide image composed and rendered by Manim.');
      slide.addNotes(`[Sources]\n${sourceNotes.join('\n')}\n[/Sources]`);
      if (helpers.warnIfSlideElementsOutOfBounds) helpers.warnIfSlideElementsOutOfBounds(slide,pptx);
    }
    await pptx.writeFile({fileName:outputPath});
    console.log(`Saved ${outputPath} (${data.slides.length} Manim slides)`);
  } finally { fs.rmSync(work,{recursive:true,force:true}); }
}
main().catch(error => {console.error(error); process.exitCode=1;});
