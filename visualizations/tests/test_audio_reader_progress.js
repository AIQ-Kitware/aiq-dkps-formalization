// No browser or dependencies required: exercise the timeline functions from the actual reader.
'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const html = fs.readFileSync(path.join(__dirname, '..', 'dkvis', 'presentation', 'audio_library.html'), 'utf8');
const js = html.split('<script>')[1].split('</script>')[0];
function extract(name) {
  const pattern = new RegExp('^function ' + name + '\\(', 'm');
  const found = pattern.exec(js);
  assert.ok(found, `missing ${name}`);
  const start = found.index;
  const rest = js.slice(start);
  const next = /\n(?:async )?function [\w]+\(/.exec(rest);
  return next ? rest.slice(0, next.index) : rest;
}
const state = {
  doc: {id:'123000',pages:[
    'An introduction to spectral theory. A first example.',
    'A Sylvester equation describes the middle.',
    'The theorem concludes with an angle bound.'
  ]}, page:0, durations:[]
};
const audio = {currentSrc:'',duration:NaN,currentTime:0};
const fields = {ttsSpeed:{value:'1'},rate:{value:'1'}};
let jump = null;
const context = vm.createContext({state,audio,$:id=>fields[id],seekPageFraction:(page,fraction)=>{jump={page,fraction}},console});
for (const name of ['estimatedPageSeconds','progressModel','clock','seekLectureFraction']) {
  vm.runInContext(extract(name),context);
}
const get = command => vm.runInContext(command,context);
assert.equal(get('clock(65)'), '1:05');
assert.equal(get('clock(3675)'), '1:01:15');
let model = get('progressModel()');
assert.equal(model.exact,false);
assert.equal(model.fraction,0);
assert.ok(model.total>0);
state.page=2;
model=get('progressModel()');
assert.ok(model.fraction>.5 && model.fraction<1,'later page must advance whole-lecture progress');
audio.currentSrc='http://localhost/audio.mp3';audio.duration=10;audio.currentTime=5;
model=get('progressModel()');
assert.ok(model.fraction>.5 && model.fraction<1,'in-page position must affect whole-lecture percentage');
get('seekLectureFraction(.1)');
assert.equal(jump.page,0);
assert.ok(jump.fraction>=0 && jump.fraction<1);
get('seekLectureFraction(.99)');
assert.equal(jump.page,2);
assert.ok(jump.fraction>=0 && jump.fraction<1);
state.durations=[10,20,30];state.page=1;audio.currentTime=5;audio.duration=20;
model=get('progressModel()');
assert.equal(model.exact,true);
assert.equal(model.total,60);
assert.equal(model.elapsed,15);
assert.equal(model.fraction,.25);
fields.rate.value='2';
model=get('progressModel()');
assert.equal(model.minutes,30,'playback speed adjusts wall-clock time');
assert.equal(model.played,7.5);

// The full reader must retain every page while exposing sentence navigation.
class MockElement {
  constructor(tag='div') {this.tag=tag;this.children=[];this.dataset={};this.className='';this.textContent='';}
  append(child){this.children.push(child)}
  replaceChildren(){this.children=[]}
  setAttribute(name,value){this[name]=value}
}
const transcript=new MockElement('div');
const count=new MockElement('span');
context.document={createElement:tag=>new MockElement(tag)};
context.$=id=>({transcript,textCount:count,ttsSpeed:fields.ttsSpeed,rate:fields.rate})[id];
state.doc.transcript=state.doc.pages.join('\n\n');
state.doc.words=state.doc.transcript.split(/\s+/).length;
for (const name of ['speechSegments','segmentWeight','showFullTranscript','seekSentence']) {
  vm.runInContext(extract(name),context);
}
get('showFullTranscript(state.doc)');
assert.equal(transcript.children.length,3,'complete transcript must retain all pages');
const rendered=transcript.children.map(section=>section.children[1].children.map(node=>node.textContent).join(''));
assert.deepEqual(rendered,state.doc.pages,'every spoken character must remain visible');
const sentence=transcript.children[2].children[1].children[0];
sentence.onclick();
assert.equal(jump.page,2,'clicking a sentence must seek in its own page');
console.log('Full transcript and lecture-wide timeline calculations passed');
