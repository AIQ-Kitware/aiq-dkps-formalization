// No browser or dependencies required: exercise the timeline functions from the actual reader.
'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const html = fs.readFileSync(path.join(__dirname, '..', 'dkvis', 'presentation', 'audio_library.html'), 'utf8');
const js = html.split('<script>')[1].split('</script>')[0];
function extract(name) {
  const pattern = new RegExp('^(?:async )?function ' + name + '\\(', 'm');
  const found = pattern.exec(js);
  assert.ok(found, `missing ${name}`);
  const start = found.index;
  const rest = js.slice(start);
  const next = /\n(?:async )?function [\w]+\(/.exec(rest);
  return next ? rest.slice(0, next.index) : rest;
}
const state = {
  doc: {id:'123000',page_chars:600,page_count:3,source_modified:123,pages:[
    'An introduction to spectral theory. A first example.',
    'A Sylvester equation describes the middle.',
    'The theorem concludes with an angle bound.'
  ]}, page:0, durations:[]
};
const audio = {currentSrc:'',duration:NaN,currentTime:0};
const fields = {ttsSpeed:{value:'1'},rate:{value:'1'}};
let jump = null;
const context = vm.createContext({state,audio,$:id=>fields[id],seekPageFraction:(page,fraction)=>{jump={page,fraction}},selectPage:(page,start,fraction,index)=>{jump={page,start,fraction,index}},console});
context.settings=()=>({profile:'kokoro',voice:'af_alloy',speed:1});
for (const name of ['durationKey','estimatedPageSeconds','progressModel','clock','seekLectureFraction']) {
  vm.runInContext(extract(name),context);
}
const get = command => vm.runInContext(command,context);
const durationKey600=get('durationKey()');
state.doc.page_chars=1200;
assert.notEqual(get('durationKey()'),durationKey600,'page-size change invalidates measured times');
state.doc.page_chars=600;
state.doc.page_count=2;
assert.notEqual(get('durationKey()'),durationKey600,'page-count change invalidates measured times');
state.doc.page_count=3;
assert.equal(get('durationKey()'),durationKey600,'stable page structure preserves measured times');
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
assert.equal(jump.index,0,'unloaded page seeks must retain the sentence for later chunk alignment');

for (const name of ['segmentWordWeight','wordPositionAtTime','sentenceAtProgress','sentenceAtAudioTime','sentenceStartFraction']) vm.runInContext(extract(name),context);
state.page=0;state.segments=state.segmentsByPage[0];state.pageTimings={version:1,chunks:[{words:5,start:0,end:15},{words:4,start:16,end:20}]};
// A long first chunk must not highlight the final sentence simply because a
// fixed percentage of the page's estimated duration has passed.
assert.equal(get('sentenceAtAudioTime(10,20)'),0);
assert.equal(get('sentenceAtAudioTime(18,20)'),1);
assert.equal(get('sentenceAtAudioTime(19.999,20)'),1);
state.pageTimings=null;
assert.equal(get('sentenceAtAudioTime(10,20)'),get('sentenceAtProgress(.5)'));
console.log('Full transcript and lecture-wide timeline calculations passed');

// Exercise the reader's actual queue actions: a phone submits one server-owned
// preparation, and revisiting the lecture renders the server's cached progress.
const queueFields = Object.fromEntries([
  'generateAll','stopGeneration','cacheCount','cacheSummary','cacheFill',
  'cacheProgress','pageCache','queueList','queueSummary','etaExplanation'
].map(id=>[id,new MockElement()]));
queueFields.cacheFill.style={};
const queueState={doc:{id:'123000'},cacheCatalog:new Map()};
const requests=[];
let inventoryRefreshes=0,catalogRefreshes=0,selectedPage=null;
const queueContext=vm.createContext({
  state:queueState,$:id=>queueFields[id],
  document:{createElement:tag=>new MockElement(tag)},
  settings:()=>({track:'g3',profile:'breeze',voice:'narrator',speed:1}),
  api:async(url,options)=>{requests.push({url,...options});return {}},
  setStatus:()=>{},renderList:()=>{},
  refreshInventory:()=>{inventoryRefreshes++},
  refreshCacheCatalog:()=>{catalogRefreshes++},
  selectPage:index=>{selectedPage=index},
  clock:seconds=>String(seconds),Number,String,Boolean
});
for(const name of ['cacheAll','renderInventory','formatGenerationStatus']) {
  vm.runInContext(extract(name),queueContext);
}
(async()=>{
  await vm.runInContext('cacheAll()',queueContext);
  assert.equal(requests.length,1,'whole lecture needs one server request');
  assert.equal(requests[0].url,'/api/audio-generation/prepare');
  assert.equal(requests[0].method,'POST');
  assert.deepEqual(JSON.parse(requests[0].body),{
    track:'g3',profile:'breeze',voice:'narrator',speed:1,lecture_id:'123000'
  });
  assert.equal(inventoryRefreshes,1);
  assert.equal(catalogRefreshes,1);
  queueContext.inventory={lecture_id:'123000',ready:1,total:3,percent:33.3,
    states:['ready','rendering','missing'],estimate_source:'initial',queue:[
      {lecture_id:'123000',page:1,kind:'cache',state:'rendering'}
    ],preparation:{state:'running',submitted:2}};
  vm.runInContext('renderInventory(inventory)',queueContext);
  assert.equal(queueFields.cacheFill.style.width,'33.3%');
  assert.equal(queueFields.cacheProgress['aria-valuenow'],'33.3');
  assert.deepEqual(queueFields.pageCache.children.map(chip=>chip.className),
    ['ready','rendering','missing']);
  queueFields.pageCache.children[2].onclick();
  assert.equal(selectedPage,2);
  assert.equal(queueFields.generateAll.disabled,true);
  assert.equal(queueFields.stopGeneration.disabled,false);
  assert.equal(queueFields.queueList.children.length,1);
  queueContext.inventory={...queueContext.inventory,ready:3,percent:100,
    states:['ready','ready','ready'],queue:[],preparation:{state:'finished'}};
  vm.runInContext('renderInventory(inventory)',queueContext);
  assert.equal(queueFields.cacheFill.style.width,'100%');
  assert.equal(queueFields.generateAll.disabled,false);
  assert.equal(queueFields.stopGeneration.disabled,true);
  assert.equal(queueFields.queueList.children.length,0);
  console.log('Server-owned lecture preparation and cache progress passed');
})().catch(error=>{console.error(error);process.exitCode=1});
