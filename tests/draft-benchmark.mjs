// Opt-in synthetic latency and cache-equivalence checks: node tests/draft-benchmark.mjs
import {performance} from 'node:perf_hooks';
import assert from 'node:assert/strict';
import {compileNaturalDraft,createDraftSession} from '../web/natural-draft.mjs';

const warmup=24,samples=160;
const facts=new Map([['p','P'],['h15','P']]);
for(let i=0;i<60;i++)facts.set('irrelevant'+i,'T'+i);
const scope=['P',...facts.keys()];
const prefix=Array.from({length:15},(_,i)=>'establish h'+i+' : $P$ | '+(i?'h'+(i-1):'p')).join('\n');
const lastH14=prefix+'\n$P$ | h14';
const lastH15=prefix+'\n$P$ | h15';
const localEdit=lastH14.replace('establish h7 : $P$ | h6','establish h7 : $P$ | h15');

function stripReuse(result){const {reusedRows,...structural}=result;return structural;}
function distribution(times){
 const sorted=[...times].sort((a,b)=>a-b);
 return {medianMs:sorted[Math.floor((sorted.length-1)*0.5)],p95Ms:sorted[Math.ceil(sorted.length*0.95)-1]};
}
function measure({name,evaluate,reference,inputAt,expectedReuse=null,beforeSample=()=>{}}){
 for(let i=0;i<warmup;i++)evaluate(inputAt(i));
 const times=[],reuse=[];
 for(let i=0;i<samples;i++){
  const input=inputAt(i);beforeSample(i);
  const start=performance.now(),actual=evaluate(input),elapsed=performance.now()-start;
  const expected=reference(input);
  assert.deepEqual(stripReuse(actual),stripReuse(expected),name+' incremental/full result mismatch at sample '+i);
  if(expectedReuse!==null)assert.equal(actual.reusedRows,expectedReuse,name+' reused-prefix count');
  times.push(elapsed);reuse.push(actual.reusedRows||0);
 }
 return {case:name,...distribution(times),meanReusedRows:Number((reuse.reduce((a,b)=>a+b,0)/reuse.length).toFixed(2)),samples};
}

const warm=createDraftSession();
const toggle=createDraftSession();
const edit=createDraftSession();
// Compare the session's public evaluation path with the same full compiler
// path used by cold cases. Calling draftProof directly omits sequence/scope
// dispatch and makes the linear baseline artificially cheap.
const cold={evaluate:text=>compileNaturalDraft(text,scope,facts),reference:text=>compileNaturalDraft(text,scope,facts)};

function nestedCases(depth,max){
 const header='cases h'+depth+', establish r'+depth+' : $P$';
 const leftBody=depth+1===max?'$P$ | p':nestedCases(depth+1,max);
 return [header,
  '  left case l'+depth,
  ...leftBody.split('\n').map(line=>'    '+line),
  '  right case rr'+depth,
  '    $P$ | p',
  '$P$ | r'+depth
 ].join('\n');
}
const caseFacts=new Map([['P','Prop'],['p','P'],['p2','P']]);
for(let i=0;i<8;i++)caseFacts.set('h'+i,'P ∨ P');
const caseScope=[...caseFacts.keys()],deepCase=nestedCases(0,8),caseDraft=createDraftSession();
const deepCaseEdited=deepCase.replace('    $P$ | p','    $P$ | p2');
const caseLineCount=deepCase.split('\n').filter(line=>line.trim()).length;
assert.ok(caseLineCount<=64,'nested case benchmark must remain inside the supported source bound');

const sequenceFacts=new Map([['P','Prop'],['Q','Prop'],['U','Prop'],['V','Prop'],['R','Prop'],['T','Prop'],
 ['h','P ∨ Q'],['j','U ∨ V'],['p','P'],['f','P → R'],['g','P → T'],['k','Q → T'],['l','U → T'],['m','V → T']]);
const sequenceScope=[...sequenceFacts.keys()];
const interleaved=['establish hr : $R$ | f p',
 'cases h, establish hT : $T$',
 '  left case hp','    $T$ | g hp','  right case hq','    $T$ | k hq',
 'establish ht : $T$ | hT',
 'cases j, establish jT : $T$',
 '  left case hu','    $T$ | l hu','  right case hv','    $T$ | m hv',
 '$T$ | jT'].join('\n');
const interleavedEdit=interleaved.replace('$T$ | jT','$T$ | ht');
const sequenceSession=createDraftSession();

const conjunctionFacts=new Map([['hp','P'],['hq','Q'],['hq2','Q']]),conjunctionScope=[...conjunctionFacts.keys()];
const conjunction=`split conjunction\n  first goal\n    $P$ | hp\n  second goal\n    $Q$ | hq`;
const conjunctionEdit=conjunction.replace('$Q$ | hq','$Q$ | hq2');
const conjunctionSession=createDraftSession();

const elementFacts=new Map([['hall','∀ x : Nat, P x'],['he','∃ y : Nat, P y']]);
for(let i=0;i<48;i++)elementFacts.set('unrelated'+i,'Type'+i);
const elementScope=[...elementFacts.keys()];
const elementRequest='take an element x satisfying $P(x)$';
const elementRequestEdit=elementRequest.replace('P(x)','Q(x)');
const elementSession=createDraftSession();
const fullElementDraft=text=>createDraftSession().evaluate(text,elementScope,elementFacts,{goal:'∀ x : Nat, P x',continuation:true});
const elementContextEdit=[...elementScope,'he2'];
const elementContextEditFacts=new Map([...elementFacts,['he2','∃ z : Nat, P z']]);
const elementContextSession=createDraftSession();
const fullElementContextDraft=text=>createDraftSession().evaluate(text,elementContextEdit,elementContextEditFacts,{goal:'∀ x : Nat, P x',continuation:true});

const localLemmaFacts=new Map([['hq','Q'],['hp','Q'],['gr','Q → R']]);
for(let i=0;i<48;i++)localLemmaFacts.set('lemmaNoise'+i,'Noise'+i);
const localLemmaScope=[...localLemmaFacts.keys()];
const localLemma=['local lemma localQ : $Q$','  proof','    $Q$ | hq','$R$ | gr localQ'].join('\n');
const localLemmaOneCharEdit=localLemma.replace('$Q$ | hq','$Q$ | hp');
const localLemmaLineShift='\n'+localLemma;
const localLemmaSession=createDraftSession();
const fullLocalLemma=text=>compileNaturalDraft(text,localLemmaScope,localLemmaFacts,{goal:'R'});

const results=[
 measure({name:'cold full evaluation · 16 proof lines / 62 typed locals',evaluate:cold.evaluate,reference:cold.reference,inputAt:()=>lastH14}),
 measure({name:'warm exact replay · 16 proof lines / 62 typed locals',evaluate:text=>warm.evaluate(text,scope,facts),reference:cold.reference,inputAt:()=>lastH14,expectedReuse:16}),
 measure({name:'single-character final premise edit · 15-row prefix',evaluate:text=>toggle.evaluate(text,scope,facts),reference:cold.reference,inputAt:()=>lastH15,expectedReuse:15,beforeSample:()=>{toggle.reset();toggle.evaluate(lastH14,scope,facts);}}),
 measure({name:'local proof-dependency edit · 7-row prefix',evaluate:text=>edit.evaluate(text,scope,facts),reference:cold.reference,inputAt:()=>localEdit,expectedReuse:7,beforeSample:()=>{edit.reset();edit.evaluate(lastH14,scope,facts);}}),
 measure({name:'nested case scopes · cold / '+caseLineCount+' lines / 8 levels',evaluate:text=>compileNaturalDraft(text,caseScope,caseFacts,{goal:'P'}),reference:text=>compileNaturalDraft(text,caseScope,caseFacts,{goal:'P'}),inputAt:()=>deepCase}),
 measure({name:'nested case scopes · exact replay',evaluate:text=>caseDraft.evaluate(text,caseScope,caseFacts,{goal:'P'}),reference:text=>compileNaturalDraft(text,caseScope,caseFacts,{goal:'P'}),inputAt:()=>deepCase}),
 measure({name:'nested case scopes · one branch conclusion edit',evaluate:text=>caseDraft.evaluate(text,caseScope,caseFacts,{goal:'P'}),reference:text=>compileNaturalDraft(text,caseScope,caseFacts,{goal:'P'}),inputAt:()=>deepCaseEdited,beforeSample:()=>{caseDraft.reset();caseDraft.evaluate(deepCase,caseScope,caseFacts,{goal:'P'});}}),
 measure({name:'interleaved sequence · cold / 2 case blocks',evaluate:text=>compileNaturalDraft(text,sequenceScope,sequenceFacts,{goal:'T'}),reference:text=>compileNaturalDraft(text,sequenceScope,sequenceFacts,{goal:'T'}),inputAt:()=>interleaved}),
 measure({name:'interleaved sequence · replay and terminal edit',evaluate:text=>sequenceSession.evaluate(text,sequenceScope,sequenceFacts,{goal:'T'}),reference:text=>compileNaturalDraft(text,sequenceScope,sequenceFacts,{goal:'T'}),inputAt:()=>interleavedEdit,beforeSample:()=>{sequenceSession.reset();sequenceSession.evaluate(interleaved,sequenceScope,sequenceFacts,{goal:'T'});}}),
 measure({name:'conjunction child goals · cold',evaluate:text=>compileNaturalDraft(text,conjunctionScope,conjunctionFacts,{goal:'P ∧ Q'}),reference:text=>compileNaturalDraft(text,conjunctionScope,conjunctionFacts,{goal:'P ∧ Q'}),inputAt:()=>conjunction}),
 measure({name:'conjunction child goals · second-goal edit',evaluate:text=>conjunctionSession.evaluate(text,conjunctionScope,conjunctionFacts,{goal:'P ∧ Q'}),reference:text=>compileNaturalDraft(text,conjunctionScope,conjunctionFacts,{goal:'P ∧ Q'}),inputAt:()=>conjunctionEdit,beforeSample:()=>{conjunctionSession.reset();conjunctionSession.evaluate(conjunction,conjunctionScope,conjunctionFacts,{goal:'P ∧ Q'});}}),
 measure({name:'structural element candidates · cold / 50 typed locals',evaluate:text=>createDraftSession().evaluate(text,elementScope,elementFacts,{goal:'∀ x : Nat, P x',continuation:true}),reference:fullElementDraft,inputAt:()=>elementRequest}),
 measure({name:'structural element candidates · exact replay',evaluate:text=>elementSession.evaluate(text,elementScope,elementFacts,{goal:'∀ x : Nat, P x',continuation:true}),reference:fullElementDraft,inputAt:()=>elementRequest}),
 measure({name:'structural element candidates · property edit',evaluate:text=>elementSession.evaluate(text,elementScope,elementFacts,{goal:'∀ x : Nat, P x',continuation:true}),reference:fullElementDraft,inputAt:()=>elementRequestEdit,beforeSample:()=>{elementSession.reset();elementSession.evaluate(elementRequest,elementScope,elementFacts,{goal:'∀ x : Nat, P x',continuation:true});}}),
 measure({name:'structural element candidates · new existential premise',evaluate:text=>elementContextSession.evaluate(text,elementContextEdit,elementContextEditFacts,{goal:'∀ x : Nat, P x',continuation:true}),reference:fullElementContextDraft,inputAt:()=>elementRequest,beforeSample:()=>{elementContextSession.reset();elementContextSession.evaluate(elementRequest,elementScope,elementFacts,{goal:'∀ x : Nat, P x',continuation:true});}}),
 measure({name:'local lemma · cold / 51 typed locals',evaluate:fullLocalLemma,reference:fullLocalLemma,inputAt:()=>localLemma}),
 measure({name:'local lemma · exact replay',evaluate:text=>localLemmaSession.evaluate(text,localLemmaScope,localLemmaFacts,{goal:'R'}),reference:fullLocalLemma,inputAt:()=>localLemma}),
 measure({name:'local lemma · one-premise edit',evaluate:text=>localLemmaSession.evaluate(text,localLemmaScope,localLemmaFacts,{goal:'R'}),reference:fullLocalLemma,inputAt:()=>localLemmaOneCharEdit,beforeSample:()=>{localLemmaSession.reset();localLemmaSession.evaluate(localLemma,localLemmaScope,localLemmaFacts,{goal:'R'});}}),
 measure({name:'local lemma · source-line shift',evaluate:text=>localLemmaSession.evaluate(text,localLemmaScope,localLemmaFacts,{goal:'R'}),reference:fullLocalLemma,inputAt:()=>localLemmaLineShift,beforeSample:()=>{localLemmaSession.reset();localLemmaSession.evaluate(localLemma,localLemmaScope,localLemmaFacts,{goal:'R'});}})
];

textOutput({node:process.version,platform:process.platform,architecture:process.arch,warmup,samples,results});
function textOutput(value){console.log(JSON.stringify(value,null,2));}
