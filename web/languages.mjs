import {BUILTIN_PACKS} from './builtin-languages.mjs';
// Data-only extension boundary. No executable JS, regex, HTML or remote URLs.
const packs=new Map(BUILTIN_PACKS.map(p=>[p.id,p]));
const fields=Object.keys(BUILTIN_PACKS[0].words);
const grammarFields=Object.keys(BUILTIN_PACKS[0].grammar);
const idPattern=/^[a-z][a-z0-9-]{1,23}$/;
const rulePattern=/^[A-Za-z_][A-Za-z0-9_'.]{0,159}$/;
const validText=(s,n=240)=>typeof s==='string'&&s.trim().length>0&&s.length<=n&&!/[\u0000-\u001f\u007f]/.test(s);
export function validatePack(p){
  if(!p||p.schema!==1||!idPattern.test(p.id)||!validText(p.label,60))throw Error('Expected a version 1 language pack with a valid id and label.');
  const words=Object.fromEntries(fields.map(k=>{
    const s=p.words?.[k];
    if(!validText(s)||/\{(?!name\})|(?<!\{name)\}/.test(s))throw Error('Invalid phrase: '+k);
    return [k,s];
  }));
  const grammar=Object.fromEntries(grammarFields.map(k=>{
    const a=p.grammar?.[k];
    if(!Array.isArray(a)||a.length>20||a.some(s=>!validText(s,60)))throw Error('Invalid grammar field: '+k);
    return [k,[...a]];
  }));
  function table(value,alias){
    if(!value||typeof value!=='object'||Array.isArray(value)||Object.keys(value).length>1000)throw Error('Invalid rule table.');
    return Object.fromEntries(Object.entries(value).map(([k,v])=>{
      if(!rulePattern.test(k)||['__proto__','constructor','prototype'].includes(k)||!(alias?Array.isArray(v)&&v.length<=20&&v.every(s=>validText(s,160)):validText(v)))throw Error('Invalid rule entry: '+k);
      return [k,alias?[...v]:v];
    }));
  }
  return {schema:1,id:p.id,label:p.label,words,grammar,rules:table(p.rules,false),aliases:table(p.aliases,true)};
}
export function registerPack(p){
  const v=validatePack(p);
  if(BUILTIN_PACKS.some(x=>x.id===v.id))throw Error('Built-in language ids are reserved.');
  packs.set(v.id,v);return v;
}
export const languagePacks=()=>[...packs.values()];
export const languagePack=id=>packs.get(id)||packs.get('en');
export const customPacks=()=>languagePacks().filter(p=>!BUILTIN_PACKS.some(x=>x.id===p.id));
export function phrase(id,key,name=''){return languagePack(id).words[key].replaceAll('{name}',()=>String(name));}
export function rulePhrase(id,rule){const p=languagePack(id);return Object.hasOwn(p.rules,rule)?p.rules[rule]:null;}
export function grammarWords(key){return [...new Set(languagePacks().flatMap(p=>p.grammar[key]))].sort((a,b)=>b.length-a.length);}
export function allAliases(){return languagePacks().flatMap(p=>Object.entries(p.aliases).flatMap(([rule,labels])=>labels.map(label=>({rule,label}))));}
