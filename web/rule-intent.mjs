import {allAliases,grammarWords} from './languages.mjs';
// Regex is generated only from escaped literal tokens. Community packs cannot
// supply executable patterns. Exact names are resolved by Lean.
const escape=s=>s.replace(/[.*+?^$(){}|[\]\\]/g,'\\$&');
function pattern(s){return /^[A-Za-z]/.test(s)?'\\b'+escape(s)+'\\b':escape(s);}
const group=key=>grammarWords(key).map(pattern).join('|');
const clean=s=>s.trim().replace(/[。.]$/,'').trim();
export const conceptLabels=()=>[...new Set(allAliases().flatMap(x=>[x.label,x.rule]))];
export function resolveIntent(value){
  if(typeof value!=='string')throw Error('Expected a mathematical rule or declaration name.');
  const input=value.trim();
  if(!input||grammarWords('automatic').includes(input))return '';
  const stripped=clean(input).replace(new RegExp('^(?:'+group('prefix')+')\\s*','i'),'');
  const key=stripped.toLowerCase();
  const matches=[...new Set(allAliases().filter(x=>x.label.toLowerCase()===key||x.rule.toLowerCase()===key).map(x=>x.rule))];
  if(matches.length>1)throw Error('Ambiguous concept; enter an exact Lean declaration.');
  if(matches.length)return matches[0];
  if(/^[A-Za-z_][A-Za-z0-9_'.]{0,159}$/.test(stripped))return stripped;
  throw Error('Unsupported phrase. Choose a known mathematical concept, enter an exact Lean declaration, or leave blank for type search.');
}
export function parseRuleIntent(value,{ordered=false}={}){
  if(typeof value!=='string')throw Error('Expected a mathematical rule or declaration name.');
  const t=clean(value);
  const sep=new RegExp('(?:[,，;；]\\s*)?(?:'+group('using')+')\\s*','i');
  const split=sep.exec(t);
  const ruleText=split?t.slice(0,split.index).trim():t;
  const premises=split?t.slice(split.index+split[0].length).replace(/^[、，,]\s*/,'').trim():'';
  if(split&&!premises)throw Error('Specify local premise names.');
  const required=premises?premises.split(new RegExp('\\s*(?:,|，|、|'+group('join')+')\\s*','i')).map(x=>x.trim()):[];
  if(required.length>8||required.some(x=>!/^[A-Za-z_][A-Za-z0-9_']{0,63}$/.test(x))||(!ordered&&new Set(required).size!==required.length))throw Error('Use up to eight local premise names; search premises must be distinct.');
  return {rule:resolveIntent(ruleText),required};
}
export function statementMarker(text){
  const s=text.trim();
  if(grammarWords('conclude').some(k=>s.toLowerCase()===k.toLowerCase()))return {kind:'conclude'};
  for(const k of grammarWords('establish')){
    if(s.toLowerCase().startsWith(k.toLowerCase()+' ')){
      const m=/^([A-Za-z_][A-Za-z0-9_']{0,63})(?:\s*:\s*(.+))?$/.exec(s.slice(k.length).trim());
      if(m)return {kind:'establish',name:m[1],type:m[2]??null};
    }
  }
  return null;
}
