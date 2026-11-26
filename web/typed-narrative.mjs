import {phrase,rulePhrase} from './languages.mjs';
export function narrate(root,lang='en',{collapsed=new Set()}={}){
  const result=[];
  const say=(key,name)=>phrase(lang,key,name);
  // Collapse is a projection of the original occurrence tree, not a proof rewrite.
  const childrenOf=n=>Array.isArray(n?.children)?n.children:[];
  const rowCount=(n,level=0)=>!n||level>12?0:1+childrenOf(n).reduce((a,c)=>a+rowCount(c,level+1),0);
  const add=(n,kind,phrase,expr,depth,fold={})=>result.push({
    kind,phrase,expr,depth,path:n.path??null,editable:n.editable===true&&typeof n.path==='string'&&!['introduce','assume','let'].includes(kind),
    truncated:n.truncated===true,omittedProofArguments:n.omittedProofArguments||0,...fold
  });
  function walk(n,d){
    if(!n||d>12)return;
    const children=Array.isArray(n.children)?n.children:[];
    if(n.kind==='introduce'||n.kind==='assume'){
      add(n,n.kind,say(n.kind,n.binder),n.binderType,d);
      for(const c of children)walk(c,d+1);
      return;
    }
    if(n.kind==='witness'){
      add(n,'witness',say('witness',n.term),n.type,d);return;
    }
    if(n.kind==='let'){
      if(children[0])walk(children[0],d+1);
      add(n,'let',say('let',n.binder),n.binderType,d);
      if(children[1])walk(children[1],d+1);
      return;
    }
    const foldable=n.kind==='apply'&&children.length>0&&typeof n.path==='string';
    const folded=foldable&&collapsed.has(n.path);
    const hiddenCount=folded?children.reduce((a,c)=>a+rowCount(c),0):0;
    if(!folded)for(const c of children)walk(c,d);
    if(n.kind==='apply'){
      const lexical=rulePhrase(lang,n.reference);
      const phrase=lexical||say('apply',n.reference||say('function'));
      add(n,n.kind,phrase+say('obtain'),n.type,d,{foldable,folded,hiddenCount});
    }else if(n.kind==='hypothesis'||n.kind==='reference'){
      add(n,n.kind,say('use',n.reference||n.term),n.type,d);
    }else{
      add(n,'opaque',say('opaque'),n.type,d);
    }
  }
  walk(root,0);
  return result;
}


// The top-level conclusion of each binder/let region is retained; nested
// application arguments are hidden behind their conclusion's disclosure.
export function outlinePaths(root){
  const paths=new Set();
  function visit(n){
    if(!n)return;
    const children=Array.isArray(n.children)?n.children:[];
    if(n.kind==='apply'&&children.length&&typeof n.path==='string'){
      paths.add(n.path);
      // Include nested applications so opening one level reveals its immediate steps.
    }
    for(const c of children)visit(c);
  }
  visit(root);return paths;
}
