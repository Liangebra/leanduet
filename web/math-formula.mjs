// A deliberately small presentation-math grammar. Tokens -> AST -> Lean
// candidate. TeX is not executed; unknown macros and ambiguous adjacency fail.
const commands={land:'∧',wedge:'∧',lor:'∨',vee:'∨',neg:'¬',lnot:'¬',to:'→',implies:'→',Rightarrow:'→',iff:'↔',Leftrightarrow:'↔',le:'≤',leq:'≤',ge:'≥',geq:'≥',ne:'≠',neq:'≠',in:'∈',subseteq:'⊆',cap:'∩',inter:'∩',cup:'∪',union:'∪',cdot:'*',times:'*',forall:'∀',exists:'∃',alpha:'α',beta:'β',gamma:'γ',delta:'δ',epsilon:'ε',theta:'θ',lambda:'λ',mu:'μ',pi:'π',rho:'ρ',sigma:'σ',phi:'φ',psi:'ψ',omega:'ω',top:'True',bot:'False'};
// Match Lean's arithmetic and set-operator precedences: + and ∪ at 65;
// *, ∩ at 70. This matters when users mix these symbols in one formula.
// The bounded `''` image operator follows Mathlib v4.19.0's
// `Mathlib/Data/Set/Operations.lean` declaration `infixl:80 " '' " => image`.
const bin={'↔':[10,11],'→':[20,20],'∨':[30,31],'∧':[40,41],'=':[50,51],'≠':[50,51],'<':[50,51],'>':[50,51],'≤':[50,51],'≥':[50,51],'∈':[50,51],'⊆':[50,51],'∪':[65,66],'+':[65,66],'-':[65,66],'∩':[70,71],'*':[70,71],'/':[70,71],"''":[80,81],'^':[80,80]};
const relation=new Set(['=','≠','<','>','≤','≥','∈','⊆','↔']);
const reserved=new Set('by fun match let in if then else do have show from where theorem lemma def import namespace end section set_option sorry admit sorryAx true false Type Prop'.split(' '));
function tokenize(s,{syntax='math'}={}){
 if(typeof s!=='string'||s.length>3000)throw Error('Formula exceeds 3000 characters.');
 s=s.trim();
 if(s.startsWith('$')&&s.endsWith('$')&&!s.startsWith('$$'))s=s.slice(1,-1);
 else if(s.startsWith('\\(')&&s.endsWith('\\)'))s=s.slice(2,-2);
 else if(s.startsWith('\\[')&&s.endsWith('\\]'))s=s.slice(2,-2);
 const t=[];let i=0;
 function push(kind,value,pos){t.push({kind,value,pos});if(t.length>512)throw Error('Too many formula tokens.');}
 while(i<s.length){
  if(/\s/.test(s[i])){i++;continue;}
  const pos=i,c=s[i];
  if(s.startsWith("''",i)){push('op',"''",pos);i+=2;continue;}
  if(c==='\\'){
   const m=/^\\([A-Za-z]+|[,;! ])/u.exec(s.slice(i));if(!m)throw Error('Unknown TeX command at '+i);
   i+=m[0].length;const cmd=m[1];
   if(['left','right',',',';','!',' '].includes(cmd))continue;
   if(cmd==='frac'){push('frac',cmd,pos);continue;}
   if(cmd==='mathbb'){
    const a=/^\s*\{\s*([NZQR])\s*\}/.exec(s.slice(i));if(!a)throw Error('Supported mathbb types: N,Z,Q,R.');
    i+=a[0].length;push('id',({N:'Nat',Z:'Int',Q:'ℚ',R:'ℝ'})[a[1]],pos);continue;
   }
   if(!Object.hasOwn(commands,cmd))throw Error('Unsupported macro \\'+cmd);
   const v=commands[cmd];push(bin[v]||'¬∀∃'.includes(v)?'op':'id',v,pos);continue;
  }
  const name=/^[\p{L}][\p{L}\p{N}_']*/u.exec(s.slice(i));
  if(name){
   // Lean's elaborated targets often contain predicate-valued binders such
   // as `(P : Nat → Prop)`. Prop (and universe sort Type) is a sort in that
   // domain, not an ordinary mathematical variable. Accept these two tokens
   // only in Lean syntax; the presentation grammar still rejects raw Lean
   // declarations.
   const leanSort=syntax==='lean'&&['Prop','Type'].includes(name[0]);
   if(reserved.has(name[0])&&!leanSort)throw Error('Unsupported identifier '+name[0]);
   push('id',name[0],pos);i+=name[0].length;continue;
  }
  const n=/^\d+(?:\.\d+)?/.exec(s.slice(i));if(n){push('number',n[0],pos);i+=n[0].length;continue;}
  if(Object.hasOwn(bin,c)||'¬∀∃'.includes(c)){push('op',c,pos);i++;continue;}
  if('(){}:,'.includes(c)){push(c,c,pos);i++;continue;}
  throw Error('Unsupported formula character at '+i+': '+c);
 }
 push('end','',s.length);return t;
}
function hasFreeName(ast,name){return ast?.kind==='free'&&ast.name===name||Object.values(ast||{}).some(x=>Array.isArray(x)?x.some(v=>v&&typeof v==='object'&&hasFreeName(v,name)):x&&typeof x==='object'&&hasFreeName(x,name));}
export function parseFormula(input,{syntax='math'}={}){
 if(!['math','lean'].includes(syntax))throw Error('Unknown formula syntax.');
 const tokens=tokenize(input,{syntax});let i=0;
 const peek=()=>tokens[i];
 function take(k,v){const t=peek();if(t.kind!==k||(v!==undefined&&t.value!==v))throw Error('Expected '+(v??k)+' at '+t.pos);i++;return t;}
 function group(open,close,depth){take(open);const x=expr(0,depth+1);take(close);return x;}
 function expr(min=0,depth=0){
  if(depth>64)throw Error('Formula nesting too deep.');
  let t=peek(),left;
  if(t.kind==='id'||t.kind==='number'){i++;left={kind:t.kind,value:t.value};}
  else if(t.kind==='('||t.kind==='{')left=group(t.kind,t.kind==='('?')':'}',depth);
  else if(t.kind==='frac'){i++;left={kind:'binary',op:'/',left:group('{','}',depth),right:group('{','}',depth)};}
  else if(t.kind==='op'&&['¬','-'].includes(t.value)){i++;left={kind:'unary',op:t.value,body:expr(t.value==='¬'?45:75,depth+1)};}
  else if(t.kind==='op'&&['∀','∃'].includes(t.value)){
    i++;const binders=[];let bounded=false;
    while(true){
      const wrapped=syntax==='lean'&&peek().kind==='(';
      if(wrapped){
        take('(');const names=[take('id').value];
        while(peek().kind==='id')names.push(take('id').value);
        let domain=null;
        if(peek().kind===':'){take(':');domain=expr(0,depth+1);}
        take(')');
        // A shared binder type is parsed outside the names it declares.
        // Reject same-spelled free references instead of accidentally
        // capturing them when the group is represented as nested binders.
        if(names.length>1&&domain){
          const scopedDomain=scopedFormula(domain);
          if(names.some(name=>hasFreeName(scopedDomain,name)))
            throw Error('A grouped binder type would capture a declared name; separate the binder groups.');
        }
        for(const name of names)binders.push({name,domain});
      }else{
        const name=take('id').value;
        if(peek().kind==='op'&&peek().value==='∈'){
          if(binders.length)throw Error('A bounded quantifier must begin with its restricted binder.');
          take('op','∈');const set=expr(0,depth+1);take(',');
          if(hasFreeName(scopedFormula(set),name))
            throw Error('Bounded quantifier set would capture '+name+'; rename the binder.');
          left={kind:'bounded',op:t.value,name,set,body:expr(0,depth+1)};bounded=true;break;
        }
        let domain=null;
        if(peek().kind===':'){take(':');domain=expr(0,depth+1);}
        binders.push({name,domain});
      }
      if(peek().kind===',')break;
      if(syntax==='lean'&&['(','id'].includes(peek().kind))continue;
      take(',');
    }
    if(!bounded){
      take(',');let body=expr(0,depth+1);
      for(let index=binders.length-1;index>=0;index--){
        const binder=binders[index];
        body={kind:'binder',op:t.value,name:binder.name,domain:binder.domain,body};
      }
      left=body;
    }
  }lse throw Error('Expected a formula at '+t.pos);
  while(true){
   t=peek();
   // Lean adjacency denotes application, unlike presentation math.
   if(syntax==='lean'&&90>=min&&['id','number','('].includes(t.kind)){
    const arg=expr(91,depth+1);
    left=left.kind==='call'?{...left,args:[...left.args,arg]}:{kind:'call',fn:left,args:[arg]};continue;
   }
   if(syntax==='math'&&t.kind==='('&&90>=min){
    i++;const args=[expr(0,depth+1)];while(peek().kind===','){i++;args.push(expr(0,depth+1));}take(')');
    left={kind:'call',fn:left,args};continue;
   }
   if(t.kind!=='op'||!Object.hasOwn(bin,t.value)||bin[t.value][0]<min)break;
   i++;const op=t.value;
   if(relation.has(op)&&left.kind==='binary'&&relation.has(left.op))throw Error('Chained relations require explicit conjunction.');
   left={kind:'binary',op,left,right:expr(bin[op][1],depth+1)};
  }
  return left;
 }
 const result=expr();take('end');return result;
}
export function renderFormula(ast){
 switch(ast.kind){
  case 'id':case 'number':return ast.value;
  case 'unary':return '('+ast.op+' '+renderFormula(ast.body)+')';
  case 'binary':return '('+renderFormula(ast.left)+' '+ast.op+' '+renderFormula(ast.right)+')';
  case 'call':return '('+[renderFormula(ast.fn),...ast.args.map(renderFormula)].join(' ')+')';
  case 'binder':return '('+ast.op+' '+ast.name+(ast.domain?' : '+renderFormula(ast.domain):'')+', '+renderFormula(ast.body)+')';
  case 'bounded':return '('+ast.op+' '+ast.name+', ('+ast.name+' ∈ '+renderFormula(ast.set)+') '+(ast.op==='∀'?'→':'∧')+' '+renderFormula(ast.body)+')';
  default:throw Error('Unknown mathematical AST node.');
 }
}
export function compileFormula(text,options){const ast=parseFormula(text,options);return {ast,scoped:scopedFormula(ast),lean:renderFormula(ast)};}

// Structural equivalence after binder names are converted to de Bruijn
// indices. This is deliberately weaker than Lean definitional equality and
// is suitable only for conservative draft-goal consistency checks.
export function sameScopedFormula(left,right,{syntax='lean'}={}){
 if(typeof left!=='string'||typeof right!=='string')return false;
 try{return JSON.stringify(compileFormula(left,{syntax}).scoped)===JSON.stringify(compileFormula(right,{syntax}).scoped);}
 catch{return false;}
}


// Bindings are a separate canonical syntax view. Bound occurrences use
// de Bruijn indices; free names remain unresolved until Lean elaboration.
// This does not equate free identifiers with Lean declarations.
export function scopedFormula(ast,scope=[]){
 switch(ast.kind){
  case 'id':{
   const index=scope.indexOf(ast.value);
   return index<0?{kind:'free',name:ast.value}:{kind:'bound',index};
  }
  case 'number':return {kind:'number',value:ast.value};
  case 'unary':return {kind:'unary',op:ast.op,body:scopedFormula(ast.body,scope)};
  case 'binary':return {kind:'binary',op:ast.op,left:scopedFormula(ast.left,scope),right:scopedFormula(ast.right,scope)};
  case 'call':{
   // In Lean's proposition language, `Not P` and `¬ P` are the same
   // built-in connective. Normalize this exact unary spelling in the scoped
   // view while keeping the authored AST/rendering untouched.
   if(ast.fn?.kind==='id'&&ast.fn.value==='Not'&&ast.args.length===1)
    return {kind:'unary',op:'¬',body:scopedFormula(ast.args[0],scope)};
   const fn=scopedFormula(ast.fn,scope),args=ast.args.map(a=>scopedFormula(a,scope));
   return fn.kind==='call'?{kind:'call',fn:fn.fn,args:[...fn.args,...args]}:{kind:'call',fn,args};
  }
  case 'binder':return {kind:'binder',op:ast.op,domain:ast.domain?scopedFormula(ast.domain,scope):null,body:scopedFormula(ast.body,[ast.name,...scope])};
  case 'bounded':{
   const inner=[ast.name,...scope];
   return {kind:'binder',op:ast.op,domain:null,body:{kind:'binary',op:ast.op==='∀'?'→':'∧',
     left:{kind:'binary',op:'∈',left:{kind:'bound',index:0},right:scopedFormula(ast.set,inner)},
     right:scopedFormula(ast.body,inner)}};
  }
  default:throw Error('Unknown mathematical AST node.');
 }
}
