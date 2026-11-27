// A deliberately small presentation-math grammar. Tokens -> AST -> Lean
// candidate. TeX is not executed; unknown macros and ambiguous adjacency fail.
const commands={land:'∧',wedge:'∧',lor:'∨',vee:'∨',neg:'¬',lnot:'¬',to:'→',implies:'→',Rightarrow:'→',iff:'↔',Leftrightarrow:'↔',le:'≤',leq:'≤',ge:'≥',geq:'≥',ne:'≠',neq:'≠',in:'∈',subseteq:'⊆',cdot:'*',times:'*',forall:'∀',exists:'∃',alpha:'α',beta:'β',gamma:'γ',delta:'δ',epsilon:'ε',theta:'θ',lambda:'λ',mu:'μ',pi:'π',rho:'ρ',sigma:'σ',phi:'φ',psi:'ψ',omega:'ω',top:'True',bot:'False'};
const bin={'↔':[10,11],'→':[20,20],'∨':[30,31],'∧':[40,41],'=':[50,51],'≠':[50,51],'<':[50,51],'>':[50,51],'≤':[50,51],'≥':[50,51],'∈':[50,51],'⊆':[50,51],'+':[60,61],'-':[60,61],'*':[70,71],'/':[70,71],'^':[80,80]};
const relation=new Set(['=','≠','<','>','≤','≥','∈','⊆','↔']);
const reserved=new Set('by fun match let in if then else do have show from where theorem lemma def import namespace end section set_option sorry admit sorryAx true false Type Prop'.split(' '));
function tokenize(s){
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
  if(name){if(reserved.has(name[0]))throw Error('Unsupported identifier '+name[0]);push('id',name[0],pos);i+=name[0].length;continue;}
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
 const tokens=tokenize(input);let i=0;
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
    i++;const wrapped=syntax==='lean'&&peek().kind==='(';if(wrapped)take('(');
    const name=take('id').value;
    if(!wrapped&&peek().kind==='op'&&peek().value==='∈'){
      take('op','∈');const set=expr(0,depth+1);take(',');
      if(hasFreeName(scopedFormula(set),name))throw Error('Bounded quantifier set would capture '+name+'; rename the binder.');
      left={kind:'bounded',op:t.value,name,set,body:expr(0,depth+1)};
    }else if(!wrapped&&syntax==='lean'&&peek().kind===','){
      take(',');left={kind:'binder',op:t.value,name,domain:null,body:expr(0,depth+1)};
    }else{
      take(':');const domain=expr(0,depth+1);if(wrapped)take(')');take(',');
      left={kind:'binder',op:t.value,name,domain,body:expr(0,depth+1)};
    }
  }else throw Error('Expected a formula at '+t.pos);
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
