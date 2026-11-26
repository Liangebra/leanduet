// Validate scope and shape of a kernel judgment received from Lean.
 // This is deliberately not a Lean type checker.
export function validateJudgment(ir){
 if(ir?.schema!==1||ir.format!=='leanduet.kernel-judgment'||typeof ir.path!=='string')throw Error('Unsupported semantic IR.');
 let budget=30000;
 const fail=()=>{throw Error('Malformed or ill-scoped semantic IR.');};
 const nat=n=>Number.isSafeInteger(n)&&n>=0;
 const decimal=n=>typeof n==='string'&&/^(0|[1-9]\d*)$/.test(n);
 const binders=new Set(['explicit','implicit','strictImplicit','instance']);
 function name(n,d=0){if(d>96||!Array.isArray(n))fail();if(!n.length)return;if(n.length!==3)fail();name(n[0],d+1);if(n[1]==='str'&&typeof n[2]==='string')return;if(n[1]==='num'&&decimal(n[2]))return;fail();}
 function level(l,d=0){if(d>96||!Array.isArray(l))fail();switch(l[0]){case'zero':if(l.length===1)return;break;case'param':if(l.length===2){name(l[1]);return;}break;case'succ':if(l.length===2){level(l[1],d+1);return;}break;case'max':case'imax':if(l.length===3){level(l[1],d+1);level(l[2],d+1);return;}break;}fail();}
 function expr(e,slots,depth=0,limit=0){
  if(--budget<0||limit>100||!Array.isArray(e))fail();
  const child=(x,bound=depth)=>expr(x,slots,bound,limit+1);
  switch(e[0]){
   case'bound':if(e.length===2&&nat(e[1])&&e[1]<depth)return;break;
   case'local':if(e.length===2&&slots.has(e[1]))return;break;
   case'sort':if(e.length===2){level(e[1]);return;}break;
   case'const':if(e.length===3&&Array.isArray(e[2])){name(e[1]);for(const u of e[2])level(u);return;}break;
   case'app':if(e.length===3){child(e[1]);child(e[2]);return;}break;
   case'lambda':case'pi':if(e.length===5&&binders.has(e[2])){name(e[1]);child(e[3]);child(e[4],depth+1);return;}break;
   case'let':if(e.length===6&&typeof e[5]==='boolean'){name(e[1]);child(e[2]);child(e[3]);child(e[4],depth+1);return;}break;
   case'nat':if(e.length===2&&decimal(e[1]))return;break;
   case'string':if(e.length===2&&typeof e[1]==='string')return;break;
   case'projection':if(e.length===4&&nat(e[2])){name(e[1]);child(e[3]);return;}break;
  }fail();
 }
 name(ir.declaration);if(!Array.isArray(ir.universes))fail();for(const u of ir.universes)name(u);
 const j=ir.judgment,slots=new Set();if(!j||!Array.isArray(j.context)||j.context.length>128||!['proof','proposition','expression'].includes(j.kind))fail();
 let last=-1;
 for(const d of j.context){
  if(!d||!nat(d.slot)||d.slot<=last||!binders.has(d.binder)||typeof d.internal!=='boolean')fail();
  name(d.name);expr(d.type,slots);if(d.value!==null)expr(d.value,slots);slots.add(d.slot);last=d.slot;
 }
 expr(j.term,slots);expr(j.type,slots);
 if(j.formula!==null){if(typeof j.formula?.matchesGoal!=='boolean')fail();expr(j.formula.term,slots);}
 return ir;
}
