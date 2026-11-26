// Deterministic realization of the extracted proof tree, not a reverse parser.
// Never identify two proofs merely because their types are equal.
const meanings = {
  'Exists.intro':['Establish existence using the witness','利用所选见证证明存在性','選んだ証人によって存在を示す'],
  'Exists.elim':['Eliminate the existential hypothesis','利用存在命题的消去规则','存在命題の消去規則を用いる'],
  'Eq.rec':['Transport along equality','沿等式进行运输','等式による移送を行う'],
  'Eq.ndrec':['Transport along equality','沿等式进行运输','等式による移送を行う'],
  'And.intro':['Combine the two claims','合并两个结论','二つの結論を連言にまとめる'],
  'And.left':['Use the first conjunct','取合取命题的第一项','連言の第一項を用いる'],
  'And.right':['Use the second conjunct','取合取命题的第二项','連言の第二項を用いる'],
  'Or.inl':['Introduce the left disjunct','由左侧命题引入析取','左側の命題から選言を導く'],
  'Or.inr':['Introduce the right disjunct','由右侧命题引入析取','右側の命題から選言を導く'],
  'Eq.symm':['Use symmetry of equality','利用等式的对称性','等式の対称性を用いる'],
  'Eq.trans':['Use transitivity of equality','利用等式的传递性','等式の推移性を用いる'],
  'False.elim':['Eliminate the contradiction','由矛盾推出结论','矛盾から結論を導く'],
  'Iff.mp':['Use the forward implication','利用等价命题的正向蕴含','同値の順方向を用いる'],
  'Iff.mpr':['Use the reverse implication','利用等价命题的反向蕴含','同値の逆方向を用いる']
};
export function narrate(root,lang='en',{collapsed=new Set()}={}){
  const ix=lang==='zh'?1:lang==='ja'?2:0,result=[];
  const tr=(en,zh,ja)=>[en,zh,ja][ix];
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
      add(n,n.kind,n.kind==='assume'?tr('Assume ','假设 ','仮定する ')+n.binder:tr('Introduce ','任取 ','任意に取る ')+n.binder,n.binderType,d);
      for(const c of children)walk(c,d+1);
      return;
    }
    if(n.kind==='witness'){
      add(n,'witness',tr('Choose witness ','选取见证 ','証人を取る ')+n.term+tr(' of type','，其类型为','、型は'),n.type,d);return;
    }
    if(n.kind==='let'){
      if(children[0])walk(children[0],d+1);
      add(n,'let',tr('Establish local binding ','建立局部绑定 ','局所束縛を導入する ')+n.binder,n.binderType,d);
      if(children[1])walk(children[1],d+1);
      return;
    }
    const foldable=n.kind==='apply'&&children.length>0&&typeof n.path==='string';
    const folded=foldable&&collapsed.has(n.path);
    const hiddenCount=folded?children.reduce((a,c)=>a+rowCount(c),0):0;
    if(!folded)for(const c of children)walk(c,d);
    if(n.kind==='apply'){
      const lexical=meanings[n.reference];
      const phrase=lexical?lexical[ix]:tr('Apply ','应用 ','適用する ')+(n.reference||tr('the displayed function','所示函数','表示された関数'));
      add(n,n.kind,phrase+tr(' to obtain','，得到','、したがって'),n.type,d,{foldable,folded,hiddenCount});
    }else if(n.kind==='hypothesis'||n.kind==='reference'){
      add(n,n.kind,tr('Use ','使用 ','用いる ')+(n.reference||n.term),n.type,d);
    }else{
      add(n,'opaque',tr('Retain the unexpanded formal term','保留未展开的形式化项','未展開の形式項を保持する'),n.type,d);
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
