// Deterministic realization of the extracted proof tree, not a reverse parser.
// Never identify two proofs merely because their types are equal.
const meanings = {
  'Exists.intro':['Establish existence using the witness','利用所选见证证明存在性'],
  'Exists.elim':['Eliminate the existential hypothesis','利用存在命题的消去规则'],
  'Eq.rec':['Transport along equality','沿等式进行运输'],
  'Eq.ndrec':['Transport along equality','沿等式进行运输'],
  'And.intro':['Combine the two claims','合并两个结论'],
  'And.left':['Use the first conjunct','取合取命题的第一项'],
  'And.right':['Use the second conjunct','取合取命题的第二项'],
  'Or.inl':['Introduce the left disjunct','由左侧命题引入析取'],
  'Or.inr':['Introduce the right disjunct','由右侧命题引入析取'],
  'Eq.symm':['Use symmetry of equality','利用等式的对称性'],
  'Eq.trans':['Use transitivity of equality','利用等式的传递性'],
  'False.elim':['Eliminate the contradiction','由矛盾推出结论'],
  'Iff.mp':['Use the forward implication','利用等价命题的正向蕴含'],
  'Iff.mpr':['Use the reverse implication','利用等价命题的反向蕴含']
};
export function narrate(root,lang='en'){
  const zh=lang==='zh',result=[];
  const add=(kind,phrase,expr,depth)=>result.push({kind,phrase,expr,depth});
  function walk(n,d){
    if(!n||d>12)return;
    const children=Array.isArray(n.children)?n.children:[];
    if(n.kind==='introduce'||n.kind==='assume'){
      add(n.kind,zh?(n.kind==='assume'?'假设 ':'任取 ')+n.binder:(n.kind==='assume'?'Assume ':'Introduce ')+n.binder,n.binderType,d);
      for(const c of children)walk(c,d+1);
      return;
    }
    if(n.kind==='witness'){
      add('witness',(zh?'选取见证 ':'Choose witness ')+n.term+(zh?'，其类型为':' of type'),n.type,d);return;
    }
    if(n.kind==='let'){
      if(children[0])walk(children[0],d+1);
      add('let',(zh?'建立局部绑定 ':'Establish local binding ')+n.binder,n.binderType,d);
      if(children[1])walk(children[1],d+1);
      return;
    }
    for(const c of children)walk(c,d);
    if(n.kind==='apply'){
      const lexical=meanings[n.reference];
      const phrase=lexical?lexical[zh?1:0]:(zh?'应用 ':'Apply ')+(n.reference||'the displayed function');
      add(n.kind,phrase+(zh?'，得到':' to obtain'),n.type,d);
    }else if(n.kind==='hypothesis'||n.kind==='reference'){
      add(n.kind,(zh?'使用 ':'Use ')+(n.reference||n.term),n.type,d);
    }else{
      add('opaque',zh?'保留未展开的形式化项':'Retain the unexpanded formal term',n.type,d);
    }
  }
  walk(root,0);
  return result;
}
