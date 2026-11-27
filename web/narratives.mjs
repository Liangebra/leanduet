import {EXAMPLES} from './core.mjs';
// These authored examples are selected only for byte-identical source.
// They are illustrative, not a proof of semantic alignment.
const examples=[
{statement:['Let P, Q, and R be propositions. Suppose ',{math:'P → Q'},' and ',{math:'Q → R'},'. Then ',{math:'P → R'},'.'],steps:{2:['Assume ',{math:'P'},' (denote the hypothesis by hp).'],3:['By the first implication and hp, we obtain ',{math:'Q'},'. Denote this by hq.'],4:['Apply the second implication to hq to obtain ',{math:'R'},'.']}},
{statement:['For propositions P and Q, ',{math:'P ∧ Q'},' implies ',{math:'Q ∧ P'},'.'],steps:{2:['To prove the conjunction, it suffices to prove both components.'],3:['The second component of the given hypothesis yields ',{math:'Q'},'.'],4:['Its first component yields ',{math:'P'},'.']}},
{statement:['Let P be a proposition and h a proof of P. Then ',{math:'P ∧ P'},'.'],steps:{2:['First establish the auxiliary claim ',{math:'P'},', denoting it by h′.'],3:['The auxiliary claim follows from the original hypothesis h.'],4:['Pair the auxiliary claim h′ with h to obtain ',{math:'P ∧ P'},'.']}},
{statement:['Let a and b be natural numbers. If ',{math:'a = b'},', then ',{math:'b = a'},'.'],steps:{2:['By symmetry of equality, the hypothesis a = b gives ',{math:'b = a'},'.']}}
,{statement:['Let ',{math:'f : α → β'},' and ',{math:'g : β → γ'},' be injective maps. Then their composition ',{math:'g ∘ f'},' is injective.'],steps:{4:['Take arbitrary a and b, and suppose ',{math:'g (f a) = g (f b)'},'.'],5:['By injectivity of f, it suffices to establish ',{math:'f a = f b'},'.'],6:['By injectivity of g, it suffices to establish ',{math:'g (f a) = g (f b)'},'.'],7:['This is precisely our hypothesis.']}}
];

const zh=[
{statement:['设 P、Q、R 为命题。若 ',{math:'P → Q'},' 且 ',{math:'Q → R'},'，则 ',{math:'P → R'},'。'],steps:{2:['假设 ',{math:'P'},'，记此假设为 hp。'],3:['由第一个蕴含与 hp，得到 ',{math:'Q'},'，记为 hq。'],4:['将第二个蕴含作用于 hq，得到 ',{math:'R'},'。']}},
{statement:['对于命题 P 和 Q，',{math:'P ∧ Q'},' 蕴含 ',{math:'Q ∧ P'},'。'],steps:{2:['要证明合取命题，只需分别证明两个分量。'],3:['由已知假设的第二个分量得到 ',{math:'Q'},'。'],4:['由其第一个分量得到 ',{math:'P'},'。']}},
{statement:['设 P 为命题，h 为 P 的一个证明。则 ',{math:'P ∧ P'},'。'],steps:{2:['先建立辅助命题 ',{math:'P'},'，将其证明记为 h′。'],3:['由原假设 h 即得辅助命题。'],4:['将 h′ 与 h 配对，得到 ',{math:'P ∧ P'},'。']}},
{statement:['设 a、b 为自然数。若 ',{math:'a = b'},'，则 ',{math:'b = a'},'。'],steps:{2:['由等式的对称性，假设 a = b 蕴含 ',{math:'b = a'},'。']}},
{statement:['设 ',{math:'f : α → β'},' 与 ',{math:'g : β → γ'},' 均为单射，则其复合 ',{math:'g ∘ f'},' 也是单射。'],steps:{4:['任取 a、b，假设 ',{math:'g (f a) = g (f b)'},'。'],5:['由 f 的单射性，只需证明 ',{math:'f a = f b'},'。'],6:['由 g 的单射性，只需证明 ',{math:'g (f a) = g (f b)'},'。'],7:['这正是我们的假设。']}}
];
const ja=[
{statement:['P、Q、R を命題とする。',{math:'P → Q'},' と ',{math:'Q → R'},' を仮定すると、',{math:'P → R'},' が成り立つ。'],steps:{2:[{math:'P'},' を仮定し、その仮定を hp とする。'],3:['最初の含意と hp から ',{math:'Q'},' を得る。その証明を hq とする。'],4:['二番目の含意を hq に適用し、',{math:'R'},' を得る。']}},
{statement:['命題 P、Q について、',{math:'P ∧ Q'},' ならば ',{math:'Q ∧ P'},' である。'],steps:{2:['連言を示すには、二つの成分をそれぞれ示せばよい。'],3:['与えられた仮定の第二成分から ',{math:'Q'},' を得る。'],4:['第一成分から ',{math:'P'},' を得る。']}},
{statement:['P を命題、h を P の証明とする。このとき ',{math:'P ∧ P'},' が成り立つ。'],steps:{2:['まず補助命題 ',{math:'P'},' を示し、その証明を h′ とする。'],3:['補助命題は元の仮定 h から従う。'],4:['h′ と h を組にして ',{math:'P ∧ P'},' を得る。']}},
{statement:['a、b を自然数とする。',{math:'a = b'},' ならば ',{math:'b = a'},' である。'],steps:{2:['等号の対称性により、仮定 a = b から ',{math:'b = a'},' を得る。']}},
{statement:[{math:'f : α → β'},' と ',{math:'g : β → γ'},' を単射とする。その合成 ',{math:'g ∘ f'},' も単射である。'],steps:{4:['任意の a、b を取り、',{math:'g (f a) = g (f b)'},' と仮定する。'],5:['f の単射性から、',{math:'f a = f b'},' を示せばよい。'],6:['g の単射性から、',{math:'g (f a) = g (f b)'},' を示せばよい。'],7:['これは仮定そのものである。']}}
];
export function authoredNarrative(source,lang='en'){
  const i=EXAMPLES.findIndex(e=>e.source===source);
  return i<0?null:({en:examples,zh,ja}[lang]||examples)[i];
}

