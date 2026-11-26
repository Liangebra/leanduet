import {EXAMPLES} from './core.mjs';
// These authored examples are selected only for byte-identical source.
// They are illustrative, not a proof of semantic alignment.
const examples=[
{statement:['Let P, Q, and R be propositions. Suppose ',{math:'P → Q'},' and ',{math:'Q → R'},'. Then ',{math:'P → R'},'.'],steps:{2:['Assume ',{math:'P'},' (denote the hypothesis by hp).'],3:['By the first implication and hp, we obtain ',{math:'Q'},'. Denote this by hq.'],4:['Apply the second implication to hq to obtain ',{math:'R'},'.']}},
{statement:['For propositions P and Q, ',{math:'P ∧ Q'},' implies ',{math:'Q ∧ P'},'.'],steps:{2:['To prove the conjunction, it suffices to prove both components.'],3:['The second component of the given hypothesis yields ',{math:'Q'},'.'],4:['Its first component yields ',{math:'P'},'.']}},
{statement:['Let P be a proposition and h a proof of P. Then ',{math:'P ∧ P'},'.'],steps:{2:['First establish the auxiliary claim ',{math:'P'},', denoting it by h′.'],3:['The auxiliary claim follows from the original hypothesis h.'],4:['Pair the auxiliary claim h′ with h to obtain ',{math:'P ∧ P'},'.']}},
{statement:['Let a and b be natural numbers. If ',{math:'a = b'},', then ',{math:'b = a'},'.'],steps:{2:['By symmetry of equality, the hypothesis a = b gives ',{math:'b = a'},'.']}}
];
export function authoredNarrative(source){const i=EXAMPLES.findIndex(e=>e.source===source);return i<0?null:examples[i];}
