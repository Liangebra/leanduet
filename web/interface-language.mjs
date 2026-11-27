// Presentation strings only. Never translate proof source, draft text, or user annotations.
const rows = [
["Interface language","界面语言","表示言語"],
["Explorer","资源管理器","エクスプローラー"],
["Notebook","笔记本","ノートブック"],
["Workbench","工作台","ワークベンチ"],
["Dark mode","深色模式","ダークモード"],
["Light mode","浅色模式","ライトモード"],
["About","关于","概要"],
["✓ Check in Lean","✓ 在 Lean 中验证","✓ Lean で検証"],
["EXPLORER","资源管理器","エクスプローラー"],
["＋ New proof","＋ 新建证明","＋ 新規証明"],
["＋ Open document","＋ 打开文档","＋ 文書を開く"],
["↓ Export Lean","↓ 导出 Lean","↓ Lean を出力"],
["↓ Export workspace","↓ 导出工作区","↓ 作業領域を出力"],
["EXAMPLE LIBRARY","示例库","例題ライブラリ"],
["PROOF OUTLINE","证明大纲","証明の概要"],
["Community","社区","コミュニティ"],
["Contribute ↗","参与贡献 ↗","貢献する ↗"],
["Discussions ↗","讨论 ↗","議論 ↗"],
["Experimental · MIT","实验性 · MIT","実験的 · MIT"],
["Independent open-source project","独立开源项目","独立したオープンソースプロジェクト"],
["Document","文档","文書"],
["Auto-sync","自动同步","自動同期"],
["Live typed reading","实时类型化阅读","型付き証明のライブ表示"],
["Focus reading","专注阅读","読解に集中"],
["Show Lean","显示 Lean","Lean を表示"],
["New statement","新建命题","新しい命題"],
["Mathematics","数学","数学"],
["Mathematical proof","数学证明","数学的証明"],
["Reading","阅读","読解"],
["Controlled text","受控文本","制御テキスト"],
["Typed proof","类型化证明","型付き証明"],
["Explore","探索","探索"],
["THEOREM","定理","定理"],
["Proof.","证明。","証明。"],
["Source-linked steps","与源码关联的步骤","ソースと対応する手順"],
["Edit proof step","编辑证明步骤","証明手順を編集"],
["Edit as","编辑方式","編集形式"],
["Guided sentence","引导式句子","ガイド付き文"],
["Lean fragment","Lean 片段","Lean 断片"],
["Cancel","取消","キャンセル"],
["Apply to Lean","应用到 Lean","Lean に適用"],
["Discard changes","放弃更改","変更を破棄"],
["Sync to Lean →","同步到 Lean →","Lean に同期 →"],
["ELABORATED PROOF TERM","经 elaboration 得到的证明项","精緻化された証明項"],
["Extract typed proof","提取类型化证明","型付き証明を抽出"],
["Read with Informath","使用 Informath 阅读","Informath で読む"],
["Narrative language","数学叙述语言","数学叙述の言語"],
["Import language","导入语言包","言語パックを読み込む"],
["Language pack format","语言包格式","言語パック形式"],
["All occurrences","所有出现项","すべての出現箇所"],
["Argument structure","论证结构","論証構造"],
["Outline","折叠为大纲","概要"],
["Expand all","全部展开","すべて展開"],
["TYPED LOCAL REPLACEMENT","局部类型化替换","局所的な型付き置換"],
["Author wording / modifiers","作者措辞 / 修饰语","著者の表現・修飾語"],
["Copy goal and context to exploration","复制目标及上下文到探索区","目標と文脈を探索へコピー"],
["Local context Γ","局部上下文 Γ","局所文脈 Γ"],
["TYPE-DIRECTED ALTERNATIVES","类型引导的候选项","型に基づく候補"],
["DEPENDENT CONSTRUCTION","依赖构造","依存構成"],
["Witness","见证","証人"],
["Evidence at the new witness","新见证处的证明","新しい証人に対する証明"],
["Build existential proof","构造存在性证明","存在証明を構成"],
["LIBRARY RULE SEARCH","定理库规则搜索","ライブラリの規則検索"],
["Goal formula (optional LaTeX)","目标公式（可选 LaTeX）","目標式（任意の LaTeX）"],
["Mathematical concept or exact declaration","数学概念或精确声明名","数学概念または正確な宣言名"],
["Find typed proofs","搜索类型化证明","型付き証明を検索"],
["Explore interpretations","探索不同解释","解釈を探索"],
["Check alternatives","验证候选解释","候補を検証"],
["Keep draft in exploration","保留草稿至探索区","下書きを探索に保存"],
["Optional AI interpretation of unrestricted wording","可选 AI 自由措辞解释","任意の表現に対するオプションの AI 解釈"],
["Suggest alternatives (AI)","建议候选解释（AI）","候補を提案（AI）"],
["Compose a multi-step proof · 组合推理","组合多步证明","複数手順の証明を構成"],
["Input format","输入格式","入力形式"],
["Controlled narrative","受控数学叙述","制御された数学叙述"],
["Formula sequence (LaTeX only)","公式序列（仅 LaTeX）","数式列（LaTeX のみ）"],
["Mathematical prose draft","数学文本草稿","数学文章の下書き"],
["Proof input","证明输入","証明入力"],
["Stage translation","生成待审转换","変換候補を準備"],
["Infer types in Lean","在 Lean 中推断类型","Lean で型を推論"],
["Extract a lemma","提取引理","補題を抽出"],
["Preview checked abstraction","预览已检查的抽象","検証済み抽象化をプレビュー"],
["Preview factored proof","预览提取后的证明","補題化した証明をプレビュー"],
["Semantic IR · kernel judgment","语义 IR · 内核判断","意味 IR · カーネル判断"],
["Inspect semantic IR","检查语义 IR","意味 IR を調べる"],
["Replacement term in this local context","此局部上下文中的替换项","この局所文脈での置換項"],
["Check replacement","验证替换","置換を検証"],
["Apply checked export","应用已验证导出","検証済みの出力を適用"],
["Mathematical exploration","数学探索","数学的探索"],
["Working notes","研究笔记","作業ノート"],
["Export notes (.md)","导出笔记（.md）","ノートを出力（.md）"],
["Use selected formula in goal search","将选中公式用于目标搜索","選択式を目標検索に使用"],
["Translate a proof draft · offline","转换证明草稿 · 离线","証明下書きを変換 · オフライン"],
["Context names (space separated)","上下文名称（空格分隔）","文脈名（空白区切り）"],
["Mathematical draft","数学草稿","数学の下書き"],
["Use selected notes","使用选中的笔记","選択ノートを使用"],
["Export Lean fragment","导出 Lean 片段","Lean 断片を出力"],
["Working objects","研究对象","作業対象"],
["New working object","新建研究对象","作業対象を追加"],
["Capture selected notes","提取选中笔记","選択ノートを取り込む"],
["Optional AI assistance","可选 AI 辅助","オプションの AI 支援"],
["Explain Lean","解释 Lean","Lean を説明"],
["Propose Lean","建议 Lean","Lean を提案"],
["UNVERIFIED AI OUTPUT","未经验证的 AI 输出","未検証の AI 出力"],
["No proposal yet.","暂无建议。","提案はまだありません。"],
["Apply proposed Lean","应用建议的 Lean","提案された Lean を適用"],
["Append explanation to notes","将解释附加到笔记","説明をノートに追加"],
["Lean 4 source","Lean 4 源码","Lean 4 ソース"],
["Complete","补全","補完"],
["Lean completion","Lean 补全","Lean 補完"],
["Close","关闭","閉じる"],
["← Sync to mathematics","← 同步到数学","← 数学へ同期"],
["LEAN DIAGNOSTICS","LEAN 诊断","LEAN 診断"],
["SELECTED STEP","选中的步骤","選択した手順"],
["STRUCTURE","结构","構造"],
["No step selected","尚未选择步骤","手順が未選択"],
["Lexical nesting, not logical dependency.","词法嵌套，而非逻辑依赖。","字句的な入れ子であり、論理的依存ではありません。"],
["Edit step","编辑步骤","手順を編集"],
["Run trusted Lean code only.","仅运行可信的 Lean 代码。","信頼できる Lean コードのみ実行してください。"],
["Local draft","本地草稿","ローカル下書き"],
["Saved locally","已保存到本地","ローカルに保存済み"],
["Not saved","未保存","未保存"],
["Synced","已同步","同期済み"],
["Edited","已编辑","編集済み"],
["Not checked","未验证","未検証"],
["Local server required","需要本地服务","ローカルサーバーが必要"],
["Local workspace","本地工作区","ローカル作業領域"],
["Static demo · checker and AI require local server","静态演示 · 验证和 AI 需要本地服务","静的デモ · 検証と AI にはローカルサーバーが必要"],
["Browser-only demo. To verify in Lean or use AI, clone the repository and run python server.py.","浏览器演示：若要在 Lean 中验证或使用 AI，请克隆仓库并运行 python server.py。","ブラウザデモ。Lean の検証や AI を使うには、リポジトリをクローンして python server.py を実行してください。"],
["Browser-only demo. Run python server.py locally for verification.","浏览器演示。请在本地运行 python server.py 进行验证。","ブラウザデモ。検証にはローカルで python server.py を実行してください。"],
["Run the local checker to see diagnostics for this revision.","运行本地验证器查看此版本的诊断。","この版の診断を見るにはローカル検証を実行してください。"],
["Representations synchronized. Lean verification and narrative review are separate.","两种表示已同步。Lean 验证与叙述审查相互独立。","表現を同期しました。Lean の検証と叙述の審査は別です。"],
["Unsynchronized edits · both drafts are retained.","存在未同步编辑 · 两份草稿均已保留。","未同期の編集 · 両方の下書きを保持します。"],
["Authored example · alignment not formally certified","人工编写示例 · 对齐未经形式化认证","人手による例 · 対応は形式的に認証されていません"],
["Structural view · not a mathematical narrative","结构视图 · 不是数学叙述","構造表示 · 数学的叙述ではありません"],
["Proof changed or not inspected. Run extraction for this revision.","证明已更改或尚未检查，请提取此版本。","証明が変更されたか未調査です。この版を抽出してください。"],
["Local Lean required; Informath is optional.","需要本地 Lean；Informath 为可选项。","ローカル Lean が必要です。Informath は任意です。"],
["Static example · authored reading, not an elaborated proof tree.","静态示例 · 人工编写的叙述，并非 elaboration 得到的证明树。","静的な例 · 人手による叙述であり、精緻化された証明木ではありません。"],
["Static demo: select a built-in example for multilingual reading; arbitrary proof extraction requires local Lean.","静态演示：请选择内置示例体验多语言阅读；任意证明的提取需要本地 Lean。","静的デモ：組み込み例で多言語読解を試せます。任意の証明の抽出にはローカル Lean が必要です。"],
["Authored example · English fallback for this language pack.","人工示例 · 此语言包暂用英文叙述。","人手による例 · この言語パックでは英語にフォールバックします。"],
["Build-time Lean extraction · exact built-in source · no live checking.","构建时由 Lean 提取 · 与内置源码完全一致 · 非实时验证。","ビルド時に Lean で抽出 · 組み込みソースと完全一致 · ライブ検証ではありません。"],
["BUILD-TIME LEAN EXTRACTION · READ-ONLY","构建时 Lean 提取 · 只读","ビルド時の Lean 抽出 · 読み取り専用"],
["AUTHORED EXAMPLE · NOT VERIFIED","人工示例 · 未验证","人手による例 · 未検証"],
["Implication composition","蕴含的复合","含意の合成"],
["Conjunction symmetry","合取的对称性","連言の対称性"],
["Nested proof","嵌套证明","入れ子の証明"],
["Equality symmetry","等式的对称性","等式の対称性"],
["Composition of injective maps","单射的复合","単射の合成"],
["Inspect the actual Lean term, its types, and applied declarations. This view is not based on tactic text.","检查实际 Lean 项、类型和应用的声明。此视图不基于 tactic 文本。","実際の Lean 項、その型、適用された宣言を調べます。この表示は tactic テキストに基づきません。"],
["A guided sentence maps to one formal fragment. It is not unrestricted natural language.","引导式句子对应一个形式化片段，并非不受限制的自然语言。","ガイド付き文は形式的断片に対応します。自由な自然言語ではありません。"],
["Write freely: questions, incomplete arguments, conjectures, counterexamples, notation of your own. No grammar or proof obligations are imposed here. Notes are local and unverified; editing them does not alter the Lean source.","自由记录问题、不完整论证、猜想、反例与自定义记号。此处不要求语法或证明义务。笔记仅保存在本地且未经验证，编辑不会改变 Lean 源码。","質問、不完全な論証、予想、反例、独自の記号を自由に記録できます。文法や証明義務はありません。ノートはローカルで未検証であり、編集しても Lean ソースは変わりません。"],
["Optional scope names identify objects already introduced elsewhere. Translation creates a candidate fragment, not a checked theorem. No server or AI required.","可选的上下文名称标识已引入的对象。转换只生成候选片段，不是已验证定理。无需服务器或 AI。","任意の文脈名は既に導入された対象を表します。変換は候補断片を生成するだけで、検証済み定理ではありません。サーバーや AI は不要です。"],
["Proposals are unverified; nothing is sent until you request it and confirm.","建议未经验证；只有在你主动请求并确认之后才会发送内容。","提案は未検証です。要求して確認するまで内容は送信されません。"],
["Candidate generated · Lean not checked","已生成候选 · 尚未交由 Lean 检查","候補を生成 · Lean 未検査"],
["Depends on an open obligation","依赖尚未完成的证明义务","未解決の証明義務に依存"],
["Open proof obligation","尚有开放的证明义务","未解決の証明義務"],
["Needs more context","需要更多上下文","追加の文脈が必要"],
["Needs an explicit element type","需要显式指定元素类型","要素型を明示してください"],
["Element type conflicts with the known carrier","元素类型与已知载体类型冲突","要素型が既知の台型と一致しません"],
["Set restriction names more than one local object","集合限制名称对应多个局部对象","集合制限の名前が複数の局所対象に対応しています"],
["A candidate is available · choose how to proceed","已有候选 · 请决定是否采用","候補あり · 採用するか選択してください"],
["Multiple supported interpretations remain","仍有多种受支持的解释","複数の対応可能な解釈が残っています"],
["Candidate search budget exhausted","候选搜索达到预算上限","候補探索の予算上限に達しました"],
["Current choice no longer fits","当前选择已不再相容","現在の選択は整合しません"],
["Draft constraints conflict","草稿约束彼此冲突","下書きの制約が矛盾しています"],
["No match in the supported rule set","当前支持的规则中没有匹配项","対応可能な規則に一致するものがありません"],
["Wording or rule is not supported","该措辞或规则目前不受支持","この表現または規則は未対応です"],
["Does not match the current goal","与当前目标不匹配","現在の目標と一致しません"]
];
const dictionaries = new Map(rows.map(([en,zh,ja])=>[en,{en,zh,ja}]));
const key='leanduet.interface-language';
export function preferredLanguage(saved,browser='en'){
  if(['en','zh','ja'].includes(saved))return saved;
  const prefix=browser.toLowerCase().split('-')[0];
  return ['zh','ja'].includes(prefix)?prefix:'en';
}
export function translate(text,lang){
  const trimmed=text.trim(), entry=dictionaries.get(trimmed);
  return entry?text.replace(trimmed,entry[lang]||entry.en):text;
}
export function mountInterface(onChange){
  const selector=document.getElementById('interfaceLanguage');
  let saved;try{saved=localStorage.getItem(key);}catch{}
  let lang=preferredLanguage(saved,navigator.language);
  const bindings=[];
  // Capture only the original static markup, before app code creates proof content.
  const walker=document.createTreeWalker(document.body,NodeFilter.SHOW_TEXT);
  while(walker.nextNode()){
    const n=walker.currentNode;
    if(dictionaries.has(n.data.trim())&&!n.parentElement.closest('script,style,textarea, #interfaceLanguage, #typedLanguage'))bindings.push([n,n.data]);
  }
  const dynamicIds=['theme','focusMode','toggleLayout','saveState','leanDirty','proseDirty','verifyState','notice','envState','output','typedStatus','narrativeStatus','inspectName'];
  const dynamic=new Map();
  const reverse=new Map(rows.flatMap(([en,zh,ja])=>[[en,en],[zh,en],[ja,en]]));
  for(const id of dynamicIds){
    const el=document.getElementById(id);if(!el)continue;
    const observer=new MutationObserver(()=>{
      const value=el.textContent, original=reverse.get(value.trim());
      if(original){dynamic.set(el,original);const translated=translate(original,lang);if(value!==translated)el.textContent=translated;}
      else dynamic.delete(el);
    });
    observer.observe(el,{childList:true,characterData:true,subtree:true});
  }
  function apply(){
    document.documentElement.lang=({en:'en',zh:'zh-CN',ja:'ja'})[lang];
    selector.setAttribute('aria-label',translate('Interface language',lang));selector.title=translate('Interface language',lang);
    selector.value=lang;
    for(const [node,original] of bindings)if(node.isConnected)node.data=translate(original,lang);
    for(const [el,original] of dynamic)el.textContent=translate(original,lang);
    for(const button of document.querySelectorAll('#examples button')){
      const original=reverse.get(button.textContent.trim());
      if(original)button.textContent=translate(original,lang);
    }
    document.title=({en:'LeanDuet — Mathematical proof workbench',zh:'LeanDuet — 数学证明工作台',ja:'LeanDuet — 数学証明ワークベンチ'})[lang];
  }
  selector.addEventListener('change',()=>{lang=preferredLanguage(selector.value);try{localStorage.setItem(key,lang);}catch{}apply();onChange?.(lang);});
  apply();
  return {language:()=>lang,t:text=>translate(text,lang),refresh:apply};
}
