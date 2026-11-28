export const BUILTIN_PACKS = [
  {
    "id": "en",
    "label": "English",
    "words": {
      "assume": "Assume {name}",
      "introduce": "Introduce {name}",
      "witness": "Choose witness {name} of type",
      "let": "Establish local binding {name}",
      "apply": "Apply {name}",
      "obtain": " to obtain",
      "use": "Use {name}",
      "opaque": "Retain the unexpanded formal term",
      "function": "the displayed function",
      "edit": "Edit this inference",
      "hidden": "hidden steps",
      "limited": " (extraction limited)"
    },
    "grammar": {
      "prefix": [
        "by",
        "use",
        "apply"
      ],
      "using": [
        "using"
      ],
      "join": [
        "and"
      ],
      "establish": [
        "Establish"
      ],
      "conclude": [
        "Conclude"
      ],
      "automatic": [
        "automatic"
      ]
    },
    "schema": 1,
    "rules": {
      "Exists.intro": "Establish existence using the witness",
      "Exists.elim": "Eliminate the existential hypothesis",
      "Eq.rec": "Transport along equality",
      "Eq.ndrec": "Transport along equality",
      "And.intro": "Combine the two claims",
      "And.left": "Use the first conjunct",
      "And.right": "Use the second conjunct",
      "Or.inl": "Introduce the left disjunct",
      "Or.inr": "Introduce the right disjunct",
      "Eq.symm": "Use symmetry of equality",
      "Eq.trans": "Use transitivity of equality",
      "False.elim": "Eliminate the contradiction",
      "Iff.mp": "Use the forward implication",
      "Iff.mpr": "Use the reverse implication"
    },
    "aliases": {
      "Eq.symm": [
        "symmetry of equality"
      ],
      "Eq.trans": [
        "transitivity of equality"
      ],
      "And.intro": [
        "conjunction introduction"
      ],
      "And.left": [
        "first conjunct"
      ],
      "And.right": [
        "second conjunct"
      ],
      "Eq.mp": [
        "equality transport"
      ],
      "IsCompact.image": [
        "continuous image of a compact set"
      ],
      "Continuous.comp": [
        "composition of continuous functions"
      ],
      "le_trans": [
        "transitivity of order"
      ],
      "Subgroup.mul_mem": [
        "subgroup multiplication closure"
      ],
      "map_add": [
        "additivity of a linear map"
      ]
    }
  },
  {
    "id": "zh",
    "label": "简体中文",
    "words": {
      "assume": "假设 {name}",
      "introduce": "任取 {name}",
      "witness": "选取见证 {name}，其类型为",
      "let": "建立局部绑定 {name}",
      "apply": "应用 {name}",
      "obtain": "，得到",
      "use": "使用 {name}",
      "opaque": "保留未展开的形式化项",
      "function": "所示函数",
      "edit": "编辑此推理",
      "hidden": "个已折叠步骤",
      "limited": "（提取未完整展开）"
    },
    "grammar": {
      "prefix": [
        "由",
        "利用",
        "应用"
      ],
      "using": [
        "使用",
        "利用假设"
      ],
      "join": [
        "和",
        "与"
      ],
      "establish": [
        "建立"
      ],
      "conclude": [
        "结论"
      ],
      "automatic": [
        "自动检索"
      ]
    },
    "schema": 1,
    "rules": {
      "Exists.intro": "利用所选见证证明存在性",
      "Exists.elim": "利用存在命题的消去规则",
      "Eq.rec": "沿等式进行运输",
      "Eq.ndrec": "沿等式进行运输",
      "And.intro": "合并两个结论",
      "And.left": "取合取命题的第一项",
      "And.right": "取合取命题的第二项",
      "Or.inl": "由左侧命题引入析取",
      "Or.inr": "由右侧命题引入析取",
      "Eq.symm": "利用等式的对称性",
      "Eq.trans": "利用等式的传递性",
      "False.elim": "由矛盾推出结论",
      "Iff.mp": "利用等价命题的正向蕴含",
      "Iff.mpr": "利用等价命题的反向蕴含"
    },
    "aliases": {
      "Eq.symm": [
        "等式对称性"
      ],
      "Eq.trans": [
        "等式传递性"
      ],
      "And.intro": [
        "合取引入"
      ],
      "And.left": [
        "合取左消去"
      ],
      "And.right": [
        "合取右消去"
      ],
      "Eq.mp": [
        "等式运输"
      ],
      "IsCompact.image": [
        "紧集的连续像"
      ],
      "Continuous.comp": [
        "连续映射的复合"
      ],
      "le_trans": [
        "序关系传递性"
      ],
      "Subgroup.mul_mem": [
        "子群乘法封闭性"
      ],
      "map_add": [
        "线性映射加法性"
      ]
    }
  },
  {
    "id": "ja",
    "label": "日本語",
    "words": {
      "assume": "仮定する {name}",
      "introduce": "任意に取る {name}",
      "witness": "証人を取る {name}、型は",
      "let": "局所束縛を導入する {name}",
      "apply": "適用する {name}",
      "obtain": "、したがって",
      "use": "用いる {name}",
      "opaque": "未展開の形式項を保持する",
      "function": "表示された関数",
      "edit": "この推論を編集",
      "hidden": "件の折りたたまれた推論",
      "limited": "（抽出範囲に制限あり）"
    },
    "grammar": {
      "prefix": [],
      "using": [
        "を用いて",
        "を用い"
      ],
      "join": [
        "および",
        "及び"
      ],
      "establish": [
        "示す"
      ],
      "conclude": [
        "結論"
      ],
      "automatic": [
        "自動検索"
      ]
    },
    "schema": 1,
    "rules": {
      "Exists.intro": "選んだ証人によって存在を示す",
      "Exists.elim": "存在命題の消去規則を用いる",
      "Eq.rec": "等式による移送を行う",
      "Eq.ndrec": "等式による移送を行う",
      "And.intro": "二つの結論を連言にまとめる",
      "And.left": "連言の第一項を用いる",
      "And.right": "連言の第二項を用いる",
      "Or.inl": "左側の命題から選言を導く",
      "Or.inr": "右側の命題から選言を導く",
      "Eq.symm": "等式の対称性を用いる",
      "Eq.trans": "等式の推移性を用いる",
      "False.elim": "矛盾から結論を導く",
      "Iff.mp": "同値の順方向を用いる",
      "Iff.mpr": "同値の逆方向を用いる"
    },
    "aliases": {
      "Eq.symm": [
        "等式の対称性"
      ],
      "Eq.trans": [
        "等式の推移性"
      ],
      "And.intro": [
        "連言導入"
      ],
      "And.left": [
        "連言の左消去"
      ],
      "And.right": [
        "連言の右消去"
      ],
      "Eq.mp": [
        "等式による移送"
      ],
      "IsCompact.image": [
        "コンパクト集合の連続像"
      ],
      "Continuous.comp": [
        "連続写像の合成"
      ],
      "le_trans": [
        "順序の推移性"
      ],
      "Subgroup.mul_mem": [
        "部分群の積に関する閉性"
      ],
      "map_add": [
        "線形写像の加法性"
      ]
    }
  }
];
