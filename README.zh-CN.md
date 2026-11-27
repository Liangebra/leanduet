<p align="center"><img src="web/logo.svg" width="64" alt="LeanDuet"></p>
<h1 align="center">LeanDuet</h1>
<p align="center"><a href="https://github.com/Liangebra/leanduet/actions/workflows/ci.yml"><img alt="Tests" src="https://img.shields.io/github/actions/workflow/status/Liangebra/leanduet/ci.yml?branch=main&style=flat-square"></a> <a href="LICENSE"><img alt="MIT" src="https://img.shields.io/badge/license-MIT-blue?style=flat-square"></a></p>
<p align="center"><a href="README.md">English</a> · <a href="README.zh-CN.md">简体中文</a> · <a href="README.ja.md">日本語</a></p>

<p align="center">面向数学证明的开源工作台。</p>
<p align="center"><a href="https://liangebra.github.io/leanduet/">在线体验</a> · <a href="docs/RESEARCH.md">研究文档</a> · <a href="https://liangebra.github.io/leanduet/community.html#zh">参与社区</a> · <a href="https://github.com/Liangebra/leanduet/discussions">讨论</a></p>

---

### 安装

需要 Python 3.10+。如需验证证明，请通过 elan 安装 [Lean 4](https://lean-lang.org/install/)。

```sh
git clone https://github.com/Liangebra/leanduet.git
cd leanduet
python server.py
```

打开 [localhost:8765](http://127.0.0.1:8765)。基础编辑器无需 Node.js、数据库或 AI 密钥。

如需使用已有 Lean 或 Mathlib 工程，先构建依赖，再运行：

```sh
python server.py --project /path/to/project
```

在线版是静态演示；类型检查、证明项提取与引理检索需要本地服务。

### 工作台

- 并排阅读数学证明和 Lean 源码，或切换为 Notebook 布局。
- 查看 elaboration 后的证明项、局部假设及其类型。
- 选中推理步骤，检索可用引理，审查并应用经过验证的局部修改。
- 使用受控数学语言组合推理，由 Lean 推断中间命题。
- 同时编辑存在命题的见证和依赖证明。
- 在普通推理行之间编写多个显式析取的嵌套双分支证明；分支假设留在局部作用域，只有共同结论返回上层。
- 本地保存，导出 Lean 文件或工作区；数学叙事支持中、英、日三语。

- 在自由探索区书写猜想、反例与未完成的思路，不必遵循形式语法；按需选取公式进入类型检查。

### 为什么做 LeanDuet？

Lean 验证的是证明项，而非数学叙述。LeanDuet 尝试把数学叙述变成证明结构的可编辑视图，在保证正确性的同时保留作者选择的推理路径。类型推断、引理检索和结构检查由 Lean 完成，AI 不是验证器。

参见 [研究文档](docs/RESEARCH.md)、[TMN](lean/TMN.lean) 与[依赖上下文](lean/Dependent.lean)。

### 当前状态

项目仍处于研究原型阶段，支持受限的单定理文件与受控语言。自由自然语言、任意归纳类型的分情况证明、完整 LSP、宇宙多态导出和源码保留式语义编辑尚未完成。本地服务不是沙箱，只运行可信 Lean 代码。AI 和 Informath 为可选功能，参见[配置](docs/CONFIGURATION.md)。

### 参与贡献

欢迎提供数学证明案例、概念词汇、形式模型、测试或编辑器改进。

[贡献指南](CONTRIBUTING.md) · [新手任务](https://github.com/Liangebra/leanduet/issues?q=is%3Aissue+is%3Aopen+label%3A%22good+first+issue%22) · [路线图](docs/ROADMAP.md)

MIT · 独立项目，非 Lean 或 Mathlib 官方产品。
