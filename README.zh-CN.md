<p align="center"><img src="web/logo.svg" width="92" alt="LeanDuet 标志"></p>

# LeanDuet — 两种语言，同一个证明

[English](README.md) · **简体中文** · [日本語](README.ja.md) · [在线体验](https://liangebra.github.io/leanduet/) · [项目介绍](https://liangebra.github.io/leanduet/about.html#zh)

LeanDuet 是一个面向数学家的实验性开源证明工作台。我们的目标不是简单地让 AI 翻译 Lean 代码，而是以依赖类型论为共同语义基础，将传统数学证明和 Lean 4 证明组织为可阅读、可编辑、可验证的关联表示。

## 现在可以做什么

- 在数学阅读视图与 Lean 源码之间定位、编辑和同步证明步骤；支持本地草稿、导入导出、深浅主题。
- 使用本地 Lean 提取真实证明项、推理类型、作用域和见证，生成类型驱动的数学叙事。
- 按目标类型或受控数学概念检索库定理；局部证明候选需通过类型检查、独立编译及结构保真检查。
- 修改存在命题的见证及对应证明义务；支持受控多步推理文本的候选编译。
- 使用已构建的兼容 Mathlib 项目；真实拓扑学案例 `IsCompact.image` 已通过独立集成测试。

## 快速开始

需要 Python 3.10+；如需验证证明，请通过 [elan](https://lean-lang.org/install/) 安装 Lean。基础工作台不需要 AI 密钥。

```sh
git clone https://github.com/Liangebra/leanduet.git
cd leanduet
python server.py
```

浏览器打开 <http://127.0.0.1:8765>。使用已构建的 Lean 项目时：

```sh
python server.py --project /absolute/path/to/project
```

[在线体验](https://liangebra.github.io/leanduet/) 仅提供静态编辑界面，不运行 Lean、Mathlib 或 AI 后端。完整功能须在本地启动服务。

## 数学研究路线

以带类型的叙事数据、局部上下文、依赖量词、等式运输和部分双向变换为基础，探索组合数学语义及结构保持的证明编辑。参见 [TMN](lean/TMN.lean)、[依赖类型模型](lean/Dependent.lean)、[研究文档](docs/RESEARCH.md)。

目前仍是研究原型：仅支持受限的单定理文件；自然语言是受控语法，不是任意中文、英文或日文；类型化编辑尚不覆盖所有宇宙多态定理，也不能保证保留原 tactic 排版。运行可信 Lean 代码，本地服务不是安全沙箱。Informath 外部运行时尚未完成实际联调。

## 共同建设

欢迎数学、形式化证明、程序语言和界面设计方向的贡献者。无需编写应用代码也可以贡献数学证明案例、数学概念词典和翻译。

[参与贡献](CONTRIBUTING.md) · [新手任务](https://github.com/Liangebra/leanduet/issues?q=is%3Aissue+is%3Aopen+label%3A%22good+first+issue%22) · [讨论区](https://github.com/Liangebra/leanduet/discussions) · [开发路线](docs/ROADMAP.md)

MIT 许可证。独立社区项目，非 Lean 或 Mathlib 官方产品。
