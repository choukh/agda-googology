# 探针: 2026-11-01 起的新工作

## 目录规则 (2026-11-01 决定, 不再变更)

1. `src/` 只放作者亲手写的成品文章: `Veblen/`, `WellFormed/`, `Bridged/`, `Lower.lagda.md`, `OCF/BTBO.lagda.md`. 任何人不得往 src 添加或改动内容.
2. `probes/` 只放 2026-11-01 确立"交替"总方向之后的新工作. 此前的全部研究材料在 [archive/](../archive/README.md).
3. probes 中的内容达到发布级标准后, 由作者另行发起任务把它整理进 src. 在此之前不动 src.

## 总方向: 交替

依据壁垒定理 (`OCF/Barrier.lagda.md`: 以 Ordᴰ 为精确初始段、含 Ω-共尾元且有有界三歧性的下标类型推出 LPO), 范式 A 今后的路是**交替**:

- 两层结构: 下标层 (有界三歧, 无 top) 做全部派发; 对象层容纳 ℕ-极限与 Ω-共尾对象 (对角 ℕ-极限), 它们只被折叠不被比较; 折叠输出回灌下标层成为新下标, 再开一层.
- 不变量 (逐个设计核对): 凡被比较的两个下标必须在下标层内有公共上界; 对角点之上可比较的子层级只来自 ℕ-阶段序列或 γ-有界的 Ordᴰ 片段.
- 认证: 一个树序数的强度标签, 只有在"树的 FGH 满足表记系统的递归方程"证成之后才算定理; 此前一律标为估计. 现有的全部标签都是估计; BTBO = ψ(Ω_Ω) 已被分支 1 判定为不成立, 估计值为 ψ₀(Ω_ω).
- 分支 (并行): (1) 纸面分析现有 BTBO 的语义: 是 Madore 的 ψ 还是 Buchholz 的 ψ, 是否等于 ψ(Ω_Ω), 此量级两者是否追平; (2) 独立路线 (不必沿用 BTBO 的 `Ord ℓ`) 实现与原版 EBO 基本列逐条一致的树序数, 逐段认证: 下标 1 → 有限下标 → 对角 → 交替, 目标 EBO = ψ₀(Λ).

## 文件

- `OCF/Barrier.lagda.md`: 布劳威尔树壁垒定理 (`--safe --without-K`, 无公理). 由 src 移入 (2026-11-01).
- `OCF/Align/Finite.lagda.md`: EBO 对齐 (一). BTBO 的 `ψ<` 与 Buchholz ψ 的五处差异 (`refl` 核实 ψ₀(Ω₂) 与 ψ₀(Ω₁) 同链); 忠实折叠 `ψᴱ`; ε₀ 片段的对应定理与 FGH 递归方程.
- `OCF/Align/BTBOSemantics.lagda.md`: 分支 1, BTBO 语义的纸面分析. 结论: 一步折叠 `ψ< zero` 就是 Buchholz 基本列的无停滞延拓, 但跨层 `ψ₀` 是 Kovács/Madore 式的"复合 + 对角", 直接折叠把目标层以上的所有层压平 (`ψΩ-flat`, Agda 核实); 极限层的对角从不把 Ω_λ 当常量, 于是 ψⁿ k = ψ₀(Ω_ω) = BO 对一切 k ≥ 2, **BTBO 的估计值是 Buchholz 序数 ψ₀(Ω_ω), 原标签 ψ(Ω_Ω) 不成立** (估计, 置信度分别约 80% 与 90%, 依据见文中表格). 用 `ψᴱ` 重建对角线才得到 ψ₀(Ω_Ω).
- `OCF/Align/EBO.lagda.md`: 记号定义的 EBO (项下标、字典序、`cmpᵀ`、`cof`、Ω-基本列 `fsT↓`、γ-链 `γ↓`、ω-基本列 `fsn↓` 六规则、`Acc`-FGH), 定义与归档版逐字相同, 另加裸值 `fsn`/`fsT`/`γT` 与对齐引理. 这是对齐程序的参照记号.
- `OCF/Align/Translate.lagda.md`: 翻译定理. ℕ-下标镜像表记到 EBO 的翻译 `toE` 与 `cof`/`pred`/`fs`/`fsΩ`/`γ` 逐一交换, 对全部 ℕ 下标无附加条件; `toE` 单射, 像集 `NS` (下标皆为 natT) 对 pred/fsn/fsT/γ 封闭. 与树侧定理合起来就是"树与记号的基本列完全一致"; 目前树侧到下标 ≤ 1, 故合成结果到 Bachmann–Howard 序数.
- `OCF/Align/FiniteAll.lagda.md`: EBO 对齐 (三), 全部有限下标 (极限 ψ₀(Ω_ω)). 树类型仍是 BTBO 的 `Ord (nat n)` (三种候选比较后采用, 见其 §1), 折叠用 Finite 的 `ψᴱ`. 跨层级外延相等 `_≈_ : Ord ℓ₁ → Ord ℓ₂ → Set`, 较低层关系 `R<` 像 `Ord<` 一样对证明递归, PER 的对称传递无条件成立且不需燃料; 对应定理 `corr : ∀ t → Shape t` **无任何前提**, 推论 `Ω-corr`/`FGH-c1`/`FGH-cω`; 六条 EBO 规则逐条相同, 样例含 ψ₂/ψ₃ 的 `fs` 与 EBO 的 `fsn↓` 逐字相同. 与 Translate 合成: 树 ↔ EBO 的基本列在全部 ℕ 下标上完全一致.
- `OCF/Align/BTBOFix.lagda.md`: BTBO 折叠的四行补丁 (injᵇ 链经共尾层直接折叠; ψ₀ 改直接折叠), 在 probes 中完整记录并编译, `refl` 核实 ψ₀(Ω₂) 的链改为经过 ψ₁; 补丁后 BTBOᶠ 估计为扩展 Buchholz 的 ψ₀(Ω_Ω), 仍是估计. 暂不合入 src, 合入时需同步改的文字列在 §5.
- `OCF/Align/Omega1.lagda.md`: 分支 2, 下标 ≤ 1 片段 (到 Bachmann–Howard 序数). 两层严格正树 `O₀ = Tr ⊥ false`, `O₁ = Tr O₀ true`, 忠实折叠 `ψ₁₀`/`ψ₁₁`; 对应定理 `corr₀`/`corr₁` 覆盖四种共尾度, 推论 `FGH-c1`/`FGH-cω`/`Ω-corr`; 与 EBO 的 `fsn↓`/`fsT↓` 在样例上 `refl` 一致.

## 进行中 (2026-11-01 第二轮)

- `OCF/Align/Cumsum.lagda.md`: 研究线, 去掉 `ordᴰ` 的累加填充, 使极限层级的基本列与记号逐项一致 (候选: 结构单调的序列、更弱的极限证据、不同的层号嵌入).

**设计事实 (2026-11-01 实验)**: BTBO 的 IR 技巧 `Ord< i p = Ord₊ i Ord<` 之所以通过终止检查, 是因为 `Ordᴰ` 上的 `<` 就是子项序, 证明 `p : i < ℓ` 的每一步都让层号结构递降. 对任意下标类型与关系 (包括句法记号的字典序 ≺) 照搬会被拒 (`TerminationIssue`, 未应用的递归出现). 所以"以记号项为层号的树族"不能直接定义; 树侧的层号只能是树 (可数层), 记号里的不可数下标 (Ω, Ω_Ω, …) 要通过对角/阶段序列表示. EBO 的可数项的基本列会经过不可数中间项 (例如 ψ₀(ψ_Ω(Ω_{Ω+1})) 的 γ-链在 Ω 层), 这些中间项在树侧必须以对象层的对角对象表示, 这正是交替路线的工作.

## 审核 (与对齐路线无关)

- `Audit/Veblen.lagda.md` (非 `--safe`, 因被审文件用 `--cubical --rewriting`): 逐定义对照标准定义审核 src/Veblen 五篇. 结论: Veblen 各层 (ω^·, ε/ζ/η, 二元到 ω+n 元, SVO, LVO) 没有改变序数值的 bug, 标准基本列规则以 `refl` 核对, 极限位的对角步只改基本列不改值 (纸面论证). 另发现: (1) `src/Lower.lagda.md` 的葛立恒数 `G (suc n) = 3 ↑⟨ n ⟩ 3` 用了下标 n 而非 `G n`, G 1 = 9, 值远小于葛立恒数 (已 Agda 核实; 修复: `3 ↑⟨ G n ⟩ 3`, 公式同改); (2) `Veblen.Transfinitary` 不能被任何模块导入, `REWRITE Φ-ż-α` 局部合流检查失败 (已复现; 修复约 40 行, 删 REWRITE 改用 `subst`, 同 Finitary 的做法); (3) Base 第 693 行散文差一. 全部只记录, 未改 src.

## 检查方式

```sh
agda --library-file=<含 stdlib/cubical 路径的文件> -i src -i probes probes/OCF/Align/Finite.lagda.md
```

`probes/probes.agda-lib` 的搜索路径含 `.` 与 `../src`. 若 `~/.agda/libraries` 指向过期的 Agda 安装, 用 `--library-file` 指定正确的库列表.
