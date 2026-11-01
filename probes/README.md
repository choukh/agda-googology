# 探针: 2026-11-01 起的新工作

## 目录规则 (2026-11-01 决定, 不再变更)

1. `src/` 只放作者亲手写的成品文章: `Veblen/`, `WellFormed/`, `Bridged/`, `Lower.lagda.md`, `OCF/BTBO.lagda.md`. 任何人不得往 src 添加或改动内容.
2. `probes/` 只放 2026-11-01 确立"交替"总方向之后的新工作. 此前的全部研究材料在 [archive/](../archive/README.md).
3. probes 中的内容达到发布级标准后, 由作者另行发起任务把它整理进 src. 在此之前不动 src.

## 总方向: 交替

依据壁垒定理 (`OCF/Barrier.lagda.md`: 以 Ordᴰ 为精确初始段、含 Ω-共尾元且有有界三歧性的下标类型推出 LPO), 范式 A 今后的路是**交替**:

- 两层结构: 下标层 (有界三歧, 无 top) 做全部派发; 对象层容纳 ℕ-极限与 Ω-共尾对象 (对角 ℕ-极限), 它们只被折叠不被比较; 折叠输出回灌下标层成为新下标, 再开一层.
- 不变量 (逐个设计核对): 凡被比较的两个下标必须在下标层内有公共上界; 对角点之上可比较的子层级只来自 ℕ-阶段序列或 γ-有界的 Ordᴰ 片段.
- 认证: 一个树序数的强度标签, 只有在"树的 FGH 满足表记系统的递归方程"证成之后才算定理; 此前一律标为估计. 现有的全部标签 (含 BTBO = ψ(Ω_Ω)) 都是估计.
- 分支 (并行): (1) 纸面分析现有 BTBO 的语义: 是 Madore 的 ψ 还是 Buchholz 的 ψ, 是否等于 ψ(Ω_Ω), 此量级两者是否追平; (2) 独立路线 (不必沿用 BTBO 的 `Ord ℓ`) 实现与原版 EBO 基本列逐条一致的树序数, 逐段认证: 下标 1 → 有限下标 → 对角 → 交替, 目标 EBO = ψ₀(Λ).

## 文件

- `OCF/Barrier.lagda.md`: 布劳威尔树壁垒定理 (`--safe --without-K`, 无公理). 由 src 移入 (2026-11-01).
- `OCF/Align/Finite.lagda.md`: EBO 对齐 (一). BTBO 的 `ψ<` 与 Buchholz ψ 的五处差异 (`refl` 核实 ψ₀(Ω₂) 与 ψ₀(Ω₁) 同链); 忠实折叠 `ψᴱ`; ε₀ 片段的对应定理与 FGH 递归方程.
- `OCF/Align/BTBOSemantics.lagda.md`: 分支 1, BTBO 语义的纸面分析 (进行中).
- `OCF/Align/Omega1.lagda.md`: 分支 2, 下标 1 片段 (进行中).
- `OCF/Notation/`: 旧的 EBO 表记探针, 作为分支 2 的规则参照暂留, 分支完成后归档.

## 检查方式

```sh
agda --library-file=<含 stdlib/cubical 路径的文件> -i src -i probes probes/OCF/Align/Finite.lagda.md
```

`probes/probes.agda-lib` 的搜索路径含 `.` 与 `../src`. 若 `~/.agda/libraries` 指向过期的 Agda 安装, 用 `--library-file` 指定正确的库列表.
