# BTBO 直达判据的内部派发与回报

## 派发原文

只做此问答的针对性证明检验。主审纸面推导：B22SourceSlots.Level.Std.named m 在源 a=suc(N.L k)（svs (SV-L k)）可用，因为 forget-toLevel 后 s≼s γ_k≤std(m+1) 即足以 ≤suc std(m+1)；经 Fstep 与 ≺→s≼ 得 suc(γ_{k+1})≤target m。若 target(m)≤K=lim std，取 suc 的真实孩子即可给 γ_{k+1} 找一个实际标准塔；只需这样的 m 在 ℕ 共尾，因为 B21StandardShape.rise 可增大起点。请用临时 QBtboCofinal.agda 编译(i)此 reserve，(ii) target 0≤K 即 γ₂ 真实且全部有限 Ω 层一次获得，(iii) (∀i→Σ m (i≤m × target m≤K))→tr₀ BTBO ≤ read EBOᶜ。若容易把普遍前提与单个 sup lim 关系联起就附带，无须否定。target 宜取 B22SourceSlots.Level.Std.target，避免对 opaque B22TowerDiagonal.target 求展开。另核实能否非循环实填 target0≤K，有见证才报告。你的新文件仅放 <实验目录>（可建自己的子目录）。旧 include <旧依赖目录> ，库 <库表>，agda +RTS -M6G -RTS --library-file=... -W noUnsupportedIndexedMatch -i src -i probes -i <旧> -i <你的实验目录>，按仓库要求安全选项，只跑一个 Agda。写一份简短原始回报到实验目录，且告我核过的具体签名。不要动项目文件、不要提交，不另开大批。

若主定理通过，请加一个有实际用处的等价式再收口：对任意零层 a，a≤K ↔（∀{x}→suc x≤a→Σ j，suc x≤std j）。前向直接析 suc≤lim；反向对 a=0/suc/lim 作结构归纳，suc 用自身，lim 逐支。这样 target0 或 legacy0 截面的每一个后继请求都可选不同实际塔，有具体的搬运攻法而非笼统的『返回』。可只用已有 reverse 表述，勿无限追加。

请确保新 target 与 B22 的同名目标可在外部实际复用：优先直接导出 B22TowerDiagonal.target，用局部 opaque unfolding D.target 实现 reserve；若保留新封装，补两者定义相同的等式。这样可直接把 B22 已证明的 OldHome/Home 或 weak 条件接进来。

若 6G 堆墙持续，把 reserve 单列成模块，以外部不透明的 D.target 作为其他文件的目标，并在 next、terminal₂、walk、btbo-cut 中给 ≼-trans、extract、≼l 的端点写显式参数，尤其 extract {x = N.γ (suc k)}。本轮排程允许加一个小型辅助文件。

收到了。请在保证可编译的前提下顺手精简 Reserve/Cofinal 内明显无用的 import（最好在最终复核之前），复杂链可留局部类型名。最后交稳定文件清单与书面回报。

归档用简报请也留第一条派发原文与追加任务回报（本机目录用占位符），主审会把临时目录里的 task.md 和最终回报纳入专题文档。

Value.≼lim⁻ 已有后继进入极限的抽取。若还在精简，SuccessorCut.take 可直接用 ≼lim⁻ (≼-trans request bound)。已有的泛化 Schedule 看起来对。

## 子智能体书面回报

# 共尾标准塔回接 BTBO 的定点检验

已编译的第 4 层条件定理。令 `std n` 为 W4 第 n 座标准塔的读值，`K = lim std`，`target` 直接复用 `B22TowerDiagonal.target`。若对每个起点 i 都有 m ≥ i 满足 target(m) ≼ K，则 BTBO 参照树的读值 ≼ K ≼ W4 的 EBO 闭项读值。整条推导构造性，无排中律、选择公理或函数外延。W4 的闭项、折叠、证书沿用原定义。

| 文件与定理 | 通过 Agda 的陈述 |
| --- | --- |
| QBtboReserve.reserve | ∀ m k，γ(k) ≼ std(m+1) → suc(γ(k+1)) ≼ target(m) |
| QBtboCofinal.second | target(0) ≼ K → Σ j，γ(2) ≼ std(j+1) |
| QBtboCofinal.finite-together | target(0) ≼ K → Σ j，∀ k，ψ₀(Ω_k) ≼ std(j+1) |
| QBtboCofinal.terminal₂ | target(0) ≼ K → γ(2) ≼ read(EBOᶜ) |
| QBtboCofinal.from-home | B22TowerDiagonal.Home → Cofinal |
| QBtboCofinal.btbo-cut、btbo | Cofinal → tr₀(BTBO) ≼ K；Cofinal → tr₀(BTBO) ≼ read(EBOᶜ) |
| QBtboSuccessorCut.criterion | 对任意零层树 a，a ≼ K 当且仅当任一 suc(x) ≼ a 都给出一个 j，使 suc(x) ≼ std(j) |

`Cofinal = ∀ i → Σ m ((i ≤ m) × (target(m) ≼ K))`。reserve 将命名槽用于合法源 suc(Lₖ)，用 forget-toLevel、Fstep 得到下一行还多出的一个后继。这一后继进入 K 后可析出一座实际塔。严格递增的标准塔允许把当下起点 i 增大至有回接的 m。原有 γ(1) ≼ std(1) 提供起步，当 m=0 有一次回接，全部有限 Ω 层便已有同一座塔作上界。

尚无本次核到的闭见证 `target(0) ≼ K` 或 `Cofinal`。B22 的闭结果 `enters-old` 给出 target(m) ≼ legacy(m)。要由它完成 m=0 的回接，仍须证明 legacy(0) ≼ K，或直接对 target(0) 的每个后继请求找到真实塔。判据 criterion 允许不同请求选择不同的塔。旧 Home 假设对所有 m 提供一个容纳整个目标的真实塔，可经 from-home 接入；本次没有实填 Home。

纸面补充：Cofinal 亦可写为存在函数 f，满足 i ≤ f(i) 且 lim(λ i → target(f i)) ≼ K。正向逐点取 Σ 见证并用 l≼，反向把每个孩子经 ≼l 嵌入这个极限。不用选择公理；此等价式未另立 Agda 声明。

编译使用仓库约定的安全选项与 6G 堆。具体闭项上直接编写调度轮次曾耗尽 6G，改将塔、行、目标作函数参数，在抽象调度证明检查完后一次性实例化。最终三份源码均过检。禁用构造扫描无命中。归档保留三份 QBtbo 源码、task.md 及本回报。
