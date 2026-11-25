# Leaf 与 Lift 全域（数学，结构律） (YiLL)：简报原文（外部模型，留档）

| 项 | 内容 |
|---|---|
| 派发 | 作者 2026-11-14 选第四十七批；外部模型，作者转发 |
| 前缀 | `YiLL` |
| 回报 | 2026-11-14 已返回并复核，见文末 |

## 简报原文（本机路径换成占位）

### 任务简报：Leaf 与 Lift 全域（数学，结构律）（前缀 YiLL）

你在 Agda 研究仓库 `<仓库>` 上工作。全程用中文。**先读 `AGENTS.md`，以及 `probes/Survey/EBOHandbook.md` 第 4 节（堆墙与工程）。** 主审会从头冷编复核你交的每个文件，只认编译过的定理。

#### 作者的决定与原则（2026-11-14，选项原文或原话）
- 作者："外部模型额度很充足，我们可以多线并行"。本路是第四十七批五路之一（选项原文 "Leaf 与 Lift 全域 (Recommended)"），与在跑的 YiPJ、YiNX、YiXV 以及本批其余各路在数学上互不依赖。
- 主线：精简块 `YiRW*` 加最小比较表，即折叠 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（都在 `probes/OCF/Lean/`）。
- **上一批的关键结果**（主审复核过）：`YiGIEnd.eboᵍ : (lf : Leaf) (li : Lift) (lk : LowKeep) (ex : Assembly.ExitCondition lf li lk) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`，即实际主线上 "三条全域律加全塔出口条件 ⇒ 终点 ≥ EBO"。三条律是 `YiAbsGIface` 的 `Laws` 在实例 `YiGIInst.gradedᵍ`、`domsᵍ` 上的命题，关系族在 `YiGIRel`（`R`、`Low`、`Nu`、`Rd`）。回报 `probes/Survey/Reports-2026-11-12/YiGI.md`。
- 原则："不能以'追求同步'为名反过来指导树的定义形状. '不同步'的解法应该靠外部的定理证明/外部发展的理论"；"第 4 层不反过来改前 3 层"（AGENTS）。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

#### 背景（主审复核过的编译事实）
- **要证的律**（`YiAbsGIface` 第 154–155 行，逐字）：
  ```agda
  Leaf = ∀ {ℓ ν} → Rd ℓ ν → R ℓ (Ωr ν) (Ωt ℓ)
  Lift = ∀ {k s x} → Gl k x → R k s x → Rd (lift k x) s
  ```
  实例：`YiGIInst.gradedᵍ`、`domsᵍ`（`Gl` 等量化域在 `domsᵍ` 里）；关系族 `YiGIRel`。
- **读法**：`Rd ℓ = Cl (Hd ℓ)`；`Cl` 的构造子 `c0`、`ca`、`cL`、`cc`；`Hd zero ν = ⊥`，`Hd (nd s h) ν` = 某个孩子的读法，或 `ShR s h ν`；`ShR sS`（后继：`cof ν ≡ c1` 且孩子读 `pred ν`），`ShR sL = ⊥`，`ShR (sΩ k)`（`cof ν ≡ cΩ κ`，`Rd k κ`，且对一切 `R k η c` 的 c，`Rd (h c) (fsT ν η)`）。
- **已有实例**：`YiGICheck.rd-fin`、`leaf-fin`（一切有限读回层号）、`lift-start`（k = 0，x = `Ωt zero`，下标 1）。
- F2 上以前证过的同类律（先检索，能搬就搬）：`YiDCRel` 的 `leafᴰ`，`YiMH*`、`YiHC*` 里的 leaf 一类。
- AGENTS "量化域先取带证据的读回域"：若 `Lift` 在 `Gl` 允许的退化树上不成立，读作 "谓词太宽"，交反例并说出龙骨实际用到的最窄量化域。

#### 要做的（按序）
0. **最小实例检查**，在临时目录：`Leaf` 在一个 Ω 形状层号（如 `nd (sΩ (fn 1)) h`）上、经 `ShR (sΩ k)` 的一个读法推导；`Lift` 在 k = `zero`、x 为 ω 与 ω+1 两棵树上。确认类型正确、前提可满足。不成立就停下回报。
1. **Leaf 全域**：对 `Rd` 推导归纳（`c0`、`ca`、`cL`、`cc` 与 `Hd` 各情形），对一切层号证完。
2. **Lift**：先 k = `zero`（孩子是可数树，读回层号 `↑ zero x` 只有后继与 ℕ 极限形状），再一般的 k（x 含 Ω 结点与 `up` 结点）。
3. 某一情形不成立时交编译的反例，或第一条挡住的引理。

**纪律**（作者同意的，必须照做）：动手证一般形式之前，先用临时文件检查前提可满足；已有引理先检索再写，不重证，搬来的证明在文首写明来源；若某一步要改树、折叠或合法性的定义，停下回报；停止条件触发时先停下回报，改题只能写成建议。

#### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiLL`（模块名 `OCF.Lean.YiLL…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰并行各路的前缀（`YiPJ`、`YiNX`、`YiXV`、`YiLK`、`YiFM`、`YiPC`、`YiVW`）。验收文件，文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行，代码之间只写范围与不显然的理由。一次性的试验放临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库的 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要自己写上前三个，否则导入仓库模块报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（包括临时目录与日志路径，写 `<实验目录>`）。
- **库文件**：在你自己的临时目录（仓库外）建一个文件 `libraries`，内容两行：
  ```
  <库目录>
  <库目录>
  ```
- **编译**，在仓库根目录：
  `agda +RTS -M5G -RTS --library-file=<你的临时目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 在临时目录编译纯 `.agda` 时另加 `-l standard-library` 与 `-i <你的临时目录>`。
  - **堆上限 5G**：同时有八路在编译，机器共 64G。若某个文件确实要超过 5G，先在回报里说明，不要擅自加大。同时只跑一个 agda。
  - 不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下），写字面路径。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`，是就是库文件的问题）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。报退出码时不要经过管道。
  - 堆墙：不要在具体推导上直接比较两个读回；具体参照树放 `opaque`；经非单射的头求解的隐式参数显式写出。
- 不在你的临时目录与你前缀的新文件之外删除或移动任何东西，不 `pkill`，不装包，不提交，不推送。不改 `probes/README.md`、`probes/LOG.md`、台账与留档（这些由主审更新；回报交给作者转回）。
- 查签名用检索（`grep`），不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；5G 仍耗尽（先在回报里说明）；第 0 步不成立。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0。

#### 回报格式（回报交给作者转回主审）
1. 判决：先说对纲领与目标意味着什么；第 0 步；各步到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码、内存（`+RTS -s` 的数）。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。



## 本会话主审复核（2026-11-14）

1 件、33 同口径代码行；主审删自身接口、5G 独立冷编 0，仅自身 Checking，源码哈希与回报一致。禁用构造、洞、本机路径、Funext 0。实际 Gl zero x 要求 x 字面为树 1；两条 noGl 否定指定 ω 与 ω+1 的该前提，r-ω₀/r-ω₀+1 与 gl-one 给非空对照，不是否定 Leaf/Lift。按第 0 步不成立即停止，Leaf 的 Ω 形状实例与两全域律均未进入。主审已将“改用实际 Gl 允许的 Ω 树作最小检查，原全域任务不变”作为具体修订向作者询问，等待答复；未自行续派。

## 回报原文（本会话执行）

YiLL 完整回报（2026-11-14；源码冻结，回报定稿）

1. 判决与范围

本路发现的是简报最小样例与实际验收接口的量化域不符；没有改变树、折叠、合法性或共享接口，没有得到新的序数值界。全域 Leaf 与 Lift 均未证明，也均未否定。按简报第 0 步停止条件暂停，后续工作没有展开。

实际 `YiGIInst.domsᵍ`（第 46–49 行）逐字定义：

```agda
Gl = λ k x → x ≡ proj₁ (O.Ωt k)
```

`YiRWOps.Ωt zero = suc zero , ◃s`。因此零层 `Gl` 仅接受字面树 1。指定的 ω 树 `ω₀ = lim nat₀ (λ n → ◃s)` 与它的后继 `ω₀+1` 均是类型正确的树，均有 `GR.R zero (E.natT 1)` 的闭推导，但它们各自的 `Gl` 前提都推出空类型。失败不在 R，也不是合法树的退化反例；在任何参照下标 s 上都不能同时满足这两个样例的 Lift 前提。

`gl-one` 给出实际 Gl 域非空的对照。`gl-exact` 对任意 k 直接读出实际 Gl 要求的等式。龙骨实际要求的对象为 `proj₁ (O.Ωt (tw n))`，对应 `YiGIInst.keelᵍ.gl` 的字面等式证据；这与“先在零层任意可数树上证明 Lift”的范围不同。此处没有建议扩大 Gl。

第 0 步：临时纯 Agda 文件在开工后 30 分钟内编译，退出码 0；前提可满足性检查得到上述两个否定。由于先验检查已确定指定 Lift 样例不成立，Leaf 的 Ω 形状 / ShR 样例未构造。第 1 步与第 2 步未进入。停止后仅将已编译的前提检查整理为仓库验收文件，并完成冷编与审计。

| 问题 | 位置 | 档 |
|---|---|---|
| ω 与 ω+1 是否属于实际 Gl 零层量化域 | YiLLPrem.noGl-ω₀、noGl-ω₀+1 | 编译定理：均不属于 |
| 两棵样例树是否合法、R 前提是否非空 | YiLLPrem.ω₀、ω₀+1、r-ω₀、r-ω₀+1 | 编译构造 / 编译定理 |
| 实际 Gl 域是否非空 | YiLLPrem.gl-one | 编译闭项 |
| Leaf 的 Ω 形状最小实例、Leaf 全域 | 简报第 0、1 步 | 未进入；无结论 |
| 实际量化域上的 Lift 全域 | 简报第 2 步 | 未进入；无结论 |
| 后续按实际 Gl 域重拟最小检查 | 建议：固定 x = Ωt k，再做 Leaf Ω 形状检查 | 判断 / 建议，未执行 |

没有有限样本测试被当作全域证明。本次只有上述精确陈述的编译结果。

2. 文件、编译与内存

代码行口径：Agda 代码围栏内包括空行；另列非空代码行。临时文件全部为 Agda，计法相同。最大驻留与总使用内存均取 `+RTS -s`，不称为操作系统 RSS。

| 文件 | 总行 / 代码行 / 非空代码行 | 删自身接口冷编退出码 | 最大驻留字节 | RTS 总使用内存 | 冷编耗时 |
|---|---:|---:|---:|---:|---:|
| probes/OCF/Lean/YiLLPrem.lagda.md | 49 / 42 / 33 | 0 | 1,515,007,848 | 2477 MiB | 16.493 s |
| <实验目录>/YiLLPrem.agda | 42 / 42 / 33 | 0 | 1,369,856,744 | 2332 MiB | 15.163 s |

仓库源文件 SHA-256：`3d43eee03c5471056cc74c343af1c71f67c46096a97983fba91304a704a3cc16`。
临时源文件 SHA-256：`005b6c94885302fcb65691be4b14e77778a88ed0be892b083a13bb21fa387ed6`。

全部编译串行运行，每次堆上限 5G；无 --ignore-interfaces。冷编只删除以下两个自身接口（各自在编译前删除）：

- probes/_build/2.8.0.2/agda/OCF/Lean/YiLLPrem.agdai
- <实验目录>/YiLLPrem.agdai

仓库冷编命令（从仓库根目录运行，直接保存和读取退出码，无管道）：

```sh
agda +RTS -M5G -s -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/YiLLPrem.lagda.md > <实验目录>/YiLLPrem-cold.log 2>&1
```

临时文件命令另加 `-l standard-library -i <实验目录>`。仓库冷编日志只有 `Checking OCF.Lean.YiLLPrem`，临时冷编日志只有 `Checking YiLLPrem`；均未重新检查共享依赖。

全部源码与实验目录：

- 仓库新源码：probes/OCF/Lean/YiLLPrem.lagda.md（唯一仓库写入）
- 私有实验目录：<实验目录>
- 临时源码：<实验目录>/YiLLPrem.agda
- 库文件：<实验目录>/libraries
- 初次临时编译日志：<实验目录>/YiLLPrem.log，退出码 0
- 初次仓库编译日志：<实验目录>/YiLLPrem-repo-initial.log，退出码 0
- 仓库冷编日志：<实验目录>/YiLLPrem-cold.log
- 仓库冷编退出码：<实验目录>/YiLLPrem-cold.exit（0）
- 临时冷编日志：<实验目录>/YiLLPrem-temp-cold.log
- 临时冷编退出码：<实验目录>/YiLLPrem-temp-cold.exit（0）
- 审计输出：<实验目录>/audit.txt
- 编译产物：上述两个自身 .agdai
- 完整回报：<回报原文>

3. 构造与定理表

下列名字均在 `probes/OCF/Lean/YiLLPrem.lagda.md`；`Gl` 为 `Doms domsᵍ.Gl`，没有另设谓词。陈述逐字如下。

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| nat₀ | `nat₀ : ℕ → Tr zero` | 零层有限后继树 | 编译构造 |
| ω₀ | `ω₀ : Tr zero` | 以 nat₀ n 为分支、相邻一步为 ◃s 的 ℕ 极限树 | 编译闭项 |
| ω₀+1 | `ω₀+1 : Tr zero` | ω₀ 的后继 | 编译闭项 |
| r-ω₀ | `r-ω₀ : GR.R zero (E.natT 1) ω₀` | ω₀ 上 R 前提非空 | 编译定理 |
| r-ω₀+1 | `r-ω₀+1 : GR.R zero (E.natT 1) ω₀+1` | ω₀+1 上 R 前提非空 | 编译定理 |
| noGl-ω₀ | `noGl-ω₀ : Gl zero ω₀ → ⊥` | ω₀ 不能满足实际 Gl | 编译否定定理 |
| noGl-ω₀+1 | `noGl-ω₀+1 : Gl zero ω₀+1 → ⊥` | ω₀+1 不能满足实际 Gl | 编译否定定理 |
| gl-one | `gl-one : Gl zero (suc zero)` | 实际零层 Gl 有闭实例 1 | 编译闭项 |
| gl-exact | `gl-exact : ∀ k (x : Tr k) → Gl k x → x ≡ proj₁ (O.Ωt k)` | 实际 Gl 已经要求输入就是该层 Ω 树 | 编译定理 |

`r-ω₀` 直接用 H.m1、H.mz、H.mw 构造；`r-ω₀+1` 再沿后继一步放宽。两个 noGl 定理用构造子不相交；它们不以 Leaf、Lift 或不可满足的辅助假设为前提。没有新增序数值比较定理，也没有宣称更高强度。

4. 第一个障碍

精确阻断的是构造 `gω : Doms.Gl domsᵍ zero ω₀`（以及 ω₀+1 对应项）；`noGl-ω₀`（第 38 行）编译证明其不可能。其目标归约成 `lim nat₀ … ≡ suc zero`；第二个目标归约成 `suc (lim nat₀ …) ≡ suc zero`。这是最小前提不成立，不是 Agda 停机、内存、隐式参数或 R 的障碍。

5. 偏离、事故与引用范围

- 最小前提检查先读取并核实实际 Gl，再检查指定的两个 Lift 样例；没有先写一般形式。发现并编译前提否定后即按第 0 步停止，没有继续做 Leaf 的 Ω 形状实例或任一全域律。
- 没有改题、改量化域、改前三层定义；没有同处两次重设计；没有编译失败、堆耗尽或超时。
- 完整读了派发简报、AGENTS.md 和 EBOHandbook §4。按关键词查阅 YiGIRel、YiGIInst、YiGIBlock、YiAbsGIface、YiGICheck 的相关定义；先检索了 YiDCRel.leafᴰ、YiMH* 与 YiHC* 的 leaf 类结论，未搬用这些 leaf 证明。数学证明直接使用现有构造子，不重证已有通用引理。
- 简报转述的 YiGIEnd.eboᵍ 与既有各路主审复核状态没有在本路独立冷编，未作为新定理的证明依据。YiPJ、YiNX 只检索/查看了局部相关内容，没有依赖其结果，没有修改其源码。没有使用外部资料或模型审查。
- 仓库源码禁用构造检索 0 命中、本机路径检索 0 命中，详见 audit.txt；没有公设、洞、停机/正性绕过、K、函数外延或额外选项。临时文件显式补齐了导入所需的库选项。
- 仅新建自身前缀源码与私有实验文件，未改任何旧文件、导航、台账或留档；没有派子路、装包、提交或推送。

源码已冻结；本回报已定稿。主审可按所列命令独立删除 YiLLPrem 自身接口后冷编复核。

## 主审对第 0 步的更正（2026-11-14，经作者转发）

执行方问："YiLL 的最小样例与实际 Gl 冲突，且简报规定“不成立就停下回报”。是否改用 Gl 实际允许的 Ω 树作最小检查（零层取树 1），继续原来的全域 Leaf/Lift 任务？" 主审核对：主线实例里 `Gl = λ k x → x ≡ proj₁ (O.Ωt k)`（`YiGIInst` 第 49 行），`Lift` 只对每层的 Ω 树陈述。简报第 0 步给的样例（k = `zero`，x 为 ω 与 ω+1）不满足 `Gl`，是主审写错样例，不是数学障碍。答复：选 1，改用 `Gl` 允许的树作最小检查（k = `zero` 时 x = `Ωt zero`；另取一个有限层号与一个 Ω 形状层号的 Ω 树），继续全域 `Leaf` 与 `Lift`。简报第 2 步 "一般的 k（x 含 Ω 结点与 `up` 结点）" 同样读作 x = `Ωt k`。


## 作者修订与续派（2026-11-14）

作者选择“修正样例并继续（推荐）”。最小检查改用实际 Gl 允许的 Ω 树，零层取树 1；原全域 Leaf/Lift 目标、共享接口、树与折叠均不变。原 YiLLPrem 冻结、原回报保留；同一任务已恢复，续作结果待独立复核。


## 续作主审复核（2026-11-14）

新增 Check 83 行、LeafNeg 143 行，原 Prem 33 行保持不变，合计 3 件、259 同口径代码行。主审对新增两件删自身接口、5G 冷编均 0，仅自身 Checking；原 Prem 哈希与前次已冷编版本相同。禁用构造、洞、本机路径、Funext 0。已读全部源码与续作完整回报。read0 覆盖所有零层带 mc 推导，leafC 在 NoΩ 层全称成立，Ω 形状 ShR/Leaf 实例已实填。noLeaf/noLeafOk 精确否定当前实例的全域 Leaf；反例 Ok/Rd/被测试分支 R 均有闭项，bound 是 R 接受参照的句法界，不是树的序数值上界。当前 eboᵍ 四项条件不能同时满足；规范塔域与一般 Lift 没有被否定。

## 续作回报原文（本会话执行）

YiLL 完整回报（续作后整体定稿；2026-11-14）

1. 判决：对纲领、目标与各步意味着什么

编译否定定理：实际 `YiGIInst.gradedᵍ`、`domsᵍ` 上的全域 `Leaf` 不成立，`YiLLLeafNeg.noLeaf : Leaf → ⊥`。即使增加层号通过 `YiRWPath.Ok` 的前提，仍被 `noLeafOk` 否定。这说明当前全域验收律覆盖了不能满足它的层号；不是对规范塔域、主线终点值或树自足目标的否定。

因此，既有 `YiGIEnd.eboᵍ` 所要求的这份全域 Leaf 前提不能在当前实例上实填。本路没有改树、折叠、合法性、Gl 或共享接口，没有给出新的 ψ₀(Ω_x) 下界或上界。若继续用分级验收，需另立规范读回域上的外部命题或发展其他外部关系理论；这仅是建议，未实施。本路不声称已确定反例是否属于任何规范塔读回域。

作者续作授权已落实：早期错误样例从零层的 ω、ω+1 修正为实际 Ω 树 1；`YiLLPrem` 源码保持冻结，早期回报原样保存在 `YiLL-report-initial.md`。

第 0 步完成，且不是具名假设：

- `YiLLCheck.shΩ` 是真正的 `ShR (sΩ zero)` 闭推导，孩子函数为 `hΩ c = zero ⊕ ↑ zero c`；`rdΩ` 读作 Ω₁；`leafΩ` 的结论是该层 Ω 树与参照 Ω_{Ω₁} 的 R 关系。取下标层 k = zero；简报中的 k = fn 1 仅为“如”所列例子，本实例仍为 Ω 形状。
- `gl0`、`rd0` 与既有 `startᴿ` 给出实际零层 Ω 树 1 的 Gl、R、读回实例。
- 为填 ShR 对所有低层 R 推导量化的分支前提，先证了 `read0`：所有零层 R 推导均能读回层号，不附加出口条件、标准形或有限性假设。
- 为填 Ω 形状样例的 Leaf 结论，证明 `leafC`：所有不含 Ω 形状的层号上 Leaf 成立。`NoΩ`、`NoΩ↑` 直接引用现有文件；该条件有 zero 与所有 `zero ⊕ ↑ zero c` 的实例。

第 1 步在 Ω 形状“从任意孩子继承读法”一行得到编译反例，触发原简报停止条件。第 2 步一般 Lift 未进入；辅助定理 read0 已覆盖所有零层输入树上的读回命题，但不把它称为全域 Lift。

反例的闭对象和结论分开：

```agda
h zero = zero
h (suc zero) = fn 1
h (suc (suc x)) = zero
h (suc (lim f a)) = zero
h (lim f a) = zero
ℓ = nd (sΩ zero) h
β = proj₁ (O.Ωt ℓ)
```

`ok : P.Ok ℓ` 与 `rd : GR.Rd ℓ (E.natT 1)` 都是闭项。rd 来自孩子树 1 的有限读法，属于 Hd 的孩子继承分支，而不是 ShR 分支。其欲填 Leaf 结论被 `not-leaf-instance : GR.R ℓ (E.Ωt (E.natT 1)) β → ⊥` 否定。

反例的证明机制：根的第一分支与孩子树 2 对应的分支都嵌入零层树 1；R 结点规则却必须检查所有被低层 R 关联的分支。孩子树 2 有 `r2 : GR.R zero (E.natT 2) c2`，并非空守卫。任意 Ω 共尾参照项的 Ω 基本列在下标 2 处严格高于 1（fsT-big），而该分支只能接受不高于 1 的参照项。`Small`、`small-down` 与 `bound` 同时处理第一位置放宽与 mc 向下封闭，所得 bound 覆盖所有 R 推导，不是对若干推导的枚举。

bound 给的是 R 所接受参照项的句法界，不能把它读成 β 的独立序数值上界或关系完备性结论。因而本路的否定精确限于验收律；没有以“读法偏低”为由否定主线树。

| 问题 | 位置 | 档 |
|---|---|---|
| 修正后的最小前提是否可满足 | YiLLCheck.shΩ、rdΩ、leafΩ、gl0、rd0 | 编译闭项 / 编译定理 |
| 无 Ω 形状的层号上的 Leaf | YiLLCheck.leafC | 编译全称定理，带 NoΩ 条件 |
| 所有零层 R 推导的读回 | YiLLCheck.read0 | 编译全称定理，无附加条件 |
| 实际实例上的全域 Leaf | YiLLLeafNeg.noLeaf | 编译否定定理 |
| 仅限通过 Ok 的层号是否足够 | YiLLLeafNeg.noLeafOk | 编译否定定理：不足 |
| 规范塔读回域上的 Leaf、一般 Lift | 未进入 | 没有结论，未否定 |
| 下一步改成规范读回域的外部验收命题 | 未执行 | 判断 / 建议 |

没有有限测试被当作全称证明。没有把具名未证假设计为已填的律。

2. 文件、冷编与内存

每次 Agda 均带 `+RTS -M5G -s -RTS`，全程单个 Agda；编译日志落私有目录，没有经过管道取退出码。代码行是围栏内包含空行的行数，括号中为非空代码行。内存为 RTS 的 maximum residency 与 total memory in use，不是操作系统 RSS。

| 仓库源码 | 总行 / 代码行（非空） | 删自身接口冷编退出码 | 最大驻留字节 | RTS 总使用内存 | 耗时 |
|---|---:|---:|---:|---:|---:|
| probes/OCF/Lean/YiLLPrem.lagda.md | 49 / 42（33） | 0 | 1,515,007,848 | 2477 MiB | 15.772 s |
| probes/OCF/Lean/YiLLCheck.lagda.md | 105 / 98（83） | 0 | 1,455,248,376 | 2386 MiB | 16.824 s |
| probes/OCF/Lean/YiLLLeafNeg.lagda.md | 178 / 171（143） | 0 | 1,462,790,840 | 2451 MiB | 17.225 s |

三个仓库文件均逐件删掉其字面路径的自身接口后冷编；依赖用共享热接口。日志中各自只有本模块的 Checking 行。没有 --ignore-interfaces，也未删除其他前缀的接口。

临时源码 YiLLStart.agda 也删自身接口冷编通过：退出码 0，最大驻留 1,457,806,392 字节。

临时源码 YiLLNeg.agda 也删自身接口冷编通过：退出码 0，最大驻留 1,401,358,296 字节。

仓库源码 SHA-256（YiLLPrem 与早期回报时完全一致）：

- `probes/OCF/Lean/YiLLPrem.lagda.md`：`3d43eee03c5471056cc74c343af1c71f67c46096a97983fba91304a704a3cc16`
- `probes/OCF/Lean/YiLLCheck.lagda.md`：`c5117c14a99d138b0203fc505a6f5fa60db8b2bf7c4611f57b2d863da8cb43de`
- `probes/OCF/Lean/YiLLLeafNeg.lagda.md`：`848a98c5c2a6ae2ab4b056166654197ef7f65f6fe39d232a26e30ab9c7957e77`

复核命令从仓库根目录运行：

```sh
agda +RTS -M5G -s -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/YiLLLeafNeg.lagda.md > <实验目录>/YiLLLeafNeg-review.log 2>&1
```

将文件名换成 YiLLPrem 或 YiLLCheck 可复核另外两件。复核前仅删对应的 `probes/_build/2.8.0.2/agda/OCF/Lean/<本模块>.agdai`。仓库内所有源码没有本机路径。

3. 定理表（关键陈述逐字）

下表全是编译结果；构造与条件定理另列。所有名字限定在所列文件内。Leaf 是 Laws gradedᵍ domsᵍ 的实际类型，未改实例。

| 名字 | 逐字陈述 | 白话 | 文件 / 档 |
|---|---|---|---|
| read0 | `read0 : ∀ {ν c} → GR.R zero ν c → GR.Rd (↑ zero c) ν` | 任意零层 R 推导给读回 | YiLLCheck / 全称定理 |
| leafC | `leafC : (ℓ : L) → NoΩ ℓ → ∀ {ν} → GR.Rd ℓ ν → GR.R ℓ (E.Ωt ν) (proj₁ (O.Ωt ℓ))` | 无 Ω 形状层号上 Leaf 成立 | YiLLCheck / 带可满足条件的全称定理 |
| shΩ | `shΩ : GR.ShR (sΩ zero) hΩ (E.Ωt (E.natT 1))` | Ω 形状的完整分支读法 | YiLLCheck / 闭项 |
| rdΩ | `rdΩ : GR.Rd ℓΩ (E.Ωt (E.natT 1))` | 该 Ω 形状层号读作 Ω₁ | YiLLCheck / 闭项 |
| leafΩ | `leafΩ : GR.R ℓΩ (E.Ωt (E.Ωt (E.natT 1))) (proj₁ (O.Ωt ℓΩ))` | 此实例的 Leaf 结论 | YiLLCheck / 指定实例定理 |
| gl0 | `gl0 : Gl zero (proj₁ (O.Ωt zero))` | 修正后 Gl 实例 | YiLLCheck / 闭项 |
| rd0 | `rd0 : GR.Rd (↑ zero (proj₁ (O.Ωt zero))) (E.natT 1)` | 树 1 读成层号 1 | YiLLCheck / 闭项 |
| rd | `rd : GR.Rd ℓ (E.natT 1)` | 反例层号从孩子 1 继承读法 | YiLLLeafNeg / 闭项 |
| ok | `ok : P.Ok ℓ` | 反例层号通过现有合法性 | YiLLLeafNeg / 闭项 |
| r2 | `r2 : GR.R zero (E.natT 2) c2` | 被检测的第 2 分支确有 R 前提 | YiLLLeafNeg / 闭项 |
| bound | `bound : ∀ {t x} → GR.R ℓ t x → Small x → t ≤ᵀ E.natT 1` | 第一位置子域内的所有 R 读法不高于项 1 | YiLLLeafNeg / 全称定理 |
| not-leaf-instance | `not-leaf-instance : GR.R ℓ (E.Ωt (E.natT 1)) β → ⊥` | 此 Ω 树不能在 R 下读作 Ω₁ | YiLLLeafNeg / 否定定理 |
| noLeaf | `noLeaf : Leaf → ⊥` | 实际全域 Leaf 不成立 | YiLLLeafNeg / 否定定理 |
| noLeafOk | `noLeafOk : (∀ a → P.Ok a → ∀ {ν} → GR.Rd a ν → GR.R a (E.Ωt ν) (proj₁ (O.Ωt a))) → ⊥` | 限定 Ok 仍不能成立 | YiLLLeafNeg / 否定定理 |

前提实例：NoΩ 的实例由既有 NoΩ↑ 给出；ShR 的低层分支前提由新定理 read0 全称实填；反例的 Ok、Rd 与被测试分支 R 由 ok、rd、r2 实填。fsn-big 的余尾前提可取通常 ω 项，fsT-big 的余尾前提可取 Ω₁；均可用 refl。Fin 的抽象签名可取零层 Sig，mz、m1 给出零和一的推导。没有附加函数外延、标准形、出口证书或不可满足的辅助前提。

全部辅助函数的逐字签名附在本回报末尾；早期 YiLLPrem 的完整结论也一并列出，不再把旧样例的域不匹配作为续作停止理由。

4. 第一个数学障碍

发生在 `GR.ca (inj₁ (c , q))`、层号为 `nd (sΩ k) h` 的情形。需要的未成立引理形状是：

```agda
∀ k h c {ν} → GR.Rd (h c) ν →
  GR.R (nd (sΩ k) h) (E.Ωt ν) (proj₁ (O.Ωt (nd (sΩ k) h)))
```

取 YiLLLeafNeg 的 k = zero、h、c = suc zero、ν = natT 1，其前提由 rd-fin 1 给出，结论由 not-leaf-instance 否定。这精确否定了全域 Leaf 的一个实例；不是把未证引理起名后当作前提继续。与正面最小 Ω 样例不矛盾：最小样例的孩子函数是实际读回，负例的孩子函数在 0、1、2 处分别为 0、1、0。

没有把此反例归到某条壁垒、派发判定定理或已有 W/V/C 墙；证明中没有折叠。没有据此要求改前三层定义。按原简报第 3 条与停止条件，交编译反例后停止，不进入一般 Lift。

5. 偏离、事故、来源与完整文件清单

- 按作者续作授权仅修正第 0 步 Lift 样例，没有扩大 Gl。原 YiLLPrem 保持源码冻结；早期回报完整副本保留。
- 先完成最小实例，再构造全域 Leaf 的反例。一般 Lift 未执行；read0 是填最小 ShR 分支前提所需的全称辅助引理，没有冒充全域 Lift。
- 临时 YiLLStart 第 1 次退出 42：泛层 GR.R 未能化成 H.Mᴴ，改用既有 rw-weak 作按层派发。第 2 次退出 42：给后继形状 Ω 树构造读法 1 时，误将 Ω_ν 的下标 ν 与目标项 1 混淆；改为从第一分支的一后继推导放宽。第 3 次退出 0。这是两处不同的局部类型修正，没有同一处两次重设计。
- 临时 YiLLNeg 第 1 次退出 42：两个 ◃c 分支遗漏显式守卫 e′，留下 4 个推断元；显式绑定并使用 e′ 后第 2 次退出 0。仓库源码首次编译与最终冷编均为 0。所有失败轮只用于诊断，没有使用其 HTML、切片或结果。
- 没有堆耗尽、超时或内部错误；没加堆，没有并发 Agda。一次只读 ps 命令被沙箱拒绝，未重试或升级权限；与数学结果无关。
- 先检索已有 leaf、读回、共尾算式。正面证明引用 YiVRRel.NoΩ/NoΩ↑、YiKVInst.Ωω/fsnΩω、JiaAuditClosure.cof-regular/fs-regular、EboLean3Base.Ωt-mono、YiGICheck.rw-weak/limᵍ/rd-fin/lift-start 等；负面证明引用 EboLeanView 的共尾视图及其逐点对齐、EboLean3Base.one≤ᴾ。没有重新证明这些已有引理；新增辅助定理覆盖原关系的 mc 行。
- 完整读过原简报、AGENTS.md、EBOHandbook §4；新定理所用的接口与现有引理已按签名和相关实现核对。简报转述的 YiGIEnd.eboᵍ 与其他主审复核状态未在本路重新冷编，未用作新证明依据。YiPJ/YiNX 只读局部、没有依赖其结果。没有调用外部文献、独立模型或子路。
- 唯一仓库写入是新增 YiLLCheck.lagda.md、YiLLLeafNeg.lagda.md；YiLLPrem 是前次新增、未改。没有改旧文件、导航、台账、留档、src 或 archive；没有提交、推送、装包、pkill 或删除他路文件。
- 三件仓库数学源码的禁用构造、洞记号与本机路径扫描均为 0 命中，详见 final-audit.json。Agda safe/without-K 冷编通过；未用函数外延或绕过停机/正性检查。

全部仓库源码：

- probes/OCF/Lean/YiLLPrem.lagda.md
- probes/OCF/Lean/YiLLCheck.lagda.md
- probes/OCF/Lean/YiLLLeafNeg.lagda.md

仓库生成接口（只删除、重建自己的这三件）：

- probes/_build/2.8.0.2/agda/OCF/Lean/YiLLPrem.agdai
- probes/_build/2.8.0.2/agda/OCF/Lean/YiLLCheck.agdai
- probes/_build/2.8.0.2/agda/OCF/Lean/YiLLLeafNeg.agdai

私有实验目录为 `<实验目录>`。其中全部文件如下（包含所有纯 Agda 源码、接口、运行脚本、日志、退出码与早期回报副本）：

- <实验目录>/YiLL-report-initial.md
- <实验目录>/YiLLCheck-final-cold.exit
- <实验目录>/YiLLCheck-final-cold.log
- <实验目录>/YiLLCheck-initial.exit
- <实验目录>/YiLLCheck-initial.log
- <实验目录>/YiLLLeafNeg-final-cold.exit
- <实验目录>/YiLLLeafNeg-final-cold.log
- <实验目录>/YiLLLeafNeg-initial.exit
- <实验目录>/YiLLLeafNeg-initial.log
- <实验目录>/YiLLNeg-1.log
- <实验目录>/YiLLNeg-2.log
- <实验目录>/YiLLNeg-final-cold.exit
- <实验目录>/YiLLNeg-final-cold.log
- <实验目录>/YiLLNeg.agda
- <实验目录>/YiLLNeg.agdai
- <实验目录>/YiLLPrem-cold.exit
- <实验目录>/YiLLPrem-cold.log
- <实验目录>/YiLLPrem-final-cold.exit
- <实验目录>/YiLLPrem-final-cold.log
- <实验目录>/YiLLPrem-repo-initial.log
- <实验目录>/YiLLPrem-temp-cold.exit
- <实验目录>/YiLLPrem-temp-cold.log
- <实验目录>/YiLLPrem.agda
- <实验目录>/YiLLPrem.agdai
- <实验目录>/YiLLPrem.log
- <实验目录>/YiLLStart-1.log
- <实验目录>/YiLLStart-2.log
- <实验目录>/YiLLStart-3.log
- <实验目录>/YiLLStart-final-cold.exit
- <实验目录>/YiLLStart-final-cold.log
- <实验目录>/YiLLStart.agda
- <实验目录>/YiLLStart.agdai
- <实验目录>/audit.txt
- <实验目录>/coldcheck.py
- <实验目录>/final-audit.json
- <实验目录>/libraries
- <实验目录>/reportgen.py
- <实验目录>/temp-coldcheck.py

最终完整回报：`<回报原文>`。

辅助签名逐字附录（以下均通过编译；类型为 Tr、L 的行是闭对象或构造，不误列成值定理）：

`probes/OCF/Lean/YiLLPrem.lagda.md`

```agda
nat₀ : ℕ → Tr zero
ω₀ : Tr zero
ω₀+1 : Tr zero
r-ω₀ : GR.R zero (E.natT 1) ω₀
r-ω₀+1 : GR.R zero (E.natT 1) ω₀+1
noGl-ω₀ : Gl zero ω₀ → ⊥
noGl-ω₀+1 : Gl zero ω₀+1 → ⊥
gl-one : Gl zero (suc zero)
gl-exact : ∀ k (x : Tr k) → Gl k x → x ≡ proj₁ (O.Ωt k)
```

`probes/OCF/Lean/YiLLCheck.lagda.md`

```agda
rd-wk0 : ∀ {x y ν} → zero ⊢ x ◃ y → GR.Rd (↑ zero x) ν → GR.Rd (↑ zero y) ν
read0 : ∀ {ν c} → GR.R zero ν c → GR.Rd (↑ zero c) ν
rdown : ∀ ℓ {ν μ x} → ν ≤ᵀ μ → GR.R ℓ μ x → GR.R ℓ ν x
succ-upper : (h : ⊤ → L) {ν : E.T} → GR.Rd (h tt) ν → GR.R (nd sS h) (E.Ωs ν) (proj₁ (O.Ωt (nd sS h)))
succ-exact : (h : ⊤ → L) {ν : E.T} → E.cof ν ≡ E.c1 → GR.Rd (h tt) (E.pred ν)
  → GR.R (nd sS h) (E.Ωt ν) (proj₁ (O.Ωt (nd sS h)))
oneC : (ℓ : L) → NoΩ ℓ → GR.R ℓ (E.natT 1) (proj₁ (O.Ωt ℓ))
leafC : (ℓ : L) → NoΩ ℓ → ∀ {ν} → GR.Rd ℓ ν → GR.R ℓ (E.Ωt ν) (proj₁ (O.Ωt ℓ))
hΩ : Tr zero → L
ℓΩ : L
shΩ : GR.ShR (sΩ zero) hΩ (E.Ωt (E.natT 1))
rdΩ : GR.Rd ℓΩ (E.Ωt (E.natT 1))
leafΩ : GR.R ℓΩ (E.Ωt (E.Ωt (E.natT 1))) (proj₁ (O.Ωt ℓΩ))
gl0 : Gl zero (proj₁ (O.Ωt zero))
rd0 : GR.Rd (↑ zero (proj₁ (O.Ωt zero))) (E.natT 1)
```

`probes/OCF/Lean/YiLLLeafNeg.lagda.md`

```agda
one<tail : ∀ x {s} → [] <ᵀ s → E.natT 1 <ᵀ (x ∷ s)
one<ψ : ∀ u {s} → [] <ᵀ s → E.natT 1 <ᵀ (E.ψ u s ∷ [])
positive : ∀ {s} → E.natT 1 <ᵀ s → [] <ᵀ s
fΩ-big : ∀ {s κ} (v : VΩ s κ) → E.natT 1 <ᵀ fΩ v (E.natT 2)
fω-big : ∀ {s} (v : Vω s) → E.natT 1 <ᵀ fω v 2
fsn-big : ∀ {s} → E.cof s ≡ E.cω → E.natT 1 <ᵀ E.fsn s 2
fsT-big : ∀ {s κ} → E.cof s ≡ E.cΩ κ → E.natT 1 <ᵀ E.fsT s (E.natT 2)
conflict : ∀ {s} → E.natT 1 <ᵀ s → s ≤ᵀ E.natT 1 → ⊥
pred-one : ∀ {S x} → Lt S x (suc zero) → x ≡ zero
  zero-ref : ∀ {t} → M t zero → t ≡ []
    bad : E.natT 1 <ᵀ [] → ⊥
  one-ref : ∀ {t} → M t (suc zero) → t ≤ᵀ E.natT 1
h : Tr zero → L
ℓ : L
β : Tr ℓ
c2 : Tr zero
u0 : Tr ℓ
u2 : Tr ℓ
  sz : Small zero
  ss : Small (suc zero)
  su0 : Small u0
  su2 : Small u2
  sb : Small β
small-down : ∀ {x y} → ℓ ⊢ x ◃ y → Small y → Small x
r2 : GR.R zero (E.natT 2) c2
bound : ∀ {t x} → GR.R ℓ t x → Small x → t ≤ᵀ E.natT 1
rd : GR.Rd ℓ (E.natT 1)
not-leaf-instance : GR.R ℓ (E.Ωt (E.natT 1)) β → ⊥
noLeaf : Leaf → ⊥
ok : P.Ok ℓ
  oh : ∀ c → P.Ok (h c)
noLeafOk : (∀ a → P.Ok a → ∀ {ν} → GR.Rd a ν → GR.R a (E.Ωt ν) (proj₁ (O.Ωt a))) → ⊥
```

源码已冻结；本整体回报已定稿，早期回报副本仍完整保留。主审可独立删除所列自身接口后冷编。
