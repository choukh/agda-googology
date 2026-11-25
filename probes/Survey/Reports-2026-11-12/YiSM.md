# 兄弟孩子那一行进主线的准备 (YiSM)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-14 08:11 至 08:55 |
| 工具调用 / agda 编译 (粗数) | 89 / 15 |
| token (usage 字段，按消息去重) | 输出 232201；新写入缓存的输入 456038；读缓存的输入 25255016；其余输入 166 |
| 写过的仓库文件 | `YiSMFold.lagda.md`, `YiSMValue.lagda.md` |
| 文件前缀 | `YiSM` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-14: 第四十批 YiSM 返回并复核; 第四十批全部返回 (主审)” 一节 |
| 主审复核后的一句结论 | 无前提: 主线候选 YiSMFold (重导出 YiRBSib, 闭项 twˢ, EBOˢ; 切片 89 / 469 / 469, 比原主线多 47 行; 导入闭包干净); 塔各项上新的一行不触发 (tw-norow, refl: 证据 rb-tw 只在塔那一项的顶层, 孩子层是 rb-no); 新塔与原塔同值 (same-twˢ); 主线已有值定理全部搬到新闭项 (btbo-twˢ, tA≼tw2ˢ, tω≼EBOˢ, tN≼EBOˢ, tA≺EBOˢ 等), 走 F2 上手造的底与已有下降引理; 新终点 ≥ 原终点未证未否定; 四件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定（2026-11-14，选项原文）
- 主线 "经指定孩子" 那一行："兄弟孩子 c′ + c (Recommended)"，即 `probes/OCF/Lean/YiRBSib` 的折叠。
- 本批本路是 "(3) 就做选定的那一行进主线的准备"，选项说明原文："把选定的写法整理成主线的候选折叠，重做主线已有的值定理的搬运（终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω_ω)) 等）；只整理与搬运，不动 src"。
- 原则："不能以'追求同步'为名反过来指导树的定义形状"。本路不改那一行的写法，只整理与搬运。

###### 已有的东西（主审复核过）
- **主线精简块**：`YiRWBlock`、`YiRWOps`、`YiRWPath`、`YiRWFold`（折叠 `ψ`、单调 `mono` 互递归，闭项 `twᶜ`、`EBOᶜ`），切片 89 / 422 / 422。
- **兄弟孩子折叠** `YiRBSib`：复制 `YiRWFold`，只换 "Ω 形状层号、目标经指定孩子 c′、嵌入在孩子 c" 那一行。
  - 证据 `Rb` 在时，在孩子 c′ + c 的层上折该层的 Ω 树，底是左项 x 的折叠，再 `⊞` 原来的回退项；
  - 证据不在时，逐字是原来那一行（`row-no`）；
  - 塔上的证据是闭项 `rb-tw`；`row-tw` 给出塔上那一行的形状；
  - `Base`、`kp`、`node⁺` 从 `YiRWFold` 导入；
  - 回报 `probes/Survey/Reports-2026-11-12/YiRB.md`。
- **主线上已有的值定理**（都对 `readRW RW.EBOᶜ` 陈述，`readRW` 在 `YiBRValue`）：
  - `YiANLim.tω≼EBOᴿ`（终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω_ω))）；
  - `YiTWEnd.tA≺EBOᴿ`；
  - `YiANEnd`、`YiEVEnd`、`YiPHEnd`、`YiKAEnd` 里的同类定理。

###### 要做的（按序）
0. **最小实例检查**，在临时目录：
   - 搬运最省的办法，是一条 "新折叠的值不低于原折叠的值"，然后用 `≼-trans` 把所有对 `readRW RW.EBOᶜ` 的下界搬到新闭项上。
   - 主审的判断：这条对一切树多半不成立。对角那一步的链拿折叠的输出作下一个分支的下标，Ω 结点的分支函数不要求单调，新旧两条链走到不同的下标，值不一定可比。
   - 所以先只对塔上的规范树（塔各项的 Ω 树、闭项 `twᶜ`、`EBOᶜ` 用到的那些）陈述，并在塔第 1 项的一个小实例上检查它成立：用 `row-tw` 的形状加 "折叠的输出不低于起点"。
   - 若小实例上就不成立，停下回报。
1. **整理候选**：新建主线候选的折叠文件。可以直接重导出 `YiRBSib`，并给出闭项（新的 `twᶜ`、`EBOᶜ`，名字自定），文首标明 "主线候选（作者 2026-11-14 定兄弟孩子），未进 src"。
   - 用 `probes/Survey/scripts/depslice.py`（或仓库里同类脚本）量切片行数，与 YiRW 的 89 / 422 / 422 对照；行数表只在回报里给。
   - 用 `probes/Survey/scripts/importclosure.py` 查导入闭包干净。
2. **值的搬运**：证新闭项的值不低于原闭项（`readRW` 意义下），量化域取第 0 步检查过的那一类；再把上列值定理搬过来。做不到一般的，就交最大可证的部分，以及第一个挡住的引理。
3. 列出主线上还有哪些定理是对原折叠陈述、而新折叠要重做的（合法性、形状、闭项的性质），只列清单，不做。

**纪律**（作者同意的，必须照做）：
- 动手证一般形式之前，先用临时文件检查前提可满足。
- 已有引理先检索再写，不重证。
- 不改任何已有文件，不碰 `src/`。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiSM`（模块名 `OCF.Lean.YiSM…`）。不碰 `archive/`，不碰另两路的前缀 `YiMH`、`YiLR`。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 6G。另两路也在编译，不用 `--ignore-interfaces`，只删自己模块的 `.agdai`。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量，执行前核对路径。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时。
  - 堆墙：不要在具体闭项上直接比较两个读回；大的参照树放 `opaque`；见 `probes/Survey/EBOHandbook.md` 第 4 节。
  - 沙箱里 `/usr/bin/time` 不可用，内存用 `+RTS -s` 看。
- 临时目录：`<实验目录>/agents/sm`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；6G 仍耗尽；第 0 步触发的停止条件。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：第 0 步的结论；候选文件与切片行数；值的搬运到哪一步；要重做的清单；对纲领与目标的意义；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 1. 判决

**第 0 步（最小实例）。** 先把临时文件写好并编译（`SMCheck0.agda`，退出码 0）。主审担心的情形没有出现在塔上，而且情况比预想的更极端：
- **塔各项上，新的一行根本不触发。** 编译定理 `tw-norow` 用 `refl` 证明：`twˢ (suc n)` 与证据全取 `rb-no` 的折叠逐字相同，对一切 n 成立。原因是顶层只经一致路径或下标层侧路径进孩子；经指定孩子的路径只作用在左项 `zero` 上。
- **新的一行只在终点 `EBOˢ` 里触发，而且只出现在 Λ 的孩子 `tw n` 的底里。** 第 1 支孩子 c′ 的底在第 0 层的分量：新写法是 `Fc c′ v + ι zero ω₀`，原写法是 `suc zero + ι zero ω₀`（`B1-new`、`B1-old`，都是 `refl`）。小实例 `B1-ge` 证明这一分量新的不低于旧的（编译定理）。
- 一般形式的 "新终点 ≥ 原终点" 没有证，也没有否定：
  - 底变大以后，链的下标序列跟着改变。
  - 要比较的是不同孩子层 `h₁ z` 上的折叠。
  - 第一个挡住的引理见第 4 节。

**候选文件与切片。** 候选折叠是 `OCF.Lean.YiSMFold`。它原样重导出 `YiRBSib`，补上 Λ 的证据 `rb-Λ = tt , rb-tw` 和闭项 `twˢ`、`EBOˢ`。文首写明 "主线候选（作者 2026-11-14 定兄弟孩子），未进 src"。
- `importclosure`：OK，闭包只有 YiRW 四件、YiRBSib 与标准库，禁用表命中 0。
- 切片用主审的 `slice_roots.py` 量，同一次运行重算出了原主线的 89 / 422：

| 层 | 原主线 YiRW | 新候选 YiSM |
|---|---|---|
| 1 块（根 tw, Λ） | 89 | 89 |
| 2 + 折叠与闭项 | 422 | 469 |
| 3 + 合法性 | 422 | 469（合法性是类型，证据 `rb-tw`、`rb-Λ` 已在闭项里） |

469 行的构成：YiRWPath 135、YiRBSib 107、YiRWOps 97、YiRWBlock 91、YiRWFold 33、YiSMFold 6。比原主线多 47 行。

**值的搬运做到哪一步。** 主线上对 `readRW RW.EBOᶜ` 和 `readRW RW.twᶜ` 陈述的值定理全部搬到了新闭项，都是编译定理、无前提：
- 塔：`btbo-tw1ˢ`、`btbo-twˢ`、`tA≼tw2ˢ`、`bho-lowerˢ`，以及同值定理 `same-twˢ`。
- 终点：`btbo-EBOˢ`、`tA≼EBOˢ`、`t₃≼EBOˢ`、`tN≼EBOˢ`（对一切 m）、`tω≼EBOˢ`（即 ψ₀(Ω_Ω+ψ₁(Ω_ω))），严格的 `tA≺EBOˢ` 与 `btbo≺EBOˢ`。
- 走的不是 "新 ≥ 旧"：
  1. 终点第 1、2 支，在 F2 上分别与一个手造的底（`Bᶠ`、`B₂ᶠ`）相关。手造的底在经孩子 c 的分量上照新的一行写，其余分量照原行写。
  2. 证明这两个底满足 `OKB`、`Start`、`Hi`。
  3. 重用 F2 上对一般底陈述的下降引理（`btbo-B`、`reach`、`reach³`、`reachG`、`Ω≽0`、`Ω≽1`）。
  4. 只换路径：新的链点 `c₁ˢ` 多一层前缀，路径多 5 步，由类型检查确认。
- `YiTWEnd` 的严格不等式改经 t₃ 证明：`tA≺EBOˢ = ≼-trans (A≺3 h h₃) (t₃≼EBOˢ h₃)`。
- `YiKAEnd` 讲的是候选 A 的 `YiKVFold.EBOᶜ`，不是主线，所以没有搬（看文件头得知）。

**要重做的清单（第 3 步，只列不做）。**
- 形状和行律：
  - `YiRWCheck` 中对 `RW.ψ` 陈述的各条：`J2-u`、`J2⊥`、`J2-k`、`J2-s`、`J2-lim`、`J2-lim-fwd`、`J2-lim-bwd`、`self-up`、`node`、`node⊥`、`kstep`，有限测试 `bω-tw`、`cω-A`、`cω-B`；`J2-b` 已被 `row-tw`、`row-no` 取代；只讲 `kp` 和路径的 `kp-fwd`、`kp-bwd`、`way-refl`、`tw1-adj`、`tw1-way` 原样可用。
  - `YiRWKall` 的 `kall`、`kall-tw`。
- 关系：
  - `YiBRFold` 的 A/S 在一切证据下（这次只做了 `rb-no`）。
  - `YiBRTw.EBOᶜ-R`、`YiBRValue.same-EBO` 在新终点上没有对应。
  - `YiRWSame` 的有限测试。
- 工具与否定：
  - `YiVRFold.fl`。
  - `YiVRRead`：`fold-≼`、`fold-≈`、`base-two`、`wit-*`、`kid-*`。
  - `YiG0Mono`。
  - `YiKidRW`：`rw-unb`、`rw-¬all`。`YiKidGen`：`inv`、`¬mono`。
  - `YiDropRW` 的 `same-V`。
  - `YiKSDesc`、`YiKSRead`：`keel`、`rowσ`、`rows₂`。判断：右边可经 `same-twˢ` 搬，左边可经 `YiSMRel` 搬。
  - `YiCertNeg`。
- 闭项性质：View 和 FGH 只在 F2 上（YiLP*），原主线精简块上本来就没有，新候选也没有。
- 合法性：`Ok` 是类型，不变；`mono` 已在 `YiRBSib` 里；`rb-tw`、`rb-Λ` 是闭项。不需重做。

**对纲领与目标的意义。**
- 纲领 2（无公理、检查器保证停机）：全部 `--safe --without-K`，满足。
- 纲领 4（最终定义与记号无关）：候选文件的导入闭包干净，满足。
- 值的搬运只用验收文件（读记号的 `HC`、`R2.Rt`），与原主线的验收方式相同。
- 目标（树自足）：
  - 这一步说明换成兄弟孩子不会丢掉任何已有的下界，终点仍 ≥ ψ₀(Ω_Ω+ψ₁(Ω_ω))。
  - 它没有说明新写法提高了终点的值。
  - 新的一行对塔闭项毫无作用，这是定理 `tw-norow`。它在终点里只改了 Λ 前缀在各孩子上的底。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 新的一行在塔各项闭项上不触发 | `YiSMValue.tw-norow` | 编译定理 |
| 新终点 ≥ 原终点：未证、未否定，卡在跨孩子层的按值单调 | `YiSMValue` 文首；第 4 节 | 未走通 |
| 在 `EBOˢ` 的计算里，新的一行只在嵌入孩子 c = 0、左项 `zero` 处触发，所以 c′+c 里的 "+c" 不起作用；`YiRBCrit` 那种情形（tw 1 的整棵 Ω 树经孩子 2 朝第 2 层折叠）不出现在 `EBOˢ` 里 | 读 `emb`、`way`、Λ 的 sL 行得出；`B1-new` 与 `br2-R` 的类型检查只是局部佐证 | 判断 |
| `EBOˢ` 与 F2 的 `EBOᶜ` 不逐层相关（底不同） | 无定理 | 判断 |
| `YiSMRel` 是 `YiBRFold` 的逐字复制（只换 ψ→ψ⁰），把 YiBRFold 对证据参数化即可消掉这份重复 | `YiSMRel` | 判断 |
| `YiKAEnd` 不属主线 | `YiKAEnd` 文首 | 读文件 |

#### 2. 文件表

仓库文件都在 `<仓库>/probes/OCF/Lean/` 下。删掉自己的 `.agdai` 后冷编，每个日志只有自己模块的 Checking 行，无警告；禁用构造检索为 0。内存是 `+RTS -s` 报告的 total memory in use。

| 文件 | 代码行 | 冷编退出码 | 内存 |
|---|---|---|---|
| YiSMFold.lagda.md（候选） | 15 | 0 | 246 MiB |
| YiSMRel.lagda.md | 328 | 0 | 3407 MiB |
| YiSMValue.lagda.md | 162 | 0 | 2755 MiB |
| YiSMEnd.lagda.md | 225 | 0 | 2870 MiB |
| 临时：<实验目录>/agents/sm/SMCheck0.agda | 约 50 | 0 | 2258 MiB |
| 临时：<实验目录>/agents/sm/SMEnd0.agda（已并入 YiSMEnd） | — | 0 | 2877 MiB |

#### 3. 定理表

全部是编译定理，无前提。

| 名字 | 逐字陈述 | 白话 | 文件 |
|---|---|---|---|
| `A`, `S` | `A : … → RelT zero F.zero (proj₁ (ψ⁰ ℓ o B zero (z≤ ℓ) β x)) (F.ψ⊥ ℓ′ ε ρ B′ x′) × RelD …`；`S : … → RelT j j′ (proj₁ (ψ⁰ ℓ o B j w β x)) (F.ψs ℓ′ ε ρ B′ j′ w′ β′ nβ x′) × RelD …`，其中 `ψ⁰ ℓ o = ψ ℓ o (rb-no ℓ)` | 不带证据时，新折叠与 F2 的折叠逐层相关 | YiSMRel |
| `tw-norow` | `(n : ℕ) → twˢ (suc n) ≡ proj₁ (ψ₀ʳ (tw (suc n)) (Ok-tw (suc n)) (rb-no (tw (suc n))) (proj₁ (Ωt (tw (suc n)))))` | 塔上新的一行不触发 | YiSMValue |
| `twˢ-R` | `(n : ℕ) → RelT zero F.zero (twˢ n) (F.twᶜ n)` | 新塔与 F2 的塔逐层相关 | YiSMValue |
| `same-twˢ` | `(n : ℕ) → readRW (twˢ n) L.≅ readRW (RW.twᶜ n)` | 与原主线的塔同值 | YiSMValue |
| `btbo-tw1ˢ`, `btbo-twˢ` | `D.BTBOᴵ ≼ readRW (twˢ 1)`；`(n : ℕ) → D.BTBOᴵ ≼ readRW (twˢ (suc n))` | 塔各项 ≥ BTBO | YiSMValue |
| `tA≼tw2ˢ` | `(h : E.HC tA) → R2.Rt h ≼ readRW (twˢ 2)` | 塔第 2 项 ≥ ψ₀(Ω_Ω+ψ₁(Ω₂)) | YiSMValue |
| `bho-lowerˢ` | `(h : E.HC t₂) → Rt h ≼ readRW (proj₁ (ψ₀ʳ two Ok-two (rb-no two) (proj₁ (Ωt two))))` | ψ₀(Ω₂) 锚点 | YiSMValue |
| `B1-new`, `B1-old` | `proj₁ (B1ˢ zero (inc c′ v)) ≡ proj₁ (Fc c′ v) + ι zero ω₀`；`proj₁ (B1ᴿ zero (inc c′ v)) ≡ suc zero + ι zero ω₀` | 第 1 支孩子 c′ 的底，新旧两种形状 | YiSMValue |
| `B1-ge` | `readRW (proj₁ (B1ᴿ zero (inc c′ v))) ≼ readRW (proj₁ (B1ˢ zero (inc c′ v)))` | 这一分量新的不低于旧的 | YiSMValue |
| `br1-R` / `br2-R` | `RelT zero F.zero (brˢ 1) (Fn 1 Bᶠ)` / `RelT zero F.zero (brˢ 2) (Fn 2 B₂ᶠ)` | 第 1、2 支与 F2 上手造的底相关 | YiSMValue / YiSMEnd |
| `ok₂`, `hi0ᶠ` | `OKB (F.tw 2) B₂ᶠ`；`V.Hi (F.tw 1) Br0ᶠ` | 手造的底满足下界条件 | YiSMEnd |
| `btbo-EBOˢ` | `D.BTBOᴵ ≼ readRW EBOˢ` | 终点 ≥ BTBO | YiSMValue |
| `tA≼EBOˢ` | `(h : E.HC tA) → R2.Rt h ≼ readRW EBOˢ` | 终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω₂)) | YiSMEnd |
| `t₃≼EBOˢ` | `(h : E.HC PH.t₃) → R2.Rt h ≼ readRW EBOˢ` | 终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω₃)) | YiSMEnd |
| `tN≼EBOˢ` | `(m : ℕ)`（模块参数）`(h : E.HC (AN.tN m)) → R2.Rt h ≼ readRW EBOˢ` | 终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω_{m+3}))，对一切 m | YiSMEnd |
| `tω≼EBOˢ` | `(h : E.HC AL.tω) → R2.Rt h ≼ readRW EBOˢ` | 终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω_ω)) | YiSMEnd |
| `tA≺EBOˢ`, `btbo≺EBOˢ` | `(h : E.HC tA) → L.suc (R2.Rt h) ≼ readRW EBOˢ`；`L.suc D.BTBOᴵ ≼ readRW EBOˢ` | 严格不等式 | YiSMEnd |

前提都可满足，实例已编译：`instA`、`inst₃`、`instN`、`instω`（YiSMEnd），`inst-tw2`、`inst-two`（YiSMValue）。

#### 4. 第一个障碍

只针对 "新终点 ≥ 原终点" 这条路线。值定理的搬运已经绕开了它。
- 在第 1 支里，新旧两条链的起点相同，但孩子 z 的底不同。所以下标序列 `z_{k+1} = s(z_k)` 不同。
- 要比较 `G(z^新_k)` 与 `G(z^旧_k)`，需要 z ↦ "孩子层 `h₁ z` 的 Ω 树以 B(·)(inc z ·) 为底的折叠" 按值单调。
- 这正是 `YiVRRead.GMono` 的带底形式，跨了不同的孩子层。它在仓库里没有证，也没有否定；`YiVRRel.β-not` 说明现有的 `Le` 关系表达不了它。
- 同一层上 "底变大则输出变大" 有 `fold-≼` 可用，不是障碍。

#### 5. 偏离与事故；未读、只凭转述引用的东西

- **偏离。**
  - 第 2 步没有走 "新 ≥ 旧"，改为在 F2 上手造相关的底，重用对一般底的下降引理。
  - 候选里另起名 `twˢ`，它与 `YiRBSib.twʳ` 逐字相同。
- **事故。**
  - 第 0 步第一次编译退出 42：误用了 `YiKVRel` 自带的另一个 `readRW`，改为 `YiKidGen.◃→≼` 后通过。
  - `YiSMValue` 第一次编译退出 42：兜底子句不展开构造子，改为显式写出各子句后通过。
  - 生成 YiSMEnd 时，一条 shell 命令因双引号里的反引号解析失败，没有执行任何操作，改用脚本文件后完成。
  - 只读执行了主审 scratchpad 里的 `verify/slice_roots.py`，没有在那里写任何东西；HTML 输出放在我自己的临时目录。
  - 没有改动任何已有文件，没有碰 `src/`，没用 `--ignore-interfaces`。
- **未读或只读签名、凭文件头引用的东西。**
  - F2 一侧的证明本体：`YiLSBtbo.btbo-tw1`、`YiT2Mono.btbo-tw`、`YiMEAnchor.bho-lowerᴹ`、`YiANReach.reachG`、`YiANEnd.AtN`、`YiPHEnd.reach³`/`A≺3`、`YiNFOCase.btbo≺A`、`YiANLim` 的 `nfω`、`lt`。
  - 记号项 tA、t₃、tN m、tω 对应哪个 ψ₀(…)：照各文件头。
  - "`YiRBCrit` 的情形不出现在 `EBOˢ` 里" 与 "新的一行只在 c = 0 处触发"，是我读定义得出的判断，没有编译。
