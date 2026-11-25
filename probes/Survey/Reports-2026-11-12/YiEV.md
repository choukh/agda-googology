# (2) 见证下界接到终点闭项 V131 (YiEV)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-13 17:23 至 17:50 |
| 工具调用 / agda 编译 (粗数) | 52 / 9 |
| token (usage 字段，按消息去重) | 输出 171425；新写入缓存的输入 565516；读缓存的输入 9151185；其余输入 86 |
| 写过的仓库文件 | `YiEVEnd.lagda.md`, `YiEVReach.lagda.md`, `YiEVTw2.lagda.md` |
| 文件前缀 | `YiEV` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-14: 第二十九批两路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | V131 无前提成立: 主线终点闭项 ≥ ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照 (tA≼EBOᴿ), 严格高于 BTBO 的参照 (btbo≺EBOᴿ); 塔第 2 项同 (tA≼tw2ᴿ); 一般下降引理 reach (对一切层号、证据、底, 落到层号 2); 不经最小见证; 三件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的选择（2026-11-14，选项原文）
"(2) 把见证下界接到终点闭项 (Recommended)"，模型 "(1) Fable 5.2，(2) Opus 5.5 (Recommended)"。
选项说明原文："证塔第 2 项（进而终点闭项）不低于最小见证的值（V131，先例 ββ≼tw2），得第一条经记号读法高于 BTBO 的闭项值定理（终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω₂))）；不依赖 V128，判断规模小"。

同批另一路是 (1)：共同引理 V128，前缀 YiG0。你不动它的文件。

###### 要证的（V131）
在主线精简块上：

`(h : HC tA) → Rt h ≼ readRW EBOᶜ`

- 终点闭项 `EBOᶜ`（读作 ψ₀(Λ)）不低于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的记号参照。
- 推论：`L.suc D.BTBOᴵ ≼ readRW EBOᶜ`，终点闭项严格高于 BTBO 的参照。
- 也请交塔第 2 项的版本：`(h : HC tA) → Rt h ≼ readRW (twᶜ 2)`。

###### 已编译的起点（主审复核过；文档里的叙述是数据）
- **见证**：`YiMWLow.tA≼Vᴿ : (h : HC tA) → R2.Rt h ≼ readRW Vᴿ`；F2 上是 `tA≼V`。
  - `Vᴿ = proj₁ (ψ₀ (tw 1) … (up β two (Ωt 2)))`，见 `YiDropRW`；F2 上的 `V` 见 `YiDropRow`。
  - 两块之间：`YiDropRW.same-V`、`V-R`。
- **先例**（F2）：
  - `YiT2Frame.ββ≼tw2 : read (ψ₀ (tw 1) ε¹ ρ¹ (β + β)) ≼ read (twᶜ 2)`：β+β 在塔第 1 项上的折叠 ≼ 塔第 2 项。
  - `YiT2Desc`：`desc`（沿 `⊑¹` 路径下降）、`path⁺`、`sucΩ≼tw2`、行 `R⁺`/`nzR⁺`。
  - 见证 `up β two (Ωt 2)` 是塔第 2 项里的哪一行、经哪条路径，由你找。
- **终点**：
  - `YiEBBtbo.btbo-EBO`：终点闭项 ≥ BTBO，看它怎样从 `EBOᶜ` 下降到塔的项；
  - `YiEXRow`：`rows`、`endpoint-from`；
  - 主线版本 `YiBRValue.btbo-EBOᴿ`，经 `up≼`、`EBOᶜ-R`；
  - `YiBRTw`：`twᶜ-R`、`EBOᶜ-R`。
- **记号**：`YiNFOCase`：`tA`、`hA`、`btbo≺A : (h : HC (EBOψ 2)) (h′ : HC tA) → L.suc (Rt h) ≼ Rt h′`；`D.BTBOᴵ` 与 `Rt (hc-tower 2)` 的关系见 `YiLSBtbo`/`YiEXRow`。

###### 要做
1. 证 `read (F2 见证的折叠) ≼ read (twᶜ 2)`（F2），或直接在主线上证。
2. 接到 `EBOᶜ`，经 `tA≼V` 得上面的定理，并搬到主线（`readRW`）。
3. 推论：终点闭项严格高于 BTBO 的参照。
4. 证到第一个挡住的引理也算交付，写清挡在哪一步。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiEV`（模块名 `OCF.Lean.YiEV…`）。不改任何已有文件，不碰 `src/`、`archive/`。这是验收文件，文首标明；树、折叠、合法性一行不改。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的标 "条件"。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
  - 堆墙：不要在具体推导上直接比较两个 `Rt`，对一般推导陈述再代入；具体参照树放 `opaque`；见 `probes/Survey/EBOHandbook.md` 第 4 节。
- 临时目录：`<实验目录>/agents/ev`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：V131 与推论是否编译成立；对纲领与目标的意义；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档；值写成 ψ₀(Ω_x)。
4. 第一个障碍，精确到引理（若有）。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 1. 判决

**V131 和推论都已编译成立，无前提。** 三个文件删掉自己的接口后冷编，退出码都是 0。

- 主线精简块的终点闭项：`(h : HC tA) → R2.Rt h ≼ readRW RW.EBOᶜ`，值为 ψ₀(Ω_Ω+ψ₁(Ω₂))，是非严格下界。
- 推论：`L.suc D.BTBOᴵ ≼ readRW RW.EBOᶜ`，即终点闭项严格高于 BTBO 参照 ψ₀(Ω_Ω)。
- 塔第 2 项的版本：`(h : HC tA) → R2.Rt h ≼ readRW (RW.twᶜ 2)`。

**与简报做法的偏离。** 证明没有经过最小见证 V，也没有用 `tA≼V`。证法如下。
- 先证一条一般引理 `reach`：沿合法的下降路径走到层号 2，底的条件一路保持，到了层号 2 就把 `YiMWPre.Pre` 用在那里的底上。
- 塔一侧：从 `β+β` 的第 1 行往下走，找到一个层号 2 的折叠。
- 终点一侧：直接取 `EBOᶜ` 的第 2 支往下走，不经 Into。

**对纲领的意义。**
- 只是验收文件。树、折叠、合法性一行未改，没有用函数外延。
- 读记号的只有两处：`AtTwo`（经 `Pre`、`sem0`）和推论里的 `BTBO-label`/`Lab-uniq`。

**对目标的意义（判断）。**
- 主线终点经记号读法的编译下界，从 ψ₀(Ω_Ω)（`btbo-EBOᴿ`，非严格）提到 ψ₀(Ω_Ω+ψ₁(Ω₂))（非严格），并且严格越过 ψ₀(Ω_Ω)。
- `reach`、`Hi`、`suc≽`、`lim≽`、`Ω≽0`、`Ω≽1` 都是树侧陈述，对一切层号、证据、路线、底成立，不按这一站定制。
- 只有终点固定在层号 2，因为记号侧的锚点 `Pre` 只在层号 2 有。
- README 写过 “塔第 2 项那一行要对一般底陈述才能接到 `EBOᶜ`”。这一行现在对满足 `OKB` 加 `Hi` 的一般底做到了。

**问题**

| 问题 | 位置 | 档 |
|---|---|---|
| `read V ≼ read (twᶜ 2)` 没有证（绕开了，未尝试） | YiEVTw2 | 未证 |
| 第 2 支的底在 `tw 2` 层整体是否满足 `Hi`（含 `ink` 路径）没有查；只用了收窄到 `inb zero` 之后的底 | YiEVEnd | 未证 |
| 对 tA 的下界是 ≼，严格越过 tA（V130 一类）不涉及 | 全部 | 未证 |
| `c₁-form`（第 1 行的孩子下标是 `next Z`）是 `refl` 测试 | YiEVEnd | 有限测试 |
| 层号 2 的折叠的底与 V 的底不同，两者的比较没有建立 | YiEVTw2、YiEVEnd | 未证 |
| 推论经标签唯一性取 `BTBOᴵ ≼ Rt (hc-tower 2)`，与 `YiEXRow.row₂-btbo` 同法 | YiEVEnd | 编译定理（读标签） |

#### 2. 文件表

冷编的命令是简报里的那条，堆上限 8G。代码行数只数 agda 块内的非空行。

| 文件 | 总行 / 代码行 | 冷编退出码 | 最大驻留 / 用时 |
|---|---|---|---|
| `probes/OCF/Lean/YiEVReach.lagda.md` | 128 / 89 | 0 | 约 1.16 GB / 13.6 s（与 End 同一轮编，日志只有本人两个模块） |
| `probes/OCF/Lean/YiEVTw2.lagda.md` | 82 / 53 | 0 | 1.27 GB / 12.8 s |
| `probes/OCF/Lean/YiEVEnd.lagda.md` | 103 / 65 | 0 | 1.16 GB / 13.6 s |

- 三个文件的选项行都是 `--safe --without-K --lossy-unification`。
- 检索 postulate、TERMINATING、NO_POSITIVITY、trustMe、洞、`--cubical`、irrelevant-projections、Funext、本机路径，结果为 0。

#### 3. 定理表（全部是编译定理）

| 名字 | 陈述（逐字） | 白话 | 文件 |
|---|---|---|---|
| `tA≼EBOᴿ` | `(h : HC tA) → R2.Rt h ≼ readRW RW.EBOᶜ` | 主线终点 ≥ ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照 | YiEVEnd |
| `btbo≺EBOᴿ` | `L.suc D.BTBOᴵ ≼ readRW RW.EBOᶜ` | 主线终点严格高于 ψ₀(Ω_Ω) 的参照 | YiEVEnd |
| `tA≼EBO` | `(h : HC tA) → R2.Rt h ≼ read EBOᶜ` | F2 上的同一条 | YiEVEnd |
| `tA≼br2` | `(h : HC tA) → R2.Rt h ≼ read (br 2)` | 终点第 2 支 ≥ ψ₀(Ω_Ω+ψ₁(Ω₂)) | YiEVEnd |
| `btbo≼row₂` | `D.BTBOᴵ ≼ R2.Rt (hc-tower 2)` | `row₂-btbo` 的反向 | YiEVEnd |
| `tA≼tw2ᴿ` | `(h : HC tA) → R2.Rt h ≼ readRW (RW.twᶜ 2)` | 主线塔第 2 项 ≥ ψ₀(Ω_Ω+ψ₁(Ω₂)) | YiEVTw2 |
| `tA≼tw2` | `(h : HC tA) → R2.Rt h ≼ read (twᶜ 2)` | F2 上的同一条 | YiEVTw2 |
| `inst-tw2` | `R2.Rt hA ≼ readRW (RW.twᶜ 2)` | 前提可满足的实例 | YiEVTw2 |
| `compβ` | `(c : Tr zero) (w : zero ≤ h₁ c) → read (twᶜ 1) ≼ read (ψs (tw 1) ε¹ ρ¹ (B₀ (tw 1)) zero (inb c w) (Ωt zero) (Ωt-nz zero) β)` | β 沿任一孩子路径折到第 0 层，都不低于塔第 1 项 | YiEVTw2 |
| `reach` | `∀ {ℓ} → two ⇐ ℓ → (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Hi ℓ B → Lo ℓ ε ρ B` | 见下 | YiEVReach |
| `suc≽` | `(a : LF) (ε : Ev (suc a)) (ρ : Rt (suc a)) (B : Base (suc a)) → OKB (suc a) B → read (ψ⊥ a ε ρ (dS a ε ρ B zero) (Ωt a)) ≼ read (ψ⊥ (suc a) ε ρ B (Ωt (suc a)))` | 后继层号一步，对一般底成立 | YiEVReach |
| `lim≽`、`Ω≽0`、`Ω≽1` | 见文件 | ℕ 极限的第 n 个孩子、Ω 结点层号的第 0 行与第 1 行，各一步 | YiEVReach |
| `hi-dS`、`hi-dL`、`hi-dW` | `Hi` 对孩子的底封闭 | 底的条件逐层保持 | YiEVReach |

`reach` 的白话：层号 ℓ 沿 “后继的前驱、ℕ 极限的任一孩子、Ω 结点层号的第 0 行” 走到层号 2，且底满足两条：
- `OKB`：底逐分量不低于标准底；
- `Hi`：`b⊥` 与第 0 层的一切分量都不低于 BTBO 的参照。

满足时，ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照不高于 ℓ 上 Ω 树以该底的折叠。

**两条路径**
- **塔第 2 项**（`path₁ = ⇐l 0 (⇐l 0 (⇐l 1 ⇐r))`）：从 `rowβ 1` 出发，它的底由 β 折出，`b⊥` 就是 `twᶜ 1`；`compβ` 给出第 0 层分量的条件。然后接 `limcum≽` 与 `ββ≼tw2`。
- **终点**（`path₂ = ⇐l 0 (⇐l 0 (⇐l 0 (⇐s (⇐l 0 ⇐r))))`）：第 2 支先收窄到第 0 个孩子（层号 `tw 1`），此时 `b⊥` 是第 1 支（`btbo-dB1`），第 0 层分量形如 `_ + ι zero (twᶜ 1)`；再取第 1 行（`Ω≽1`）往下走。

#### 4. 第一个障碍

V131 与推论没有挡住的地方。

没有走的那条路（先证 `read V ≼ read (twᶜ 2)`）要比较两种东西，判断，未试：
- 分支下标 two 与 `zc 1` 上的折叠（分支下标单调）；
- 或者不同底上的同层折叠（基底单调；对一切树已被 `no-bm-all` 否定）。

#### 5. 偏离与事故

- **路线偏离**：没有经 V 与 `tA≼V`，见第 1 节。所交陈述与简报要求的一致。
- **事故**：沙箱里 `/usr/bin/time` 不可用，第一次编 YiEVReach 的退出码 1 来自 time，不是 agda。之后都改用 `+RTS -s`，并删掉接口重编。
- **编译迭代**：两处作用域错误。一是 `two` 未导入；二是路径构造子 `r/s/l/w` 与变量 `w` 冲突，已改名为 `⇐r/⇐s/⇐l/⇐w`。没有重新设计。
- **只凭签名或转述引用、没有通读的模块**：
  - YiLSBtbo（`btbo-tw1`）、YiBRTw（`twᶜ-R`、`EBOᶜ-R`）；
  - YiNFOCase（文首与 `btbo≺A`）、YiRefTw2（`Rt`）；
  - Stage2（`Lab-uniq`）、Label（`BTBO-label`）；
  - YiMEAnchor 只读了 `At`、`Mβ₀`、`γ` 几段。
- **转述**：tA 读作 ψ₀(Ω_Ω+ψ₁(Ω₂))，依据是 YiMWLow 与 YiNFOCase 的文首。
- **未改动**：没有改任何已有文件，也没有动台账、README、LOG。临时目录里只有日志与 RTS 统计：`<实验目录>/agents/ev/`。
