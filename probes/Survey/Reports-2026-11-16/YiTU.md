# 第 2 站闭项的上界工具（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-16 22:56 至 23:25 |
| 工具调用 / agda 编译 (粗数) | 67 / 4 |
| token (usage 字段，按消息去重) | 输出 149714；新写入缓存的输入 353745；读缓存的输入 13361644；其余输入 126 |
| 写过的仓库文件 | `YiTUReduce.lagda.md` |
| 文件前缀 | `YiTU` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 1 件退出 0，禁用构造 0；Goalᶻ 归约到每个链点一行折叠的值上界 UB（ub→goalᶻ），n = 0、1 已证，n ≥ 2 未证；值序到层号可比不需要值单调（emb↑） |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b73/YiTU.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。全程用中文。最后一条消息就是你的回报。

## 回报原文

### YiTU 回报：第 2 站闭项的上界工具

#### 1. 判决

**这对纲领与目标意味着什么。** 本路只在验收侧（第 4 层）新增关系与定理，没有改树、折叠、合法性，也不涉及"树自足"。翻译账上没有新的树侧定义；新文件读记号，因为它用参照 `Level`/`Value` 与 `BTBOFull`，导入闭包审计结果为 FAIL，验收文件本应如此。

结论分三条：
- **`Goalᶻ` 没有证出来（未走通）。** 我把它归约到一族纯粹的折叠值上界 `UB (pt n)`：每个链点上一行折叠的值不高于 ψ₀(Ω_{lvl x+1})。n = 0、1 两个实例是编译定理，n ≥ 2 未证。
- **层号比较不需要 `VMᴸ`。** 从"值序 read(pt n) ≼ γ_m"到"层号可比"，可以照 `BTBOFull.Upp` 的写法，经 `V2`（先用 `ordᴰ` 累加规范化，再给保序嵌入）和 `V3` 完成。这一条是编译定理。它推翻了 YiXV 检查点报告 (b)B3 的判断："还需要实际回灌点的 native 参照封顶与参照列比较"。它和 `YiVmNegChain.no-bound` 不矛盾，因为 `V2` 不走 `⊑ᴵ`。
- **剩下的只有一般折叠的值上界。** YiXV 余项里的 B3（参照列比较）、B4（部分和吸收与合成）、B5（新旧塔第 1 项的搬运）都已在新文件里编译。B1/B2（一般折叠的保持与它的出口）还缺，已化成 `UB (pt n)`。

**各步到哪里**
- 第 0 步（YiXV 的上界机制、离 `Goalᶻ` 还差哪几条）完成。临时文件 `<实验目录>/YiTUStep0.agda` 首次编译退出 0，内容后来搬进仓库文件。
- 第 1 步：给出条件定理 `ub→goalᶻ` 和前提的两个实例，`Goalᶻ` 本身未证。
- 第 2 步没有进入，因为它要以 `Goalᶻ` 为前提。

**目前最紧的上界**
- 行 0：`read (G (pt 0)) ≼ D.γ 1`（`YiXVStart.row0-upper`）。
- 行 1：`read (G (pt 1)) ≼ D.γ 2`（`YiXVNeedOne.need1`）。
- 塔第 1 项 `twᶻ 1` 本身没有任何编译过的上界。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| `Goalᶻ` ⇐ 一切链点上的 `UBᴱ` | `YiTUReduce.ub→goalᶻ` | 编译定理（条件） |
| 行界下标任意即可推出 `Goal` | `rows→goal` | 编译定理 |
| 值序 ⇒ 层号前驱嵌入（不要 VMᴸ） | `emb↑` | 编译定理 |
| `UB (pt 0)`、`UB (pt 1)` | `ub0`、`ub1` | 编译定理 |
| `UB (pt n)`，n ≥ 2 | 无 | 未证（未走通，没有否定） |
| `UB x` 对一切第 0 层的树 x 成立 | 无 | 判断：期望成立。`YiLSTw1.lower-↑` 给 ψ₀(Ω_{lvl x}) ≼ G x，与它相容；+1 的余量能吸收 Ω_a·k 一类的超出 |
| 证 `UB` 必须有可数层号上对任意树的折叠上界模拟 | 无 | 判断（纸面分析，见第 4 节） |
| 同步对象的输出与 ψ₀(Ω_{Ω₂}) 比较，还需要带 Ω 形层号的参照（`Level` 的下标 `Ordᴵ` 只有 zero/suc/lim） | 无 | 判断 |

#### 2. 文件表

| 文件 | 代码行（非空/物理） | 冷编退出码 |
|---|---|---|
| `probes/OCF/Lean/YiTUReduce.lagda.md`（新） | 118 / 146 | 0。先删自身 `.agdai`，6G 上限，约 16 秒，日志只有本模块一行 Checking |
| `<实验目录>/YiTUStep0.agda`（临时，不进仓库） | 约 100 | 0 |

自查：禁用构造为 0，本机路径为 0。

#### 3. 定理表（都在 `YiTUReduce`，档位都是编译定理）

先说明两个目标与一个下标：`Goal = read (twᶜ 1) ≼ D.BTBOᴵ` 是旧块 YiLeg 上的目标；`Goalᶻ = readRW (twᶻ 1) ≼ D.BTBOᴵ` 是新主线上的目标（两者都来自 `YiXVStart`）。`lvl x = toLevel (read x) (HSr x)`，即树 x 读成的参照层号。

| 名字 | 逐字陈述 | 白话 |
|---|---|---|
| `γ⁺-step` | `∀ k → D.γ (suc k) ≼ D.γ (suc (suc k))` | 参照列从第 1 项起逐项不降 |
| `absorb-suc` | `∀ k → L.ψ⁰ (L.Ω (L.suc (D.L k))) ≼ D.γ (suc (suc k))` | 层号加 1 仍落在参照的下一项之内（抄自 `YiXVRef.ref-absorb` 的后半） |
| `rows→goal` | `(∀ n → Σ ℕ (λ m → read (G (pt n)) ≼ D.γ (suc m))) → Goal` | 每一行有某个参照项作上界就够，部分和由参照列吸收 |
| `goalᶻ` | `Goal → Goalᶻ` | 经 `rel≅ twᶻ1-R` 搬到新主线 |
| `St-read` | `(x : S.Tr S.zero) → St (read x)` | 第 0 层的树读回后，极限严格递增 |
| `emb↑` | `∀ x m → read x ≼ D.γ m → PEmb (lvl x) (D.L (suc m))` | 值序给出层号的前驱嵌入：`V1`，再 `V2`，再 `V3` |
| `UB`（定义） | `UB x = read (G x) ≼ L.ψ⁰ (L.Ω (L.suc (lvl x)))` | 待证的行界 |
| `UBᴱ`（定义） | `UBᴱ x = Σ L.Ordᴵ (λ a → (read (G x) ≼ L.ψ⁰ (L.Ω a)) × PEmb a (L.suc (lvl x)))` | 更弱的行界形状 |
| `step` | `∀ x m → UBᴱ x → read x ≼ D.γ m → read (G x) ≼ D.γ (suc (suc (suc m)))` | 一行的值界推进一步 |
| `ub→goalᶻ` | `(∀ n → UBᴱ (pt n)) → Goalᶻ` | 主归约 |
| `ubs→goalᶻ` | `(∀ n → UB (pt n)) → Goalᶻ` | 主归约，用 `UB` 的形状 |
| `ub→same` | `(∀ n → UBᴱ (pt n)) → (readRW (twᶻ 1) ≼ D.BTBOᴵ) × (D.BTBOᴵ ≼ readRW (twᶻ 1))` | 条件下，塔第 1 项与 BTBO 的参照互相 ≼ |
| `ub0` | `UB (pt 0)` | 等于 `row0-upper` |
| `ω⊑` | `L.ωᴵ L.⊑ᴵ L.suc (lvl (pt 1))` | `pt 1` 的层号逐项是有限层号 |
| `ub1` | `UB (pt 1)` | 由 `YiXVNeedOne.row` 加 `ω⊑` 得到 |

#### 4. 第一个障碍

**`UB (pt 2)`**，逐字是 `read (G (pt 2)) ≼ L.ψ⁰ (L.Ω (L.suc (lvl (pt 2))))`；也可以换成更弱的 `UBᴱ (pt 2)`。

它被挡住是**工程/设计上的**，不是数学上的：没有编译过的否定，我判断它在数学上成立。缺的是一个工具：一切可数层号（`h₁ x`）上、对任意树的折叠值上界模拟。

纸面分析如下：
- `G (pt 2)` 按定义（`refl`）是若干块的极限。每块是层号 `h₁ (f n)` 上 Ω 树的折叠，并带着继承来的底。
- 在后继层号的 Ω 行上，链点 `ψs … (up zero tt (suc c_n))` 是低一层的**任意树**，不是 Ω 树。
- 所以现有只对 Ω 树折叠的界（`ε₀-upper`、`allpre`、`NeedOne`）用不上。必须有一整套逻辑关系式的模拟，也就是 YiXV 的 UR/World/Out。
- YiXV 记下的接线缺口还在：极限上折的 bwd 行里，底 γ 不是孩子 m 的规范 `bs`。我判断应当让"底对参照前缀的界与路径无关"，即 γ 可以任意、只要它被同一个参照前缀界住，这与 YiXV 私有的 SeedInput 想法一致。
- 难点在参照一侧：要有一个参照 ψ 尊重的序，并且这个序支持各层的部分和吸收。我判断这是 YiXV 停下的地方。

#### 5. 偏离与事故；只凭转述引用的东西

- 没有偏离简报，没有遇到 251 或 124。临时文件里有 `UnsupportedIndexedMatch` 警告，因为临时文件的选项没有加 `-W`；仓库文件没有这个警告。
- **没有读、只凭转述的：**
  - YiXV 的余项 B1–B5 只按留档报告 `Reports-2026-11-12/YiXV.md` 读；243 件里只读了 `Start`、`NeedOne`、`SourcePrefixes`、`Ref`、`ReadFamily`、`ReadOmega`、`ReadRouteWorldInput`，其余只检索过签名。
  - `BTBOFull` 的 `V1`/`V2`/`V3`/`PW₁–₃` 只按签名用，用法与 `BTBOFull.Upp` 相同，没有读它们的证明。
  - `YiTFTight.Y₂-tw`、`YiSYSmall.fb`，以及 YiKT/YiTF 的两个值判断，都只来自简报转述，我没有核对。

主文件：<仓库>/probes/OCF/Lean/YiTUReduce.lagda.md
临时文件：<实验目录>/work/YiTU/YiTUStep0.agda

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：第 2 站闭项的上界工具（前缀 YiTU，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。本路选项原文 "第 2 站闭项的上界工具 (Recommended)"。同批另四路与你互不导入。

#### 作者的决定与背景（2026-11-17）
- 作者定：主线停逐项，改攻整体引理（读回域上的 Leaf 加 LowKeep）；参照只用记号关系 M。第七十三批选项原文："Fable 先读定义的独立审核：值会不会掉 (Recommended), 第 2 站闭项的上界工具 (Recommended), 构造续：限在读回域推导上的证据 (Recommended), 定义改动的候选原型"；摆脱侧 "前缀 3：自身折叠后的上折 (Recommended)"。同批五路：审核 `YiVA`（Fable 5.2）、上界 `YiTU`、构造续 `YiRQ`、定义候选 `YiDX`、摆脱侧 `YiPT`（Opus 5.5），互不导入。

- **决定性问题**：塔第 1 项（及以它为前缀的层号，例如同步对象 `kl 1 = tw 1 ⊕ ↑ (tw 1) (Ωt (tw 1))` 的孩子 `a₁ c`）上，折叠折到更低层时值会不会掉。若掉，就要改折叠的定义（第 4 层逼出，交作者）。
- **第七十一、七十二批的事实**（主审 8G 冷编复核过，读陈述；回报在 `probes/Survey/Reports-2026-11-16/`）：
  - 已成立：精确标签下 LowKeep 对一切不含 Ω 形状的层号无条件成立（`YiXPExact.lowKeepAt-noΩ`；合流后 `YiMGFrame.lowKeepAtᵐ-noΩ`）；Leaf 在读回域上（`YiGLDom.dom-top`、`YiMGRel.topᵐ`）；记号侧工具（`YiELLim.limAt`、`YiTAChain.ex-add′`、`ex-limc`、`lbl-limc`、`YiTAReal.real-exact`、`cofΩ-all`）。
  - 关系与证据档的否定（只否定接口或证据，不否定值）：`YiXPNeg.no-index-tree-tw1ˣ`；`YiTLReduce.no-index-top`、`block-frame`、`no-lbl-hh`；`YiMGNeck.no-chain-neck`、`no-frame-neck-child`；`YiKTSlot.no-above` 与同文件配套否定（槽位 `p*`）；`YiTFTw1.no-stepU′-tw1`、`no-wholeU-tw1`（前提全部实填）；`YiTFTight.no-tight′`、`vacuous`（`TightStep 1` 等价于实际底的前缀前提不可满足）。
  - 机制（编译）：`YiTFTw1.kp-leaf`：塔第 1 项叶子上，槽位在孩子里、目标非零且不含 Ω 时折叠走链；`YiKTSlot` 的有限测试：同一孩子里分支类型与读法相同的两个槽位，一个走链（`p*`），一个保留（`p₀`）；`YiTFBound.bS`：Ω₁ 树加可数尾巴的树读法低于 Ω₁+Ω₁；`YiTFTight.Y₂-tw : proj₁ Y₂ ≡ twᶻ 1`（实际继承底含第 2 站的闭项）。
  - **值上两个执行方判断不一致**（都未编译）：构造一路 YiKT（Fable 5.2）判断 `TightStep 1` 的结论 `Cand` 不成立、同步对象的值低于里程碑 ψ₀(Ω_{Ω₂})，机制是 `kp` 对 "Ω 形状、槽位在孩子里、路径经 `inc`" 恒走链加最小比较表在塔第 1 项上的退路行；配对否定一路 YiTF 判断有补偿（叶子自己的下标槽位被保留，加上自折叠，分支约为 ψ_d(Ω_c)，对一切可数 c 取上确界可达 ψ_d(Ω_Ω) 量级），净结果未定。
- 其他：`YiVNIdx.Gen.no-value-index-mono≈`（下标的树侧值序不能作下标单调的前提）；`YiFOValue.fallback-prefix`（退路保留此前折叠的值）；`YiXUFirst.first-ceiling`（干净对象第一支 ≤ ψ₀(Ω₄)）；`YiCXWindow`（局部派发允许不唯一的标签窗口）；`YiTDOrder`、`YiCVDomain`（全域派发等价于记号系统；现主线比较表在龙骨上不满足共现覆盖）；摆脱侧 `YiRRTwo.prefix-two`。

#### 本路的问题
配对否定一路 YiTF 指出：任何实际输出的值上界，都要先界住第 2 站的闭项 `twᶻ 1`（实际继承底在第 1 层含它：`YiTFTight.Y₂-tw`；第 0 层继承底不低于它：`YiSYSmall.fb`）。仓库里成规模的上界资产是暂停的 YiXV 一组（243 件；作者 11-15 设检查点暂停，本路由作者 11-17 选项重开，目标为上界工具），它的目标 `YiXVStart.Goalᶻ = readRW (twᶻ 1) ≼ D.BTBOᴵ`（只是类型）；已有 `YiXVSourcePrefixes.allpre : ∀ n → read (Start.pre n) ≼ L.ψ⁰ (E.Ω (suc (suc n)))` 等；留档 `probes/Survey/Reports-2026-11-12/YiXV.md`。另有 `YiXUFirst.first-ceiling`、`chain1-model`（干净对象第一支的上界与模拟证书）。

#### 要做的（按序）
0. 读 YiXV 的上界机制（检索 `allpre`、`Goalᶻ` 与它的归约文件），列出离 `Goalᶻ` 还差哪几条；在临时文件里编译最近的一条。不成立就停下回报。
1. **证 `Goalᶻ`**（第 2 站闭项不高于 BTBO 的参照 ψ₀(Ω_Ω)）；做不到就交最紧的上界与第一个挡住的引理。
2. 若有 `Goalᶻ`：往同步对象的输出（`YiSYSmall` 的 `Gᴱ` 的 `out`、`chain`）推上界，给出它与 ψ₀(Ω_{Ω₂}) 的比较。若能编译证明它**严格低于**里程碑，写成编译否定并停下（定义层面的信号，交作者）。

#### 规则（主审写给内部子智能体，必须照做）
- **先读** `AGENTS.md` 全文；性能问题先查 `probes/Survey/EBOHandbook.md` 4.2、4.6 节与 Bedrock 性能手册 `<Bedrock>/dev/cubical-agda-performance.md` 的 C-9（在变量上陈述、定义等式作假设、在唯一调用点实例化）、C-10（具体的站作 opaque 原子或模块参数）、S-1/S-3（重的构造在出生处封进 opaque，并在同一块里导出规格等式）、C-24、Q-1（`--profile=definitions`）、Q-23（量底价、二分）、H-6（251 之后不原样重跑）。
- **只新建文件**，放 `probes/OCF/Lean/`，用你的前缀（见上）。不改任何已有文件，不碰 `src/`、`archive/`，不碰别的前缀。中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行（判决与档位、做了什么、不否定什么、入口）；代码之间只写范围与不显然的理由。一次性的试验放你的临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要把前三个也写上，否则报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（写 `<实验目录>`、`<仓库>`）。
- **编译**（仓库根目录）：`agda +RTS -M6G -RTS --library-file=<库文件> -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`；临时目录的纯 `.agda` 另加 `-i <你的临时目录>`。退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 Agda 内部错误。报退出码不经过管道。同时只跑一个 agda，堆上限 6G（同批另有四路，外部广撒网也可能在编，机器共 64G；峰值超过 4G 先改形状）。不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下，写字面路径）。大的 `refl` 前加 `timeout 600`。
- **停下的条件**：退出 251 时不原样重跑，先按 C-9、C-10、S-1 改形状并定位（附 profile 或二分数据）；改过形状后同一上限仍撞墙才停。同一处两次重新设计仍过不了检查器也停。若某一步要改树、折叠或合法性的定义，停下回报。没有编译的否定时只写 "未走通"。
- **过程**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。动手证一般形式之前先用临时文件检查前提可满足；已有引理先检索（`grep`）再写，不重证，搬来的证明在文首写明来源。查签名用检索，不整篇读大文件。
- 不在你的临时目录与你前缀的新文件之外写、删、移任何东西；不 `pkill`，不写 `/tmp`，不装包，不提交，不改 `probes/README.md`、`probes/LOG.md`、台账与留档。
- **两条已更正的事实**（不要再照旧说法写）：`YiMXNote.¬Mono` 否定的是记号一侧非标准形项的项序单调，**不是**树侧折叠的跨层单调（树侧跨层单调目前没有编译的否定）；`YiKWObjects.kept` 是新封装的对象，与 `YiC1Slot` 不透明块里的 `kept` 不是同一个。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0；文首标 "不读记号" 的文件用 `python3 probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包。

#### 回报（最后一条消息就是回报，主审会原样留档）
1. 判决：先说对纲领与目标意味着什么；各步到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理；是数学上挡住还是工程上挡住。
5. 偏离与事故；没有读、只凭转述引用的东西。
不用 "只差"、"自然" 一类形容；判断与定理分开写。

