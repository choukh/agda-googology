# 塔第 2 项以上的值参照 (YiRef)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-13 08:55 至 09:27 |
| 工具调用 / agda 编译 (粗数) | 69 / 21 |
| token (usage 字段，按消息去重) | 输出 147841；新写入缓存的输入 305635；读缓存的输入 11453474；其余输入 120 |
| 写过的仓库文件 | `YiRefTw2.lagda.md` |
| 文件前缀 | `YiRef` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: F3 与值参照返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 出口归约到逐行, 无前提 (closed-PH, endpoint); Row₂ 等陈述 (未证); 参照框架无 Ω 结点层号, 推荐记号直连的下界模拟; 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方。全程用中文写文件与回报。主审会复核你交的每个文件，只认编译过的定理。

作者 2026-11-13 的方向（原话）："先重点排查 YiUp，把关键路径上的问题都尽早暴露出来，如果没有问题，就上攻，其他候选路线仅作后备"。这一路是作者选的 "塔第 2 项以上的值参照"，说明："现参照框架的层号没有 Ω 结点层号。查清仓库里可用的参照（EBO 参照树、出口 ebo-lower 要什么），给出塔第 2 项一站可用的参照与陈述，小编译验证。Opus 5.5。"

同批在跑四路（`YiLim`、`YiOmC`、`YiUpSim`、`YiView`），你不读它们的输出，也不动它们的文件。

###### 背景（只信编译定理）
- **主候选 YiUp 线**（`probes/OCF/Lean/` 下的 `YiUpBlock`、`YiUpFold`、`YiUpLegal`、`YiUpVal`、`YiUpValTw1`，主审已复核）：
  - 塔 `tw n`（空白页的块 `YiFreshBlock`：`tw 0 = zero`，`tw (suc n) = Ωₗ (tw n) (λ c → tw n ⊕ ↑ (tw n) c)`，`Λ = lim tw`）；
  - 读回 `YiFreshValRead.read : Tr zero → T₀`，`T₀ = L.Ordᶜ L.zero`，参照框架是 `OCF.Align.Level`；
  - 值定理 `YiUpVal.bho-lower : L.ψ⁰ (L.Ω I2) ≼ read (ψ₀ two tt (Ωt two))`，以及 `YiUpValTw1.bho-tw1`；
  - 条件定理 `btbo-tw1′`（BTBO 参照 `D.BTBOᴵ`）。
- **V81 执行方说**（判断，未核）：参照框架 `OCF.Align.Level` 的层号只有零、后继、ℕ 极限，塔第 2 项（层号含 `Ωₗ`，以可数树为分支的 Ω 结点层号，读作 Ω_Ω 一类）的值验收要另找参照。
- **已有的参照与出口**（检索陈述）：
  - `probes/OCF/Align/EboLeanTree.lagda.md`：`EBO-tree′`、`fgh-EBO′`、`HC`、`hc-tower`。
  - `probes/OCF/Lean/YiMonoExit.lagda.md`：`exit`、`ebo-lower`、`Closed`。
  - 旧块上更高的值定理：`YiSyncTwo`（`X₂≼TΛ`，参照 `S2.X₂`，读作 ψ₀(Ω_Ω+Ω₂)，没有记号标签 `X₂-unlabel`）；`YiLamVBtbo`（`btbo-TΛ`、`BTBO-label`）；`YiRelK`。

###### 要回答与交付
1. **清单**：仓库里哪些参照（树、记号项、ψ 函数）的层号含 Ω 结点层号（以可数序数为下标的 Ω_x，x ≥ Ω）。各在哪个模块、与 `_≼_` 怎样接、有没有记号标签、是否已有编译的 "参照 ≼ 闭项" 一类定理可作样板。用检索，不整篇读大文件。
2. **出口要什么**：`ebo-lower` 的前提 `Closed P` 逐字写出；说明在 YiUp 线上要交的 "一族（记号项，树）" 长什么样，它对塔第 2 项一站意味着什么。
3. **塔第 2 项一站的陈述**：
   - 选一个可用的参照 R₂（例如读作 ψ₀(Ω_{Ω+1}) 或 ψ₀(Ω_Ω) 一类，由你据清单定）；
   - 写出 "R₂ ≼ read (YiUp 塔第 2 项的闭项)" 的精确陈述，或换成经 `ebo-lower` 的形式；
   - 新文件 `YiRefTw2`（验收文件）里**只编译陈述与参照的定义**（陈述写成类型 `Set`，不证），并做小的有限测试，确认参照与闭项的类型接得上（例如 `read` 的类型、层号的读法）。
4. **若参照框架确实缺 Ω 结点层号**：给出最小的扩展方案（Agda 草图），或指出现成可借的参照；估计行数；说明它会不会触及壁垒（`probes/OCF/Barrier.lagda.md`）。

###### 先读什么
- `AGENTS.md` 全篇。
- `YiUpVal`、`YiUpValTw1`（检索 `read`、`I2`、`At`、`btbo-tw1′`）；`YiFreshValRead`。
- `OCF.Align.Level`（检索层号的定义、`ψ`、`ψ⁰`、`Ω`）。
- `EboLeanTree` 文首与 §3；`YiMonoExit` 全读（短）。
- `YiSyncTwo`、`YiLamVBtbo` 的文首。
- `probes/Survey/OrdinalNotationsGuide.md`（查记号用）。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiRef`（模块名 `OCF.Lean.YiRef…`），验收文件，文首标 "验收文件"，可导入记号与参照框架。不改任何已有文件，不碰 `src/`、`archive/`。
- 中文 literate Agda。每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞（陈述写成 `Set` 类型的定义，不留洞）、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 6G。
  - 冷编译只删自己模块的接口，写字面路径；不删别人的 `.agdai`。
  - 大的参照树放 `opaque`（手册 §4）。
- 临时目录：`<实验目录>/agents/ref`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- **过程要求**：每次回复都要有工具调用；读完先写清单，再动手编译。
- 结束前自查：每个文件删自己的接口后冷编译退出码 0；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：塔第 2 项一站用什么参照；有没有现成的；缺什么；暴露出的关键路径问题，表：问题、位置、档。
2. 参照清单（表：名字、模块、读法、与 `_≼_` 的接法、有无标签、已有定理）。
3. 文件表与定理表（名字、逐字的陈述、档）。
4. 扩展方案（若需要）与行数估计。
5. 偏离与事故。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 回报: YiRef (塔第 2 项一站的值参照)

##### 1. 判决
**对纲领与目标.** 这一站的参照不需要新的参照框架，也不触及壁垒。参照可以直接用记号沿基本列造的树：`EboLeanTree` 的 `hc` 对一切可数标准形给出 `HC` 推导与布劳威尔树，层号含 Ω 结点也可以，并且带标签。缺的是证明用的关系，要把带 ψ_Ω 的记号项（或 Level 里的替身）对到第 `tw 1` 层的块树上。这只是验收层的事（第 4 层），不改树、折叠、合法性。

- **采用的参照 R₂**：`Rt (hc-tower 3)`，读作 ψ₀(Ω_{Ω_Ω})，即出口 `ebo-lower` 在 k = 3 的那一行。另给两个小站：ψ₀(Ω_{Ω+1})（`Rt h₊`，标准形是本文件新证的）和 ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}})（k = 3 那一行的第 1 个基本列项）。这三个参照都在 `L.Ordᶜ L.zero` 里，与 `read` 的值域相同，都带标签（编译定理）。
- **有没有现成的**：
  - 树的构造是现成的（`hc`、`hc-tower`、`lab-tree`）。
  - `OCF.Align.Level` 里读作 ψ₀(Ω_{Ω+1}) 且带标签的参照，本文件之前没有：已有的两个在别的树类型上（`Ordˢ` 和 `OCF.Free.Level`）。
  - Level 里的朴素版本没有标签（`naiveO-unlabel`）。
- **缺什么**：
  - 块树与记号之间的模拟关系，以及它在塔第 2 项上的折叠保持引理。
  - YiUp 上的 `Into 2`。

**关键路径上的问题**

| 问题 | 位置 | 档 |
|---|---|---|
| Level 的层号只有 `zero`、`suc`、`lim f s`，没有 Ω 结点层号（V81 的判断已核实）。`YiUpVal` 那种逐层模拟（`S : T₁ → Tr one → Set`）在 `tw 1` 这一层（Ω 结点，读作层 Ω）找不到对应的参照层。 | `Level.lagda.md:62-65` | 定义事实 |
| k = 3 那一行的闭包含 BTBO 那一行：`fsn (EBOψ 3) 0 ≡ EBOψ 2`，并且 `row₂→btbo : Row₂ → Rt (hc-tower 2) ≼ read Tw₂`。所以这一站本身就包含一个 BTBO 下界（对 Tw₂，不是对 Tw₁）。另：V81 怀疑 ℕ 极限层号的跨孩子行会掉值，`Tw₂` 的计算经过同一组行（层号 `tw 1 ⊕ ↑c`，c 可含 ℕ 极限），这个疑点在这一站没有被绕开。 | YiRefTw2 | 编译定理 + 有限测试；"同一组行" 是判断 |
| 越过 BTBO 的第一步就塌缩到层 Ω：`fsn t₊ 1 ≡ ψ₀(ψ_Ω(Ω_Ω))`。所以塔第 2 项上任何高过 BTBO 的站，证明都要一个关系，把带 ψ_Ω 的记号项对到 `Tr (tw 1)` 的树。 | YiRefTw2 的有限测试 | 测试；推论是判断 |
| `Into n`（`read (twᶜ n) ≼ read EBOᶜ`）在 YiUp 上没有定理，检索也没有找到基底单调的引理。`EBOᶜ` 的第 n 支用的是由前缀折出的底，不是 `B₀ (tw n)`。 | `YiUpFold` 的 `ψ⊥ (lim g)` 行；`YiPhiBlock.B₀` | 缺口（所需引理的形状是判断） |
| `Rt (hc-tower 2)` 与 `btbo-tw1′` 用的 `D.BTBOᴵ` 之间，这里没有编译的连接。 | `YiUpValTw1` | 缺口。可能的路径（判断）：`Label.BTBO-label` + `EboLeanCmp.lab⟦⟧` + `Lab-uniq` 给出与 `N.BTBOᴵ` 的 ≅，但 `EboLeanCmp` 要把归档拷贝加进 `-i`；`N` 与 `D` 的关系未查。 |
| 给具体的参照树另起名字再拿来比较，检查器会沿 `hc-tower` 的良基证明展开，6G 堆耗尽（退出 251）。写法：只用 `Rt` 作用在推导上，引理对一般的推导陈述，再代入具体推导。 | 临时试验 | 实测 |

##### 2. 参照清单（只列读法里含 x ≥ Ω 的 Ω_x）

| 名字 | 模块 | 读法 | 与 `_≼_` 怎样接 | 标签 | 已有 "参照 ≼ 闭项" 定理 |
|---|---|---|---|---|---|
| `tree (hc-tower k)`, `EBO-tree′` | Align/EboLeanTree | ψ₀(Ω-塔_k)：k=2 是 ψ₀(Ω_Ω)，k=3 是 ψ₀(Ω_{Ω_Ω}) | 经 `YiMonoExit.toL` 到 `L.Ordᶜ L.zero` | 有：`EboLeanLab.ebo-lab′`；`EboLeanCmp.lab⟦⟧` | k≥3 没有；`exit`/`ebo-lower` 只是归约 |
| `hc nt ct`（任意可数标准形） | 同上 | 任意 | 同上 | `lab-NF′` | 样板 `TTopValRef.Y⊤`（ψ₀(Ω_{Ω²})），但它在 `OCF.Free.Level` 上 |
| `N.BTBOᴵ`, `D.BTBOᴵ` | NoCumsum；Diagonal（经 YiBtValBT） | ψ₀(Ω_Ω) | 直接 | `Label.BTBO-label` | `YiLamVBtbo.btbo-TΛ`（旧块，无前提）；`YiUpValTw1.btbo-tw1′`（YiUp，条件定理） |
| Stage2 的替身层 `ℓ₀`：`ψ⁰ (Ω ℓ₀) ≡ BTBOᴵ` | Align/Stage2 | ψ₀(Ω_Ω+1)（`ts-label`）；ψ₀(Ω_Ω+y)（`Ctx₀`，y 可数）；`X₂`：ψ₀(Ω_Ω+Ω₂)；朴素的 `NO`：ψ₀(Ω_{Ω+1})；`T₂`：ψ₀(Ω_Ω·2) | 直接（层号可数） | `X₂-unlabel`、`naiveO-unlabel` 是否定；`T₂` 只有部分标签 | `YiSyncTwo.X₂≼TΛ`、`YiRelKOne.X₂≼TΛᴷ`（旧块） |
| `X₁₂`, `Xω`, `X²`, `Xε`, `Xψ₁`, `χ₁`, `X₃` | YiShp*、YiL1Base、YiAboveCtx、YiStepTree | ψ₀(Ω_Ω+…) | 直接 | `X₁₂-label`、`χ₁` 有标签，其余读法是判断 | 旧块：`X₁₂≼TΛ`、`Xε≼TΛ`、`Xψ₁≼TΛ`；`X₃≼ᵇ` 是条件定理 |
| `T2ᴸ`, `Tkᴸ`, `Tωᴸ` | GoodL、OmegaK | ψ₀(Ω_Ω·2)、ψ₀(Ω_Ω·k)、ψ₀(Ω_Ω·ω) | 直接 | 有 | 对 YiUp 的闭项没有见到 |
| `TO` | Uniform3OmegaPlus1 | ψ₀(Ω_{Ω+1}) | 树类型是 `Ordˢ`，接不上 `read` | `TO-label` | 无 |
| `Ref` | CtxMonoAccept | ψ₀(Ω_{Ω+1}) | 在 `OCF.Free.Level` 上 | `label-Ref` | `TreeLevelsO8`（SumOne 线的上界义务） |
| **新：** `Rt (hc-tower 3)`、`Rt (hω-inv (hc-tower 3) refl 1)`、`Rt h₊` | Lean/YiRefTw2 | ψ₀(Ω_{Ω_Ω})、ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}})、ψ₀(Ω_{Ω+1}) | 直接 | `lab₃`、`lab₃₁`、`lab₊` | 只有陈述 |

"YiShp 一族都用 Stage2 式的替身前缀"这一点，是据 README 和各文首说的，没有逐个核对。

##### 3. 出口要什么
`YiMonoExit` 的前提，逐字：
```agda
record Closed (P : T → L.Ordᶜ L.zero → Set) : Set where
  field
    step1 : ∀ {t X} → P t X → cof t ≡ c1 → Σ (L.Ordᶜ L.zero) λ X′ → P (pred t) X′ × (L.suc X′ ≼ X)
    stepω : ∀ {t X} → P t X → cof t ≡ cω → ∀ n → Σ (L.Ordᶜ L.zero) λ X′ → P (fsn t n) X′ × (X′ ≼ X)
ebo-lower : ∀ {P} → Closed P → (Y : L.Ordᶜ L.zero) →
  (∀ k → Σ (L.Ordᶜ L.zero) λ X → P (EBOψ k) X × (X ≼ Y)) → toL EBO-tree′ ≼ Y
```

- 典范的一族 `PH t X = Σ (HC t) λ h → Rt h ≼ X` 不需要任何前提就封闭（`closed-PH`）。所以出口归约成逐行的陈述 `∀ k → Rt (hc-tower k) ≼ read EBOᶜ`（`endpoint`）。
- 换别的一族（例如 P t X = 块树 x 模拟 t 且 read x ≼ X），只是把内容从 "行" 搬进 `Closed`。
- 编号（判断）：
  - `tw 1` 读作层 Ω，所以 `twᶜ 1` 约为 ψ₀(Ω_Ω)，即 EBOψ 2。
  - `tw 2` 读作层 Ω_{Ω+1}，所以 `twᶜ 2` 约为 ψ₀(Ω_{Ω_{Ω+1}})，不低于 EBOψ 3。
  - 编号核对：`twᶜ 1 ≡ Tw1′` 是 `refl`。
- 对塔第 2 项一站：k = 3 那一行拆成 `Row₂` 与 `Into 2` 两件。
  - 它的闭包第 0 项是 BTBO 那一行。
  - 第 1 项是 ψ₀(Ω_{Ω_{ψ₀(Ω_Ω)}})，见 `row₂→btbo`、`row₂→step`。

##### 4. 文件表与定理表
文件：`<仓库>/probes/OCF/Lean/YiRefTw2.lagda.md`，验收文件，235 行。删掉自己的接口后冷编译退出码 0，用时 11.4 s，堆上限 6G。禁用构造与本机路径的检索结果为 0。

陈述（只是 `Set`，未证）：
- `Row₂ = Rt (hc-tower 3) ≼ read Tw₂`
- `Step₂ = Rt (hω-inv (hc-tower 3) refl 1) ≼ read Tw₂`
- `Step₂⁺ = Rt h₊ ≼ read Tw₂`
- `Into n = read (twᶜ n) ≼ read EBOᶜ`

其中 `Tw₂ = twᶜ 2`，`Rt h = toL (tree h)`，`t₊ = E.ψ [] (E.Ωs (E.Ωt (E.natT 1))) ∷ []`，`h₊ = hc nf₊ (c∷ c[])`。

编译定理（都无前提）：
- `closed-PH : Closed PH`
- `endpoint : (Y : T₀) → (∀ k → Rt (hc-tower k) ≼ Y) → toL EBO-tree′ ≼ Y`；前提可满足：`endpoint-sat : ∀ k → Rt (hc-tower k) ≼ toL EBO-tree′`
- `row₂-exit : Row₂ → Σ T₀ λ X → PH (EBOψ 3) X × (X ≼ read Tw₂)`
- `row₂→step : Row₂ → Step₂`
- `row₂→btbo : Row₂ → Rt (hc-tower 2) ≼ read Tw₂`
- `step⁺→btbo : Step₂⁺ → Rt (hc-tower 2) ≼ read Tw₂`
- `nf₊ : NF t₊`
- `lab₃ : LL.Labᴸ (tree (hc-tower 3)) (EBOψ 3)`、`lab₃₁`、`lab₊ : LL.Labᴸ (tree h₊) t₊`
- 辅助引理 `hω-inv`、`fs≼`、`tree-≼`

有限测试（都是 `refl`）：
- `twᶜ 1 ≡ Tw1′`
- `tw 2 ≡ Ωₗ (tw 1) (λ c → tw 1 ⊕ ↑ (tw 1) c)`
- `at (tw 2) (inj₁ (inj₁ tt)) ≡ tw 1`
- `Br (tw 2) (inj₁ (inj₁ tt)) ≡ Tr (tw 1)`
- `Br (tw 1) (inj₁ (inj₁ tt)) ≡ Tr zero`
- `tw 1 ⊕ ↑ (tw 1) zero ≡ tw 1`
- `Ωt (tw 2)` 的形状
- `cof (EBOψ 3) ≡ cω`、`fsn (EBOψ 3) 0 ≡ EBOψ 2`、`fsn (EBOψ 3) 1 ≡ ψ₀(Ω_{Ω_{EBOψ 2}})`
- `cof t₊ ≡ cω`、`fsn t₊ 0 ≡ EBOψ 2`、`fsn t₊ 1 ≡ ψ₀(ψ_Ω(Ω_Ω))`

##### 5. 扩展方案（行数都是估计）
- **C（Ordᴵ 加 Ω 结点构造子，ψ 不变）：排除。** Level 的 ψ 用 `with <ᴵ-dec (σ q) p` 派发（`Level.lagda.md:404`）。Stage2 的 D1（Ω_Ω 结点的分支遍历全部可数层号，与 `tw 1` 同形）有编译否定 `dec→WLPO : (∀ a → Dec (a ≺ᴵ suc ωᴵ)) → WLPO`；一般形式是 `Barrier.barrier : Ω-Extension → LPO`。机制已逐条核对：分支层号要与固定目标三向比较。改成按槽位派发，就等于把 YiFreshBlock 重写一遍当参照，它就不再是独立的参照（判断）。
- **B（Level 的可数替身 ℓ₀ / D3 的 M_k）：现成，但标签止于 ψ₀(Ω_Ω+Ω₂)**（`X₂-unlabel`）。塔第 2 项还要塌缩到层 Ω 的替身，以及层 Ω+c 的替身（c 要先折叠），翻译成分重。不推荐（判断）。
- **A（推荐）：记号直连的下界模拟。** 草图：
```agda
data Mᴱ (j : LF) : E.T → Tr j → Set where
  m0 : ∀ {t x} → cof t ≡ c0 → Mᴱ j t x
  m1 : ∀ {t x} → cof t ≡ c1 → Mᴱ j (pred t) x → Mᴱ j t (suc x)
  mω : ∀ {t f} → cof t ≡ cω → (∀ n → Mᴱ j (fsn t n) (f n)) → Mᴱ j t (lim f)
  mΩ : ∀ {t ν p g} → cof t ≡ cΩ ν → (∀ {s c} → Mᴱ (at j p) s c → Mᴱ j (fsT t s) (g (fromBr j p c))) → Mᴱ j t (Ω p g)
  mw : ∀ {t x x′} → Mᴱ j t x → j ⊢ x ◃ x′ → Mᴱ j t x′
Pᴱ t X = Σ (Tr zero) λ x → Mᴱ zero t x × (read x ≼ X)
```
  - 关系加 `Closed Pᴱ`：约 40 到 80 行。
  - 折叠保持（`ψ⊥`/`ψs` 对 `Mᴱ`，记号的规则 6 链对块的 `iter step` 链）：一层约 300 到 600 行，对照 `YiUpVal` 的 355 行。
  - ℕ 极限层号那部分就是 `LOWER′` 型的开问题，规模不明。
  - 不触壁垒：不比较块的层号，只比较记号项，`cmpᵀ` 对语法项可判定（判断）。

##### 6. 偏离与事故
- 比 "只编译陈述与参照定义" 多做了几件：连接陈述的小定理（`closed-PH`、`endpoint`、`endpoint-sat`、`row₂→…`、`step⁺→btbo`）、ψ₀(Ω_{Ω+1}) 的标准形证明 `nf₊`、三条标签。这一站本身一条也没有证。
- 临时试验里三次堆耗尽（退出 251，各约 70 s）；原因见上表最后一行，已改写法。一次 `-v` 追踪也是 251。用交互模式算了记号的基本列。
- 为测试 `twᶜ 1 ≡ Tw1′` 导入了 `YiUpValTw1`，多约 4 s。
- 只新建了这一个文件，没有改任何已有文件，没有删别人的接口文件，没有提交。临时文件都在 `<实验目录>/agents/ref`。
- 对 "塔第 2 项" 的理解：取 `twᶜ 2`（与 `Tw1′ = twᶜ 1` 的编号一致）。旧块 README 的编号不同（那里读作 BTBO 的是第 2 项）。
