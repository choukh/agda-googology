# (1) 证 Tower：主线严格越过 ψ₀(Ω_Ω+ψ₁(Ω₂)) (YiTW)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-13 17:56 至 18:12 |
| 工具调用 / agda 编译 (粗数) | 24 / 4 |
| token (usage 字段，按消息去重) | 输出 85077；新写入缓存的输入 282672；读缓存的输入 4242207；其余输入 46 |
| 写过的仓库文件 | `YiTWEnd.lagda.md`, `YiTWLow.lagda.md` |
| 文件前缀 | `YiTW` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-14: (1) Tower 返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 无前提: Tower, V130 (主线见证严格高于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照), tA≺EBOᴿ (主线终点闭项严格高于该参照); 缺口 1 由一般引理 low 闭合 (一切路径), 缺口 2 不需要; 两件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的选择（2026-11-14，选项原文）
"(1) 证 Tower，主线严格越过 (Recommended)"，模型 "(1)(3) Fable 5.2，(2) Opus 5.5 (Recommended)"。
选项说明原文："补两条缺口（槽位路径上起点折叠 ≥ BTBO；后继情形上折的三条保持），得主线见证严格高于 ψ₀(Ω_Ω+ψ₁(Ω₂))；这一类引理也是两路候选判据的卡点"。

同批另一路是 (2)：把下降引理搬到候选 A，前缀 YiKA。你不动它的文件。

###### 要证的（台账 V132）
`YiG0Low.Tower`（F2）：

`Tower = ∀ n → M⁰ (fsn tA n) (G (suc DR.E₀))`

- `fsn tA n` 是 ψ₀(Ω_Ω+ψ₁(γₙ))，见 `YiMWLow.tA-fs`（`refl`）。
- 它成立就由已编译的 `tower→V130` 得主线见证严格高于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照：
  `Tower → (h : HC tA) → O.suc (R2.Rt h) ≼ readRW Vᴿ`。
- 若能直接证终点闭项严格高于 tA（`O.suc (R2.Rt h) ≼ readRW EBOᶜ`），也算交付。

###### 已编译的起点（主审复核过；文档里的叙述是数据）
**`YiG0Low`、`YiG0Mono`**（回报 `probes/Survey/Reports-2026-11-12/YiG0.md`）：
- `G-low`：加法型一般引理，`M⁰ (ψ₀ᵗ t) (G c₀) → M⁰ η y → M⁰ (ψ₀ᵗ (t ++ η)) (G (c₀ + y))`；
- `G-suc`、`G-mw`、`G-strict`、`G-infl`、`formS`（`G (suc x)` 是链 `zs x` 各行的部分和极限）；
- `G-mono`：G 沿字面 ◃ 跨层单调。

**YiG0 的第一个障碍**（§4，判断部分要核）：
- `G (suc E₀)` 是层号 a = `h₁ E₀` 上链 `zs` 的折叠。`zs 2` 之下字面地有一个结点：槽位是 a 的子层号 2 上的那个，分支是 `next (Up one d (Ωt a) u)`。"(0,0) 位置的子层号是 2" 只做了纸面展开。
- 要照 `YiMEAnchor.At` 的三条保持（`PF`、`QH`、`VW`）让 ψ₀(Ω_Ω+ψ₁(γₙ)) 对着这个结点的折叠，缺两条：
  1. **起点沿槽位路径的折叠不低于 BTBO**：`D.BTBOᴵ ≼ read (ψs a … (B₀ a) zero (posW a p₁) (Ωt zero) … (Ωt a))`。已有的 `YiLSTw1.KG` 只管提升形路径（`LiftP`），`posW` 走 `inl`，不在它的域里。
  2. **后继情形的上折**：`ψs`、`ψ⊥` 作用在 `next (Up … u)` 上不是 `next` 的形状，三条保持各要一份。
- 执行方判断：在层号 a 上直接写 `Mᴰ` 实例走不通（关系太刚）。

**可能有用的新工具**：
- `YiEVReach`（回报 `YiEV.md`）：
  - 底的条件 `Hi`（`b⊥` 与第 0 层各分量 ≥ BTBO 的参照）与 `OKB` 沿孩子的底封闭（`hi-dS`、`hi-dL`、`hi-dW`）；
  - 一般下降 `reach`；`AtTwo`：层号 2 处带前缀的锚点用于一般底。
- `YiMWPre`：`sem→M⁰`（`lower⁰` 的逆）、`M⁰-≼`、`Pre`（带记号前缀的 ψ₀(Ω₂) 锚点，对任意底）。
- `YiMEBase`/`YiMEAnchor`：`Mᴰ`、`M⁰`、`lower⁰`、`At`。
- `YiVR*`：块侧值关系与折叠保持 `fl`、`fold-≼`。
- `YiLSTw1`：`G`、`K`、`KG`、`lower-↑`。

**第十六次独立审查的判断**（纸面，`Review16.md`）：
- 见证值严格高于 tA，把握高。理由：β₁ 最左一次出现折到第 0 层时回灌 G，链点高于 BTBO。
- 若你找到编译的反面（见证值 ≼ tA 的参照），同样交上。

###### 要做
1. 证 `Tower`，或直接证主线见证（或终点闭项）严格高于 tA 的参照。路线由你定。
2. 做不到就交第一个挡住的引理；能单独编译的缺口引理（上面的 1、2）分别交上。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiTW`（模块名 `OCF.Lean.YiTW…`）。不改任何已有文件，不碰 `src/`、`archive/`。这是验收文件，文首标明；树、折叠、合法性一行不改。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的标 "条件"。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
  - 堆墙：不要在具体推导上直接比较两个 `Rt`，对一般推导陈述再代入；具体参照树放 `opaque`；见 `probes/Survey/EBOHandbook.md` 第 4 节。
- 临时目录：`<实验目录>/agents/tw`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽；连续两条同形的退化反例。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：`Tower`（或严格越过 tA）是否编译成立；对纲领与目标的意义；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档；值写成 ψ₀(Ω_x)，并写清参照的读法依据。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 回报：V132（`Tower`）与 V130，前缀 YiTW

##### 1. 判决

**`Tower` 编译成立，V130 编译成立，终点闭项严格越过 tA 也编译成立。三条都是无前提的闭项，8G 冷编退出码 0。**

- `tower : Tower`（F2），即 `∀ n → M⁰ (fsn tA n) (G (suc DR.E₀))`。
- `V130 : (h : HC tA) → O.suc (R2.Rt h) ≼ readRW Vᴿ`（主线精简块）。它由 `strictE` 直接得到，不经 `tower→V130`。
- `tA≺EBOᴿ : (h : HC tA) → O.suc (R2.Rt h) ≼ readRW RW.EBOᶜ`（主线精简块的终点闭项）。

**对纲领与目标：**
- 两个文件都是验收文件（读记号），不进成品；树、折叠、合法性一行未改。
- 主线见证与终点闭项的值都严格高于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照。这里 "严格" 的内容只是 "参照的后继不高于它"，不是值的定位。
- 没有给出 `G (suc E₀)`、见证或终点的值；不涉及上界。
- 证明里没有新的翻译脚手架：新引理 `low` 只说树（折叠值不低于孩子），记号只在已有的 `reach` 里出现。

**做法与简报预想的不同：没有用上折，缺口 2 没有碰。**
- `G (suc x)` 的链第 1 项 `next (Ωt ℓ)` 之下字面地就有 `up (Ωt ℓ) 0 (Ωt (g 0))`，不必走到 `zs 2`。
- 这个嵌入的折叠是孩子 0 上的折叠，底是 `dL g … (B₀ ℓ) 0 (Ωt ℓ)`。只要这个底满足 `YiEVReach.Hi`，已有的 `reach` 就给出 tA 的参照。
- `Hi` 的第 0 层分量正是简报的缺口 1。它由新引理 `low` 闭合，对一切路径成立，包括走 `inl` 的 `posW`。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| `Tower` | `YiTWLow.tower` | 编译定理，无前提 |
| V130（见证严格高于 tA 的参照） | `YiTWLow.V130`，F2 上 `V130ᶠ` | 编译定理，无前提 |
| 终点闭项严格高于 tA 的参照 | `YiTWEnd.tA≺EBOᴿ`，F2 上 `tA≺EBO` | 编译定理，无前提 |
| 缺口 1（起点沿槽位路径的折叠不低于 BTBO） | `YiTWLow.low` 加 `Main.hi′` | 编译定理；量化域是读自第 0 层的树的层号 `h₁ x`、带 `OKB` 的底、一切路径 |
| 缺口 2（后继情形上折的三条保持） | 无 | 未做（这条证法不需要） |
| V128 强形式（`G c` 对 ψ₀(Ω_Ω+ψ₁(Ω_η))） | 无 | 未做 |
| tB 第 1 行 | 无 | 未做 |
| 见证或终点的值、上界 | 无 | 未做 |

##### 2. 文件表

都在 `<仓库>/probes/OCF/Lean/`。删自己的两个接口后冷编，堆上限 8G，每份日志只有本模块一行 `Checking`。禁用构造与本机路径检索为 0。

| 文件 | 总行 / 代码行 | 冷编退出码 | 内存（`+RTS -s` total in use） |
|---|---|---|---|
| `YiTWLow.lagda.md` | 213 / 140 | 0 | 2099 MiB |
| `YiTWEnd.lagda.md` | 77 / 48 | 0 | 1941 MiB |

冷编日志在 `<实验目录>/agents/tw/`，文件名 `YiTWLow.cold.log`、`YiTWEnd.cold.log`。

##### 3. 定理表

记号：
- `read` 是 `YiLSRead.read`；`G`、`h₁`、`εh`、`ρh` 是 `YiLSTw1` 的；`E₀`、`V` 是 `YiDropRow` 的。
- `Hi`、`reach`、`_⇐_` 是 `YiEVReach` 的；`tA` 是记号项 ψ₀(Ω_Ω+ψ₁(Ω₂))（`YiNFOCase`）。
- 参照的读法依据：`R2.Rt h` 是 `HC` 推导沿记号基本列造的树，ψ₀(Ω_x) 的写法来自项本身。

| 名字 | 逐字的陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `nlt` | `∀ n k → NLt (cmp (add n k) k)` | 孩子编号 n+k 与 k 比较不会是 "小于" | Low | 编译定理 |
| `low` | `(x : Tr zero) (ε : Ev (h₁ x)) (ρ : Rt (h₁ x)) (B : Base (h₁ x)) → OKB (h₁ x) B → (w : zero ≤ h₁ x) (β : Tr zero) (nβ : zero ⊢ zero ◃ β) → read x ≼ read (ψs (h₁ x) ε ρ B zero w β nβ (Ωt (h₁ x)))` | 层号 `h₁ x` 的 Ω 树沿任意路径、任意起点折到第 0 层，值不低于 x | Low | 编译定理 |
| `Main.hi′` | `Hi (g 0) B′`，其中 `B′ = dL g (εh x) (ρh x) (B₀ ℓ) 0 (Ωt ℓ)`，`x = lim f s`，`ℓ = lim g`，`g n = h₁ (f n)` | x 不低于 BTBO 的参照时，孩子 0 的这个底的 `b⊥` 与第 0 层各分量都不低于 BTBO 的参照 | Low | 编译定理（模块前提 `hb : D.BTBOᴵ ≼ read (lim f s)`） |
| `Main.T◃` | `ℓ ⊢ Tu ◃ zs x 1`，`Tu = up (Ωt ℓ) 0 (Ωt (g 0)) (Ωt-nz (g 0))` | 链第 1 项之下字面地有这个嵌入 | Low | 编译定理 |
| `strictX` | `(x : Tr zero) → two ⇐ h₁ (seq0 x) → D.BTBOᴵ ≼ read x → (h : HC tA) → O.suc (R2.Rt h) ≼ read (G (suc x))` | x 是 ℕ 极限、第 0 项的层号能下降到 2、x 不低于 BTBO 的参照，则 `G (suc x)` 严格高于 tA 的参照 | Low | 编译定理 |
| `weakX` | 同上，结论 `R2.Rt h ≼ read (G (suc x))` | 非严格版 | Low | 编译定理 |
| `pathE` | `two ⇐ h₁ (seq0 DR.E₀)`，值 `⇐l 0 ⇐r` | `E₀` 的 (0,0) 位置的子层号是 2（上一路只做了纸面展开，这里由类型检查确认） | Low | 编译定理 |
| `strictE` | `(h : HC tA) → O.suc (R2.Rt h) ≼ read (G (suc DR.E₀))` | `G (E₀+1)` 严格高于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照 | Low | 编译定理 |
| `fsM` | `∀ {t} (h : HC t) (y : Tr zero) → R2.Rt h ≼ read y → cof t ≡ cω → ∀ n → MB.M⁰ (fsn t n) y` | 值序给出各基本列项的第 0 层关系 | Low | 编译定理 |
| `tower` | `Tower` | tA 的各基本列项 ψ₀(Ω_Ω+ψ₁(γₙ)) 对着 `G (suc E₀)` | Low | 编译定理 |
| `V130ᶠ` | `(h : HC tA) → O.suc (R2.Rt h) ≼ read DR.V` | F2：见证值严格高于 tA 的参照 | Low | 编译定理 |
| `V130` | `(h : HC tA) → O.suc (R2.Rt h) ≼ readRW Vᴿ` | 主线：同上 | Low | 编译定理 |
| `strictL` | `(ℓ : LF) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Hi ℓ B → two ⇐ kid0 ℓ → (h : HC tA) → O.suc (R2.Rt h) ≼ read (ψ⊥ ℓ ε ρ B (Ωt ℓ))` | ℕ 极限层号上第 0 行经 `reach` 不低于参照，第 1 行字面地在第 0 行之上 | End | 编译定理 |
| `tA≺br2` | `(h : HC tA) → O.suc (R2.Rt h) ≼ read (br 2)` | 终点的第 2 支严格高于参照 | End | 编译定理 |
| `tA≺EBO` | `(h : HC tA) → O.suc (R2.Rt h) ≼ read EBOᶜ` | F2 终点闭项严格高于 tA 的参照 | End | 编译定理 |
| `tA≺EBOᴿ` | `(h : HC tA) → O.suc (R2.Rt h) ≼ readRW RW.EBOᶜ` | 主线终点闭项，同上 | End | 编译定理 |

**前提可满足：**
- `strictX` 的三条前提在 `E₀` 上实填：`pathE`、`DR.btbo≼E₀`。
- `strictL` 的前提在 `YiEVEnd` 的 `h₁ c₁` 与 `B₁` 上实填：`path₁`、`ok-dW …`、`hi-dW …`。
- `HC tA` 有实例 `hA`；`YiTWEnd.inst` 是代入后的闭项。

**`low` 的证法：**
- 对 x 归纳。
- 后继：结点到第 0 层不保留（`kp` 定义性地化掉），取链第 1 行；它是 `next` 作用在孩子层 `next β₁` 的折叠上，而 `OKB` 给 `Ωt a ⊴ β₁`。
- ℕ 极限：路径 `inlu` 时第 n 行直接是孩子 n 上的折叠；路径 `inl k` 时取第 n+k 行，`way` 一定走后向一行（`nlt`、`caseB`），所以嵌入一行（`emb`）不出现。

##### 4. 第一个障碍

**`Tower` 与 V130 上没有障碍。** 往上的下一个没有做的引理：

- 本路只用到孩子 0 里层号 2 的一行，所以下界停在 tA 的参照加 1。
- 要给 `G (suc E₀)` 更高的记号下界（例如 tB 第 1 行，或 V128 的强形式），`reach` 在层号 2 处的 `Pre` 不够。需要 `YiMWPre.Pre` 在更高层号上的类比：对孩子层号 `g n`（ℕ 极限）上的 Ω 树、带 `Hi` 的底，给出带前缀的关系式下界。
- 这一步是否要用到上折的保持（缺口 2），我没有判断依据；本路没有尝试。

**判断（未编译）：** `low` 对 "含 Ωₗ 的层号" 没有陈述；回退一行（`inb`）上同样的结论是否成立没有查。

##### 5. 偏离与事故；没有读、只凭转述引用的东西

- **偏离：**
  - 路线没有按简报列的两条缺口走：缺口 1 以一般形式闭合（`low`），缺口 2 没有做。
  - `V130` 不经 `tower→V130`，直接由 `strictE` 得到；`tower` 另证（由非严格的 `weakE` 加 `sem→M⁰`、`rω⁰`）。
  - 多交了一个文件 `YiTWEnd`（终点闭项的严格版），是简报里 "也算交付" 的那一条。
  - 第一个文件没有在 30 分钟内写出：前面读定义与比较路线用时较长。
- **事故：**
  - `YiTWLow` 第一次编译报 `ClashingDefinition`（局部名 `T` 与 `YiLegBlock.T` 重名），改名 `Tu` 后通过。写文件时误写了一个不存在的名字 `DR.plus≽′`，编译前已改成 `YiLSRead.plus≽`。没有堆耗尽。
  - 两处修改用了 `sed -i` 改自己的文件。
  - `rm` 只删了自己的两个 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/`）。没有碰别人的文件，没有提交。
- **没有读或只读了一部分：**
  - `Review16.md`、`YiEV.md`、`EBOHandbook.md` 第 4 节、`IdeaLedger`、`YiNFO`、`YiNFOCase`、`YiEBShape`、`YiEBBtbo`、`YiT2Frame`、`YiInv`、`YiDropRW`、`YiBR*`、`YiVR*`、`YiRWCheck`：没有读或只看了文首；关于审查结论的说法取自简报。
  - `YiLSFold` 只读了文首、`OKB` 一段、`St`/`run` 一段与 `MS`/`VS`/`lower`；`YiLSRel` 只看了签名；`YiRefTw2` 只检索了 `Rt`；`Level.lagda.md` 只检索了签名。
  - `R2.Rt` 与 `YiMEBase.Rt` 可互换，是由类型检查通过确认的，没有读两处定义的全文。
