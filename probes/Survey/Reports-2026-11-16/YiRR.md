# 摆脱侧：右边放宽的底关系（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-16 15:24 至 16:03 |
| 工具调用 / agda 编译 (粗数) | 83 / 22 |
| token (usage 字段，按消息去重) | 输出 262923；新写入缓存的输入 455957；读缓存的输入 17029182；其余输入 130 |
| 写过的仓库文件 | `YiRRClimb.lagda.md`, `YiRRFold.lagda.md`, `YiRRPair.lagda.md`, `YiRRRel.lagda.md`, `YiRRTrans.lagda.md`, `YiRRTwo.lagda.md`, `YiRRUp.lagda.md` |
| 文件前缀 | `YiRR` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 8 件全部退出 0，禁用构造 0，导入闭包全部干净；新关系 N（右规则 ≼W）对折叠封闭（fl、climb），第 0、1 层推出值序；两条实际链前缀 2 的值界无前提成立（prefix-two）；第 2 层自反被否定（no-rfl₂），前缀 3 的起点义务 Obl3 未证 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b72/YiRR.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。全程用中文。最后一条消息就是你的回报。

## 回报原文

#### YiRR 回报：右边放宽的底关系（摆脱侧，不读记号，执行方 Opus 5.5）

##### 1. 判决

**对纲领与目标的意义**
- 全部 8 个文件都只在树侧。导入闭包审计：禁用表命中 0，闭包里只有 `OCF.Lean.*`。
- 没有改树、折叠或合法性，只新增一个比较关系 `N`，属于第 4 层，没有反过来改前 3 层。
- 新规则 `≼W` 的条件只用树自己的两样东西：槽位所在层的 Ω 树 `Ωt`，和第一位置序 `⊴◃`。规则形状不来自记号的基本列。
- 进展：两条实际链的值比较，原来只有前缀 0、1，现在第一次在**前缀 2 上无条件成立**（`prefix-two`）。证法是一个对折叠封闭的树侧关系，这是 "让树自足" 方向上的一个编译事实。
- 没有做到的：一切前缀（ActualMissing）、Offset、Cover、`UL.FirstRow` 都未填。本路没有任何新的强度声称。

**各步结果**
- 第 0 步：完成。关系推出值序（带条件 `Ser`，第 0、1 层无条件）；`no-next` 的反例对象 `left ≼ right` 在 `N` 下无前提成立。
- 第 1 步：同层折叠保持 `fl` 与跨层 `climb` 已推广到 `N`，都不用传递性。传递性只在第 0、1 层证出；第 2 层未走通。
- 第 2 步：前缀 2 的底前提与值界完成，无前提。一切前缀未走通，前缀 3 的第一个未填分量已编译成命题 `Obl3`。因为 Cover 没有填，没有走到 `from-cover`，记号只在末端读一次这一点无从确认。
- 第 3 步：翻译账见下文。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 新关系推出值序（前提 `Ser`：分支关系处处有上界，只有 `w≼w` 一行用到） | `YiRRRel.sound` | 编译定理（条件） |
| 第 0、1 层推出值序，无条件 | `YiRRRel.ser₀`、`ser₁`、`sound₁` | 编译定理 |
| 第 2 层 `Ser` 能否满足（等于问：第 1 层的每棵树在 `N` 下是否都有上界） | — | 判断：构造性下未必可证，未否定 |
| `left ≼ right`、`source-carry ≼ target-carry` | `YiRRPair` | 编译定理，无前提 |
| 传递性，前提为分支关系自反 `Rfl` | `YiRRTrans.trans`；第 0、1 层 `rfl₀`、`rfl₁` | 编译定理 |
| 第 2 层 `Rfl` 不成立 | `YiRRTrans.no-rfl₂` | 编译否定 |
| 第 2 层及以上 `N` 是否传递 | — | 未走通（无证明，也无反例） |
| 同层折叠保持 `N`（`NoΩ` 层号） | `YiRRFold.fl` | 编译定理 |
| 跨层爬升 `climb` 推广到 `N` | `YiRRClimb.climb` | 编译定理 |
| 前缀 2 的底前提与值界 | `YiRRTwo.base2`、`prefix-two` | 编译定理，无前提 |
| 深层 "纯上折" 一类分量 | `YiRRUp.ladder`、`deep₃`、`deep₄` | 编译定理 |
| 前缀 3 的第一个未填起点关系 | `YiRRThree.Obl3`（形状由 `refl` 编译） | 未证，未否定 |
| `Le ⊆ N` | — | 未证：`w≼w` 的分支关系在反变位置，与 `YiWBRel.W` 同一情形 |

##### 2. 文件表

都在 `<仓库>/probes/OCF/Lean/` 下。8G 机器上每个文件都删掉自己的 `.agdai` 后冷编，上限 6G，日志里只有本模块一行 `Checking`。

| 文件 | 总行 / 代码行 | 冷编退出码 | 用时 | 最大驻留 |
|---|---|---|---|---|
| `YiRRRel.lagda.md` | 285 / 211 | 0 | 3.1s | 323MB |
| `YiRRPair.lagda.md` | 45 / 29 | 0 | 2.1s | 209MB |
| `YiRRFold.lagda.md` | 267 / 225 | 0 | 2.8s | 283MB |
| `YiRRClimb.lagda.md` | 125 / 109 | 0 | 2.7s | 253MB |
| `YiRRTrans.lagda.md` | 83 / 60 | 0 | 2.2s | 193MB |
| `YiRRUp.lagda.md` | 82 / 59 | 0 | 2.1s | 186MB |
| `YiRRTwo.lagda.md` | 188 / 136 | 0 | 3.7s | 253MB |
| `YiRRThree.lagda.md` | 82 / 62 | 0 | 11.8s | 333MB |

自查：禁用构造检索为 0，本机路径为 0；8 个模块的导入闭包审计全部 OK。

##### 3. 定理表

**关系的定义**（`YiRRRel`）
- `≼W : ∀ {a p g} (z : B S p) → EB p z → ((z′ : B S p) → RB p z z′ → NS S RB RD EB a (g z′)) → NS S RB RD EB a (Ω p g)`
- `NE ℓ p z = (y : Tr (at ℓ p)) → proj₁ (Ωt (at ℓ p)) ⊴◃ y → NB ℓ p z (fromBr ℓ p y)`

白话：右边的槽位结点可以在入口分支 z 处进入。入口条件：z 不高于一切第一位置不低于该槽位层 Ω 树的树。进入条件：左边在 z 之上的每个分支之下。

**定理**

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `sound` | `(ℓ : L) → Ser ℓ → {x y : Tr ℓ} → N ℓ x y → V.val ℓ x V.≼ V.val ℓ y` | 关系推出值序；`≼W` 一行取入口条件在 Ωt 处的见证，不要前提 | YiRRRel | 编译定理（条件） |
| `sound₁` | `{x y : Tr L1} → N L1 x y → V.val L1 x V.≼ V.val L1 y` | 第 1 层无条件 | YiRRRel | 编译定理 |
| `Up≼` | `∀ {ℓ} (j : L) (d : Dn ℓ j) (b b′ : Tr⁺ ℓ) → N ℓ (proj₁ b) (proj₁ b′) → {y y′ : Tr j} → N j y y′ → N ℓ (proj₁ (Up j d b y)) (proj₁ (Up j d b′ y′))` | 上折保持 `N`，含 `≼W` 一行（逆换型 `mvBr⁻`、`mvE`） | YiRRRel | 编译定理 |
| `entry` | `(ℓ : L) → NoΩ ℓ → (y : Tr ℓ) → proj₁ (Ωt ℓ) ⊴◃ y → N ℓ (proj₁ (Ωt ℓ)) y` | 不含 Ω 形状的层号的 Ω 树可作入口 | YiRRRel | 编译定理 |
| `left-right` | `N L2 (proj₁ Self.left) (proj₁ Self.right)` | YiWBNeg 的反例对象在 `N` 下通过 | YiRRPair | 编译定理 |
| `carry` | `N L2 (proj₁ Self.source-carry) (proj₁ Self.target-carry)` | 同上，carry 那一对 | YiRRPair | 编译定理 |
| `fl` | `(ℓ : L) → NoΩ ℓ → (o : Ok ℓ) (r r′ : Rb ℓ) (B B′ : Base ℓ) → B ⊴ⁿ B′ → Dom B′ → (j : L) (w : j ≤ ℓ) (β β′ : Tr⁺ j) → N j (proj₁ β) (proj₁ β′) → {x x′ : Tr ℓ} → N ℓ x x′ → N j (proj₁ (ψ ℓ o r B j w β x)) (proj₁ (ψ ℓ o r′ B′ j w β′ x′))` | 同层折叠保持；`≼W` 行保留时用 `kpE`，走链时用链的第 1 项，靠 `Dom` 与 `geβ`，不用传递性 | YiRRFold | 编译定理 |
| `climb` | `∀ {j ℓ ℓ′} (v : ℓ ⊑ ℓ′) {w : j ≤ ℓ} {w′ : j ≤ ℓ′} → Fit v w w′ → NoΩ ℓ → (o′ : Ok ℓ′) (r : Rb ℓ) (r′ : Rb ℓ′) (B : Base ℓ) (B′ : Base ℓ′) → B ⊴ⁿ pull-base v B′ → Dom B′ → (β β′ : Tr⁺ j) → N j (proj₁ β) (proj₁ β′) → N j (proj₁ (ψ ℓ (pull-ok v o′) r B j w β (proj₁ (Ωt ℓ)))) (proj₁ (ψ ℓ′ o′ r′ B′ j w′ β′ (proj₁ (Ωt ℓ′))))` | `YiLXClimb.climb` 换成 `N`；本地 `Fit` 多 `fSi` | YiRRClimb | 编译定理 |
| `trans` | `(ℓ : L) → Rfl ℓ → {a b c : Tr ℓ} → N ℓ a b → N ℓ b c → N ℓ a c` | 分支关系自反时传递 | YiRRTrans | 编译定理（条件） |
| `no-rfl₂` | `Rfl L2 → ⊥` | 第 2 层的自反前提不成立 | YiRRTrans | 编译否定 |
| `Ladder.ladder` | `∀ {y} → N j (proj₁ (Ωt j)) y → N ℓ a (proj₁ (Up j d b y))`，其中 `a = proj₁ (Up k (down d tt) b (proj₁ (Ωt k)))`，模块参数 `(νk : NoΩ k) (d : Dn ℓ (nd sS (λ _ → k))) (b : Tr⁺ ℓ) (hb : N ℓ (proj₁ b) (proj₁ b))` | 纯上折梯子，对推导归纳，不用传递性 | YiRRUp | 编译定理 |
| `base2` | `St.G.base-at 2 ⊴ⁿ OP.pull-base v2 (St.T.base-at 2)` | 前缀 2 的全部底分量 | YiRRTwo | 编译定理，无前提 |
| `prefix-two` | `V.val zero (proj₁ (St.G.piece 2)) V.≼ V.val zero (proj₁ (St.T.piece 2))` | 前缀 2 的值界 | YiRRTwo | 编译定理，无前提 |
| `obl3-start` | `Obl3 → N (C.g 2) (proj₁ (Qs3 (C.g 2) (inc tt self))) (proj₁ (Qt3 (C.g 2) (inc tt (inc tt (inc tt self)))))` | 把前缀 3 的起点义务化成显式形状 | YiRRThree | 编译定理（`Obl3` 未证） |

##### 4. 第一个障碍

是前缀 3、分量（第 3 层，`inc tt self`）的起点关系 `YiRRThree.Obl3`：
- 左边：`Up L2 (down stop tt) (Up L1 (down (down stop tt) tt) (Ωt L3) (Ωt L1)) (Ωt L2)`。
- 右边：第 4 层 Ω 树折叠到第 3 层（目标路径 `inc tt self`），起点是 `SF₃`（第 3 层 Ω 树的 self 折叠），底是 `Bp`。
- 两边的形状都由 `refl` 编译确认。

判断：右边分支里是 "self 折叠后的上折"，而 `ladder` 只处理 "纯上折"。要过这一关，需要一条新的交换引理，形如 `Up j d (ψ_self γ b) y ≼ ψ_self γ (Up j d b y)`，其中含 `ψ_s(U) ≽ s + ψ_γ(U)` 一类加法比较。我目前认为这是**数学上没有现成引理**，不是工程挡住。未证，也未否定。

一切前缀另有工程障碍：对变量 n，`C.g n`、`C.h n`（以及 `wg n`）不化简，`Fit` 与 `v_n` 无法照 `fS (fS fself)` 写出，要先证层号等式再搬运。这一项是判断，没有编译。

##### 5. 翻译账与其他判断

**翻译账**
- **新定义 `≼W` 的来源**：入口条件里只有槽位层的 `Ωt` 和 `⊴◃`，规则形状来自 YiWB 的值序证明（`val-left-right` 用到非首分支 `Ωt L1`），不读记号。
- **树侧逼出的选择**："入口之上一切分支" 这种上闭的写法，是为了让折叠保持不需要传递性：走链时只知道链的第 1 项高于入口。
- **新增脚手架**：`KE`/`kpE`，以及 `mvBr⁻`、`pshBr⁻` 两组逆换型，都是 `≼W` 在折叠与上折下保持所必需的，与翻译无关。`Fit` 的 `fSi`、`F1`–`F3` 一类形状等式是实例接线（工程）。
- **翻译是否加深**：没有加深。没有新构造子或结点字段，闭包定理没有新增专属前提，验收用值序。
- **提供的信息**：`fl`、`climb` 都对结构参数陈述；写明新用到的字段（槽位层 Ω 树，以及底的 `Dom`）；配对否定是 `no-rfl₂`。

**与 YiKT "树走链、记号保留" 的关系**（判断）
- `nodeW` 的走链一行（入口 ≤ 槽位层 Ω 树 ≤ 底 ≤ 链的第 1 项）可能是同一机制的一部分。
- 但不是同一件事：本路的 `fl` 只对 `NoΩ` 层号，而且比较的是两棵树；LowKeep 关心塔第 1 项（Ω 形状层号）上折叠与记号的保留之差。

##### 6. 偏离与事故
- 没有遇到 251 或超时。临时文件 `YiRRStep0.agda`、`YiRRTwoT.agda`、`YiRRThreeT.agda` 在我的临时目录里。
- 偏离：`YiRRClimb` 自带一份 `Fit`（多 `fSi`），没有复用 `YiLXClimb.Fit`。`sound` 在第 2 层及以上带 `Ser` 前提。
- 没有读、只凭简报转述引用的内容：第七十一批各结果（`YiXPExact`、`YiELLim`、`YiTLReduce` 等）、YiKT 一路的新证据、`UL.FirstRow` 的内容。本次读过的有 `YiTZAccept`、`YiTZLocal`、`YiTNLocal` 中涉及 Cover、Offset 的部分。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：摆脱侧，右边放宽的底关系（不读记号）（前缀 YiRR，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。本路选项原文 "右边放宽的底关系 (Recommended)"。AGENTS 目标 "让树自足"、"攀爬与摆脱翻译要平衡"（1:1）：本路是这一批的摆脱侧，交主线会引用的树侧编译事实，不读记号。同批另四路与你互不导入。

#### 作者的决定与背景（2026-11-16）
- 作者定：主线停逐项，改攻整体引理（读回域上的 Leaf 加 LowKeep）；参照只用记号关系 M。第七十二批选项原文："构造：塔第 1 项上的 LowKeep (Recommended), 配对否定：找塔第 1 项上的反例 (Recommended), 合流两个关系族 (Recommended), 记号侧：截断加法与部分和链点"；摆脱侧 "右边放宽的底关系 (Recommended)"。同批五路：构造 `YiKT`（Fable 5.2）、配对否定 `YiTF`、合流 `YiMG`、截断加法 `YiTA`、摆脱侧 `YiRR`（Opus 5.5），互不导入。
- **第七十一批的结果**（主审 8G 冷编复核过，读陈述；回报在 `probes/Survey/Reports-2026-11-16/`）：
  - `YiXPExact.lowKeepAt-noΩ : ∀ ℓ → NoΩ ℓ → LowKeepAtˣ ℓ`、`lowKeepˣ`：精确标签 `YiGLFrame.Lbl` 下 LowKeep 对一切不含 Ω 形状的层号无条件成立；保持引理族的一般各行不用槽位标签的性质（`YiXPRel`、`YiXPRows`、`YiXPFold` 对抽象 `Lab` 参数化），框架只靠 `uniq`、`below`、`YiXPFrame.lbl-path`。`YiXPNeg.no-index-tree-tw1ˣ`：折叠 `YiRWFold.kp` 对 "Ω 形状、槽位在孩子里、路径经 `inc`" 恒为 `nothing`（走链），记号一侧在孩子里更深的槽位处保留，于是逐槽位证据域 `IndexTree` 在塔第 1 项上为空（只否定证据域）。
  - `YiELLim.limAt : ∀ u → cof u ≡ cω → LimAt u`；`YiELZero.no-all`（带下界证据 `M⁰` 的第 0 层树不都有精确标签）→ 第 0 层分支前提要换精确读回 `Ex⁰ η d = Lbl (↑ zero d) η`（`ex→M⁰`、`ex-lower`、`child-lbl`）；`YiELOmega.Lblᵒ`（下标层为第 0 层的 Ω 形状层号有精确标签，带 `CofΩ` 字段）、`uniqᵒ`、`belowᵒ`（要 `PosOk`）、关系族 `Rᵉ`（第 0 层分支前提用 `Ex⁰`）、`topᵉ`、`lbl-layer`；`YiELChain.ex-next`、`ex-add`（要 `HdLe p s`）。`Rˣ` 与 `Rᵉ` 之间没有映射。
  - `YiWBNeg.Neg.no-next`、`no-base`：只放宽左边的底关系（含最宽的 `Ω≼`）给不出两条实际链前缀 2 的底前提；`val-left-right`：值序上成立，用的是右边一个第 1 层槽位结点的**非首分支**（该槽位层号自己的 Ω 树）。
  - `YiTLReduce`：同步对象（`kl 1 = tw 1 ⊕ ↑ (tw 1) (Ωt (tw 1))`）各孩子层号 `a₁ c` 上 Leaf 无前提（`leaf-a₁`）；`tail-fromᴱ`、`k2′-from-keep : (∀ c → Gvᴱ.KeepOut c) → (∀ c → Gvᴱ.KeepFeed c) → Kᴱ′ 2`（`KeepOut c = ∀ {s} → GR.R (a c) s (proj₁ (Ωt (a c))) → (h : E.HC (E.ψ [] s ∷ [])) → Rt h ≼ K.readRW (proj₁ (out c))`）；`no-lbl-a₁`（这些层号没有 `Lbl`）；第一个挡住的引理 `TightStep d`（顶槽位上紧的链的一步，`StepU′ (a₁ (suc d))` 的实例，陈述已编译），三种现有证据在那里都为空（`no-index-top`、`block-frame`、`no-lbl-hh`）。纸面方向（YiTL 判断）：把框架换成只在实际推导的 κ 处检查，量化域限在读回域的推导上（前缀读空，退路行只承载平凡参照）。
- **决定性问题**（主审判断）：塔第 1 项（及以它为前缀的层号）上的 LowKeep 成不成立。成立要一种新证据；不成立就要改折叠的那一行（第 4 层逼出的定义改动，交作者）。
- 其他已编译的事实：`YiVNIdx.Gen.no-value-index-mono≈`（下标的树侧值序不能作下标单调的前提）；`YiFOValue.fallback-prefix`（退路保留此前折叠的值）；`YiXUFirst.first-ceiling`（干净对象第一支 ≤ ψ₀(Ω₄)）；`YiORBound.original-neg`（封闭关系下原行仍不过判据）。

#### 本路的问题（YiWB 回报）
`YiLXClimb.climb` 要源底不高于拉回的目标底（按 `YiVRRel.Le`）。两条实际链前缀 2 起，源底分量 `YiOGSelf.source-next` 的第一分支里有 `left`（第 0 层槽位的 Ω 结点，分支在 `YiWBNeg` 的 ρ 读法下无界）；任何只放宽左边的关系都给不出底前提（`YiWBNeg.Neg.no-base`）。值序上 `left ≼ right` 成立（`val-left-right`），用的是右边一个第 1 层槽位结点的非首分支，取该槽位层号自己的 Ω 树 `Ωt L1`。YiWB 的建议规则（判断）："槽位结点可在不高于其层号 Ω 树的分支处进入"；它在折叠下保持要三样：底不低于该层的 Ω 树（`climb` 现有的 `Dom`）、分支函数单调、关系传递（`Le` 的传递性没有编译结果）。

#### 要做的（按序）
0. **最小检查**：写出右边放宽的关系（在 `YiVRRel.LeS` 或 `YiWBRel.WS` 的基础上加一条右规则），证它推出值序（不以值序作前提，见 `YiVNIdx` 的否定），并在 `left`、`right` 那一对分量上成立（即 `no-next` 的反例对象在新关系下通过）。不读记号。不成立就停下回报。
1. **传递性与折叠保持**：证新关系传递（或给出它不传递的编译反例），再证同层折叠对它单调（照 `YiLXFold.fl`），推广 `climb`。
2. **实例化**：两条实际链的前缀 2（再试一切前缀，从而 `YiOFLocal.ActualMissing`、`Offset`、`Cover`）；能走下去就经 `YiTZAccept.from-cover` 到 `UL.FirstRow`，确认末端读记号只一次。
3. 交翻译账；说明这条右规则与 YiKT 一路的新证据（"树走链、记号保留" 的结点）是不是同一件事（判断）。

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

