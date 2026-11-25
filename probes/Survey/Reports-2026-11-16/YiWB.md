# 摆脱侧：比 Le 宽的底关系（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-16 13:31 至 14:02 |
| 工具调用 / agda 编译 (粗数) | 62 / 13 |
| token (usage 字段，按消息去重) | 输出 171257；新写入缓存的输入 481053；读缓存的输入 11117786；其余输入 102 |
| 写过的仓库文件 | `YiWBNeg.lagda.md`, `YiWBRel.lagda.md` |
| 文件前缀 | `YiWB` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 2 件全部退出 0，禁用构造 0，导入闭包干净；只放宽左边的底关系（含最宽的 Ω≼）给不出前缀 2 的底前提（Neg.no-next、no-base），值序上却成立（val-left-right）；缺的是右边槽位结点的非首分支 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b71/YiWB.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。全程用中文。最后一条消息就是你的回报。

## 回报原文

#### 回报：YiWB（摆脱侧：比 Le 宽的底关系，不读记号）

##### 1. 判决

**对纲领与目标意味着什么。** 这一路没有改树、折叠和合法性，只新增验收侧的关系与否定定理，导入闭包里没有记号。

题设的放宽是："一个分支取值在低层的 Ω 结点，只要每个分支都被极限链上某一项支配，就可以放在这条链之下"。我把它推广到最宽的左规则 `Ω≼`：Ω 结点的每个分支都在右边之下，结点就在右边之下。这样放宽后仍然给不出前缀 2 的底前提，有编译否定。

障碍在右边，不在左边。值序上 `val left ≼ val right` 成立（编译定理），这个比较用到的是右边一个第 1 层槽位结点的**非首分支**，取的是 `Ωt L1`，即该槽位层号自己的 Ω 树。`Le` 和一切只放宽左边的关系都只允许从右边 Ω 结点的第一分支进入（`≼w`）。

这一步属于"提供信息"：否定定理划出了"只放宽左边"这一类关系不够用，值定理指明了缺的是哪一步。

**各步进度。**
- 第 0 步：不成立（编译否定），按规则停下。
- 第 1、2 步：未做。
- 第 3 步：只交翻译账和判断（见文末）。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 题设的放宽（`chain≼`）以及最宽的左规则 `Ω≼` 能否放下源前缀 2 的底分量 `source-next` | `YiWBNeg.Neg.no-next` | 编译定理（否定） |
| W 形式的底前提，对齐到目标前缀 0、1 | `no-wbase-two-at0/1` | 编译定理（否定，无条件） |
| W 形式的底前提，对齐到目标前缀 2 | `no-wbase-two` | 编译定理（否定，以 `Dry target-next` 为条件） |
| `Dry target-next` 是否成立 | 未证 | 判断：很可能成立（目标链只含第 3 层以上的 Ω 树，第 2 层的底分量 `right` 满足 `Dry`） |
| 值序上 left ≼ right | `val-left-right` | 编译定理 |
| `Le ⊆ Wᴸ`，且严格更宽 | `le→wᴸ`, `wide`/`narrow` | 编译定理 |
| 遗传版 `W` 是否包含 `Le` | — | 判断：分支关系在 `w≼w` 里处于反变位置，放宽它会让 `w≼w` 的要求变强，一般不预期包含；未编译 |
| `W` 推出值序 | 第 0 层 `w→v₀`；更高层 | 第 0 层是编译定理。更高层与 `Le` 一样，没有一般定理，需要分支关系自反（判断） |
| 折叠保持、climb 推广、实例化到 Cover/FirstRow | — | 未做（第 0 步不成立） |
| 右边放宽（槽位结点可在不高于其层号 Ω 树的分支处进入）能否在折叠下保持 | — | 判断，未做 |

##### 2. 文件表

| 文件 | 总行 / 代码行 | 冷编退出码 |
|---|---|---|
| `<仓库>/probes/OCF/Lean/YiWBRel.lagda.md` | 134 / 82 | 0（日志只有本模块的 Checking 行） |
| `<仓库>/probes/OCF/Lean/YiWBNeg.lagda.md` | 259 / 176 | 0（日志只有本模块的 Checking 行） |

- 每次编译约 2 秒，未遇到堆的问题。
- 两个文件都没有禁用构造，也没有本机路径（已检索）。
- `importclosure.py` 检查：YiWBRel 闭包 13 个模块，YiWBNeg 闭包 40 个模块，两者禁用表命中都是 0，结果 OK。
- 一次性试验 `YiWBT0`–`YiWBT3.agda` 留在临时目录 `<实验目录>/work/YiWB/`。

##### 3. 定理表（全部为编译定理）

**YiWBRel**
- `chain≼ : ∀ {S RB RD p g f r} → ((z : B S p) → Σ ℕ λ n → WS S RB RD (g z) (f n)) → WS S RB RD (Ω p g) (lim f r)`
  题设的规则是 `Ω≼` 的特例。
- `le→wᴸ : (ℓ : L) {x y : Tr ℓ} → R.Le ℓ x y → Wᴸ ℓ x y`
  沿用 Le 分支关系的版本包含 `Le`。
- `wide : W L1 (Ω s₀ (λ _ → zero)) (suc zero)`、`wideᴸ`（同形）、`narrow : R.Le L1 (Ω s₀ (λ _ → zero)) (suc zero) → ⊥`
  新关系严格比 `Le` 宽。
- `w→v₀ : ∀ {RB RD} {x y : Tr zero} → WS (Sig zero) RB RD x y → V.val zero x V.≼ V.val zero y`
  第 0 层推出值序，不以值序作前提。
- `wrefl₀ : (z : Tr zero) → W zero z z`

**YiWBNeg**
- `two-is : C.g 1 ≡ L2`
  实际链的孩子逐字是第 2 层。
- `Mono.ρ-mono : ∀ {x y} → WS (Sig L2) RB RD x y → ρ x V.≼ ρ y`，模块参数为 `(rz : RB p₁ zero zero) (rr : (z : Tr zero) → RB p₀ z z)`
  `ρ` 把第 2 层的树读到第 1 层的值：第 0 层槽位的结点取全部分支，其余结点只取第一分支，嵌入记作 +1。它沿 `Le` 的规则加 `Ω≼` 单调。
- `dry→free : (x : Tr L2) → Self.Dry L2 x → Free (ρ x)`
  首位置路径上没有第 0 层槽位结点的树，读出的值里没有 Ω。
- `unbounded : (b : V.V L1) → Free b → ((z : Tr zero) → V.val zero z V.≼ b) → ⊥`
  没有 Ω 的值盖不住一切第 0 层的树。
- `grow : (z : Tr zero) → V.val zero z V.≼ ρ (proj₁ (U z))`
- `left-ρ : (b : V.V L1) → Free b → ρ (proj₁ leftT) V.≼ b → ⊥`
- `ρ-sn : ρ (proj₁ Self.source-carry) V.≼ ρ (proj₁ Self.source-next)`
- `Neg.no-left : (Y : Tr L2) → WS (Sig L2) RB RD (proj₁ Self.left) Y → Self.Dry L2 Y → ⊥`
- `Neg.no-next : (Y : Tr L2) → WS (Sig L2) RB RD (proj₁ Self.source-next) Y → Self.Dry L2 Y → ⊥`
- `Neg.no-base : (Rel : (j : L) → Tr j → Tr j → Set) → (∀ {x y} → Rel L2 x y → WS (Sig L2) RB RD x y) → ∀ {ℓ′} (v : C.g 2 ⊑ ℓ′) (B′ : F.Base ℓ′) → Self.Dry (C.g 1) (proj₁ (OP.pull-base v B′ (C.g 1) (inc tt self))) → ((j : L) (w : j ≤ C.g 2) → RF.Pr w → Rel j (proj₁ (St.G.base-at 2 j w)) (proj₁ (OP.pull-base v B′ j w))) → ⊥`
  任何在第 2 层落进 `WS` 的底关系，都给不出源前缀 2 的底前提。
- 实例：
  - `no-wbase-dry`（`W`）、`no-lbase-dry`（`Wᴸ`）、`no-base-le`（`Le`，用另一机制复现 `YiLXOne.no-base-dry`）。
  - 例如 `no-wbase-dry : ∀ {ℓ′} (v : C.g 2 ⊑ ℓ′) (B′ : F.Base ℓ′) → Self.Dry (C.g 1) (proj₁ (OP.pull-base v B′ (C.g 1) (inc tt self))) → St.G.base-at 2 ⊴ᵂ OP.pull-base v B′ → ⊥`
- `no-wbase-two-at0 : St.G.base-at 2 ⊴ᵂ OP.pull-base {b = C.h 0} self (St.T.base-at 0) → ⊥`
- `no-wbase-two-at1 : St.G.base-at 2 ⊴ᵂ OP.pull-base {b = C.h 1} (inc tt self) (St.T.base-at 1) → ⊥`
- `no-wbase-two : Self.Dry (C.g 1) (proj₁ Self.target-next) → St.G.base-at 2 ⊴ᵂ OP.pull-base v2 (St.T.base-at 2) → ⊥`（条件定理）
- `no-carry-w : W L2 (proj₁ Self.source-carry) (proj₁ Self.target-carry) → ⊥`
- `val-left-right : V.val L2 (proj₁ Self.left) V.≼ V.val L2 (proj₁ Self.right)`
  配对：值序成立。用到 `tick-zero : Self.Hi.tick zero ≡ proj₁ (next⁺ (Ωt L2))`（在 opaque 里展开 `Self.Hi.tick`）。

**前提可满足。**
- `rz`、`rr` 由 `NW`（遗传版 W）与 `NL`（Wᴸ）实填。
- `Dry` 前提在对齐 0、1 时由 `Self.omega-two`、`Self.right-dry` 实填。
- 只有 `Dry target-next` 未实填。

##### 4. 第一个障碍

障碍是 `YiWBNeg.Neg.no-next`（机制：`ρ-mono` + `left-ρ` + `dry→free`），属于数学上的阻挡，不是工程问题。

- 源分量的第一分支里含 `left`。`left` 是第 0 层槽位的 Ω 结点，它的分支在 ρ 读法下无界（`grow`）。
- 任何只在左边放宽的关系，在右边进入第 1 层槽位结点时都只能走第一分支。右边满足 `Dry` 时，ρ 读出的值没有 Ω（`dry→free`），盖不住无界的分支（`unbounded`）。
- 值序上的比较要走非首分支 `Ωt L1`（`val-left-right`）。

##### 5. 偏离与事故；没有读、只凭转述引用的东西

**事故**
- 第一个试验文件写错了目录（写在 `work/` 下），已移进 `work/YiWB/`。
- 临时文件补上了 `-W noUnsupportedIndexedMatch`。
- `--lossy-unification` 把 `ρ` 当成单射，导致类型错误。改为显式写出隐式参数后通过（文中有一句说明）。

**来源与偏离**
- `≼⊹ʳ` 照 `YiLPNoBM.≼⊹ʳ` 搬来，那里是旧块的值，文中已注明。
- 第 3 步没有改任何已有文件。

**没有读的**
- `EBOHandbook` §4.2/4.6 和 Bedrock 性能手册：没有出现性能问题，所以没读。
- `YiGL*`：只读了 `YiGLFrame` 的 `Lbl`/`LimAt` 定义，以及 `YiGLFrame`、`YiGLExact`、`YiGIRel` 的文首。
- `YiTZAccept`、`UL.FirstRow`：读了，但没有用到。
- 简报里第七十批各路（YiGL、YiSY、YiVN）的结论，是照转述引用的，没有复核。
- `AGENTS.md`：全文取自会话注入的上下文。

##### 翻译账与判断（第 3 步）

**翻译账**
- 新增 `WS` = `LeS` 加 `Ω≼`。规则形状取自值序 `YiVWVal._≼_` 自己的 `Ω≼`，不来自记号。
- `ρ` 是树侧读法，受 `YiOGSelf.Dry` 的首位置读法启发。
- 没有新增脚手架。
- 这一步是信息：用编译否定划出"只放宽左边"不够，用值定理指出缺的是右边的非首分支。

**与 YiGL 一路"精确标签"的关系（判断）**
- 对象不同：YiGL 的关系是树对记号项，精确标签给槽位的**层号**一个唯一的记号项；本路是树对树，缺的是槽位结点处的**分支选择**。
- 共同点：两边都是"只有下界或首位置的信息不够，需要槽位处的精确信息"。本路需要的分支恰好是槽位层号自己的 Ω 树 `Ωt L1`，可以看成树侧给该层号的精确名字。
- 结论：在这个意义上，我判断两者是同一现象在两侧的表现，但没有编译的对应。

**若下一路做右边放宽（判断）**
规则可以写成"槽位结点可在不高于其层号 Ω 树的分支处进入"。它要在折叠塌缩时保持，需要三样东西：
1. 底不低于该层的 Ω 树，这就是 climb 现有的 `Dom`；
2. 分支函数单调；
3. 关系传递。`Le` 的传递性目前没有编译结果，已检索。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：摆脱侧，比 Le 宽的底关系（不读记号）（前缀 YiWB，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。作者 2026-11-16 定第七十一批，本路选项原文 "摆脱侧：比 Le 宽的底关系 (Recommended)"，执行方 Opus 5.5。AGENTS 目标 "让树自足"、"攀爬与摆脱翻译要平衡"（1:1）：本路是这一批的摆脱侧，交主线会引用的树侧编译事实，不读记号。同批另三路与你互不导入。

#### 第七十批的结果（主审 8G 冷编复核过，读陈述）
- **整体引理 YiGL**（`probes/OCF/Lean/YiGL*`）：读回域 `YiGLDom.Dom`（`dz`、`dC`、`dN`、`dc`）上 Leaf 对一切层号形状成立（`dom-top`），接口 `YiAbsGIface` 的 Leaf、Lift 无前提成立（`leafᴰ`、`liftᴰ`），全域 Leaf 的反例在域外（`not-in`）。LowKeep 未证：现有条件保持引理 `YiGTFold.pres : ∀ ℓ → Kit ℓ → PresAt ℓ` 要的框架 `NodeFrame`，在槽位标签取下界读法 `Rd` 时，对一切后继形状层号无居民（`YiGLFrame.no-frame-S`、`no-tree-child`）；换成精确标签 `YiGLFrame.Lbl`（`Lbl zero ν = ν ≡ []`；后继逐字；ℕ 极限要 `cof ν ≡ cω`、`NF ν`、`LimAt ν`、各孩子标签与基本列的比较；Ω 形状取 `⊥`）后有居民（`frameˣ-S`、`YiGLNode.frameᴸ-S`）；`uniq`、`below`、`lbl-rd`；精确标签的关系族 `YiGLExact.Rˣ`（第 0 层与 `GR.R` 相同），`topˣ`（含 ℕ 极限层号；`topˣ-ω` 在 `no-omega-seed` 的对象上成立），`LowKeepAtˣ`、`LowKeepˣ`（陈述，无居民），`prefixˣ-B₀`、`betaˣ`；`YiGLNode.node-rowˣ`（结点一行的条件定理）。回报 `probes/Survey/Reports-2026-11-16/YiGL.md`。
- **对位调整 YiSY**：`ebo-from-stations′ : (∀ n → Kᴱ′ (suc n)) → toL ET.EBO-tree′ ≼ K.readRW MT.EBOᶻ`；第 3 站下界归约为 `YiSYSmall.k2′-from-tail : Gᴱ.Tail → Kᴱ′ 2`，`Tail` 未证；`two-shape`、`kl-index`。
- **摆脱侧 YiLX**：`YiLXClimb.climb`（字面路径上源 Ω 树折叠按 `YiVRRel.Le` 不高于目标的，一般形式，不读记号），前缀 0、1；前缀 2 起底前提被否定（`YiLXOne.no-base-two-at0` 等：源底里分支取值在第 0 层的 Ω 结点，`Le` 放不进极限链之下）。
- **配对否定 YiVN**：`YiVNIdx.Gen.no-value-index-mono≈`：以下标的树侧值序作前提的下标单调不成立（谓词太宽）。所以前提只能是字面路径、关系或读回域。
- **作者定**：主线停逐项，改攻整体引理；参照只用记号关系 M（`OCF.Align.Level` 的下标类型只有 `zero`、`suc`、`lim`，接不到终点）。

#### 本路的问题
`YiLXClimb.climb` 要求源底不高于拉回的目标底（按 `YiVRRel.Le`）。两条实际链的前缀 2 起，源底分量 `St.G.base-at 2 (C.g 1) (inc tt self)`（等于 `YiOGSelf.source-next`）的第一分支含 `source-carry`：嵌进第 2 层、分支取值在第 0 层的 Ω 结点；`Le` 不能把它放到极限链下面（`YiLXOne.source-wet`、`no-base-dry`、`no-base-two-at0`、`no-base-two-at1`；对齐到前缀 2 为条件否定 `no-base-two`）。YiLX 判断这是 "关系太窄"。

#### 要做的（按序）
0. **最小检查**：设计一个比 `Le` 宽的底关系（例如允许把分支取值在更低层的 Ω 结点放在一条极限链之下，只要每个分支都被链上某项支配），写出它与 `Le`、值序 `YiVWVal._≼_` 的关系（它必须仍能推出值序，也必须**不**以值序作前提，见 YiVN 的否定）；在 `source-next` 与目标前缀 2 的分量上确认它成立。不读记号。不成立就停下回报。
1. **折叠保持**：证同层折叠对这个新关系单调（照 `YiLXFold.fl` 的结构），再推广 `climb`。
2. **实例化**：得到 `YiOFLocal.ActualMissing` 的前缀 2（再试一切前缀，从而 `Offset`、`Cover`）；能走下去就经 `YiTZAccept.from-cover` 到 `UL.FirstRow`，确认末端读记号只一次。
3. 交翻译账；说明这个新关系与 YiGL 一路的 "精确标签" 是不是同一件事在两侧的表现（判断即可）。

#### 规则（主审写给内部子智能体，必须照做）
- **先读** `AGENTS.md` 全文；性能问题先查 `probes/Survey/EBOHandbook.md` 4.2、4.6 节与 Bedrock 性能手册 `<Bedrock>/dev/cubical-agda-performance.md` 的 C-9（在变量上陈述、定义等式作假设、在唯一调用点实例化）、C-10（具体的站作 opaque 原子或模块参数）、S-1/S-3（重的构造在出生处封进 opaque，并在同一块里导出规格等式）、C-24、Q-1（`--profile=definitions`）、Q-23（量底价、二分）、H-6（251 之后不原样重跑）。
- **只新建文件**，放 `probes/OCF/Lean/`，用你的前缀（见上）。不改任何已有文件，不碰 `src/`、`archive/`，不碰别的前缀。中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行（判决与档位、做了什么、不否定什么、入口）；代码之间只写范围与不显然的理由。一次性的试验放你的临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要把前三个也写上，否则报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（写 `<实验目录>`、`<仓库>`）。
- **编译**（仓库根目录）：`agda +RTS -M8G -RTS --library-file=<库文件> -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`；临时目录的纯 `.agda` 另加 `-i <你的临时目录>`。退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 Agda 内部错误。报退出码不经过管道。同时只跑一个 agda，堆上限 8G（同批另有三路，主审也在编译）。不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下，写字面路径）。大的 `refl` 前加 `timeout 600`。
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

