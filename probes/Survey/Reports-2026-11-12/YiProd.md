# 派发来历的产出端 (YiProd)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-12 06:57 至 07:36 |
| 工具调用 / agda 编译 (粗数) | 49 / 11 |
| token (usage 字段，按消息去重) | 输出 251479；新写入缓存的输入 784052；读缓存的输入 9336552；其余输入 78 |
| 写过的仓库文件 | `YiProdArith.lagda.md`, `YiProdFold.lagda.md`, `YiProdTest.lagda.md` |
| 文件前缀 | `YiProd` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-12: 派发来历的产出端一路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 产出端合法，卡住的一对在一个坐标上保留（有限测试），跨支证据为空；回归 btbo-TΛ 未搬；三件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 作者的方针: "边重构边做, 只动值的前沿碰到的那块"; 你这一路是重构兼值的那一路: **派发来历的产出端, 即保留机制的重构, 为 ψ₀(Ω_Ω·2) 铺路**. 不改块. 主审会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 背景 (事实)

- 一致折叠在 ψ₀(Ω_Ω·2) 那一站被问到一对位置 (`YiDlLost` 的 `rN`, `pN`), 它们在同一支里, 但派发不知道 (第九次审查 `probes/Survey/RR9-OmegaOmega2.md`, 全读).
- 保留时带结构搬运的折叠: `YiZipMove`, `YiZipWay` (`Way′`), `YiZipFold` (`Fold′`), `YiZipLost` (`kept-at`; 反面 `cross-keep`, `no-slot`).
- 派发的来历 (上一路, `probes/Survey/Reports-2026-11-12/YiCtx.md` 全读): `YiCtxFold` (同支证据闸门 `FoldC`, 对一切派发与证据来源合法, `cross-fold`); `YiCtxNeg` (`kept→dec`: 证据由裸树上的函数给就是判定; `Ψᴹ-not-lgl`: 标注不进第一位置关系就不合法); `YiCtxAnn` (`module Marked`, 标注随折叠走的消费端 `Ψᴹ-lgl`; `stuck-kept` 小例子上那一对保留). **没做的是产出端**: 规范计算里, 自折叠沿链输出的树要带上满足 `LglA` 的标注. 回报 §5 写了缺的类型 (大致): 链点的标注 `(n : ℕ) → Σ (Pv (chain k gk n)) λ π → LglA S (chain k gk n) noM π`; 相邻链点之间的 `CpA`; 自折叠输出的标注 `Pv (Ψ k V (selfZ k) t)` 及其 `LglA` 保持, 这要求加法、ω 倍、部分和、累加族、`nodeAt`、链与折叠本身都有带标注的版本与单调引理; `Ψn′` 的 keep′ 情形要拆开. 执行方判断不要判定 (那一对的证据在构造时就是 `refl`), 估 400 到 800 行.
- 改块的写法 (台账 U29: 作用域构造子) 是判断, **这一路不改块**.

#### 要交的, 分步; 每做成一步先交

1. **产出端**: 写出带标注的自折叠 (或你认为更省的写法), 使规范计算里链点的输出带上合格的标注; 证它合法 (照 `Ψᴹ-lgl`), 读法 ψ₀(Λ) 的闭项与塔各项合法.
2. **检验**: 在读法 ψ₀(Ω_{Ω+1}) 的闭项 (或 `Tw 3`) 的规范计算里, 卡住的那一对 (`rN`, `pN`) 现在保留 (有限测试或定理); 跨支的那一对仍不保留.
3. **回归**: 这个折叠上至少 `btbo-TΛ` 仍成立 (照 `YiDlVBtbo` 的搬法; 若超过约 150 行新代码, 记为 "未搬" 并说原因). 不要求搬其余的值定理.
4. **做不过去时**: 编译出确切原因: 哪一处的标注造不出, 手里有什么、缺什么; 是不是在要求判定什么 (对照 `kept→dec`, `full→dec`, `cmp-full→lpo`, 逐条核机制).

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K; 堆到 6G 仍耗尽. 没有编译的否定时只写 "未走通".

#### 先读什么

`AGENTS.md` 全篇 (特别是 "律带公共上界", "量化域先取带证据的读回域", "归到已知的墙要逐条核机制", Agda 一节, 文字预算); `probes/Survey/EBOHandbook.md` §4.1 到 §4.5; 上面列的 YiZip 与 YiCtx 文件全读; `YiDlFold.lagda.md`, `YiLamFold.lagda.md` 只检索 `cmpw`, `rootW`, `ptsΩ`, `Kfk`, `nrmk`; `YiNextBase.lagda.md` 只检索 `chain`, `plus`, `succ`, `psum`, `nodeAt`, `Ψn`, `ΩT`; 块 `YiNextCore.lagda.md`. 查签名用检索.

#### 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiProd` (模块名 `OCF.Lean.YiProd…`). 折叠与检验是非验收文件 (只导入 `probes/OCF/Lean/` 的主线文件与标准库); 回归放验收文件. 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞 (写入文件时也不要留洞), `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`, 函数外延. 无关参数 `.( … )` 可以用.
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 仓库文件里不写本机路径. 不要把仓库整个拷到临时目录.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽. 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块; 另有两路也在编译.
- 你的临时目录: `<实验目录>/agents/prod`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 过程要求: 读完上面的文件后尽快动手, 第一个文件在 25 分钟内写出并编译; 每次回复都要有工具调用, 不要在一次回复里只思考.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0; 对非验收文件跑 `python3 probes/Survey/scripts/importclosure.py <模块名…> --only OCF.Lean.`.

#### 回报格式 (只在回报里交一次)

1. 判决: 做到第几步; 一段话说对目标意味着什么 (不改块, 规范计算里卡住的那一对能否保留; 回归是否保住).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值, 是否验收文件, 导入闭包结果.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断).
4. 办法与翻译账 (新东西读的是什么, 哪些由树的要求逼出).
5. 第一个障碍: 精确到行, 附检查器报错原文 (若有); 缺的东西的 Agda 类型; 是不是在要求判定什么.
6. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 回报原文

#### 1. 判决

做到第 2 步。第 3 步（回归）记为"未搬"，第 4 步没有触发。

对目标意味着什么：
- **不改块，产出端能造出合格的标注。** 新写的折叠里，消费端 `Ψᵖ` 照 `Ψᴹ`。后继层号 `top` 那一句的链改由产出端 `Φ` 给：`Φ` 是只保留的自折叠，输出在 Ω 结点层号上带标注，链点的标注由带标注的加法接起来。
- **合法性（编译定理）。** 链点满足 `LglA`（`chL`、`chC`）。`Ψᵖ-lgl` 对一切派发与证据来源成立。闭项 `TΛᵖ`（读法 ψ₀(Λ)）、`Twᵖ n`、`T⁺ʷᵖ` 都合法。
- **证据从哪里来。** 只在一处产生：`Φ` 进 Ω 结点层号的某一支 η 时（嵌入或 `Kfk` 的内层折叠，`subΩ`），这一支里两个位置的证据是 `refl`。其余地方只传递。没有比较两棵裸树。
- **卡住的那一对（有限测试）。** 在 `T⁺ʷᵖ` 的规范计算里，链的第 1 点、坐标 ξa、第 1 个分量是 `rN` 上的结点。它的标注沿 `YiDlLost.occN` 的路径走到 `pN`，证据是 `just refl`，派发保留在 `YiZipLost` 的槽位 `sN`；不带证据时折叠。
- **跨支那一对（编译定理）。** 对一切标注都不保留，因为它的证据类型是空的。
- **回归没有保住。** 这个折叠上 `btbo-TΛ` 没有证（原因见 §5）。
- **一个保留意见（有限试验，不进仓库）。** ξa 是不是新折叠在零层链上真被问到的坐标，没有检查。临时试验 `chain zero gk 1 ≡ ξa` 用 `refl` 编不过：左边头构造子是 `lim`，右边是 `suc`。`YiDlLost` 对旧折叠也只是在 ξa 处直接求值。作为补充，编译定理 `inner-all` 覆盖一切坐标：内层折叠造的每个结点，分支里的每个结点都带证据。

#### 2. 文件表

全部在 `<仓库>/probes/OCF/Lean/`，都是非验收文件。

| 文件 | 代码行 / 总行 | 冷编退出码 | 常驻内存峰值 | 导入闭包 (`--only OCF.Lean.`) |
|---|---|---|---|---|
| `YiProdArith.lagda.md` | 226 / 295 | 0 | 472 MB | OK，35 个模块（本地 26），禁用 0，范围外 0 |
| `YiProdFold.lagda.md` | 320 / 417 | 0 | 725 MB | OK，36 个（本地 27），禁用 0，范围外 0 |
| `YiProdTest.lagda.md` | 143 / 210 | 0 | 468 MB | OK，38 个（本地 28），禁用 0，范围外 0 |

- 每个文件都是删掉自己的 `.agdai` 后冷编，日志里只有本模块的一行 `Checking`。
- 选项行都是 `--safe --without-K --lossy-unification`。
- 禁用构造的检索为 0（postulate、洞、TERMINATING、NO_POSITIVITY、trustMe、irrelevant-projections、cubical、funext、本机路径都没有）。

#### 3. 定理表

##### YiProdFold：折叠与合法性（都在 `module Prod (D : ∀ k K → Ext′ k K) (E : Ev)` 内，实例 `Prod dl′ evF`）

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `Ψᵖ-lgl` | `∀ m {k} (V : Lw k) S x t μ π → LglA S t μ π → Lgl m (Ψᵖ m V S x t μ π)` | 消费端在带标注的合法输入上保合法 | 编译定理 |
| `Φ-lgl` | `∀ m {k} (V : Lw k) x ξ → Lgl k ξ → Lgl m (Φ m V x ξ)` | 产出端（裸树）保合法，对一切层号 | 编译定理 |
| `Φ-lglA` | `∀ {j h k} (V : Lw k) (x : PX (lc j h) k) S σ ξ → Lgl k ξ → LglA S (Φ _ V x ξ) (Φmk V x S σ ξ) (Φpv V x ξ)` | Ω 结点层号上，产出端的输出带上合格的标注 | 编译定理 |
| `Φ-cpA` | `… → Cp k ξ ξ′ → CpA S (Φ _ V x ξ , Φmk V x S σ ξ , Φpv V x ξ) (Φ _ V x ξ′) (Φmk V x S σ ξ′) (Φpv V x ξ′)` | 产出端保带标注的第一位置 | 编译定理 |
| `chL` | `∀ k (V : Lw k) (S : Pre k → Set) n → LglA S (chT k V n) noM (chP k V n)` | 链点带标注合法 | 编译定理 |
| `chC` | `∀ k (V : Lw k) (S : Pre k → Set) n → CpA S (chT k V n , noM , chP k V n) (chT k V (suc n)) noM (chP k V (suc n))` | 相邻链点带标注地递增 | 编译定理 |
| `TΛᵖ-legal`, `Twᵖ-legal`, `T⁺ʷᵖ-legal` | `Lgl zero TΛᵖ`；`∀ n → Lgl zero (Twᵖ n)`；`Lgl zero T⁺ʷᵖ` | 闭项合法 | 编译定理 |

##### YiProdArith：带标注的加法（Ω 结点层号 `lc j h` 上）

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `plusA-weak` | `∀ {S x} μx πx (a : Raw M) μa πa → NE a → CpA S (x , μx , πx) (plus M x a) (plusM μx a μa) (plusP πx a πa)` | 带标注地 x 不超过 x + a | 编译定理 |
| `plusA-cp`, `plusA-lgl` | 同形（略） | 加法保带标注的第一位置与合法 | 编译定理 |
| `succA-lgl`, `psumA-lgl`, `KfkA-lgl`, `KfkA-cp` | 同形（略） | 后继、部分和、`Kfk` 同理 | 编译定理 |
| `fgL` | `∀ (S S′ : Pre k → Set) t μ π → LglA S t μ π → LglA S′ t noM π` | 去掉外层标注保合法 | 编译定理 |
| `fgC` | 同形（第一位置） | 去掉外层标注保第一位置 | 编译定理 |

##### YiProdTest：检验

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `T⁺ʷ-form` | `T⁺ʷᵖ ≡ G.lim (λ n → Ψᵖ zero V2 (λ r → noS {suc (tw 2)} (inj₂ r)) (λ r → fx zero (suc (tw 2)) (inj₂ r)) (chT (tw 2) V2 n) noM (chP (tw 2) V2 n))` | 消费端吃的是带标注的链 | 有限测试 |
| `ch1`, `gK-form′`, `Tt-node′`, `gKc-1′` | `chT (tw 2) V2 1 ≡ G.lc p₀ gK′`；`gK′ ξa ≡ G.lim gKc′`；`Tt′ ξa ≡ G.lc rN gN′`；`gKc′ 1 ≡ G.lc rN bN′` | 那个结点在链的第 1 点里 | 有限测试 |
| `marked` | `walk pathN (bN′ G.top) (pM π₁ G.top) ≡ just (pN , just refl)`，其中 `π₁ = pL (pB (chP (tw 2) V2 1) ξa) 1` | 规范标注在 `pN` 上的证据是 `refl` | 有限测试 |
| `kept-here` | `cmpe₀ rN pN (just refl) ≡ keep′ sN (byEq refl ⨾ byMv L L)` | 有证据时保留 | 有限测试 |
| `lost-bare` | `cmpe₀ rN pN nothing ≡ fold′` | 没有证据时折叠 | 有限测试 |
| `node-kept` | `∀ (g : Raw L → Raw (tw 2)) μ (π : Pv (G.lc pN g)) → Ψᵖ LN V2 (SB (tw 2) rN) (cmpe₀ rN) (G.lc pN g) (lcM (just refl) μ) π ≡ G.lc sN (λ η → Ψᵖ LN V2 (SB (tw 2) rN) (cmpe₀ rN) (g (mv L L η)) (μ (mv L L η)) (pB π (mv L L η)))` | 消费端在这个结点上保留 | 编译定理（`refl`） |
| `cross-anyᵖ` | `∀ (e : Maybe (SB (tw 2) q₂ r₃)) → cmpe₀ q₂ r₃ e ≡ dl′ (lev (tw 2) q₂) (tw 2) r₃` | 跨支那一对对一切标注只走 D | 编译定理 |
| `cross-noEv` | `SB (tw 2) q₂ r₃ → ⊥` | 跨支那一对的证据类型是空的 | 编译定理 |
| `ev-in-branch` | `∀ {k g} (η : Raw k) (l : Lgl k η) r r′ e → evx (subΩ (selfR (lc k g)) η l) r r′ e ≡ just refl` | 进一支时给 `refl` | 编译定理 |
| `ev-self` | `∀ k r r′ e → evx (selfR k) r r′ e ≡ e` | 自派发只传递 | 编译定理 |
| `AJΦ` | `∀ {j h k} (V : Lw k) (x : PX (lc j h) k) S σ → (∀ r → IsJ (σ r)) → ∀ t → AJ (Φ _ V x t) (Φmk V x S σ t)` | σ 处处给证据时，输出的每个结点都带证据 | 编译定理 |
| `inner-all` | `… → (∀ r r′ e → IsJ (evx x r r′ e)) → ∀ r t → AJ (Φ _ V x t) (Φmk V x (SB _ (pos x r)) (λ r′ → evx x r r′ nothing) t)` | 内层折叠造的结点，分支里处处有证据（对一切源树、一切坐标） | 编译定理 |

#### 4. 办法与翻译账

**办法。**
- `PX m k` 记三样东西：源位置 → 目标位置 `pos`；分支域上的搬运 `mvx`（带保 top、保第一位置、保合法）；同支证据的传递 `evx`。
- 自派发 `selfR` 原样传递；`sub₂`、`subℕ` 传 `nothing`；`subΩ` 给 `just refl`。
- `Φ` 用 `G.lc (pos r) …` 直接造结点。根见证的分支域经 `cv` 与 `subst` 换成层号 k 的树。
- 标注只放在 Ω 结点层号上。原因：块的 `add` 在 Ω 结点层号上 `x + top = suc x`，加法不打开结构，标注可以逐个构造子随加法走。其余层号上 `SB` 为空，链点不带标注（`noP`）。

**由树的要求逼出的部件。**
- 证据只在 `subΩ` 产生：块里 Ω 结点层号的位置是 `Σ η …`，同支就是第一坐标相等（`SB`）。
- 链点是加法，所以要带标注的加法、后继、部分和、`Kfk`。
- `NE`（不含嵌入）由 `em-flat` 逼出：嵌入在加法下被打开。
- `cv`、`rtv`：块里 `Lo` 与 `lev` 不定义性相等。
- `LglA`、`CpA` 照 `Ψᴹ-not-lgl` 的要求。

**脚手架与记号。**
- 脚手架只有测试用的 `Dir`、`walk`。
- 没有用记号规则，没有 `Lab`，没有新构造子，闭包定理没有专属前提。

**性质：提供信息。** 产出端在 Ω 结点层号上新用到的字段是位置的第一坐标，并在规范实例上实填。

**已知的缺口（判断）。** `plusP` 把左加数整个接到右加数的结点分支底下时，左加数里的结点相对右加数的结点标 `noM`（定义如此）。所以同一内层折叠里经后继、部分和累加拼起来的跨加数那一对，不带证据。改用"家支标注"（每棵树带"家在 η"的证据）能补上，这一路没有做。

#### 5. 第一个障碍：第 3 步（回归），未搬

没有检查器报错，没有写代码。按简报，估计超过约 150 行新代码，所以记"未搬"。规模是我的判断，约 220 到 270 行。

**原因，逐条核机制。**
1. **派发结果的类型不同。** `YiDlVBtbo` 经 `YiDlVRel`，依赖 `YiNextValRel`、`YiNextValPath`、`YiNextValLgl` 的 `ΨNR`、`ΨnR`、`ΨNDnP`、`ΨnLglR`、`ΨNLglR`、`substR`、`cmpR`，都是对 `Way` 陈述的。这个折叠的结点那一句用 `Way′`（来自 `FoldC.cmpe`），这一族都要写 `Way′` 版本。
   - 经 `ΨN′-eq` 搬运不行：它只是命题相等，而 `ptRʷ` 要的是两份合法性证明之间的关系 `LglR`，沿树的相等搬证明会碰到证明相关。
   - 这一部件是 YiZip、YiCtx、YiProd 三个折叠共用的。
2. **自折叠是另一个函数。** 后继层号 `top` 那一句的链由 `Φ` 给，不是消费端，所以要另证 `ΦR`。`Φ` 的分支域搬运是基于 `Lay` 的，主线的 `ΨN`、`nodeAt` 在 `Raw (lev m s)` 上，两边分支域的类型只在位置具体时才定义性相等。
   - 若非 Ω 层号的链改用消费端，可以省掉 `ΦR`，约省 50 行；这会改第 1 步的折叠，我没改。

**缺的 Agda 类型（未写）。**
- `WR′ : (m : M.LF) (m′ : N.LF) {j j′} → MF.Way m j → Way′ m′ j′ → Set`。保留项要带 `run t` 的恒等型关系：`∀ k η η′ → RR k (NB.lev m′ s′) η η′ → RR k j′ η (run t η′)`。
- `ΨNR′ : … (w : MF.Way m (MF.lev k r)) (w′ : Way′ m′ (NB.lev k′ r′)) → WR′ m m′ w w′ → … → RR m m′ (MF.ΨN m k r w gm gk) (ΨN′ m′ k′ r′ w′ gm′ gk′)`，以及对应的 `ΨNDnP′`、`ΨNLglR′`。
- `ΨRᵖ : … VRʷ V V′ → (∀ r r′ → PR k k′ r r′ → ∀ e → WR′ m m′ (x r) (x′ r′ e)) → RR k k′ ξ ξ′ → ∀ μ π → RR m m′ (MF.Ψ m V x ξ) (Ψᵖ m′ V′ S x′ ξ′ μ π)`，以及 `ΨLglRᵖ`（关于 `ML.Ψ-lgl` 与 `Ψᵖ-lgl` 两份证明的 `LglR`）。
- `ΦR : … RR k k′ ξ ξ′ → RR k k′ (MF.Ψ k V (MF.self k) ξ) (Φ k′ V′ (selfR k′) ξ′)`，以及 `ΦLglR`。

**是否在要求判定什么：不要。**
- `kept→dec`：它的前提是"证据来源是两棵裸树上的函数"。这里的证据由派发记录 `PX` 的 `evx` 与标注带着，不是裸树的函数（`ev-in-branch`、`ev-self`）。
- `Ψᴹ-not-lgl`：它说的是不进第一位置关系的自由标注。这里的链点标注满足 `LglA`（`chL`、`chC`，编译定理）。
- `full→dec`、`cmp-full→lpo`：前提是派发对一切位置完全。这个派发不完全（跨支那一对折叠，`cross-anyᵖ`）。

#### 6. 偏离与事故

**设计上的偏离。**
- 没有直接用 `YiCtxAnn.Marked` 的 `Ψᴹ`。它在嵌入与 `top` 上退回 `FoldC` 的 `Ψᶜ`，而 `Ψᶜ` 后继层号 `top` 那一句的链是裸的；所以另写了完整的消费端 `Ψᵖ`，结点那一句逐字照 `Ψᴹ`。
- 产出端没有用 `YiZipWay` 的 `Mv` 与 `nodeAt`，改用基于 `Lay` 的 `mvx` 与直接的 `G.lc`。好处是省掉对构造器泛化的带标注 `nodeAt`；代价是回归时与主线的关系更难（§5 第 2 条）。
- 非 Ω 层号上，链也由 `Φ` 给，不带标注。

**编译中的小改动。** 以下都不是同一处的重新设计：
- `YiProdFold` 少导入 `limM`、`limP`。
- `Φ-lglA` 的 `wl` 与 `wΩ none` 子句里，`σ` 的元变量解不出，改成显式写出。
- `YiProdTest`：`noS` 的隐式参数，以及少导入 `noM`。
- `AJ-Kfk` 结点子句里的 `_` 导致终止检查失败，改成显式写出 `g (Lay.tp (Lo i r))`。

**其他。**
- 一次性试验 `ProdReach.agda` 放在 `<实验目录>/agents/prod/scratch/`，不进仓库。
- 日志与 `closure.txt` 在 `<实验目录>/agents/prod/`。
- 没有改任何已有文件，没有提交。
