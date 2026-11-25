# 派发的来历随折叠上下文走 (YiCtx)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-12 04:18 至 04:54 |
| 工具调用 / agda 编译 (粗数) | 39 / 14 |
| token (usage 字段，按消息去重) | 输出 217108；新写入缓存的输入 446610；读缓存的输入 7387995；其余输入 68 |
| 写过的仓库文件 | `YiCtxAnn.lagda.md`, `YiCtxFold.lagda.md`, `YiCtxNeg.lagda.md`, `YiCtxTest.lagda.md` |
| 文件前缀 | `YiCtx` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-12: 派发的来历随折叠上下文一路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 同支证据闸门合法，跨支误保留消掉；证据由裸树上的函数给要判定；标注随折叠走的消费端合法，产出端没试；四件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 作者的指示是 "朝着最终目标的关键路径走"; 作者这一批选了 **"派发的来历随折叠上下文走"**: 不改块, 折叠下到某一支时把这一支的下标传给派发, 试着消掉跨支误保留, 并保留卡住的那一对; 配一条: 做不到时编译出为什么非改块不可. 主审会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 背景 (事实)

- 一致折叠的派发只拿到 (目标层号, 裸源位置), 不知道这一对位置是否在同一支 (第九次审查, `probes/Survey/RR9-OmegaOmega2.md`, 全读).
- 保留时带结构搬运的折叠已有 (都在 `probes/OCF/Lean/`): `YiZipMove.lagda.md` (`mv`, `mv-cp`, `mv-lgl`, `mv-br`), `YiZipSim.lagda.md` (`Sim`, `mv-sim`), `YiZipWay.lagda.md` (`Way′`: 保留带搬运 `Mv`; `ΨN′-lgl`, `ΩT′-lgl`, `ΨN′-eq`), `YiZipFold.lagda.md` (`module Fold′ (D : ∀ k K → Ext′ k K)`, 比较 `cmpz`, 位置对齐 `PT`, `viaM`, `orW`; `TΛ′-legal`), `YiZipLost.lagda.md` (`kept-at`: 卡住的那一对 (`YiDlLost` 的 `rN`, `pN`) 保留在原槽位; **反面** `cross-keep` 与 `no-slot`: 只按结构对齐时, 跨支、目标层没有对应槽位的一对 (`q₂` 在第 2 支, `r₃` 在第 3 支) 也保留). 回报 `probes/Survey/Reports-2026-11-12/YiZip.md` §5: 执行方判断判据要两支相等或极限层号相等的判定; 不判定的出路是来历随树走, 可能要改块 (没有判定).
- 已编译的否定 (不能有的): `YiUniNegCmp.cmp-full→lpo`, `YiUniNegStep.step-full→lpo`, `YiLamNLim.full→dec` (对一切位置完全的派发推出判定); 读 `probes/Survey/IdeaLedger.md` 的 U11 到 U27.

#### 要交的, 分步; 每做成一步先交

1. **设计**: 在 `YiZipFold` 的基础上 (新文件, 不改旧文件), 让折叠把所在的支作为上下文传给派发 (例如 Ω 结点层号上折叠第 η 支时, 派发的输入多带 η 或从 η 来的路径数据), 使比较只在 "目标位置与源位置来自同一个上下文" 时按结构对齐, 否则走原来的派发. 不改块 (`YiNextCore` 不动), 只改第 2 层. 证合法性 (照 `Ψ′-lgl`), 读法 ψ₀(Λ) 的闭项与塔各项合法.
2. **两个检验** (有限测试或定理): 卡住的那一对 (`rN`, `pN`) 仍保留; 跨支的那一对 (`q₂`, `r₃`) 不再保留 (或说明它在规范计算里根本不会以这种方式被问到, 用编译事实).
3. **配对的一条**: 若上下文传不进去 (例如派发被问到的地方, 折叠手里没有那一支的下标), 编译出确切原因: 是哪一行, 手里有什么、缺什么; 并说明要改块的话改哪一处 (判断, 不要改). 若能做到, 说明它是否在要求判定什么 (对照上面的否定, 逐条核机制).

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K; 堆到 6G 仍耗尽. 没有编译的否定时只写 "未走通".

#### 先读什么

`AGENTS.md` 全篇 (特别是 "律带公共上界", "量化域先取带证据的读回域", "归到已知的墙要逐条核机制", Agda 一节, 文字预算); `probes/Survey/EBOHandbook.md` §4.1 到 §4.5; 上面列的 YiZip 文件全读; `YiDlFold.lagda.md`, `YiLamFold.lagda.md` 只检索 `cmpw`, `rootW`, `ptsΩ`, `Kfk`, `nrmk`; `YiNextCore.lagda.md` (块). 查签名用检索.

#### 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiCtx` (模块名 `OCF.Lean.YiCtx…`). 非验收文件 (只导入 `probes/OCF/Lean/` 的主线文件与标准库, 文首写 "非验收文件"). 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`, 函数外延. 无关参数 `.( … )` 可以用.
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 仓库文件里不写本机路径. 不要把仓库整个拷到临时目录.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽. 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块; 另有两路也在编译.
- 你的临时目录: `<实验目录>/agents/ctx`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 过程要求: 读完上面的文件后尽快动手, 第一个文件在 25 分钟内写出并编译; 每次回复都要有工具调用, 不要在一次回复里只思考.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0; 跑 `python3 probes/Survey/scripts/importclosure.py <模块名…> --only OCF.Lean.`.

#### 回报格式 (只在回报里交一次)

1. 判决: 做到第几步; 一段话说对目标意味着什么 (不改块能不能给派发来历; 跨支误保留消掉没有).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值, 导入闭包结果.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断).
4. 办法与翻译账.
5. 第一个障碍: 精确到行, 附检查器报错原文 (若有); 缺的东西的 Agda 类型; 是不是在要求判定什么.
6. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 回报原文

#### 1. 判决

三步都做了，但第 2 步只做成一半：跨支误保留消掉了（编译定理，对任何证据来源和任何标注都成立）；卡住的那一对在主线闭项里仍然折叠。

对目标意味着什么：
- **不改块，派发可以拿到来历的接口。** 做法是"同支证据闸门"：折叠在 Ω 结点那一句把目标的支 η 和源的支 η′ 交给证据来源。拿到 `η ≡ η′` 时按 YiZip 的结构对齐，拿不到时只走原来的派发 `D`。闸门折叠对一切派发 `D`、一切证据来源 `E` 都合法，闭项 TΛᶜ（读法 ψ₀(Λ)）、Twᶜ、T⁺ʷᶜ 也都合法。
- **证据从哪里来，是卡住的地方。** 两条来源分别编译出了结论：
  - (a) 证据来源是两棵裸树上的函数。若它在卡住那一对的支下标 ηN 上给证据，它就判定 `ηN ≡ ·` 对一切树成立（`kept→dec`）。实例 `evF` 遇到 ℕ 极限就不给证据，而 ηN 是 `suc` 后接 ℕ 极限，所以那一对仍折叠（`lost-evF`）。
  - (b) 证据作为逐次出现的标注随折叠走，不要求判定。消费端只在标注进入第一位置关系时合法：进入时 `Ψᴹ-lgl` 成立；标注自由时，合法输入会折出不合法输出（`Ψᴹ-not-lgl`）。在小源树上，结点带了证据，卡住的那一对就保留（`stuck-kept`，有限测试）。
- **没做的是产出端。** 规范计算里，自折叠沿链输出的树要带上满足 `LglA` 的标注，这一段未试。所以"不改块能否给派发来历"的结论是：消费端能（编译定理），产出端未走通（未试，不是否定）。

#### 2. 文件表

全部在 `<仓库>/probes/OCF/Lean/`。各文件都是删掉自己的 `.agdai` 后冷编译，日志里只有本模块的 Checking 行。

| 文件 | 代码行/总行 | 冷编译退出码 | 常驻内存峰值 | 导入闭包 (`--only OCF.Lean.`) |
|---|---|---|---|---|
| YiCtxFold.lagda.md | 116/161 | 0 | 406 MB | OK，本地 21 个，禁用 0 |
| YiCtxTest.lagda.md | 56/98 | 0 | 401 MB | OK，本地 24 个，禁用 0 |
| YiCtxAnn.lagda.md | 171/237 | 0 | 422 MB | OK，本地 25 个，禁用 0 |
| YiCtxNeg.lagda.md | 95/142 | 0 | 417 MB | OK，本地 26 个，禁用 0 |

- 选项行都是 `--safe --without-K --lossy-unification`。
- 禁用构造检索为 0：postulate、洞、TERMINATING、NO_POSITIVITY、trustMe、irrelevant-projections、cubical、funext 都没有。
- 文件里没有本机路径。
- importclosure 的退出码是 0。

#### 3. 定理表

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `Ψᶜ-lgl` | `∀ m {k} (V : Lw k) x ξ → Lgl k ξ → Lgl m (Ψᶜ m V x ξ)`（在 `module FoldC (D : ∀ k K → Ext′ k K) (E : Ev)` 内） | 闸门折叠对一切派发和证据来源都保合法 | Fold | 编译定理 |
| `TΛᶜ-legal`, `Twᶜ-legal`, `T⁺ʷᶜ-legal` | `Lgl zero TΛᶜ`；`∀ n → Lgl zero (Twᶜ n)`；`Lgl zero T⁺ʷᶜ` | 实例 (`dl′`, `evF`) 的闭项合法 | Fold | 编译定理 |
| `wΩ-no` | `∀ D E {k g} (V : ∀ η → Lgl k η → Lw (g η)) w η l q η′ l′ r → (η ≡ η′ → ⊥) → FoldC.cmpc D E (wΩ V w) (η , l , q) (η′ , l′ , r) ≡ D (lev (g η) q) (lc k g) (η′ , l′ , r)` | 两支下标不同时只走 D | Test | 编译定理 |
| `cross-fold` | `∀ D E → FoldC.cmpc D E V2 q₂ r₃ ≡ D (lev (tw 2) q₂) (tw 2) r₃` | 跨支那一对，对一切证据来源都不按结构保留 | Test | 编译定理 |
| `kept-if` | `∀ E (e : ηN ≡ ηN) → E zero ηN ηN ≡ just e → FoldC.cmpc dl′ E V2 rN pN ≡ keep′ sN (byEq refl ⨾ byMv L L)` | 有证据时卡住的那一对保留在 YiZipLost 的槽位 | Test | 条件定理（见下方注 1） |
| `cross-inst`, `lost-evF`, `evF-ηN`, `ηN-form`, `fin-D`, `fin-same` | `cmpc V2 q₂ r₃ ≡ fold′`；`cmpc V2 rN pN ≡ fold′`；`evF zero ηN ηN ≡ nothing`；`Σ (ℕ → R) λ f → ηN ≡ G.suc (G.lim f)`；… | evF 下两对都折叠；有限支里的同支一对 D 本来就保留 | Test | 有限测试 |
| `Ψᴹ-lgl` | `∀ m {k} (V : Lw k) S x t μ π → LglA S t μ π → Lgl m (Ψᴹ m V S x t μ π)`（在 `module Marked (D) (E)` 内） | 标注进入第一位置关系 (`CpA`) 时，逐次出现证据的折叠保合法 | Ann | 编译定理 |
| `lglA-no` | `∀ S t → Lgl k t → LglA S t noM noP` | 不带标注时就是原来的合法性 | Ann | 编译定理 |
| `cross-anyM` | `∀ (e : Maybe (SB (tw 2) q₂ r₃)) → cmpe₀ q₂ r₃ e ≡ dl′ (lev (tw 2) q₂) (tw 2) r₃` | 标注里放不进跨支证据（`2 ≡ 3` 没有元素） | Ann | 编译定理 |
| `stuck-kept`, `stuck-old` | `Ψᴹ LN V2 (SB (tw 2) rN) (cmpe₀ rN) (G.lc pN (λ _ → G.zero)) (lcM (just refl) (λ _ → noM)) noP ≡ G.lc sN (λ _ → G.top)`；不带标注时 `≡ G.lim (λ _ → G.top)` | 结点带证据，卡住的那一对就保留 | Ann | 有限测试 |
| `const-lglA`, `const-kept`, `const-legal` | `ηs = 2+ω` 同支一对（源层号字面是 ℕ 极限）的常值序列，带同一份证据：带标注合法、输出逐项保留、输出合法 | — | Ann | 有限测试与编译定理 |
| `diag1→dec` | `(E : Ev) (k : LF) (η₀ : Raw k) → IsJust (E k η₀ η₀) → ∀ η′ → Dec′ (η₀ ≡ η′)` | 在一个点的对角上给证据，就判定与这个点的字面相等 | Neg | 编译定理（前提实例：`evF`，取 `η₀ = G.zero`） |
| `kept→dec` | `∀ E (e : ηN ≡ ηN) → E zero ηN ηN ≡ just e → ∀ η′ → Dec′ (ηN ≡ η′)` | 让卡住那一对保留的证据来源，在判定 `ηN ≡ ·` | Neg | 编译定理（前提同注 1） |
| `kept→decα` | `… → ∀ α → (∀ n → α n ≡ false) ⊎ (ηN ≡ ηα α → ⊥)` | 对布尔序列族的不带函数外延的判定形 | Neg | 编译定理（不是 WLPO，另一方向要函数外延） |
| `Ψᴹ-not-lgl` | `(∀ (t : Raw (tw 2)) μ π → Lgl (tw 2) t → Lgl M (Ψᴹ M V2 (SB (tw 2) qs) (cmpe₀ qs) t μ π)) → ⊥` | 标注自由时，合法输入（常值序列，证据交替）折出不合法输出 | Neg | 编译定理 |
| `in-not-lglA` | `LglA (SB (tw 2) qs) (G.lim (λ _ → ts)) (limM μs) noP → ⊥` | 上面那份输入不满足带标注的合法性 | Neg | 编译定理 |
| `em-flat` | `∀ (z : Raw (tw 2)) (η : R) (l : Lgl zero η) (a : Raw (up zero η)) → plus (tw 2) z (G.em (η , l) a) ≡ add (up zero η) (λ r → G.lc (η , l , r)) z a` | 块里唯一的作用域 em 在加法下打开成完整位置 | Neg | 编译定理 (`refl`) |

**注 1（`kept-if`、`kept→dec` 的前提可满足性）：** 没有可构造的实例。由 `kept→dec`，任何实例都判定 `ηN ≡ ·`。前提不矛盾（判断）：例如带排中律的模型里可以有。

**机制核对（逐条读了陈述）：**
- `cmp-full→lpo`、`step-full→lpo`：前提是对一切位置完全；我的 `kept→dec` 只要单个对角点上的证据，靠沿 `e` 的搬运 (J) 推出，没有槽位，也没有完全性。
- `full→dec`：结论的形式相同（含 ℕ 极限的两棵树的字面相等的 `Dec′`），但比较对象是层号，用的是 `slot→eq`；我的是支下标 `R`。
- `kept→dec` 的前提只涉及规范的那一对；量化发生在结论一侧。
- `Ψᴹ-not-lgl` 的探针是自由标注（非规范）。它读作"标注太宽，必须进入 `CpA`"，不读作数学障碍；`Ψᴹ-lgl` 是与它配对的正面。

#### 4. 办法与翻译账

- **由树侧逼出的部件：**
  - 闸门（YiZip 的 `cross-keep` 反面，加上 `mv-sim` 只在层号相等时是拷贝）。
  - `SB`：同支就是第一坐标字面相等，因为块里 Ω 结点层号的位置带支下标。
  - `CpA`、`LglA`：合法性逼出，`Ψᴹ-not-lgl` 说明不进第一位置关系就不行。
- **脚手架：** `evF`（有限结构的证据），在卡住的那一对上无用。
- **记号与 Lab：** 没有用任何记号规则，没有 Lab，没有新增翻译。
- **性质：** 这一轮属于"提供信息"：编译出的否定划出了不能有的字段（裸树上的完全证据来源、不进合法性的标注）。
- **代价：** `evF` 实例相对 YiZipFold，丢掉了 YiZip 保留的 (rN, pN)，换来的是不再跨支保留。

#### 5. 第一个障碍（没有检查器报错，产出端没有试）

- **证据来源路线**
  - 位置：`YiCtxFold.lagda.md` 第 70–71 行，`cmpe (wΩ {k} {g} V w) (η , l , q) (η′ , l′ , r) e = gate e (D …) …`，其中 `e = E k η η′`。
  - 手里有：η、η′（裸树）、l、l′、q、r。
  - 缺：`Maybe (ηN ≡ ηN)` 的 `just`，而且要由两棵裸树上的函数给出。
  - 是否要求判定：要。由 `kept→dec`，这等于判定 `ηN ≡ ·`。
- **标注路线（不判定）**
  - 第一处没建的位置：`YiCtxFold.lagda.md` 第 89–90 行（同 YiZipFold 的 ws-top 子句）：`Ψn′ m k (x (inj₁ tt)) (λ η → Ψᶜ m V (λ r → x (inj₂ r)) η) (λ η → Ψᶜ k V (selfZ k) η)`。这里的 `gm` 折叠链点，链点是自折叠 `gk` 的裸输出；卡住的那一对就在这样的链点里（YiDlLost 的 `gKc 1`）。
  - 缺的类型大致是：
    - 链点的标注 `(n : ℕ) → Σ (Pv (chain k gk n)) λ π → LglA S (chain k gk n) noM π`；
    - 相邻链点之间的 `CpA`；
    - 因此需要自折叠输出的标注 `Pv (Ψ k V (selfZ k) t)` 及其 `LglA` 保持。这又要求 plus/add、succ、psum、Kfk、nodeAt、chain 以及 Ψ 本身都有带标注的版本和单调性引理。
  - 另一处：`Ψn′` 的 keep′ 情形 `nodeAt m p G.lc (λ η → gm (run t η))` 会把 `gm` 用到任意裸输入上，所以 `Ψn′` 要拆开（fold′ 走带标注的链，keep′ 走裸树加 `noP`）。
  - 是否要求判定（判断）：不要。卡住那一对的证据在构造时就是 `refl`：两个结点都由 Kfk 下到第 `nrmk zero ξa` 支时的派发 `λ r → selfZ (tw 2) (nrmk zero ξa , _ , r)` 造出（R9Same 的 `same-branch-rN/pN`）。
  - 规模（判断）：400 到 800 行。
- **若要改块，改哪一处（判断，没有改）**
  - 问题所在：`KS (lc k g) (η , _) = layer (g η)`，即 em 作用域里的子树全在 `g η` 层，放不下整层的树，所以 add 必须把它打开（`em-flat`）。
  - 改法：给 `G.R` 加一个作用域构造子，体内的结点用相对于这一支的位置，体内可以用 `out : Raw (lc k g) → 体` 回到整层，使 `x + 作用域(i, s) = 作用域(i, s[zero ↦ out x])`。这样"同支"就是"同一作用域里、没有经过 out"，由结构定出。

#### 6. 偏离与事故

- **第 1 步交了两个变体：**
  - FoldC：以证据来源作闸门，有闭项。
  - Marked（`Ψᴹ`）：以标注作证据，只有消费端的合法性定理；它在 `top` 上没有标注，所以闭项就是 `Ψᶜ`，没有另写。
- **YiCtxFold 第一次编译通过后重构过一次：** 证据改为显式输入 `cmpe`，`cmpc` 包一层。重构后重新编译通过。
- **YiCtxAnn 初稿终止检查失败：** 原因是 Σ 打包的参数不被认作更小，改成柯里化后通过。这是同一处的第一次重设计，没有触发停下条件。
- **YiCtxNeg 写入时一度含一个洞 `{!!}`：** 在第一次编译之前就换成了 `out-0`、`out-1`，从未进过检查器。
- **命名：** `kept→wlpo′` 改名为 `kept→decα`，避免被读成 WLPO。
- **前缀重名：** `probes/OCF/Align/` 下已有 `YiCtxBase`、`YiCtxFork`、`YiCtxStep`（模块名 `OCF.Align.YiCtx…`，不是我写的）。与我的 `OCF.Lean.YiCtx…` 不冲突，但容易混淆。
- **其他：** 没有改任何已有文件；临时文件只有日志与 `closure.txt`，在 `<实验目录>/agents/ctx/`。
