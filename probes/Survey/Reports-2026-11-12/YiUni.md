# 一致折叠的接口与否定 (YiUni)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-12 00:55 至 01:26 |
| 工具调用 / agda 编译 (粗数) | 58 / 20 |
| token (usage 字段，按消息去重) | 输出 190832；新写入缓存的输入 415459；读缓存的输入 9717644；其余输入 94 |
| 写过的仓库文件 | `YiUniCnt.lagda.md`, `YiUniForced.lagda.md`, `YiUniIf.lagda.md`, `YiUniKeepGen.lagda.md`, `YiUniNegBase.lagda.md`, `YiUniNegCmp.lagda.md`, `YiUniNegKeep.lagda.md`, `YiUniNegStep.lagda.md`, `YiUniTw2.lagda.md` |
| 文件前缀 | `YiUni` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-12: 一致折叠的接口与否定返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 接口 Uni 定稿，两个规范实例实填；累加的保留分支族由合法性逼出；跨支比较与链的步派发完全都推出 LPO；九件冷编退出码全 0，非验收文件 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 作者的指示是 "朝着最终目标的关键路径走" (最终目标: 布劳威尔树上 ψ₀(Λ) 的合法闭项, 值不低于 EBO). 主审定的下一个目标: 在主线块上写出 ψ₀(Λ) 的合法闭项, 用 **一套对塔的一切项与 Λ 一致的折叠** (不按站加情形). 按 AGENTS 的 "摆脱先手" 规则, 开攀爬模块之前要先有已编译的结果说明这一站要加的是哪一种东西, 以及哪些字段不能有. **你这一路就是这个摆脱侧: 把一致折叠的接口写成记录, 在规范实例上实填, 并对同一接口写出编译的否定.** 主审会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇. 特别是 "律带公共上界, 构造与否定配对", "量化域先取带证据的读回域", "攀爬与摆脱翻译要平衡", "归到已知的墙要逐条核机制", "前提要可满足", Agda 一节.
2. `probes/Survey/EBOHandbook.md` 只读 §3.1, §4.1 到 §4.5, §5.2, §5.4.
3. 主线块与下一站 (都在 `probes/OCF/Lean/`):
   - 块: `YiLeanCore.lagda.md` (层号是树 `LF`; Ω 结点 `lc k g`, `g : Raw k → LF` 是全函数, 没有守卫), `YiNextCore.lagda.md` (`upT`, `tw`, `Λ`; `tw 2` 是层号 0 上的 Ω 结点, 读作 Ω; `tw 3` 读作 Ω_Ω).
   - 可数层号上的折叠: `YiLeanFold.lagda.md` (`Lv`: `v0`, `vs`, `vl` 带 `Shift`; `Ψ`; `cmp` 是保守的派发).
   - 下一站: `YiNextBase.lagda.md` (`Lv` 多一种 `vΩ`, 只管层号 `tw 2`; 保留结点的分支族沿下标结构累加, 坐标先归一: `Kf-cp`, `Kf-lgl`, `nrm-lgl`), `YiNextFold.lagda.md` (`Ψ` 与 `Ψ-lgl` 互递归, `Ψ-cp`), `YiNextTop.lagda.md` (闭项 `T⁺`), `YiNextTower.lagda.md` (`Legal-tw`, `Legal-Λ`), 有限测试 `YiNextAccTest.lagda.md` (`lost`, `could`).
4. 回报与台账: `probes/Survey/Reports-2026-11-11/YiNext.md` (全读, 特别是 §3, §6: 第 4 项的分支层号是结点层不为 0 的 Ω 结点, 保留时的分支族要对带结点的下标单调, 归一只处理 ℕ 极限 —— 这是执行方的判断), `probes/Survey/IdeaLedger.md` §5 (U1 到 U12; 注意: U1 到 U8 是在旧块上做的, 是否适用于新块没有判定).
5. 旧块上的接口与否定, 作为写法参考 (不要照搬结论): `probes/OCF/Align/YiOmNegBranch.lagda.md` (`top-branch→lpo`), `YiOmFoldRel.lagda.md` (相对坐标的行), `YiGenNegWall.lagda.md`, `probes/Survey/RR6-Uncountable.md` (第六次审查: 那条 LPO 定理只否定一种函数类型; "受支配的域").
查签名用检索, 大文件不要整篇读.

#### 1 要交的, 分步; 每做成一步先交

1. **接口文件** `YiUniIf.lagda.md`: 一个记录, 陈述 "对塔的一切项与 Λ 一致的折叠" 要满足的律. 至少覆盖: Ω 结点所在层号任意 (不只 `tw 2`) 时折叠与保留的行; 第一位置的保持; 合法性的保持. 律里出现的每一对下标都带字面公共上界的证据 (AGENTS). 量化域取带证据的读回域 (塔 `tw n`, `upT` 的读回, 以及它们的链点), 不取一切合法树. 接口定稿后只增不改; 另一路构造以后会实填它.
2. **规范实例上实填**: 可数层号 (`YiLeanFold`) 与 `tw 2` (`YiNextFold`) 两处的实例, 证明它们满足接口的相应部分. 实填不过的字段就是接口写错了, 改接口 (只在定稿之前).
3. **同一接口的否定**: 对接口里看起来要用到的每一种额外能力, 写出编译的定理说它能不能有. 候选 (判断, 先挑战再用): Ω 层号上完全的位置比较 (U11; `lost`/`could` 说明保守派发丢掉了什么); 保留结点的分支对一切下标定义并对第一位置单调 (U10 的理由); 旧块上 U1, U6, U8 的类比在新块上是否还在. 每条否定写清: 定理里有没有折叠, 有没有值, 失败的是哪个字段; 是不是壁垒定理的实例. 每个前提给出可满足的实例.
4. **结论**: 用编译的结果说明这一站 (从 `tw 2` 推广到塔的一切项) 要加的是哪一种东西: 由树的要求 (合法性, 第一位置, 壁垒) 逼出的, 还是只为翻译记号的规则. 写进回报, 不另写报告文件.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K (可交显式前提的条件定理); 堆到 6G 仍耗尽. 没有编译的否定定理时只能写 "未走通".

#### 2 过程要求

- 读完上面的文件后尽快动手: 接口文件的第一版在 25 分钟内写出并编译.
- 每写完一个文件就编译; 每次回复都要有工具调用, 不要在一次回复里只思考.

#### 3 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiUni` (模块名 `OCF.Lean.YiUni…`). 接口与实例若只导入 `probes/OCF/Lean/` 的主线文件与标准库, 就不是验收文件 (文首写明 "非验收文件", 不导入 `OCF.Align.Value`, `OCF.Align.Level` 等带记号闭包的模块); 否定定理若要用参照, 放单独的验收文件. 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 无关参数 `.( … )` 可以用. 函数外延只准作显式前提.
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽. 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块; 别的智能体也在编译.
- 非验收文件写完后跑 `python3 probes/Survey/scripts/importclosure.py --only OCF.Lean.YiUni` 查导入闭包 (看输出里的记号模块数).
- 你的临时目录: `<实验目录>/agents/uni`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 4 回报格式 (只在回报里交一次)

1. 判决: 做到第几步; 一段话说对目标意味着什么 (这一站要加的是哪一种东西, 由什么逼出; 哪些字段不能有).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值, 是否验收文件, 导入闭包的检查结果.
3. 接口: 记录的字段, 逐字.
4. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 否定定理附: 有没有折叠, 有没有值, 失败的字段, 前提的实例.
5. 翻译账: 接口的哪些字段读自记号的规则, 哪些由树的要求逼出.
6. 第一个障碍与偏离事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 回报原文

#### 1 判决

**四步都做完了。** 九个文件都在 `probes/OCF/Lean/`，都不是验收文件。删掉自己的接口后冷编译，退出码全是 0，每个日志只有自己那一行 `Checking`。

**接口。** `YiUniIf` 里的记录 `Uni` 写出一致的折叠要满足的律，`k` 任意；另有读回域记录 `Dom`。两个规范实例都实填通过：可数层号的 `Cnt` 与 `tw 2` 的 `Tw2`。实填之后接口没有改过，文首标了 "定稿"。

**对目标意味着什么。** 从 `tw 2` 推广到塔的一切项，要加的东西分两类。

第一类由树的要求逼出，都是编译定理：
- 结点层 `k` 任意的 Ω 结点层号上，要有公共上界数据：各支的数据 `bC`，以及沿 "加上一段" 的单调 `top-up`。`tw 3` 的分支层号的结点层就不是 0 (`branch-tw3`)。
- 保留结点的分支族 `Kb` 必须是累加的，并且推广到含结点与嵌入的下标 (`KbG`)：
  - 单调律由合法性的保持逼出 (`keep-br`, `chain-up`)；
  - 不累加、直接取各支 `top` 的像，与单调矛盾 (`honest-keep→⊥`, `noacc-not-br`)；
  - 对任意 `k` 都能填 (`KbG-br`)。

第二类是一个新出现的派发 `stp`：链的每一步把第 η 支的 `top` 折到结点自己那一层 `k`。
- 在 `tw 2` 上 `k = 0`，一律折叠就已经完全 (`tw2-stp-full`)。
- 越过 `tw 2` 以后，在 `tw 3` 的分支层号 `Lα α` 上，它在第 0 个链点完全就推出 LPO (`step-full→lpo`)。
- 跨支的位置比较 `cmp` 在 `tw 2` 上已经如此：对一切位置对完全就推出 LPO (`cmp-full→lpo`)。

所以 `stp` 与 `cmp` 只能保守，或者带公共上界的证据。这是 LPO 逼出的，但不是壁垒定理的字面实例。记号里 "Ω 层号的完全比较" 这条规则翻译不到树上。

**不能有的字段 (编译否定)：**
- `CmpFull`：对一切位置对完全的比较。
- `StpFull`：在结点层非零的 Ω 结点层号上完全的步派发。
- "`Kb` 在每个合法下标上等于那一支 `top` 的像"。

**没有判定的：** 值。保守的派发与 `KbG` 用结点下标的 `top` 支代替它本身，值上的代价没有量过。

#### 2 文件表

代码行是 agda 代码块里的非空行，常驻内存是冷编译的峰值。

| 文件 | 代码行 | 冷编译退出码 | 常驻内存峰值 | 验收文件 |
|---|---|---|---|---|
| YiUniIf (接口) | 70 | 0 | 0.37G | 否 |
| YiUniTw2 (`tw 2` 实例) | 62 | 0 | 0.41G | 否 |
| YiUniCnt (可数层号实例) | 64 | 0 | 0.36G | 否 |
| YiUniNegBase (否定的部件) | 59 | 0 | 0.37G | 否 |
| YiUniNegCmp | 83 | 0 | 0.38G | 否 |
| YiUniNegStep | 40 | 0 | 0.37G | 否 |
| YiUniNegKeep | 67 | 0 | 0.37G | 否 |
| YiUniForced | 39 | 0 | 0.36G | 否 |
| YiUniKeepGen | 71 | 0 | 0.37G | 否 |
| 合计 | 555 | | | |

**导入闭包。**
- 按简报的命令 `importclosure.py --only OCF.Lean.YiUni` 跑九个模块：禁用表命中都是 0。"--only 之外" 是主线的 `OCF.Lean.YiNextCore`、`YiNextBase`、`YiNextFold`、`YiNextTop`，这是简报允许的导入，脚本因此退出 1。
- 加上 `--only OCF.Lean.YiNext` 再跑，九个都是 OK。

**禁用构造。** 检索 `postulate`、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`irrelevant-projections`、洞、`Funext`、本机路径：都是 0。九个文件的选项行都是 `--safe --without-K --lossy-unification`。

#### 3 接口 (`YiUniIf`，逐字)

```agda
record Uni : Set₁ where
  field
    Bd  : LF → Set
    bS  : ∀ {k} → Bd (suc k) → Bd k
    bL  : ∀ {f} → Bd (lim f) → ∀ n → Bd (f n)
    bC  : ∀ {k g} → Bd (lc k g) → ∀ η → Lgl k η → Bd (g η)
    Ψ   : ∀ m {k} → Bd k → Ext m k → Raw k → Raw m
    cmp : ∀ {k} → Bd k → (q r : Pre k) → Way (lev k q) (lev k r)
    ωw  : ∀ m {k g} → Bd (lc k g) → Ext m (lc k g) → Way m k
    Kb  : ∀ m {k g} → Bd (lc k g) → Ext m (lc k g) → Raw k → Raw m
    stp : ∀ {k g} (V : Bd (lc k g)) η → Lgl k η → Ext k (g η)
    obd : ∀ m {k g} (V : Bd (lc k g)) → Ext m (lc k g) → ∀ η → Lgl k η → Ext m (g η)
    cpt : ∀ {k g} → Bd (lc k g) → ℕ → Raw k
    cpt-lgl : ∀ {k g} (V : Bd (lc k g)) n → Lgl k (cpt V n)

    zero-row : ∀ m {k} (V : Bd k) x → Ψ m V x G.zero ≡ G.top
    suc-row  : ∀ m {k} (V : Bd k) x a → Ψ m V x (G.suc a) ≡ succ m (Ψ m V x a)
    lim-row  : ∀ m {k} (V : Bd k) x f → Ψ m V x (G.lim f) ≡ G.lim (λ n → Ψ m V x (f n))
    node-row : ∀ m {k} (V : Bd k) x r g → Ψ m V x (G.lc r g) ≡
      ΨN m k r (x r) (λ η → Ψ m V x (g η)) (λ η → Ψ (lev k r) V (cmp V r) (g η))
    em-rowˢ : ∀ m {k} (V : Bd (suc k)) x a → Ψ m V x (G.em tt a) ≡ Ψ m (bS V) (λ r → x (inj₂ r)) a
    em-rowˡ : ∀ m {f} (V : Bd (lim f)) x n a → Ψ m V x (G.em n a) ≡ Ψ m (bL V n) (λ r → x (n , r)) a
    em-rowᶜ : ∀ m {k g} (V : Bd (lc k g)) x η l a →
      Ψ m V x (G.em (η , l) a) ≡ Ψ m (bC V η l) (λ r → x (η , l , r)) a
    top-row⁰ : ∀ m (V : Bd zero) x → Ψ m V x G.top ≡ succ m G.top
    top-rowˢ : ∀ m {k} (V : Bd (suc k)) x → Ψ m V x G.top ≡
      Ψn m k (x (inj₁ tt)) (λ η → Ψ m (bS V) (λ r → x (inj₂ r)) η) (λ η → Ψ k (bS V) (self k) η)
    top-rowˡ : ∀ m {f} (V : Bd (lim f)) x → Ψ m V x G.top ≡
      G.lim (psum m (λ n → Ψ m (bL V n) (λ r → x (n , r)) G.top))
    top-rowᶜ : ∀ m {k g} (V : Bd (lc k g)) x → Ψ m V x G.top ≡
      ΩT m k (ωw m V x) (Kb m V x)
        (λ n → Ψ m (bC V (cpt V n) (cpt-lgl V n)) (obd m V x (cpt V n) (cpt-lgl V n)) G.top)
    cpt-zero : ∀ {k g} (V : Bd (lc k g)) → cpt V 0 ≡ G.top
    cpt-suc  : ∀ {k g} (V : Bd (lc k g)) n → cpt V (suc n) ≡
      plus k (cpt V n) (Ψ k (bC V (cpt V n) (cpt-lgl V n)) (stp V (cpt V n) (cpt-lgl V n)) G.top)

    Ψ-lgl : ∀ m {k} (V : Bd k) x ξ → Lgl k ξ → Lgl m (Ψ m V x ξ)
    Ψ-cp  : ∀ m {k} (V : Bd k) x {ξ ξ′} → Cp k ξ ξ′ → Cp m (Ψ m V x ξ) (Ψ m V x ξ′)
    Kb-br : ∀ m {k g} (V : Bd (lc k g)) x → Br (layer k) m (Kb m V x)
    top-up : ∀ m {k g} (V : Bd (lc k g)) x η l y ly →
      Cp m (Ψ m (bC V η l) (obd m V x η l) G.top)
           (Ψ m (bC V (plus k η y) (plus-lgl k η y l ly)) (obd m V x (plus k η y) (plus-lgl k η y l ly)) G.top)

record Dom (U : Uni) : Set where
  open Uni U
  field
    bd-tw : ∀ n → Bd (tw n)
    bd-Λ  : Bd Λ

DomTo : Uni → ℕ → Set
DomTo U zero = Uni.Bd U zero
DomTo U (suc n) = DomTo U n × Uni.Bd U (tw (suc n))
```

**能力 (不在记录里，是被否定的候选)：**
- `At m j = Σ (Pre m) λ s → lev m s ≡ j`
- `IsKeep`：`keep` 为 `⊤`，`fold` 为 `⊥`
- `Full m k x = ∀ r → At m (lev k r) → IsKeep (x r)`
- `CmpFull U {k} V = ∀ q → Full (lev k q) k (Uni.cmp U V q)`
- `StpFull U {k} {g} V η l = Full k (g η) (Uni.stp U V η l)`

**律里成对出现的下标都带字面上界：**
- `Ψ-cp` 里是 `Cp k ξ ξ′`；
- `Kb-br` 经 `Br`，是 `Le` 的证据；
- `top-up` 里是 `η` 与 `plus k η y`。

`cmp` 是函数，不是律，它收到的是不带证据的一对位置；对这样的一对要求完全，就是 N1 否定的东西。

#### 4 定理表

除标明的以外，档位都是编译定理，无前提。

**实例**

| 名字 | 陈述 | 白话 | 文件 |
|---|---|---|---|
| `Tw2` | `Tw2 : Uni` | YiNextFold 填满接口的全部字段，各行都是 `refl`；`stp`、`obd` 一律折叠，`ωw` 读 `p₀`，`Kb = Kf` | YiUniTw2 |
| `dom₂`, `T₃-uni` | `DomTo Tw2 2`；`T₃ ≡ Uni.Ψ Tw2 zero V₂ (λ _ → fold) G.top` | 读回域填到 `tw 2`；`T₃` 就是接口的闭项形状 | YiUniTw2 |
| `Cnt`, `dom₁`, `lvC` | `Cnt : Uni`；`DomTo Cnt 1`；`∀ η → Lgl zero η → Bc ⌜ η ⌝` | 可数层号的实例；在 Ω 结点层号上 `Bd` 为空 | YiUniCnt |
| `no-lc`, `no-tw2` | `∀ {k g} → Bc (lc k g) → ⊥`；`Bc (tw 2) → ⊥` | 可数实例到不了 `tw 2` | YiUniCnt |

**否定的部件 (YiUniNegBase)**

| 名字 | 陈述 | 白话 |
|---|---|---|
| `found→at` | `∀ α → Found α → At (Tα α) (suc zero)` | α 有真值，则极限层号 `Tα α` 里有层号 1 的槽位 |
| `keep→found` | `∀ α (s : Pre (Tα α)) → lev (Tα α) s ≡ suc zero → Found α` | 有这样的槽位，则 α 有真值 |
| `decide` | `∀ α (w : Way (Tα α) (suc zero)) → (Found α → IsKeep w) → Found α ⊎ (Found α → ⊥)` | 能保留处都保留的派发，判定了 α |

**N1 (YiUniNegCmp)**

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `cmp-full→lpo` | `(c : (q r : Pre (tw 2)) → Way (lev (tw 2) q) (lev (tw 2) r)) → (∀ q → Full (lev (tw 2) q) (tw 2) (c q)) → LPO` | `tw 2` 上对一切位置对完全的比较推出 LPO | 编译定理 |
| `uni-cmp→lpo` | `(U : Uni) (V : Uni.Bd U (tw 2)) → CmpFull U V → LPO` | 接口形式 | 编译定理 |
| `tw2-not-full` | `CmpFull Tw2 V₂ → ⊥` | 现有实例在 `lost` 那一对上不完全 | 编译定理 |
| `probe-lgl`, `probe-row` | `∀ q r → Lgl (tw 2) (probe q r)`；节点行把 `(q, r)` 交给 `cmp` | 任意一对位置都会被某棵合法树问到 | 编译定理 |
| `cmp-under` | `∀ {a b} (w : R) → Lgl zero w → Cp zero a w → Cp zero b w → Cp zero a b ⊎ Cp zero b a` | 合法的公共上界之下的两棵树可比 | 编译定理 |
| `bound→found` | `∀ α (w : R) → Lgl zero w → Cp zero (ηα α) w → Cp zero two w → Found α` | 那一对的两个下标有合法公共上界，则 α 有真值 | 编译定理 |
| `bounded-keep` | `cmpᵂ {G.suc G.top} {G.suc G.top} (G.suc G.top) tt (inj₁ refl) (inj₁ refl) (inj₁ tt) (inj₂ (inj₁ tt)) ≡ keep (inj₁ tt) refl` | 带公共上界的比较保留了 `lost` 那一对 | 有限测试 |

- 有没有折叠：`cmp-full→lpo` 没有，只有比较函数与它的完全性。
- 有没有值：没有。
- 失败的字段：`cmp` 的完全性，在位置对 `(qα α, r₁)` 上。`qα α` 是第 `suc (lim (fα α))` 支的根，层号 `Tα α`；`r₁` 是第 `two` 支的根，层号 1。
- 机制：判定 "层号 1 是不是极限层号 `Tα α` 的某个位置的层号"。这与旧块 `top-branch→lpo` 是同一机制。
- 是不是壁垒定理的实例：不是。前提里没有带精确嵌入、顶元与有界三歧的下标类型。
- 前提的实例：`c = cmp V₂`，即一律折叠；完全性是被否定的那一条。`uni-cmp→lpo` 取 `U = Tw2, V = V₂`。
- 读法：被问到的树是任意合法树 (`probe`)，不是规范链点。按 AGENTS 应读作 "对一切位置对要求完全，谓词太宽"。`bound→found` 说明 LPO 落在没有合法公共上界的那一对上。

**N2 (YiUniNegStep)**

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `branch-tw3` | `∀ α → upT (up zero (ηα α)) ≡ Lα α`，其中 `Lα α = lc (Tα α) (up (Tα α))` | `tw 3` 的第 `ηα α` 支是结点层 `Tα α` 的 Ω 结点层号 | 编译定理 (`refl`) |
| `step-full→lpo` | `(s : ∀ α → Ext (Tα α) (up (Tα α) G.top)) → (∀ α → Full (Tα α) (up (Tα α) G.top) (s α)) → LPO` | 把这一支的 `top` 折到 `Tα α` 的派发若完全，推出 LPO | 编译定理 |
| `stp-full→lpo` | `(U : Uni) (Vα : ∀ α → Uni.Bd U (Lα α)) → (∀ α → StpFull U {k = Tα α} {g = up (Tα α)} (Vα α) (Uni.cpt U (Vα α) 0) (Uni.cpt-lgl U (Vα α) 0)) → LPO` | 接口形式：只要求第 0 个链点上完全 | 编译定理 |
| `stp-full→lpo-dom` | 同上，`Vα α` 取 `Uni.bC U (Dom.bd-tw D 3) (ηα α) (lim-lgl α)` | 读回域的形式 | 编译定理 |
| `tw2-stp-full` | `∀ {k g} (V : Lv (lc k g)) η l → StpFull Tw2 V η l` | `tw 2` 上一律折叠就是完全的 | 编译定理 |

- 有没有折叠：核心形式没有；接口形式里有 `stp` 与律 `cpt-zero`。
- 有没有值：没有。
- 失败的字段：`stp` 的完全性，在第 0 个链点 (`top`) 的位置 `r₀` 上，它的层号是 1。`r₀` 在 `upT (Tα α)` 的第 0 支里，那一支定义性地是 `tw 2`。
- 机制：与 N1 相同。不是壁垒定理的实例。
- 前提的实例：核心形式取 `s = step-fold` (一律折叠)。接口形式的 `U, Vα` 目前没有实例，因为 `Tw2` 与 `Cnt` 在 `Lα α` 上 `Bd` 都为空；接口形式只作为 "有一套覆盖 `tw 3` 各支的折叠" 时的推论。

**N3 (YiUniNegKeep)**

| 名字 | 陈述 | 白话 |
|---|---|---|
| `honest-keep→⊥` | `(U : Uni) (V : Uni.Bd U (tw 2)) → (∀ η l → Uni.Kb U (tw 2) {k = zero} {g = ⌜_⌝} V (self (tw 2)) η ≡ Hon U V η l) → ⊥`，其中 `Hon U V η l = Uni.Ψ U (tw 2) (Uni.bC U {k = zero} {g = ⌜_⌝} V η l) (λ r → self (tw 2) (η , l , r)) G.top` | 保留结点的分支若取各支 `top` 的像，与 `Kb-br` 矛盾 |
| `noacc-not-br` | `Br (layer zero) (tw 2) (Tv (tw 2) lv (self (tw 2))) → ⊥` | `Tw2` 的族去掉累加 `Kf` 后不单调 |

- 有没有折叠：有，只用 `top-rowˢ` 与 `top-row⁰` 两行。
- 有没有值：没有。
- 失败的字段：`Kb-br` 的单调分量，在下标对 `top ⊑ suc top` 上。两支的像分别是位置 `p₀` 与 `s₂` 的结点；从后者往下走只碰到 `top` 的 ω 倍 (`S-noCp`)。
- 是不是壁垒定理的实例：不是。结论是 ⊥，与判定无关。
- 前提的实例：`U = Tw2, V = V₂`。`hon` 与 `Kb-br` 合起来不可满足，这正是定理；`hon` 描述的族本身处处有定义 (`Tv`)。

**逼出 (YiUniForced)**，在以 `U : Uni` 为参数的模块里：

| 名字 | 陈述 | 白话 |
|---|---|---|
| `chain-up` | `∀ m {k g} (V : Bd (lc k g)) x → ωw m V x ≡ fold → ∀ n → Cp m (Ψ m (bC V (cpt V n) (cpt-lgl V n)) (obd m V x (cpt V n) (cpt-lgl V n)) G.top) (Ψ m (bC V (cpt V (suc n)) (cpt-lgl V (suc n))) (obd m V x (cpt V (suc n)) (cpt-lgl V (suc n))) G.top)` | 折叠时，`top-up` 在链点上的实例由 `Ψ-lgl` 逼出 |
| `keep-br` | `∀ m {k g} (V : Bd (lc k g)) x (s : Pre m) (e : lev m s ≡ k) → ωw m V x ≡ keep s e → Br (layer k) m (Kb m V x)` | 保留时，`Kb-br` 由 `Ψ-lgl` 逼出 |

前提的实例：`chain-up₂` 与 `keep-br₂`，都在 `Tw2` 上，前者折到第 0 层，后者折到 `tw 2` 自己。

**任意 `k` 的累加族 (YiUniKeepGen)**

| 名字 | 陈述 | 白话 |
|---|---|---|
| `KfG-br` | `∀ m k T → (∀ η → Lgl k η → Lgl m (T η)) → Br (layer k) m (KfG m k T)` | 累加推广到含结点与嵌入的下标：结点下标取它的 `top` 支，嵌入进孩子层；单调且合法 |
| `nrmG-lgl` | `∀ k η → Lgl k (nrmG k η)` | 坐标的归一总是合法 |
| `KbG-br` | `∀ m {k g} (V : Bd (lc k g)) x → Br (layer k) m (KbG m V x)` | 任意 `Uni` 都能在任意结点层填 `Kb-br` |

**判断 (没有编译)：**
- J1：结点层是极限 `j` 时，`upT (suc j)` 里大概没有层号字面等于 `j` 的位置。那要在 `Raw j` 里有读回为 `j` 的合法树，并且极限层号字面相等。若是这样，以这种层号为目标时 `ωw` 只能折叠。这是旧块 U5、U6 "极限层号字面相等" 的新块版本。
- J2：N2 里由 α 定的那族支，在 `tw 3` 的保留结点上会作为分支函数的值被问到，因为 `Kb` 对一切下标定义。所以 N2 不是 "谓词太宽"。要编译这一条，得先有覆盖 `tw 3` 的 `Uni`。
- J3：保守的 `stp`、`cmp` 与 `KbG` 在值上的代价没有量。
- J4：与台账的对照。
  - U10 的理由已编译成定理 (`honest-keep→⊥`)。
  - U11 有了对一切位置对的编译否定，以及 `bound→found`。
  - U12 "归一只处理 ℕ 极限"：`nrmG` 与 `KfG` 也处理结点与嵌入。
  - U6 在新块上的类比是 N3：不要函数外延，结论是 ⊥，机制是单调而不是判定。
  - U8 在新块上不出现：`Kb` 处处有定义，没有守卫。
  - U1 的类比拆成两条：不累加推出 ⊥ (N3)，派发完全推出 LPO (N1, N2)。

#### 5 翻译账

| 字段 | 来源 |
|---|---|
| `Bd`, `bS`, `bL`, `bC` | 树的要求：嵌入那一行要孩子层的数据。`bC` 对任意 `k`，是塔逼出的 (`branch-tw3`) |
| `zero/suc/lim/node/em`、`top⁰/topˢ/topˡ` 各行 | 照主线，形状读自记号 (ψ(0) 为顶，后继取 ω 倍，保留与折叠，链行)；本路没有新增 |
| `top-rowᶜ` 的形状 | 链 (`cpt-suc`：这一点加上第 η 支的 `top` 折到 `k`) 与节点的折叠行同形，读自记号的基本列。`ωw`、`cpt` 单列成字段是块逼出的：`Pre (lc k g)` 里没有层号 `k` 的字面位置 |
| `stp`, `obd` | 类型由块逼出 (分支层高于 `k`)；不能完全 (N2)，是 LPO 逼出的保守 |
| `cmp` | 节点行要它；不能完全 (N1) |
| `Kb`, `Kb-br` | `Kb-br` 由 `Ψ-lgl` 逼出 (`keep-br`)；累加由 `Kb-br` 逼出 (N3)；任意 `k` 可填 (`KbG-br`) |
| `top-up` | 链点上的实例由 `Ψ-lgl` 逼出 (`chain-up`)。接口对一切 `η, y` 陈述，比逼出的强，这是照 `vΩ` 的 `u` 字段做的设计选择 (判断) |
| `Ψ-lgl`, `Ψ-cp` | 树的要求 |
| `Dom` | 目标 |

为翻译记号而新加的字段：没有。记号的完全比较翻译不过来 (N1, N2)。

#### 6 第一个障碍与偏离事故

**检查器方面的第一个障碍。** `YiUniCnt` 的 `no-tw2` 报错原文：

`[SplitError.UnificationStuck] I'm not sure if there should be a case for the constructor vΩ ... when checking that the pattern vΩ V u has type Lv (tw 2)`

原因：指标是具体的 `tw 2`，合一要删掉 `up zero ≟ ⌜_⌝` 这个等式，那需要 K。改成对变量指标的 `no-lc`，`no-tw2 = no-lc`。另外两处小错：`cl` 的隐式参数 `f` 推不出，显式写出；`G.top ≡ G.suc G.top` 在哪个类型里有歧义，写出 `{A = R}`。

**数学上的障碍。** 现有两个实例在 `tw 2` 之上的 Ω 结点层号上 `Bd` 都为空，所以 `Dom` 与 `stp-full→lpo` 的接口形式在本路里没有实例。这要由构造一路来填。

**偏离。**
1. 可数层号的实例建在 `YiNextCore` 与 `YiNextFold` 上，用谓词 `Cn` 限制到零、后继、ℕ 极限，不是字面的 `YiLeanFold`。原因：`YiLeanCore` 与 `YiNextCore` 是不同的模块，`LF` 是两个类型，接口只能选一个块，我选了主线 `YiNext`。这几行与 `YiLeanFold` 逐字相同。
2. 层号的量化域是带证据的 (`Bd`, `Dom`)，但各行与 `Ψ-lgl` 对层里的一切合法树陈述，没有限制到链点。规范实例对一切合法树都满足；这只在完全性上要紧，而完全性已单列在记录之外。
3. 定稿以后只在接口的文首加了 "定稿" 字样，代码没有改。

**事故：没有。**
- 只删过自己的 `.agdai`，用的是字面的精确路径。
- 没有改已有文件，没有碰 `src/`、`archive/`、`/tmp` 的别处，没有提交。
- 日志都在 `<实验目录>/agents/uni/`。
