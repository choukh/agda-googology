# 派发换成燃料搜索的折叠，再试 ψ₀(Ω_Ω·2) (YiDl)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-12 02:17 至 02:43 |
| 工具调用 / agda 编译 (粗数) | 63 / 20 |
| token (usage 字段，按消息去重) | 输出 131826；新写入缓存的输入 255800；读缓存的输入 9590689；其余输入 112 |
| 写过的仓库文件 | `YiDlFold.lagda.md`, `YiDlInst.lagda.md`, `YiDlLost.lagda.md`, `YiDlMore.lagda.md`, `YiDlVLost.lagda.md` |
| 文件前缀 | `YiDl` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-12: 燃料搜索一路返回并复核; ψ₀(Ω_Ω·2) 未走通; 第五份概率评估 (主审)” 一节 |
| 主审复核后的一句结论 | 合法，值搬得过来；ψ₀(Ω_Ω·2) 未走通：被问到的位置源层号是 ℕ 极限，燃料搜索不保留；九件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 作者的指示是 "朝着最终目标的关键路径走" (最终目标: 布劳威尔树上 ψ₀(Λ) 的合法闭项, 值不低于 EBO). 上一个目标已完成: 一致折叠 `probes/OCF/Lean/YiLamFold.lagda.md` 的读法 ψ₀(Λ) 的闭项 `TΛ` 合法无前提, 568 行, 值不低于 BTBO (`YiLamVBtbo.btbo-TΛ`). **下一站卡在一处: 派发 `dfin` 在目标层不是字面有限数时一律折叠, 值的证明在 ψ₀(Ω_Ω·2) 那一站停在这里. 你的任务: 把派发换成只读层号字面结构的燃料搜索, 保持合法, 再试 ψ₀(Ω_Ω·2) 那一步.** 主审会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇. 特别是 Agda 一节, "攀爬与摆脱翻译要平衡" (翻译账), "用记号验收强度", "中间站给界", "结论的写法".
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 与 §5.4.
3. 折叠与接口: `probes/OCF/Lean/YiLamFold.lagda.md` 全读 (`dfin` 只在 `cmpw` 的 `wΩ` 子句与 `ptsΩ` 里出现; `Ψ-lgl` 对一切派发成立); `YiLamIf.lagda.md` (姊妹接口 `Uniᴾ`), `YiLamNInst.lagda.md` (`Lam : Uniᴾ`, `domΛ`).
4. 燃料搜索: `YiLamNFuel.lagda.md` (`look`, `pol`, `dpol`, `dlev`; `sound`: 保留的都在目标之下; `fin-only`: 只保留字面有限层号的位置; `dlev-full-J`: 在塔里实际问到的那个极限目标 `J` 上完全; `dpol-not-full₀`). 那个极限目标在哪里被问到: `YiLamNAsk.lagda.md`. 不能有的: `YiLamNLim.lagda.md` (`full→dec`: 对一切位置完全就判定极限层号的字面相等).
5. 值: `YiLamVBtbo.lagda.md` (`btbo-TΛ`, 经链观察读回互模拟 `obs≅` 从主线搬来), `YiLamVOne.lagda.md` (`T⁺ʷ` 不低于 ψ₀(Ω_Ω+Ω₁), `χ₁≼ʷ`), `YiLamVStep.lagda.md` (条件定理 `T2≼ᴳʷ : Stepᴳʷ → GL.T2ᴸ ≼ NA.read W.T⁺ʷ`), `YiLamVLost.lagda.md` (卡住的地方: `lost`, `root-lost`, `could`). 回报 `probes/Survey/Reports-2026-11-12/YiLamV.md` §5 (为什么 `Stepᴳʷ` 证不出: 参照 Level 的 `ψ` 在结点层号低于目标层时保留, 新折叠在非字面有限的目标层上一律折叠).
查签名用检索, 大文件不要整篇读.

#### 1 要交的, 分步; 每做成一步先交

1. **派发换成燃料搜索的折叠** (非验收文件): 新建文件, 把 `YiLamFold` 里的 `dfin` 换成 `dlev` (或对派发参数化后实例化), 其余照旧. 证合法性: `TΛ`, 塔各项与读法 ψ₀(Ω_{Ω+1}) 的闭项都合法、无前提. 填 `Uniᴾ` 与读回域. 有限测试: 在 `YiLamNAsk` 那个极限目标上现在保留; 在 `YiLamVLost` 那个结点上根现在保留. 用 `probes/Survey/scripts/importclosure.py` 查导入闭包.
2. **值搬过来** (验收文件): 新折叠的闭项不低于 BTBO, 并不低于 ψ₀(Ω_Ω+Ω₁) 的带标签参照. 办法自选 (照 `YiLamV` 的转运; 或证 "派发保留得更多, 值不降" 一类的一步定理, 若成立).
3. **决定性的一步**: 在新折叠上证 `Stepᴳʷ` 的对应, 得到 ψ₀(Ω_Ω·2) 的带标签参照 (`GL.T2ᴸ`, `GL.T2-label`) 不高于读法 ψ₀(Ω_{Ω+1}) 的闭项 (或 `TΛ`). 做不过去时: 给出值停在哪里的编译事实; 或者编译出燃料搜索在 `Stepᴳʷ` 问到的那个位置上找不到该保留的槽位 (那里的目标层没有字面模数), 写清那个目标层的形状.

只要下界 (作者 2026-11-11 的原则): 选证法时不引入上界, 同值, 逐项精确. 下界从已闭合的最高锚点往上做.

**翻译账**: 回报里写清新派发读的是什么 (只读层号的字面结构, 不读记号), 哪些由树的要求逼出.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K (可交显式前提的条件定理, 函数外延只放验收文件); 堆到 6G 仍耗尽 (先按手册 §4.2). 做不成的部分写成带确切类型的模块参数. 没有编译的否定时只写 "未走通".

#### 2 过程要求

- 读完上面的文件后尽快动手: 第一个文件在 20 分钟内写出并编译.
- 每写完一个文件就编译; 每次回复都要有工具调用, 不要在一次回复里只思考.

#### 3 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiDl` (模块名 `OCF.Lean.YiDl…`). 折叠与实例做成非验收文件 (只导入 `probes/OCF/Lean/` 的主线文件与标准库, 文首写 "非验收文件"); 值放验收文件 (文首写 "验收文件"). 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 无关参数 `.( … )` 可以用.
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 堆墙多出在比较具体闭项的地方: 陈述逐字写, 不用别名; 大参照树放 `opaque`; 经非单射的头求解的隐式参数显式写出 (手册第 4 节).
- 仓库文件里不写本机路径. 不要把仓库整个拷到临时目录.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块.
- 你的临时目录: `<实验目录>/agents/dl`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几步; 一段话说对目标意味着什么 (新派发下闭项是否合法; 值是否越过 ψ₀(Ω_Ω·2); 若没有, 停在哪里, 原因是不是燃料搜索够不到).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值, 是否验收文件, 导入闭包的检查结果.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 用到的参照与它的验收定理.
4. 办法与翻译账.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 回报原文

#### 1 判决

第 1 步和第 2 步做成了。第 3 步未走通：没有证出 `Stepᴳʷ`，换成交了一组编译事实，说明值停在哪里、为什么停。

对目标意味着什么：
- **合法性。** 派发换成燃料搜索以后，闭项 `TΛ`（读法 ψ₀(Λ)）、塔的各项 `Tw n`、`T⁺ʷ`（读法 ψ₀(Ω_{Ω+1})）都合法，无前提。`Ψ-lgl` 对一切派发 `D` 成立，因为折叠 `Fold D` 是对派发参数化写的。
- **值。** 新折叠上已编译的下界有：BTBO ≼ `TΛ`；ψ₀(Ω_Ω+Ω₁) 的带标签参照 ≼ `T⁺ʷ`。新折叠还没有越过 ψ₀(Ω_Ω·2)，条件定理 `T2≼ᴳʷ` 已经搬到新折叠上。
- **停在哪里，原因是燃料搜索够不到。** 停在 `T⁺ʷ` 问到的结点 `Tt ξa`。它也在 `Stepᴳʷ` 结论里的项 `Ψ₀ (gK (d (suc m)))` 之下，对一切 m 成立（`asked-step`）。这个结点的链在第一步遇到位置 `pN`：
  - `pN` 的层号字面是 ℕ 极限，分量是 `fin 2, fin 5, fin 9, …, fin 27`（有限测试）。判断：这是 ω 型的层号。
  - 目标层 `LN` 里有这个层号的槽位（`couldP`）。
  - 新派发仍然折叠它（`lostP`；一般形式 `dl-lim`：源层号字面是 ℕ 极限时，对一切目标都折叠）。
  - 所以这个结点上的派发不完全（`not-full`）。
- **根本原因。** 燃料搜索只保留字面有限的层号（`fin-only`）。要保留 `pN`，派发必须给出两个 ℕ 极限层号相等的证明，即 `lev LN s ≡ lev (tw 2) pN`。只读字面结构的计算给不出这个证明，因为这需要两个函数相等。
- **判断，不是定理。** `Stepᴳʷ` 在 k ≥ 1 时要的正是这种层号：参照的 Level `ψ` 在这里保留结点，新折叠在这里折叠。

#### 2 文件表

全部在 `<仓库>/probes/OCF/Lean/`。每个文件都删掉自己的 `.agdai` 后按依赖次序冷编译，日志里只有本模块的 `Checking` 行。

| 文件 | 总行 / 代码行 | 冷编译退出码 | 常驻内存峰值 | 验收文件? | 导入闭包 |
|---|---|---|---|---|---|
| `YiDlFold.lagda.md` | 144 / 106 | 0 | 0.40 GB | 否 | `--only OCF.Lean.`：禁用表 0，闭包外 0，OK |
| `YiDlInst.lagda.md` | 134 / 89 | 0 | 0.39 GB | 否 | 同上，OK |
| `YiDlLost.lagda.md` | 152 / 89 | 0 | 0.40 GB | 否 | 同上，OK |
| `YiDlMore.lagda.md` | 54 / 39 | 0 | 0.39 GB | 否 | 同上，OK |
| `YiDlVRel.lagda.md` | 132 / 104 | 0 | 1.40 GB | 是 | 未单独跑 |
| `YiDlVBtbo.lagda.md` | 123 / 83 | 0 | 1.77 GB | 是 | 未单独跑 |
| `YiDlVOne.lagda.md` | 172 / 120 | 0 | 1.69 GB | 是 | 未单独跑 |
| `YiDlVLost.lagda.md` | 50 / 34 | 0 | 1.65 GB | 是 | 未单独跑 |
| `YiDlVStep.lagda.md` | 90 / 62 | 0 | 1.70 GB | 是 | 对它跑过一次（不带 `--only`）：禁用表命中 18（`Value`, `Stage2`, `GoodL`, `Correspond` 一类），验收文件预期如此 |

- 禁用构造（`postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、`Funext`、`--cubical`）检索为 0。
- 选项行都是 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。

#### 3 定理表

##### 编译定理，无前提

| 名字 | 逐字的陈述 | 白话 | 文件 |
|---|---|---|---|
| `dl≡dlev` | `∀ k K r → dl k K r ≡ dlev k K r` | 新派发与 `YiLamNFuel.dlev` 逐点相等（`dl` 在目标层 `zero` 上定义性地折叠） | YiDlFold |
| `Ψ-lgl` | `∀ m {k} (V : Lw k) x ξ → Lgl k ξ → Lgl m (Ψ m V x ξ)` | 在 `Fold D` 里对一切派发 D 成立 | YiDlFold |
| `TΛ-legal` | `Lgl zero TΛ` | 读法 ψ₀(Λ) 的闭项合法 | YiDlFold |
| `Tw-legal` | `∀ n → Lgl zero (Tw n)` | 塔的各项合法 | YiDlFold |
| `T⁺ʷ-legal` | `Lgl zero T⁺ʷ` | 读法 ψ₀(Ω_{Ω+1}) 的闭项合法 | YiDlFold |
| `Dl`, `domΛ` | `Dl : Uniᴾ`, `domΛ : Domᴾ Dl` | 填满接口与读回域；各行是 `refl`，`stp` 是 `dl` | YiDlInst |
| `stp-full-J` | `StpFullᴾ Dl VJ G.top tt` | 在 `YiLamNAsk` 的极限目标 `J` 上，链的派发对一切位置完全 | YiDlInst |
| `more` | `∀ k K r → IsKeep (dfin k K r) → IsKeep (dl k K r)` | 新派发逐点保留得不少于 `dfin` | YiDlMore |
| `dl-lim` | `∀ k K r → LimL (lev K r) → dl k K r ≡ fold` | 源层号字面是 ℕ 极限时一律折叠 | YiDlLost |
| `not-full` | `Full LN (tw 2) (cmpw V2 rN) → ⊥` | 那个结点上的派发不完全 | YiDlLost |
| `btbo-Tw2` | `D.BTBOᴵ ≼ NA.read (W.Tw 2)` | 也有 `btbo-Tw3` | YiDlVBtbo |
| `btbo-TΛ` | `D.BTBOᴵ ≼ NA.read W.TΛ` | BTBO 是 `TΛ` 的下界 | YiDlVBtbo |
| `aboveʷ` | `L.suc D.BTBOᴵ ≼ NA.read W.T⁺ʷ` | 也有 `aboveΛ` | YiDlVOne |
| `ΩΩ+1ʷ` | `L.ψ⁰ (L.suc (L.Ω S2.ℓ₀)) ≼ NA.read W.T⁺ʷ` | 参照经 `S2.ts-label` 验收为 ψ₀(Ω_Ω+1) | YiDlVOne |
| `χ₁≼ʷ` | `S2.χ 1 ≼ NA.read W.T⁺ʷ` | 参照经 `S2.χ1-label` 验收为 ψ₀(Ω_Ω+Ω₁) | YiDlVOne |
| `asked` | `NA.read (Ψ₀ (gK ξa)) ≼ NA.read W.T⁺ʷ` | | YiDlVLost |
| `asked-node` | `NA.read (Ψ₀ (G.lc rN X.bN)) ≼ NA.read W.T⁺ʷ` | 那个结点的值不高于 `T⁺ʷ` | YiDlVLost |
| `asked-step` | `∀ m → NA.read (Ψ₀ (G.lc rN X.bN)) ≼ NA.read (Ψ₀ (gK (d (suc m))))` | 那个结点的值不高于 `Stepᴳʷ` 结论里的项 | YiDlVLost |

##### 条件定理

| 名字 | 逐字的陈述 | 文件 |
|---|---|---|
| `T2≼ᴳʷ` | `Stepᴳʷ → GL.T2ᴸ ≼ NA.read W.T⁺ʷ` | YiDlVStep |

其中
`Stepᴳʷ = ∀ k m → GL.χ k ≼ NA.read (d m) → GL.χ (suc k) ≼ NA.read (Ψ₀ (gK (d (suc m))))`。

##### 有限测试（`refl` 或 `tt`）

在 YiDlInst：
- `asked◁ : NJ ◁ Tw 3`：在新的 `Tw 3` 里，沿同一条路径仍问到那个结点；`VJ : Lw (lc J (up J))` 通过类型检查。
- `keeps♯ : IsKeep (stp VJ G.top tt r♯)`：在 `r♯` 上现在保留（旧折叠是 `lost`）。
- `root-kept : rootW (lev (tw 2) rN) zero ⌜_⌝ (witU zero) (cmpw V2 rN) ≡ keep (0 , 0 , 0 , inj₂ (inj₁ tt)) refl`：`YiLamVLost` 那个结点的根现在保留（旧折叠是 `root-lost`）。

在 YiDlLost：
- `gKc-1 : gKc 1 ≡ G.lc rN bN`
- `node-fold : Ψ zero V2 (λ _ → fold) (G.lc rN bN) ≡ G.lim (λ n → Ψ zero V2 (λ _ → fold) (bN (chain LN Gk n)))`
- `occP : Occ pN (bN G.top)`，`limP : LimL (lev (tw 2) pN)`，`couldP : At LN (lev (tw 2) pN)`，`lostP : cmpw V2 rN pN ≡ fold`
- `LP-0`, `LP-1`, `LP-2`, `LP-5`：`pN` 的层号的分量 0, 1, 2, 5 依次是 `fin 2`, `fin 5`, `fin 9`, `fin 27`。

##### 用到的参照

`S2.χ 1`（`S2.χ1-label`）、`L.ψ⁰ (L.suc (L.Ω S2.ℓ₀))`（`S2.ts-label`）、`GL.T2ᴸ`（`GL.T2-label`）。标签只出现在验收文件里。

#### 4 办法与翻译账

**办法。**
- `YiDlFold`：把 `YiLamFold` 的折叠逐字抄进 `module Fold (D : ∀ k K → Ext k K)`，`cmpw` 的 `wΩ` 子句和 `ptsΩ` 里的 `dfin` 换成 `D`，再取 `open Fold dl public`。公共上界 `Lw`、`VΛ`、`Kfk`、`nrmk` 直接从 `YiLamFold` 导入。
- 值的搬运：把 `YiLamVRel`、`VBtbo`、`VOne`、`VStep` 逐字搬过来。用脚本把 `W.` 前缀分成两类：
  - 派发无关的名字指 `YiLamFold`，记作 `WL`；
  - `Ψ`, `cmpw`, `ptsΩ`, `Tw`, `T⁺ʷ`, `TΛ` 指新折叠。

  因为 `dl zero _` 定义性地是折叠，`ptRʷ` 不用改。
- 障碍上的位置 `s` 是在临时目录里用 Agda 交互求值、加一个有限的字面搜索找出的，之后作为字面项写进 `YiDlLost`。

**翻译账。**
- **新派发读什么。** 只读层号的字面结构：
  - 目标层号的头构造子；
  - ℕ 极限只看前 `n + 1` 个分量（燃料 `φ n = n`），Ω 结点层号只看 `top` 支；
  - 源层号是否字面是 `fin n`（`finOf`）。

  不读记号的项、序、基本列。
- **由树的要求逼出的：**
  - 派发要给出 `lev m s ≡ lev K r` 的证明。不开 K、没有函数外延时，ℕ 极限层号的相等算不出来，所以只能保留字面有限的层号。障碍的根就在这里。
  - 合法性对一切派发成立，所以换派发不需要新的合法性论证。
- **新增脚手架。** `dl` 的 `zero` 子句：为了让值的转运逐字通过，与 `dlev` 逐点相等（`dl≡dlev`）。它来自验收方便，不来自记号。
- **这一步带来的信息。** 障碍从 "目标层不是字面有限" 推进到 "源层号不是字面有限"，第一处出现在 ω 型的层号。翻译没有变深。

#### 5 第一个障碍

**缺的引理。** `Stepᴳʷ`，类型就是上面逐字写出的那一行。没有写过过不了检查器的证明，所以没有报错原文。

**编译到的事实。** `YiDlLost` 的 `lostP` 与 `not-full`：

| 项 | 形状 |
|---|---|
| 目标层 `LN = lev (tw 2) rN` | `⌜nrmk (1 + Tw 2)⌝`，是 ℕ 极限，分量里嵌套 ℕ 极限 |
| 源位置 | `pN = (nrmk zero ξa , nrmk-lgl zero ξa , inj₂ s)`，其中 `s = 0 , 1 , 0 , 0 , 0 , inj₂ (inj₁ tt)` |
| 源层号 `lev (tw 2) pN` | ℕ 极限，分量是 `fin 2, fin 5, fin 9, …` |
| 目标层里的槽位 | `s` 本身 |

要保留 `pN`，派发得在这个特定输入上返回 `keep s e`，证明 `e : lev LN s ≡ lev (tw 2) pN` 的两边都是 ℕ 极限。

判断（不是定理）：
- 以位置为输入的派发要认出 `pN` 与 `rN` 在同一个分支（坐标同为 `nrmk ξa`），就要判定 `Raw zero` 树的相等，这碰到壁垒。完全的派发还会判定 ℕ 极限层号的字面相等，见 `YiLamNLim.full→dec`。
- 可能的出路是带来历的位置，`YiLamNLim` 说它没有被否定。

**判断：`Stepᴳʷ` 缺的是什么。**
- k = 0（即 χ₁）只要有限层号，已经证出。
- k ≥ 1 要 ψ₀(Ω_Ω+Ω_{χ_k})，其中 χ_k > ω。参照在 ω 及以上的层号上保留结点，新折叠在那里折叠。
- 折叠后的值是否由更高一层补偿回来，没有做全局的论证。

#### 6 偏离与事故

- **`dl` 不是字面的 `dlev`。** `dl` 多一个目标层 `zero` 的子句，已用 `dl≡dlev` 证明两者逐点相等。燃料用 `dlev` 的 `φ n = n`，没有另选。
- **多交了三份文件。** `YiDlMore`（逐点保留不少于 `dfin`，这是 "保留得更多、值不降" 的前一半，后一半没有证）、`YiDlLost`、`YiDlVLost`。
- **结点与坐标改用新折叠算。** `YiLamNAsk` 那个结点的路径、`YiLamVLost` 那个结点的坐标 `ξa` 都用新折叠重新算过，不是直接拿旧折叠的。
- **开发中的编译错误。** 一次：`YiDlMore` 的 ParseError（绝对 λ 写法），已修好。
- **文件操作。**
  - 没有改任何已有文件；tracked 文件的 `git diff` 为空。
  - 只用字面的精确路径删过自己的 `.agdai`，没有用 `--ignore-interfaces`。
  - 求值试验在 `<实验目录>/agents/dl/x/`（`Probe.agda` 与临时库文件）。
  - 编译日志在 `<实验目录>/agents/dl/`，冷编译日志是 `cold-<模块>.log`。
