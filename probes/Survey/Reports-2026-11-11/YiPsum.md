# 累加能否去掉 (YiPsum)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-11 05:21 至 06:16 |
| 工具调用 / agda 编译 (粗数) | 76 / 23 |
| token (usage 字段，按消息去重) | 输出 343666；新写入缓存的输入 658355；读缓存的输入 16870516；其余输入 112 |
| 写过的仓库文件 | `YiPsumBase.lagda.md`, `YiPsumFold.lagda.md`, `YiPsumInst.lagda.md`, `YiPsumOrig.lagda.md`, `YiPsumTw3.lagda.md`, `YiPsumVal.lagda.md`, `YiPsumZp.lagda.md` |
| 文件前缀 | `YiPsum` (在 `probes/OCF/Align/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 累加一题返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 能去掉，带定义域（证书一致，极限处路径取第 0 支，槽位取规范位置）；塔的第 3 项的闭项各支里没有部分和，根的坐标上仍有归一；七件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库> = <仓库>) 的一路执行方, 任务是一道判定题: "折叠里极限层号处的累加 (部分和) 能否去掉". 交定理或编译过的否定. 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

### 0 先读什么

1. `AGENTS.md` 全篇. 特别是 Agda 一节 (选项, 无关参数, 文字预算, 退出码, 堆) 与 "结论的写法" (三档; 否定要编译定理; 前提要可满足). 作者对累加有保留: `probes/Survey/EBOHandbook.md` §3.8 (累加与它的毛刺), 另读 §4.1 到 §4.5, §5.4.
2. `probes/Survey/Reports-2026-11-11/README.md` 的 §2; 再读同目录 `YiRawFold.md` 的回报原文 §5, §6 (a) (部分和一行是怎么来的, 缺的那条引理的类型), 与 `YiRawNeg.md` 里关于 `psum` 的几条.
3. 代码 (都在 `probes/OCF/Align/`, 模块名 `OCF.Align.<名>`; 都已定稿, 可以导入, 不许编辑):
   - **被问的折叠**: `YiRawFoldBase` (`Ext`: `low` 或 `mix w`; `inS`, `inL`; `psum`, `psum-step`, `psum-legal`; `CohP`), `YiRawFold` (`Ψ`; 关键子句 `Ψ m (lim f) pl L (mix w) G.top = G.lim (psum m (λ n → Ψ m (f n) … (mix (λ r → w (n , r))) G.top tt tt))`; `own`, `ownT`; `Ψ-legal`, `Ψ-cp`; `Φᵐ`, `Φ`), `YiRawFoldInst` (`ω+1-body₀`), `YiRawFoldUp` (`Φᵐ-below`, `Zp`), `YiRawFoldNoLim` (`side-lim-illegal`: 目标与公共上界都取 ω, 派发取 "目标是 K 自己" 时, 各支折叠逐项排成的极限不合法; 原因是相邻两支输出的槽位是同一层号的不同位置).
   - 接口: `YiRawIf` (`Tgt`, `dispatch`, `dispatch-complete`), `YiLvIf` (`lev`, `shift`, `Tri`, `Kept`).
   - 规范比较: `YiLvNegCanon` (`ccompare`, `canon`, `canon-const`, `ccompare-slot`, `ccompare-levels`, `ccompare-shift`: 槽位只由两个层号决定, 沿路径搬位置不变, 都是命题相等).
   - 值的序与部分和: `YiRawNegNorm` (`_≼_`, `lim≼psum`, `psum-inflates`, `cum-above`).
   - 块: `RR5IrrCore` (`Cp`, `Dn`, `DnK`, `DnT`, `Lgl`), `RR5IrrCheck`.
   查签名用检索, 大文件不要整篇读.

### 1 问题

上一轮写在 `Raw K` 上的折叠做成了, 但有一行带累加: 保留模式 (外部派发是 `mix w`) 下, 极限层号 `lim f` 上的 `top` 取各支折叠的**部分和**, 而不是各支折叠逐项排成的极限. 构造路这样取的依据是 `side-lim-illegal`, 但那条否定只针对 `self` 派发 (槽位就是树里的位置, 同一层号在不同分支是不同位置). 对**规范槽位**的派发 (`own`, `ownT`, `at q` 经 `ccompare`), 逐项的极限合法不合法, 没有证也没有否定. 缺的那一条是

```agda
∀ n → Cp m (Ψ m (f n) (pl n) (proj₂ L n) (mix (λ r → w (n , r))) G.top tt tt)
           (Ψ m (f (suc n)) (pl (suc n)) (proj₂ L (suc n)) (mix (λ r → w (suc n , r))) G.top tt tt)
```

对规范槽位的 `w`. 构造路的判断 (未验证): 它要 "派发沿路径限制后作为函数相等", 即函数外延加层号相等证明的唯一性.

### 2 交什么

**二选一, 都要编译:**

- **(甲) 去掉累加.** 写折叠的一个变体 (在你自己的文件里, 不改 `YiRawFold`): 保留模式下极限层号的 `top` 取各支的逐项极限, 至少对规范槽位的派发; 证明输出合法, 带嵌套证据, 保持第一位置 (需要 `CohP` 一类前提就写明并说明规范实例上可满足); 接口 `YiRawIf.RawFold` 的实例与派发完全性不丢; `tw 3` 的闭项在变体里仍然合法. 说明变体与原折叠的输出在规范实例上的关系.
- **(乙) 去不掉.** 给一个具体的 `Plain` 且合法 (并且一致) 的层号, 规范槽位的派发, 使逐项的极限不合法 (像 `side-lim-illegal` 那样的编译否定); 说明它否定的是哪一类派发, 不否定什么. 再回答: 是不是 "凡保留模式下逐项的极限合法的派发, 都推出某条不可得的原则 (函数相等, 或更强)".

**不论哪一种, 再交累加对值的影响:**
- 在规范实例上 (例如公共上界 ω, ω·2, 以及 `YiRawFoldInst` 的 `ω+1-body₀` 那一处), 部分和的值与逐项极限的值是否相等 (在 `YiRawNegNorm._≼_` 的意义下互相 `≼`, 或你写明的值序). `psum-inflates` 说在相邻项相等的列上部分和严格偏高; 折叠里的各项是不是总是严格增长并且对加法吸收 (每一项是加法不可分解的), 从而部分和不偏高? 写成定理, 或给出偏高的折叠实例.

先做最便宜的决定性实验: 公共上界与目标都取 ω, 派发取 `ownT ω` (规范槽位), 看第 1, 2 支的输出之间有没有字面的第一位置.

**停下的条件.** 同一处连续三次重新设计仍过不了检查器; 需要 Funext 或 K (这时把它写成显式前提的条件定理, 并另给不带它的最强结果). 没有编译定理的地方只写 "未走通".

### 3 规则

- **只新建文件**, 前缀 `YiPsum`, 放 `probes/OCF/Align/`, 中文 literate Agda (`.lagda.md`). 不改任何已有文件 (含 README, LOG, RESULTS, AGENTS), 不碰 `src/`, `archive/`. 同时在跑的另四路用前缀 `YiOmFold`, `YiOmNeg`, `YiRawVal`, `YiLvAll`, 不要动它们的文件, 也不要依赖它们.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. Funext 只准作显式前提, 所在文件文首标 "条件".
- **文字预算** (AGENTS Agda 一节): 每个模块文首不超过 5 行 (判决与档位, 做了什么, 不否定什么, 入口指向); 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件. 一次性的试验放你的临时目录, 用纯 `.agda`.
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Align/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Align/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径).
- 你的临时目录: `<实验目录>/agents/psum`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0; `python3 probes/Survey/scripts/importclosure.py OCF.Align.<模块>` 通过; 检索禁用构造为 0.

### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: (甲) 还是 (乙), 一段话说对纲领与目标意味着什么 (累加是这个块逼出的, 还是一种可以换掉的写法).
2. 文件表: 文件, 代码行数, 冷编译退出码.
3. 定理表: 名字, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 条件定理写出前提的 Agda 类型与可满足性.
4. 累加对值的影响: 定理或实例.
5. 第一个障碍: 精确到子句, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
不用 "只差", "自然" 一类形容.

## 回报原文

### 判定题 "折叠里极限层号处的累加能否去掉" 回报 (前缀 YiPsum)

#### 1 判决

**(甲)，带定义域。** 部分和那一行可以换成逐项极限，保留模式下也可以，没有 Funext，没有 K。条件是：

- 派发的槽位取结构规范位置 (新写的 `csQ`/`pre`)；
- 层号在域 `Domᵗ K pl L = ZpL K L × CohP K pl L` 里：证书一致，并且每个极限的每一步路径在极限处只取第 0 支。

域里有 ω+n、ω·2、ω·2+1，以及累加归一坐标的读回 `read0 (1 + cum v)`。`tw 3` 的闭项 `T₃ᵗ` 无前提合法，各支的折叠里没有部分和；它走的是 `T₃ᶜ` 那条根链 (坐标 `κ v = 1 + cum v`)，不是 `T₃ᵐ` 那条根不改行的链。

对纲领与目标：这一行累加是一种可以换掉的写法，不是块逼出的。块逼出的是另外两件：

- **槽位必须规范。** 取位置自己的 `self` 派发不行 (已有 `side-lim-illegal`；新增 `self-not-cohX`)。
- **证书必须一致。** 逐项的折叠连定义都要无关地用到一致性前提 `Dm`，因为链点的守卫要推进输出合法。

`ZpL` 是证明用到的范围，是否必要没有证也没有否定。

代价：

- 折叠的定义域从 "一切 `Plain` 且 `Legal` 的 K" 缩到 `Domᵗ`。
- `YiRawIf.RawFold` 没有字面的实例，四条律写成同形的 `RawFoldOn Domᵗ`。
- `tw 3` 根不改行的版本没有做成 (缺的引理见 §5)。

翻译账：新增脚手架是 `csQ`/`unshiftQ`/`pre`、`Scheme`、`CohX`/`CohS`/`Dm`、`ZpL`、`ZC`，都由块的字面第一位置逼出，没有读记号。第 4 层逼出：无。

乙的第二问 ("凡保留模式下逐项极限合法的派发，都推出不可得的原则吗")：**否。** `pre` 之后的派发逐项合法，不需要任何原则 (编译定理)。原来的 `ownT ω` (`ccompare`，不过 `pre`) 才归到函数相等，见 §3 的 `YiPsumOrig`。

#### 2 文件表

都在 `<仓库>/probes/OCF/Align/`。删自己七个接口后按依赖序冷编译，每个约 2 秒，常驻内存约 0.45G。

| 文件 | 代码行 | 冷编译 |
|---|---|---|
| `YiPsumBase.lagda.md` | 146 | 0 |
| `YiPsumFold.lagda.md` | 279 | 0 |
| `YiPsumZp.lagda.md` | 82 | 0 |
| `YiPsumInst.lagda.md` | 157 | 0 |
| `YiPsumTw3.lagda.md` | 114 | 0 |
| `YiPsumOrig.lagda.md` (条件) | 140 | 0 |
| `YiPsumVal.lagda.md` | 192 | 0 |

- 依赖序：Base，Fold，Zp，Inst，Tw3，Orig，Val。
- `importclosure.py` 七个模块都是 "禁用表命中 0，OK"。
- 检索 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`--cubical`、`irrelevant-projections` 为 0。
- `Funext` 只在 `YiPsumOrig` 作显式前提。
- 日志在 `<实验目录>/agents/psum/` (`*.cold.log`)。

#### 3 定理表

除标明的以外都是编译定理。

**`YiPsumBase`**

| 名字 | 白话 | 档 |
|---|---|---|
| `restrictX`, `CohX` | 派发沿路径的限制；极限处后一支的派发限制回来等于前一支的 (函数的相等) | 定义 |
| `csQ`, `unshiftQ`, `upQ`, `pre` | "`v` 在规范位置上的值"，对层号与分支编号结构递归；类型沿递归定义性不变，没有层号方程与搬运 | 定义 |
| `pre-inS` | `pre` 与后继处的限制可交换，`refl` | 编译 |
| `pre-complete`, `pre-sound` | 过 `pre` 后派发仍完全，也不多保留 | 编译 |
| `pre-ω-step` | ω 上第 n+1 支限制一步等于第 n 支，`refl` | 编译 |
| `test-pre-slot`, `test-canon-slot` | 槽位与 `ccompare` 的规范槽位同一格 (只核对了一个位置) | 有限测试 |
| `self-not-cohX` | 接口的 `self` 派发在 ω 上不满足 `CohX` | 编译否定 |

**`YiPsumFold`** (`module Termwise (S : Scheme)`)

| 名字 | 白话 | 档 |
|---|---|---|
| `Ψᵗ` | `Ψ` 改一行：极限层号上 `top` 不分保留与否都逐项；多一个无关参数 `Dm`；`own`/`ownT` 取方案的 | 定义 |
| `Ψᵗ-legal` | 输出合法 | 条件定理 |
| `Ψᵗ-nested`, `Ψᵗ-cp`, `Ψᵗ-pos` | 嵌套证据、保持第一位置 | 编译 |
| `belowᵗ` | 小公共上界的 `top` 折叠是大的第一位置，对一切路径、一切外部派发 (原来 `Φᵐ-below` 只有 `Zp` 路径) | 编译 |
| `top-rowᵗ`, `node-rowᵗ`, `top-rowˢᵗ` | 行，`refl` | 编译 |
| `keepᵗ`, `foldᵗ` | 携带强度的两条 | 编译 |

`Ψᵗ-legal` 的前提：
```agda
(D : Dm k pl L)   -- Dm k pl L = CohP k pl L × CohS k pl L
CohX k L x
```
可满足：`YiPsumInst.dm-gen` 在 `Domᵗ` 上给出 `Dm`；`CohX` 由 `preCoh` 或 `cohX-low` 给出。

**`YiPsumZp`**

| 名字 | 白话 |
|---|---|
| `cs-restrict` | 规范化与沿 `Zp` 路径的限制可交换 |
| `unshift-restrict` | `unshiftQ` 沿自己的路径限制下来就是 `down` |
| `csQ-coh`, `preCoh` | `ZpL K L → CohL K L → ∀ x → CohX K L (pre K L x)`；K 与路径是变量 |

证法：对路径归纳，把被规范化的函数一起推广，每一步定义性。

**`YiPsumInst`** (方案 `canonˢ`：`own`/`ownT` 先过 `pre`)

| 名字 | 白话 | 档 |
|---|---|---|
| `cohS-gen`, `dm-gen` | `Domᵗ K pl L → C.Dm K pl L` | 编译 |
| `rawFoldᵗ : RawFoldOn Domᵗ` | 接口四条律在域上 (`keep-law`, `fold-law`, `position`, `legal`) | 编译 |
| `entry-complete`, `entry-sound`, `complete-ownᶜ` | 派发完全与不多保留 | 编译 |
| `dom-ω+`, `dom-ω2`, `dom-ω2+1` | 域的实例 | 编译 |
| `closedᵗ-legal`; `Ωω+1ᵗ-legal`, `Ωω+2ᵗ-legal`, `Ωω2ᵗ-legal`, `Ωω2+1ᵗ-legal` | 闭项合法 | 编译 |
| `body₀ᵗ-row` | `ω+1-body₀` 同一处，推进用的输出是各支的逐项极限 `G.lim sideᶜ`，`refl` | 编译 |
| `body₀ᵗ-legal`, `sideᶜ-step` | 它合法；相邻两支对一切 n 有字面第一位置 | 编译 |
| `test-slotᶜ` | 槽位 (2, 根) | 有限测试 |

**`YiPsumTw3`**

| 名字 | 白话 |
|---|---|
| `ZC`, `zc→zpL`, `zp-add-cp`, `add-zc`, `cum-zc`, `κ-zc` | 累加归一坐标的证书读回后是 `ZpL` 的 |
| `read0-dom`, `κ-dom` | 一致且 `ZC` 的坐标，读回在 `Domᵗ` 里 |
| `T₃ᵗ`, `T₃ᵗ-legal` | 闭项与合法性，无前提 |
| `T₃ᵗ-start`, `T₃ᵗ-feedback`, `T₃ᵗ-branch` | 行，`refl` |

**`YiPsumOrig`** (原方案；公共上界与目标都取 ω，派发 `ownT ω`)

| 名字 | 白话 | 档 |
|---|---|---|
| `step₀₁`, `step₁₂` | 第 0, 1, 2 支依次是字面第一位置 (最便宜的决定性实验的结果) | 有限测试 |
| `step₂₃-only`, `step₂₃-if` | 第 2 支是第 3 支的第一位置，当且仅当第 2 支字面等于第 3 支的第一支 | 编译 |
| `pointwise` | 两个派发函数在 `Pre (fin 2)` 上逐点相等 | 编译 |
| `step₂₃-from-eq`, `step₂₃-cohX` | 由函数相等或 `CohX` 推出那一步 | 编译 |
| `step₂₃-funext` | `Funext → Cp ω (sideᵒ 2) (sideᵒ 3)` | 条件定理 |
| `orig-termwise-legal` | 原方案下逐项折叠合法 | 条件定理 |

- `step₂₃-funext` 的前提是标准的 `Funext`，与理论相容，不可证。
- `orig-termwise-legal` 的前提是 `O.Dm`；它在 ω 上的第 2 条方程就是上面那个函数相等，没有证。
- **判断 (不是定理)：** 不带 Funext 时那一步在 Agda 里证不出。依据是 `refl` 被检查器拒绝，加上闭项的典范性。

**`YiPsumVal`**：见 §4。

**变体与原折叠的关系。** 子句逐条平行，差三处：那一行逐项；派发先过 `pre`；多一个无关的 `Dm`。两者是两个递归定义，极限之下的字面相等要函数外延，没有比 (与上一轮对 `foldᶠ` 的情形相同)。能直接比的一处是 `termwise-below-psum`。

#### 4 累加对值的影响

值序是 `YiRawNegNorm._≼_`，只比了目标第 0 层的输出。这里的 `psum` 是 `YiRawFoldBase.psum`；`YiRawNegNorm` 的 `lim≼psum`/`psum-inflates` 说的是 `YiLvNegCum.psum` (每步多加一个后继)，所以重证了一份。

| 名字 | 结论 | 档 |
|---|---|---|
| `lim≼psumᵖ` | 部分和不降值 | 编译 |
| `psum-flat` | 各项吸收时部分和不升值 | 条件定理 |
| `absorb-suc` | `closedᵐ k + closedᵐ (suc k) ≼ closedᵐ (suc k)`，对一切 `Plain` 且 `Legal` 的 k | 编译 |
| `ω-psum≼lim`, `ω-lim≼psum` | ω 上部分和与同样各项的逐项极限互相 `≼` | 编译 |
| `ω2-psum≼lim`, `ω2-lim≼psum` | ω·2 上同样 | 编译 |
| `const-inflates`, `const-not-back` | `Kc = lim (λ _ → zero)` 上部分和严格偏高 | 编译 |
| `termwise-below-psum` | 同一层号上 `closedᵗ Kc ≺ closedᵐ Kc` | 编译 |

- `psum-flat` 的前提 `Absorb g = ∀ n → plus zero (g n) (g (suc n)) ≼ g (suc n)`；可满足：`ω-absorb`, `ω2-absorb`。
- `absorb-suc` 没有用 "各项加法不可分解" 或 "严格增长"。它只用三件：折叠保持第一位置；输出以 `cO` 为第一位置 (`Ψ-low`)；`x + cO k` 的第一位置里有 `suc x` (`one-below`)。
- `Kc` 合法、一致、在 `Domᵗ` 里，但各支相同，是退化的层号，不是规范读回的 ω。

**没有比的：** `ω+1-body₀` 那一处 (保留模式，输出在 `Raw ω` 里)。那里没有值序，部分和是否偏高没有判定。已有的只是逐项版在那里合法 (`body₀ᵗ-legal`)。

#### 5 第一个障碍

**(a) 原派发。** 子句是 `Ψ ω (lim fin) … (mix w) G.top`，`w = ownT ω`。临时目录试验 `Exp2.agda` 里 `b23 = inj₂ (inj₁ refl)` 被拒，报错原文：

```
error: [UnequalTerms]
1 != 2 of type ℕ
when checking that the expression refl has type
B 2 ≡ Nd.t (ndT (lim fin) (fin 2) (fin-plain 3) (fin-legal 3)
 (inS (mix (λ r → tri→way (OCF.Align.YiLvNegCanon.ccompare (suc (lim fin)) ω-plain (…) (inj₁ tt) (inj₂ (3 , r)))))))
```

缺的是 `u₂ ≡ u₃` (`YiPsumOrig` 里的两个派发函数)。逐点是 `refl`，作为函数不是定义性相等。

构造路上一轮的判断 "要函数外延加层号相等证明的唯一性" 只对这种写法成立。换成 `csQ` 以后两样都不要。

**(b) 变体的域的边界：`ZpL` 之外。** `unshiftQ` 在 `lim (suc m) p` 处一律交 `stay`，`cs-restrict`/`unshift-restrict` 的归纳在那里没有子句。缺的是对一般 `CP` 路径的同两条引理。没有证，也没有否定。

**(c) `tw 3` 根不改行的版本** (链点 `1 + v`，像 `T₃ᵐ`)。链点的下一点是 `η + closedᵗ …`，它的证书要一致并且 `ZC`。缺：

```agda
∀ a (l : Lgl zero a) (z : ZC a l) (ch : Coh a l) →
  Coh (closedᵗ (read0 a) (rplain a) (read0-legal a l) (read0-dom a l z ch))
      (closedᵗ-legal (read0 a) (rplain a) (read0-legal a l) (read0-dom a l z ch))
  × ZC (closedᵗ (read0 a) (rplain a) (read0-legal a l) (read0-dom a l z ch))
       (closedᵗ-legal (read0 a) (rplain a) (read0-legal a l) (read0-dom a l z ch))
```

前一半是上一轮 `OutCoh` 的同形物，没有攻。所以 `T₃ᵗ` 里部分和仍在根的坐标 (`cum`) 上，这一条与 `T₃ᶜ` 相同。

**(d) 值。** 缺第 ω 层 (一般目标层) 上的值序。

#### 6 偏离与事故

- **变体不只改一行。** 派发也换了 (`pre`)；目标是 K 自己时槽位是规范位置而不是位置自己。折叠多了无关参数 `Dm`，只在 `Domᵗ` 上有定义。
- **没有交 `YiRawIf.RawFold` 的字面实例**，交的是同形的 `RawFoldOn Domᵗ`。`YiRawNegModel.Forced` 已说明：逐项且读 `L` 的折叠不可能有无前提的 `legal`。
- **`T₃ᵗ` 按 `T₃ᶜ` 的根链做**，不是 `T₃ᵐ` 的。
- **另一处累加没有动。** `YiLvFoldAdd.add` 在 `x + top` 极限层号处的逐项累加 (更早一轮的写法) 仍在原折叠与变体里。本题只处理了 `Ψ` 的部分和行。
- **中途重写过自己的文件。** 第一版规范化用 `YiLvNegCanon.back` 加位置与方程的对，只证到极限自己那一步；改成不带方程的 `csQ` 后一般定理成立。仓库里只留最终版。
- **`YiPsumOrig` 带 `Funext` 前提**，文首标了 "条件"。
- 删接口只删了自己七个模块的 `.agdai`，写的是字面路径，一次命令。冷编译外面套了 `/usr/bin/time -l`。
- 临时试验 `Exp1` 到 `Exp4` 在 `<实验目录>/agents/psum/x/`；其中 `Exp2` 是那条被拒的 `refl`，退出码 42 是预期的。
- 没有改任何已有文件，没有碰另四路的文件，没有提交，没有推送。
