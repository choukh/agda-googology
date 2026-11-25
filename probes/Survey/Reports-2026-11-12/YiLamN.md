# 接口实填与极限目标派发的事实与否定 (YiLamN)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-12 01:41 至 02:10 |
| 工具调用 / agda 编译 (粗数) | 52 / 10 |
| token (usage 字段，按消息去重) | 输出 163143；新写入缓存的输入 386589；读缓存的输入 7436803；其余输入 82 |
| 写过的仓库文件 | `YiLamIf.lagda.md`, `YiLamNAsk.lagda.md`, `YiLamNAskV.lagda.md`, `YiLamNFuel.lagda.md`, `YiLamNInst.lagda.md`, `YiLamNLim.lagda.md`, `YiLamNRel.lagda.md` |
| 文件前缀 | `YiLam` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-12: 接口实填与极限目标的派发一路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 对上姊妹接口 Uniᴾ；塔的第 3 项里问到极限目标，那里一律折叠；燃料搜索在那一处完全；固定极限目标上完全推出字面相等的判定（谓词太宽）；七件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 作者的指示是 "朝着最终目标的关键路径走" (最终目标: 布劳威尔树上 ψ₀(Λ) 的合法闭项, 值不低于 EBO). 主线块上已经有一套一致折叠的设计候选 `probes/OCF/Lean/YiLamFold.lagda.md` (读法 ψ₀(Λ) 的闭项 `TΛ` 合法无前提). 按 AGENTS 的 "构造与否定配对, 共用接口" 与 "摆脱先手", **你这一路做两件事: (一) 让这个设计对上已定稿的接口 `YiUniIf.Uni`; (二) 对它的派发在目标层不是有限数 (极限或不可数) 时的情形, 写出编译的事实与否定.** 另一路在做 `TΛ` 的值, 你不做值. 主审会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇. 特别是 "律带公共上界, 构造与否定配对", "量化域先取带证据的读回域" (反例对象不在读回域内的否定读作 "谓词太宽"), "归到已知的墙要逐条核机制", "前提要可满足", Agda 一节.
2. `probes/Survey/EBOHandbook.md` 只读 §3.1, §4.1 到 §4.5, §5.2.
3. 设计与测试: `probes/OCF/Lean/YiLamFold.lagda.md` 全读 (`dfin` 只在目标层字面是 `suc^n zero` 时按头构造子保留, 否则折叠; `cmpw` 在 Ω 结点层号上用 `dfin`; `rootW` 用根见证 `Wit`; `ptsΩ` 的下一点用 `dfin k (g η)`; 观察取部分和 `psum`), `YiLamTest.lagda.md` (`noWitω`, `dfinω`: 极限根层没有见证, 派发一律折叠).
4. 已定稿的接口与它的否定 (只增不改): `YiUniIf.lagda.md` (`Uni`, `Dom`; 注意 `top-rowᶜ` 的第三个参数是链点上折叠值的序列本身, 不是部分和; 律 `top-up`), `YiUniTw2.lagda.md`, `YiUniNegCmp.lagda.md` (`cmp-full→lpo`, `bound→found`), `YiUniNegStep.lagda.md` (`step-full→lpo`, `stp-full→lpo-dom`), `YiUniNegKeep.lagda.md`, `YiUniForced.lagda.md`. 回报: `probes/Survey/Reports-2026-11-12/YiUni.md` (特别是 §4 的判断 J1, J2).
5. 旧块上同形的否定 (写法参考, 结论不要照搬): `probes/OCF/Align/YiGenNegWall.lagda.md` (`chain→weak-eq`: 极限层号字面相等的弱判定), `YiGenFoldGap.lagda.md`.
6. 第八次审查的手算 (判断, 没有编译): 规范链上会问到目标层是极限的派发, 例如 `⌜x + top⌝ = suc ⌜x⌝` 而 `⌜x⌝` 是极限; 诚实的派发在那里要在 `Pre (lim h)` 里无界地找槽位, 或者判定极限层号的字面相等. 不违反壁垒的出路它列了两条: 带燃料的字面搜索; 位置带来历 (受支配的域).
查签名用检索, 大文件不要整篇读.

#### 1 要交的, 分步; 每做成一步先交

1. **接口实填.** 若 `YiLamFold` 的折叠能填 `Uni` (含 `top-rowᶜ` 与 `top-up`), 给出实例. 若填不上 (例如观察取部分和与 `top-rowᶜ` 不定义性相等), 新建一个接口文件 `YiLamIf.lagda.md`, 写出只差这几行的姊妹记录 (原接口不改), 证明 `YiLamFold` 填满它, 并写出两份记录之间的关系 (哪条律在部分和的写法下不再需要, 用定理说). 读回域 `Dom` 也要填 (`bd-tw`, `bd-Λ`).
2. **极限目标在规范计算里被问到吗.** 编译的事实: 在 `TΛ` (或 `Tw n`) 的计算里, 有没有一次派发的目标层不是字面有限数 (照 `YiAboveLost.asked` 的写法: 那个结点的读回在闭项的读回之下, 且派发用的是 `dfin` 在非有限目标上的值). 有的话写出最早的一处.
3. **那里能有什么.** 编译的定理: 在读回域上, 在目标层是极限层号时派发对一切位置完全 (保留一切层号在目标之下的位置) 推出什么 (LPO, WLPO, 极限层号字面相等的弱判定, 或别的), 或者给出一种不要判定的完全派发. 再试带燃料的字面搜索: 写出它, 证它可靠 (保留的都在目标之下), 并用有限测试或定理说它在第 2 步找到的那一处是否保留. 每条否定写清: 定理里有没有折叠, 有没有值, 失败的是哪个字段; 是不是壁垒定理的实例; 每个前提给出可满足的实例; 反例对象在不在读回域内.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K (可交显式前提的条件定理); 堆到 6G 仍耗尽. 没有编译的否定定理时只能写 "未走通".

#### 2 过程要求

- 读完上面的文件后尽快动手: 第一个文件在 25 分钟内写出并编译.
- 每写完一个文件就编译; 每次回复都要有工具调用, 不要在一次回复里只思考.

#### 3 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiLamN` (接口文件可以叫 `YiLamIf`; 模块名 `OCF.Lean.YiLam…`). 尽量做成非验收文件 (只导入 `probes/OCF/Lean/` 的主线文件与标准库, 文首写 "非验收文件"); 要用参照的放单独的验收文件. 中文 literate Agda (`.lagda.md`). 不改任何已有文件 (包括 `YiLamFold`, `YiUniIf`), 不碰 `src/`, `archive/`.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 无关参数 `.( … )` 可以用. 函数外延只准作显式前提.
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 仓库文件里不写本机路径. 不要把仓库整个拷到临时目录.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽. 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块; 另一路也在编译.
- 非验收文件写完后跑 `python3 probes/Survey/scripts/importclosure.py <你的模块名…> --only OCF.Lean.YiLam --only OCF.Lean.YiNext --only OCF.Lean.YiUni` 查导入闭包.
- 你的临时目录: `<实验目录>/agents/lamn`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 4 回报格式 (只在回报里交一次)

1. 判决: 做到第几步; 一段话说对目标意味着什么 (设计对不对得上接口; 极限目标在规范计算里是否被问到; 那里能有什么, 不能有什么).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值, 是否验收文件, 导入闭包的检查结果.
3. 接口: 实例或姊妹记录的字段, 逐字; 与 `Uni` 的差.
4. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 否定定理附: 有没有折叠, 有没有值, 失败的字段, 前提的实例, 是否在读回域内.
5. 翻译账: 新加的东西哪些读自记号的规则, 哪些由树的要求逼出.
6. 第一个障碍与偏离事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 回报原文

#### 1 判决

三步都做完了。所有文件冷编译退出码 0，常驻内存峰值不超过 1.3G。

- **设计和接口对不对得上.** `YiLamFold` 填不了已定稿的 `Uni`，原因是它的 `top-rowᶜ` 第三个参数取部分和。用 `Lam` 自己的字段时，`Uni` 的 `top-rowᶜ` 在 `tw 2` 上不成立 (`no-plain-row`，编译定理)；换别的字段能否填上，是判断，我认为填不上。为此新建了姊妹记录 `Uniᴾ`：除 `top-rowᶜ` 的第三个参数改成 `psum` 并去掉 `top-up` 外，与 `Uni` 逐字相同。`YiLamFold` 填满了 `Uniᴾ`，各行和 `cpt-zero`、`cpt-suc` 都是 `refl`。读回域填到塔的一切项与 Λ (`domΛ`)，`TΛ` 正是接口的闭项形状 (`TΛ-uni`, `refl`)。
- **两份记录的关系 (定理).** 部分和写法下，链行合法不需要任何联系两个链点的律 (`rowᶜ-lglᴾ`, `chain-upᴾ`)。不写部分和时，各项合法推不出极限合法 (`plain-needs-mono`)，`Uni` 要 `top-up` 正是为了这一处。
- **极限目标在规范计算里被问到吗.** 被问到。`Tw 3` 里有一个 Ω 结点 `VJ`，层号 `lc J (up J)`，`J` 是 ℕ 极限层号，且 `finOf J ≡ nothing`。它的折叠 `NJ` 在 `Tw 3` 之下：结构上 `asked◁`，值上 `asked : NA.read NJ ≼ NA.read (Tw 3)`。`VJ` 的链第一步用 `dfin J (up J top)`，处处折叠。这一步第 0 个分量的根由位置 `r♯` 派发，`r♯` 层号为 1，派发结果是折叠；而 `J` 里有层号 1 的槽位 (`could`)。
  - 这是塔里最早的一处，这一点是判断。依据：`Tw 2` 各支没有 Ω 结点 (`noΩ₂`，编译)，根层号的链只用 `dfin zero`。
  - `Tw 3` 内部这一处是沿一条路径走到的，没有证明它在 `Tw 3` 里最早。
- **那里能有什么.**
  - 第 2 步那一处 (`J`) 可以有不做判定的完全派发。燃料取层号本身的字面搜索 `dlev` 在 `J` 上对一切位置完全 (`dlev-full-J`)，因为 `J` 的第 `i` 个分量字面上是 `fin (i+2)` (`F-fin`)；它也保留了 `r♯` (`keeps♯`，有限测试)。`Lam` 的 `stp` 在那里不完全 (`lam-not-full-J`)。
- **那里不能有什么.**
  - 读回域里取一个固定的极限目标就够：`tw 3` 的第 `suc a₀` 支，其链第一步的目标 `j₀`。任何对一切位置完全的派发，都对每个 α 判定字面相等 `T₀ ≡ Tα α` (`full→dec`；接口形式 `stp-full→decᴾ`)。
  - 再加函数外延 `FunextL` 作显式前提，就推出 WLPO (`full→wlpo`，条件定理)。
  - 对 N2 那一族支，`Lam` 版本的完全性推出 LPO (`lam-lpo`)。
  - `dlev` 只保留字面有限层号的位置 (`fin-only`)，所以从不判定极限层号的相等；它在 `j₀` 上不完全 (`dpol-not-full₀`)。
  - 这些否定的对象，是 "对一切位置完全" 这个谓词，不是路线。

#### 2 文件表

全部在 `probes/OCF/Lean/`。内存是 `/usr/bin/time -l` 测的峰值，每个文件都是删掉自己的 `.agdai` 后冷编译，日志里只有本模块的 `Checking` 行。

| 文件 | 代码行 | 冷编译 | 内存峰值 | 验收文件 | 导入闭包 |
|---|---|---|---|---|---|
| `YiLamIf.lagda.md` | 57 | 0 | 417MB | 否 | OK |
| `YiLamNInst.lagda.md` | 57 | 0 | 365MB | 否 | OK |
| `YiLamNRel.lagda.md` | 64 | 0 | 360MB | 否 | OK |
| `YiLamNAsk.lagda.md` | 83 | 0 | 397MB | 否 | OK |
| `YiLamNAskV.lagda.md` | 14 | 0 | 1226MB | 是 (导入 `OCF.Align.Value`, `YiNextAcc`) | 不查 |
| `YiLamNLim.lagda.md` | 92 | 0 | 396MB | 否 | OK |
| `YiLamNFuel.lagda.md` | 144 | 0 | 382MB | 否 | OK |

- 导入闭包：`importclosure.py <6 个非验收模块> --only OCF.Lean.YiLam --only OCF.Lean.YiNext --only OCF.Lean.YiUni`，每个模块禁用表命中 0，`--only` 之外 0。
- 禁用构造检索 (`postulate`, `TERMINATING`, `POSITIVITY`, `trustMe`, `irrelevant-projections`, 洞) 为 0。选项行都是 `--safe --without-K --lossy-unification`。

#### 3 接口

**`Uniᴾ` 与 `Uni` 的差.** 只有两处，其余字段逐字相同。

1. `top-rowᶜ` 改为：
```
top-rowᶜ : ∀ m {k g} (V : Bd (lc k g)) x → Ψ m V x G.top ≡
  ΩT m k (ωw m V x) (Kb m V x)
    (psum m (λ n → Ψ m (bC V (cpt V n) (cpt-lgl V n)) (obd m V x (cpt V n) (cpt-lgl V n)) G.top))
```
2. 去掉 `top-up`。

另有 `Domᴾ (U : Uniᴾ)`，字段为 `bd-tw : ∀ n → Bd (tw n)` 与 `bd-Λ : Bd Λ`。能力谓词 `CmpFullᴾ`、`StpFullᴾ` 照 `YiUniIf` §3 写。

**实例 `Lam` 的字段** (`YiLamNInst`)：
- `Bd = Lw`，`Ψ = Ψ`，`cmp = cmpw`
- `bS (ws V) = V`；`bL (wl V st) = V`；`bC (wΩ V w) = V`
- `ωw m {k} {g} (wΩ V w) x = rootW m k g w x`
- `Kb m {k} (wΩ V w) x = Kfk k (λ η → Ψ m (V (nrmk k η) (nrmk-lgl k η)) (λ r → x (nrmk k η , nrmk-lgl k η , r)) G.top)`
- `stp {k} {g} (wΩ V w) η l = dfin k (g η)`
- `obd m (wΩ V w) x η l r = x (η , l , r)`
- `cpt {k} {g} (wΩ V w) n = Pk.co (ptsΩ k g V n)`；`cpt-lgl` 取 `Pk.lw`
- 各行与 `cpt-zero`、`cpt-suc` 是 `refl`；`Kb-br` 用 `Kfk-br`

**读回域与闭项.** `domΛ = record { bd-tw = Lw-tw ; bd-Λ = VΛ }`；`TΛ-uni : TΛ ≡ Uniᴾ.Ψ Lam zero (Domᴾ.bd-Λ domΛ) (λ _ → fold) G.top`；`Tw-uni` 对一切 n 成立。

#### 4 定理表

除标明的以外，档位都是编译定理，无前提。

**YiLamNRel**

| 名字 | 陈述 | 白话 |
|---|---|---|
| `rowᶜ-lglᴾ` | `∀ m {k g} (V : Bd (lc k g)) x → Lgl m (ΩT m k (ωw m V x) (Kb m V x) (psum m (obsᴾ m V x)))`，在任意 `U : Uniᴾ` 下 | 链行合法只用 `Kb-br` 与各项的 `Ψ-lgl` |
| `chain-upᴾ` | `∀ m {k g} (V : Bd (lc k g)) x n → Cp m (psum m (obsᴾ m V x) n) (psum m (obsᴾ m V x) (suc n))` | 对一切序列，相邻部分和都在第一位置 (由 `plus-weak`) |
| `plain-needs-mono` | `Σ (ℕ → R) λ h → (∀ n → Lgl zero (h n)) × (Lgl zero (G.lim h) → ⊥)` | 序列 1, 0, 0, … 各项合法，极限不合法；它的部分和合法 (`spike-psum`) |
| `no-plain-row` | `L.Ψ zero (Lw-tw 2) (λ _ → fold) G.top ≡ ΩT zero zero (L.ωw zero (Lw-tw 2) (λ _ → fold)) (L.Kb zero (Lw-tw 2) (λ _ → fold)) obs₂ → ⊥` | 用 `Lam` 的字段，`Uni` 的链行在 `tw 2` 上不成立；用的是 `plus-ne` (最左深度) |

**YiLamNAsk** (`_◁_` 指沿 ℕ 极限的分量或第 0 层加法的右加数往下走)

| 名字 | 陈述 | 白话 |
|---|---|---|
| `asked◁` | `NJ ◁ Tw 3` | 那个结点的折叠在 `Tw 3` 之下 |
| `VJ` (类型检查) | `VJ : Lw (lc J (up J))`，其中 `J = up zero (plus zero G.top Y)`，`Y = succ zero G.top` | 路径是 `tw 3` 的链点 1，再沿分量 0, 1, 0, 1, 0 |
| `J-nonfin` | `finOf J ≡ nothing` | 目标层不是字面有限数 |
| `step-is-dfin`, `step-fold` | `stp VJ G.top tt ≡ dfin J (up J G.top)`；`∀ r → stp VJ G.top tt r ≡ fold` | 链第一步的派发是 `dfin`，处处折叠 |
| `NJ-form`, `pt1` | `NJ ≡ G.lim (psum zero (obsΩ VJ))`；`cpt VJ 1 ≡ plus J G.top (Ψ J (bC VJ G.top tt) (λ _ → fold) G.top)` | 链点 1 用的是全折叠的像 |
| `comp0` | `ωw J (bL (bC VJ G.top tt) 0) (λ r → stp VJ G.top tt (0 , r)) ≡ stp VJ G.top tt r♯` | 这一步第 0 个分量的根由 `r♯` 派发 |
| `lost`, `could` | `stp VJ G.top tt r♯ ≡ fold`；`At J (lev (upT J) r♯)`；`r♯-lev : … ≡ suc zero` | 有槽位却折叠了 |
| `noΩ₂` | `∀ η l → NoΩ (bC (Lw-tw 2) η l)` | `tw 2` 各支里没有 Ω 结点 |

**YiLamNAskV** (验收文件)

| 名字 | 陈述 | 白话 |
|---|---|---|
| `asked` | `NA.read NJ ≼ NA.read (Tw 3)` | 值的形式，由 `◁→≼` 得到 |

**YiLamNLim**

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `full→dec` | `(x : Ext j₀ (upT j₀)) → Full j₀ (upT j₀) x → ∀ α → Dec′ (Eqᴸ α)`，其中 `Eqᴸ α = T₀ ≡ Tα α` | 一个固定的极限目标上派发完全，就判定极限层号的字面相等 | 编译定理 |
| `stp-full→decᴾ` | `(U : Uniᴾ) (D : Domᴾ U) → StpFullᴾ U {k = j₀} {g = up j₀} (Uniᴾ.bC U (Domᴾ.bd-tw D 3) (G.suc a₀) l₀) (Uniᴾ.cpt U … 0) (Uniᴾ.cpt-lgl U … 0) → ∀ α → Dec′ (Eqᴸ α)` | 接口形式 | 编译定理 |
| `eq→false` | `∀ α → Eqᴸ α → ∀ n → α n ≡ false` | 字面相等推出 α 全假 | 编译定理 |
| `false→eq` | `FunextL → ∀ α → (∀ n → α n ≡ false) → Eqᴸ α` | 反方向要函数外延 | 条件定理 |
| `full→wlpo` | `FunextL → (x : Ext j₀ (upT j₀)) → Full j₀ (upT j₀) x → WLPO` | 加函数外延后推出 WLPO | 条件定理 |
| `lam-not-full₀` | `StpFullᴾ Lam V₀ G.top tt → ⊥` | `Lam` 在 `j₀` 上不完全 | 编译定理 |
| `lam-lpo` | `(∀ α → StpFullᴾ Lam {k = Tα α} {g = up (Tα α)} (bC (Lw-tw 3) (ηα α) (lim-lgl α)) G.top tt) → LPO` | N2 对 `Lam` 的形式 | 编译定理 |
| `lam-not-fullα` | α 取常值 true 时，同上的 `StpFullᴾ … → ⊥` | `Lam` 在 N2 那一族上不完全 | 编译定理 |

条件定理缺的前提是 `FunextL = ∀ {f g : ℕ → LF} → (∀ n → f n ≡ g n) → f ≡ g`。

否定定理的附注：
- **有没有折叠、值.** `full→dec` 都没有，只有一个派发和它的完全性。接口形式只多用了 `cpt-zero`。
- **失败的字段.** 第 `suc a₀` 支在第 0 个链点上的 `stp` 的完全性。
  - 失败的位置是 `rα α = (0 , suc (em 0 (em tt (lim (fα α)))) , lim-lgl α , inj₁ tt)`，层号 `Tα α`。
  - `j₀` 的槽位层号只有 `T₀` 与 `zero` (`slot→eq`)。
- **机制.** 判定两个极限层号的字面相等。旧块 `YiGenNegWall.chain→weak-eq` 是同一类机制，但那里含折叠的行，得到的是弱判定；这里不含折叠，得到的是完全判定，目标也是单一固定的。我没有把它归作旧墙的实例。
- **是不是壁垒定理的实例.** 不是，前提里没有带精确嵌入、顶元与有界三歧的下标类型。
- **前提的实例.** `x` 取 `Lam` 的 `stp`；接口形式取 `U = Lam`，`D = domΛ`。`FunextL` 在立方类型论里成立 (外部事实)。
- **在不在读回域内.** 那一支在读回域内 (`bd-tw 3`, 合法下标 `suc a₀`)，链点是规范的 `top`。但 `rα α` 不是 `Lam` 这一步会去问的位置 (判断：分量的根层号 `T₀` 是极限，`witU` 给 `none`，`Kb` 不求值，观察只问链点)。所以按 AGENTS，这条读作 "对一切位置要求完全，谓词太宽"；除非某个设计在这里保留，例如根保留后 `Kb` 对一切下标都要。

**YiLamNFuel** (`dpol φ` 是燃料取 `φ n` 的字面搜索派发，`dlev` 是 `φ n = n`)

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `sound` | `∀ φ k K r → IsKeep (dpol φ k K r) → At k (lev K r)` | 保留的都在目标之下 (由 `Way` 的类型直接得到) | 编译定理 |
| `fin-only` | `∀ φ k L → IsKeep (pol φ k L) → Σ ℕ λ n → fin n ≡ L` | 只保留字面有限层号的位置，从不判定极限相等 | 编译定理 |
| `keeps♯` | `IsKeep (dlev J (upT J) r♯)` | 第 2 步那一处保留 | 有限测试 |
| `dlev-full-J` | `∀ K → Full J K (dlev J K)` | 在 `J` 上对一切位置完全，用到 `F-fin : ∀ i → F i ≡ fin (suc (suc i))` | 编译定理 |
| `lam-not-full-J` | `StpFullᴾ Lam VJ G.top tt → ⊥` | `Lam` 在 `J` 上不完全 | 编译定理 |
| `dpol-not-full₀` | `∀ φ → Full j₀ (upT j₀) (dpol φ j₀ (upT j₀)) → ⊥` | 燃料搜索在 `j₀` 上不完全 (由 `full→dec` 看，这是必然的) | 编译定理 |

**判断 (没有编译)**
- 换别的字段，`YiLamFold` 的 `Ψ` 也填不上 `Uni`。
- `Tw 3` 是塔里第一个问到极限目标的项。
- `dfin` 只在 `cmpw` 的 `wΩ` 子句与 `ptsΩ` 里出现 (读代码)。
- 把 `ptsΩ` 与 `cmpw` 里的 `dfin` 换成 `dlev`，合法性保持，因为 `Ψ-lgl` 对一切派发成立；这要另开一个参数化的折叠文件，本路没有做。
- `YiLamFold` 是否满足 `top-up`，没有确定。

#### 5 翻译账

| 新东西 | 来源 |
|---|---|
| `Uniᴾ` 的 `psum` 观察 | 树的要求：链行合法而不需要单调律 (`plain-needs-mono`, `rowᶜ-lglᴾ`)。链的形状本身仍读自记号的基本列，本路没有新增 |
| 去掉 `top-up` | 部分和写法逼出 |
| `_◁_`, `◁→≼` | 验收工具，与记号无关 |
| `look`, `dpol`, `dlev` | 只读目标层号的字面结构 (有限数、ℕ 极限的前若干分量、Ω 结点的 `top` 支)，不用记号 |
| 燃料取层号本身 | 设计选择 (判断)，依据是规范目标 `J` 有字面模数 (`F-fin`) |
| 各条否定 | 不含记号 |

为翻译记号而新加的字段：没有。

#### 6 第一个障碍与偏离事故

**检查器方面.** 第一个报错是 `YiLamNLim` 的 `[NotInScope] Not in scope: Lw`，漏导入了 `Lw`，补上即通过。其余文件一次通过。
**数学上的障碍.** `YiLamFold` 的部分和观察与 `Uni` 的 `top-rowᶜ` 不定义性相等，所以新开了 `Uniᴾ`。

**偏离.**
1. 两份记录的关系定理放在 `YiLamNRel`，没有放进接口文件，使接口文件只含记录与谓词。
2. "最早" 只就塔的项号而言，而且是判断；`Tw 3` 内部是沿一条路径找到的。
3. 第 3 步的单目标否定，其位置不是规范计算会问的位置 (判断)，读法见 §4。
4. `dlev` 没有接进折叠，不在任务之内。
5. `YiLamIf` 首行原写 "只差两处"，已改为 "除下面两处外逐字相同"，改后全部冷编译。

**事故：没有.**
- 只用字面精确路径删过自己 7 个模块的 `.agdai`，没有用 `--ignore-interfaces`。
- 没有改已有文件，没有碰 `src/`、`archive/` 或 `/tmp` 的别处，没有提交。
- 日志在 `<实验目录>/agents/lamn/`。
