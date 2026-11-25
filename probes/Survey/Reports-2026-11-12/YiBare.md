# 实验甲：保留脚手架是否承重 (YiBare)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-12 06:57 至 07:39 |
| 工具调用 / agda 编译 (粗数) | 81 / 21 |
| token (usage 字段，按消息去重) | 输出 167176；新写入缓存的输入 347484；读缓存的输入 16583851；其余输入 156 |
| 写过的仓库文件 | `YiBareBounds.lagda.md`, `YiBareFold.lagda.md` |
| 文件前缀 | `YiBare` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-12: 实验甲返回并复核; 第七批合读 (主审)” 一节 |
| 主审复核后的一句结论 | 合法性与 ψ₀(Ω_Ω+Ω₁·ω) 及以下的值不依赖那 68 行；ψ₀(Ω_Ω+Ω₁²) 起用到第 1 层的保留与 witU zero；八件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 作者的方针: "边重构边做, 只动值的前沿碰到的那块"; 你这一路是重构前的 **实验甲: 测 "保留的脚手架" 是否承重**. 主审会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 背景 (事实)

- 树的语言评估 (`probes/Survey/TreeLanguage-2026-11-12.md`, 全读; 台账 `probes/Survey/IdeaLedger.md` §7 的 R1) 把读法 ψ₀(Λ) 的闭项前三层 568 行里的 68 行归为 "纯为保留": 根见证 (`Wit`, `rootW`, `selfU`, `sxU`, `witU`, `witT`) 与有限层号的字面判等 (`fin`, `eqFin`, `slotFin`, `finOf`, `dfin₀`, `dfin`). 评估者判断合法性不需要它们 (`Ψ-lgl` 对一切派发成立), 建议实验甲: 派发一律折叠, 公共上界数据的见证全取 `none`, 看现有值定理哪些还成立.
- 对派发参数化的折叠: `probes/OCF/Lean/YiDlFold.lagda.md` (`module Fold (D : ∀ k K → Ext k K)`); 公共上界数据与它的构造在 `YiLamFold.lagda.md` (`Lw`, `wΩ`, `Wit`, `Lw-Ω̂`, `lgl→Lw`, `Lw-tw`, `VΛ`). 只求合法的最便宜版本的先例: 第八次审查的 `R8Lam` (台账 U19; 只有转述).
- 现有值定理 (回归集, 都无前提): `YiDlVBtbo.btbo-TΛ` (BTBO 是下界), `YiDlVOne` 的 `χ₁≼ʷ`, `YiShpOne` 的 `X₁₂≼ʷ`, `YiShpOmega` 的 `Xω≼ʷ`, `YiShpSq` 的 `X²≼ʷ`, `YiShpEps` 的 `Xε≼ʷ`, `YiL1Base` 的 `base₁`, `Xψ₁≼ʷ`, `YiIntoTw3` 的 `T⁺ʷ≼TΛ`, `YiL1Lam` 的 `Xψ₁≼TΛ`.

#### 要交的, 分步; 每做成一步先交

1. **裸折叠** (非验收文件): 用 `YiDlFold.Fold` 取派发一律折叠 (或在一个新文件里取), 公共上界数据取见证全为 `none` 的版本 (另写 `Lw-tw` 与 `VΛ` 的一份, 或一个把见证置为 `none` 的函数), 闭项 `TΛᵇ`, `Twᵇ n`, `T⁺ʷᵇ` 合法 (由 `Ψ-lgl` 给出). 给出它的同口径切片行数 (用主审的脚本 `<实验目录>/verify/slice_roots.py`, 要 `agda --html` 的输出目录, 只在你的临时目录里生成), 与 568 行对比.
2. **回归** (验收文件): 把回归集里的定理逐个搬到裸折叠上 (照 `YiDl` 一路把 `YiLamV*` 搬到 `YiDlFold` 的做法: 换前缀与派发, 逐字搬). 对每条定理给出结果: 编得过 (交定理), 或编不过 (给出第一处失败: 哪个引理, 哪一行用到了被去掉的见证或判等, 检查器报错原文).
3. **结论**: 列一张表: 每条定理是否依赖这 68 行; 依赖的话依赖哪一部分 (见证还是判等). 由此说明这 68 行换来的是哪一档值 (判断, 依据表).

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K; 堆到 6G 仍耗尽. 搬某条定理超过约 150 行新代码还没过, 就记为 "未搬过" 并给出原因, 接着搬下一条.

#### 先读什么

`AGENTS.md` (Agda 一节, 文字预算, 结论的写法); `probes/Survey/EBOHandbook.md` §4.1 到 §4.5; `TreeLanguage-2026-11-12.md`; `YiDlFold.lagda.md`, `YiLamFold.lagda.md`; 回归集各文件只检索要搬的定理与它们的依赖. 查签名用检索.

#### 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiBare` (模块名 `OCF.Lean.YiBare…`). 裸折叠是非验收文件 (只导入 `probes/OCF/Lean/` 的主线文件与标准库); 回归放验收文件. 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞 (写入文件时也不要留洞), `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`, 函数外延.
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 仓库文件里不写本机路径. 不要把仓库整个拷到临时目录.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽. 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块; 另有两路也在编译.
- 你的临时目录: `<实验目录>/agents/bare`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 过程要求: 读完上面的文件后尽快动手, 第一个文件在 20 分钟内写出并编译; 每次回复都要有工具调用, 不要在一次回复里只思考.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0; 对非验收文件跑 `python3 probes/Survey/scripts/importclosure.py <模块名…> --only OCF.Lean.`.

#### 回报格式 (只在回报里交一次)

1. 判决: 一段话说这 68 行是否承重, 换来的是哪一档值.
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值, 是否验收文件, 导入闭包结果; 裸折叠的切片行数.
3. 回归表: 定理, 在裸折叠上编得过 / 编不过, 失败的第一处 (引理, 用到的被去掉的东西, 报错原文).
4. 定理表: 新交的定理, 逐字的陈述, 档.
5. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 回报原文

#### 实验甲 (裸折叠) 回报

##### 1. 判决

68 行在合法性上不承重; 在 ψ₀(Ω_Ω+Ω₁·ω) 及以下的值上也不承重, 这一段都有编译过的定理为据。它们现在换来的, 是三条更高的已证界: X² (ψ₀(Ω_Ω+Ω₁²)), Xε (ψ₀(Ω_Ω+ε_{Ω₁+1})), Xψ₁ (ψ₀(Ω_Ω+ψ₁(Ω_Ω))), 以及这三条搬到 TΛ 上的版本。这三条的证明都要用到两样东西: 目标层 1 在层号 0 槽位上的派发保留 (判等一侧; `dl` 本身就是 `fin`/`eqFin`/`finOf` 加燃料搜索), 以及 Ω_Ω 的根见证 `witU zero`。

具体如下 (编译定理):
- **逐字编过**: `btbo-TΛ`, `T⁺ʷ≼TΛ`。
- **逐字编不过, 改写后编过**: `χ₁≼ʷ`, `X₁₂≼ʷ`, `Xω≼ʷ`, 每个文件改动不超过 21 行代码。逐字的证明用了根见证, 但裸折叠的链从 `P 0 = top` 起步, 部分和的第 0 项给出同一个 Ω₁ 结点 `G.lc p₀ gm₀`。
- **三条高界在裸折叠上没有重证**: 状态是 "未搬过", 不是否定。

另一个事实: 见证为 `none` 时, `ΩT` 的结点分支族不进值 (编译定理 `top-none`, 是 `refl`)。所以 (b1) 的 61 行 (`Kfk`, `nrmk` 一族) 在裸折叠的值里也不出现, 只是因为类型和合法性还留在切片里。

##### 2. 文件表

全部冷编译: 先删掉自己的接口, 按依赖次序逐个编; 每个日志只有自己模块的 `Checking` 行; 禁用构造 0, 本机路径 0。

| 文件 | 总行 / 代码行 | 退出码 | 常驻内存峰值 | 验收文件 |
|---|---|---|---|---|
| YiBareFold | 88 / 52 | 0 | 0.36G | 否 |
| YiBareVRel | 132 / 104 | 0 | 1.27G | 是 |
| YiBareVBtbo | 124 / 83 | 0 | 1.67G | 是 |
| YiBareVOne | 163 / 112 | 0 | 1.57G | 是 |
| YiBareShpOne | 111 / 71 | 0 | 1.62G | 是 |
| YiBareShpOmega | 164 / 116 | 0 | 1.56G | 是 |
| YiBareIntoTw3 | 97 / 63 | 0 | 1.56G | 是 |
| YiBareBounds | 51 / 27 | 0 | 1.56G | 是 |

文件都在 `<仓库>/probes/OCF/Lean/` 下。

- **导入闭包**: 非验收文件 YiBareFold 跑 `importclosure.py OCF.Lean.YiBareFold --only OCF.Lean.`, 结果 OK: 本地 18 个模块, 禁用表命中 0, `--only` 之外 0。
- **切片行数** (`slice_roots.py`, 根取 `TΛᵇ, TΛᵇ-legal`):

| 闭项 | 切片行数 |
|---|---|
| 基线 `YiLamFold:TΛ` | 568 (复现) |
| 回归对象 `YiDlFold:TΛ` | 595 |
| 裸折叠, 原脚本 | 566 |
| 裸折叠, 去掉一条边 | 510 |

- **566 与 510 的差**: 原脚本把 YiDlFold 根上的 `open Fold dl public` 挂到 `Fold` 的每个块上, 于是 `dl`, YiLamNFuel 的 35 行, `fin`/`eqFin`/`finOf` 被算进去, 共 56 行。我在临时目录写了只去掉这条边的变体, 同口径得到 510。
- **相对 568, 净省 58 行**: 去掉 62 行, 即 68 行减去仍在切片里的 `Wit` 3 行与 `rootW` 3 行 (`Lw` 的类型和 `wΩ` 的 top 子句点名它们); 新增 4 行 (`Dᵇ` 2 行, `open` 1 行, `module Fold` 1 行)。
- **相对 595, 净省 85 行**。

##### 3. 回归表

"逐字" 指换前缀与派发后照搬; 失败项在临时目录的纯 `.agda` 副本里逐个删去, 再找下一处。行号是原文件的。

| 定理 | 逐字搬运 | 第一处失败 (引理, 原文行, 用到的被去掉的东西, 报错原文) | 改写后 |
|---|---|---|---|
| `btbo-TΛ` | 编过 | — | — |
| `χ₁≼ʷ` (YiDlVOne) | 编不过 | 见下 (1) | 编过 |
| `X₁₂≼ʷ` | 编不过 | `term₂` (59–60 行) 的 `refl`: `G.lim … != G.lc p₀ Bᵗ`。用到: 根见证 | 编过 |
| `Xω≼ʷ` | 编不过 | `chain-eq` (171–173 行) 的 `refl`: `G.lim …`。用到: 根见证 | 编过 |
| `X²≼ʷ` | 编不过 | 见下 (2) | 未搬过 |
| `Xε≼ʷ` | 编不过 | 见下 (3) | 未搬过 |
| `base₁` | 编不过 | 见下 (4) | 未搬过 |
| `Xψ₁≼ʷ` | 编不过 | 经 `node≼T` 与 `base₁` | 未搬过 |
| `T⁺ʷ≼TΛ` | 编过 | 只删旁注 `keep₅` (83–84 行, `W.dl` 不在作用域, 原文里没被用到); 同一条 `path₃` 仍到达 `T⁺ʷᵇ`, `at-T⁺ʷ` 是 `refl` | — |
| `Xψ₁≼TΛ` | 编不过 | 经 `Xψ₁≼ʷ` | 未搬过 |

(1) `χ₁≼ʷ` 的失败:
- 文件次序里第一处是 `c₁` (81–82 行; `aboveʷ`, `ΩΩ+1ʷ` 用它), 报错 `_A_77 ⊎ _B_78 !=< Σ ℕ (λ n → Cp (tw 2) (G.suc G.top) (add (tw 2) G.lc G.top (psum (tw 2) …)))`。
- `χ₁` 自己这条链: `term₁` (112–113 行) 报 `G.lim (λ n → add (tw 2) G.lc G.top (psum …)) != G.lc p₀ gK`; `χ₁≼ʷ` (171 行) 报 `WL.Kfk zero Tt (iter (λ η → plus zero η (gk₁ η)) G.top m) != acc (…)`。
- 用到的被去掉的东西: 根见证 `witU zero = at (inj₁ tt) refl`。它经 `rootW` 让 `Φ₂ = W.Ψ (tw 2) V2 (self (tw 2))` 在根 `p₀` 保留。

(2) `X²≼ʷ` 的失败:
- `dl-keep` (92–93 行): `fold != keep (inj₁ tt) refl of type Way (lev (tw 2) s₂) (lev (tw 2) s₀″)`。属于判等。
- 随后 `γ₁-form`, `G₂γ₁` (`G.lim …`), 原因同上。
- `N₂≼T` (220–223 行): `WL.Kfk zero Tt … !=`。属于见证: 根链第 1 点不再含 Ω₂ 结点 `Tt (suc top)`。
- `node≼T`, `X²≼ʷ` 随之失败。
- `X²≼node` (关于结点 `G.lc s₀″ Bq`) 仍编得过。

(3) `Xε≼ʷ` 的失败:
- `ψ₁-top` (173–174 行): `G.lim … != G.lc (inj₁ tt) K₁`。目标层 1 的根保留, 见证与判等两样都要。
- `module E = Lv1 (λ r → W.cmpw V2 s₂ …) refl` (186 行): `fold != (keep (inj₁ tt) refl)`。属于判等。
- `γ1⊴`, `Eε⊴`, `Xε≼Bq` 随之失败; `Xε≼ʷ` 经 `node≼T` 失败。

(4) `base₁` 的失败:
- YiL1Read 的 `R₁` (85–87 行): `OCF.Lean.YiLamNFuel.byFin (λ n → n) (suc zero) (lev (up zero a) r) (finOf (lev (up zero a) r)) != fold of type Way (suc zero) (lev ⌜ a ⌝ r)`。属于判等。
- YiL1Stmt 的 `node-form` (45–47 行, `acc …`) 与 `point→base` (59–61 行): `OCF.Lean.YiLamFold.Kfk zero ShpEpsV.Tψ … != acc …`。用到 `ψ₁ top` 的结点形状。
- YiShpTwo 的 `dl-p₀`, `ψ₁-top`, `γ₂-1`, `X₂′≼ᶜ` 失败。
- YiL1Emb 的 `lower₁ᴱ`, `base₁-0` 随之失败。
- YiL1Chain 与 YiL1NrmEmb 逐字编过。

##### 4. 定理表

档位全是: 编译定理, 无前提, 序数值下界 (单向 `≼`)。

| 文件 | 定理 (逐字陈述) |
|---|---|
| YiBareFold | `TΛᵇ-legal : Lgl zero TΛᵇ`; `Twᵇ-legal : ∀ n → Lgl zero (Twᵇ n)`; `T⁺ʷᵇ-legal : Lgl zero T⁺ʷᵇ`; `TΛᵇ-form : TΛᵇ ≡ G.lim (psum zero Twᵇ)`; `top-none : ∀ m {k} {g : Raw k → LF} (V : ∀ η → Lgl k η → Lw (g η)) (x : Ext m (lc k g)) → Ψ m (wΩ V none) x G.top ≡ G.lim (psum m (λ n → Ψ m (V (co (ptsΩ k g V n)) (lw (ptsΩ k g V n))) (λ r → x (co (ptsΩ k g V n) , lw (ptsΩ k g V n) , r)) G.top))` |
| YiBareVBtbo | `btbo-Tw2 : D.BTBOᴵ ≼ NA.read (W.Twᵇ 2)`; `btbo-Tw3`; `btbo-TΛ : D.BTBOᴵ ≼ NA.read W.TΛᵇ` |
| YiBareVOne | `aboveʷ : L.suc D.BTBOᴵ ≼ NA.read W.T⁺ʷᵇ`; `ΩΩ+1ʷ : L.ψ⁰ (L.suc (L.Ω S2.ℓ₀)) ≼ NA.read W.T⁺ʷᵇ`; `χ₁≼ʷ : S2.χ 1 ≼ NA.read W.T⁺ʷᵇ`; `aboveΛ : L.suc D.BTBOᴵ ≼ NA.read W.TΛᵇ` |
| YiBareShpOne | `X₁₂≼ʷ : X₁₂ ≼ NA.read W.T⁺ʷᵇ` |
| YiBareShpOmega | `Ω₁n≼ : ∀ n → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA (P (suc n))) ≼ NA.read (Ψ₀ (chain (tw 2) Φ₂ (suc n)))`; `Xω≼ʷ : Xω ≼ NA.read W.T⁺ʷᵇ` |
| YiBareIntoTw3 | `T⁺ʷ≼Tw3 : NA.read W.T⁺ʷᵇ ≼ NA.read (W.Twᵇ 3)`; `T⁺ʷ≼TΛ : NA.read W.T⁺ʷᵇ ≼ NA.read W.TΛᵇ` |
| YiBareBounds | `ΩΩ+1≼TΛ`, `χ₁≼TΛ`, `X₁₂≼TΛ`, `Xω≼TΛ : Xω ≼ NA.read W.TΛᵇ` (另有四条到 `W.Twᵇ 3`) |

读法:
- `S2.χ 1` 读作 ψ₀(Ω_Ω+Ω₁), `X₁₂` 读作 ψ₀(Ω_Ω+Ω₁·2): 原文有标签验收。
- `Xω` 读作 ψ₀(Ω_Ω+Ω₁·ω): 这是判断。

有限测试 (临时目录): `dl (suc zero) (tw 2) s₀″`, `dfin (suc zero) (tw 2) s₀″`, 以及两者在 `p₀` 上, 都等于 `keep (inj₁ tt) refl`, 退出 0。这说明回归集用到的派发保留, 68 行里的 `dfin` 也给得出。

##### 依赖表 (由回归表得出; 归类是判断)

| 定理 | 依赖 68 行的部分 |
|---|---|
| `btbo-TΛ`, `T⁺ʷ≼TΛ` | 不依赖 |
| `χ₁`, `X₁₂`, `Xω` | 只有逐字证明依赖见证 (`witU zero`); 值不依赖 |
| `X²`, `Xε`, `base₁`, `Xψ₁` 及其搬到 TΛ 的版本 | 判等 (目标层 1, 槽位层号 0) 与见证都用到; 裸折叠上未定 |

逐字证明里用到的见证只有 `witU zero` 一处。`selfU`, `sxU`, `witT` 没有在任何失败里出现, `T⁺ʷ≼Tw3` 不用它们也编过。

**判断, 未编译**: X² 在裸折叠上可能仍然成立。要用的是一条比较引理: "目标层 1 的全折叠, 不低于 Ω₁ 乘以目标层 0 的全折叠"; 再加上 `fold1` 对裸折叠里那个 Ω₂ 结点的改写。估计超过 150 行, 所以没有尝试。

##### 5. 偏离与事故

- 搬运不是全逐字:
  - YiBareVOne 的 §3 改写了。`gK`, `sucK`, `ctx`, `topStep`, `d`, `ch≼` 用的是原名, 定义不同 (作用相同)。
  - YiBareShpOne 的 §2 改写了。
  - YiBareShpOmega 的记录 `Fam` 改了: `top` 字段由结点形状 (`H`, `topEq`, `HM`, `HS`) 换成一条 `topC : Cp …`; `Fam-step` 多带前缀 `c` 与 `Cp (G.lc p₀ B) c`。
  - 删去用不到的辅助项: `c₃d`, `gk₃`, `e₁`, `c₃a`, `c₃c`, `Btop`, `hB`, `gk₅`, `e₅`, `c₅a`, `topH`, `topF`, `nxt`, `chain-eq`。
  - 文件头都说明了这些改动。
- 我的搬运脚本两次把临时副本写进了 `probes/OCF/Lean/`, 文件名是 `YiBareVOneVerb_tmp`, `YiBareShpOneVerb_tmp` (带 YiBare 前缀); 随即移到临时目录, 仓库里现在只有上表 8 个文件。
- 有一次切片用了过时的 HTML (源文件刚加了 `top-none`), 得到 495, 已作废; 重新生成 HTML 后复现 510。
- 有一个后台任务 (逐字链的删除循环) 超过 120 秒转入后台, 对结果没有影响。
- 只删过自己的 7 个接口 (第 8 个当时还不存在); 没有用 `--ignore-interfaces`; 没有提交。
- 临时目录里留着逐字失败的副本和脚本: `<实验目录>/agents/bare/v/` 下的 `*V.agda` 与日志, 以及 `slice_noopen.py`, `slice_diff.py`, `dropiter.sh`。
