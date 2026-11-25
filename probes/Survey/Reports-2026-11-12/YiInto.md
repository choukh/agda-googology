# 读法 ψ₀(Ω_{Ω+1}) 的闭项不高于 TΛ (YiInto)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-12 04:18 至 04:32 |
| 工具调用 / agda 编译 (粗数) | 35 / 6 |
| token (usage 字段，按消息去重) | 输出 80133；新写入缓存的输入 187995；读缓存的输入 3487298；其余输入 56 |
| 写过的仓库文件 | `YiIntoBounds.lagda.md`, `YiIntoTw3.lagda.md` |
| 文件前缀 | `YiInto` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-12: T⁺ʷ ≼ TΛ 一路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | T⁺ʷ≼TΛ 无前提；六条下界搬到 TΛ 上；两件冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 作者的指示是 "朝着最终目标的关键路径走"; 作者这一批选了 **"读法 ψ₀(Ω_{Ω+1}) 的闭项不高于 TΛ"**: 把已证的界搬到 `TΛ` 上; 或者直接在塔的第 3 项的子项上证. 主审会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 背景 (事实)

- 一致折叠 `probes/OCF/Lean/YiDlFold.lagda.md` (实例取燃料搜索 `dl`) 的闭项: `TΛ` (读法 ψ₀(Λ); 定义性地是塔各项闭项 `Tw n` 的部分和的极限), `T⁺ʷ` (读法 ψ₀(Ω_{Ω+1}), 折的是层号 `suc (tw 2)` 的顶), `Tw n` (第 `tw n` 层的顶; `Tw 2` 读法为 BTBO, `Tw 3` 读法 ψ₀(Ω_{Ω_Ω})).
- 已证 (编译定理): `TΛ` 不低于 BTBO 并严格高过一步 (`YiDlVBtbo.btbo-TΛ`, `YiDlVOne.aboveΛ`); `Tw n ≼ TΛ` (`Tw≼TΛ` 一类); `T⁺ʷ` 不低于 ψ₀(Ω_Ω+ε_{Ω₁+1}) 的参照 (`YiShpEps.Xε≼ʷ`, 以及 `YiShpOne`, `YiShpOmega`, `YiShpSq` 的几站). **`T⁺ʷ ≼ TΛ` 没有证**, 所以这些界还不是 `TΛ` 的界.
- 第九次审查的判断 (`probes/Survey/RR9-OmegaOmega2.md` §3 的 (d1)): 这条要 Ω 结点层号上的层号嵌入下折叠单调, 而 `dl` 对嵌入不单调 (嵌入可能把有限层号映到无穷层号, 保留就丢了); 另一条路是直接在 `Tw 3` 的子项上证: `Tw 3` 的结构里, 层号 `suc (tw 2)` 字面出现在一个更大的 Ω 结点层号的分支里 (判断, 未编译).

#### 要交的, 分步; 每做成一步先交

1. **找位置**: 编译出 `Tw 3` (或 `TΛ`) 的计算里, 有一个子项的读回不低于 `NA.read W.T⁺ʷ` 所用的那棵折叠, 或者与它互模拟 (照 `YiNextValFin.T₃≅`, `YiDlVBtbo.obs≅` 的转运办法). 写清那个子项在哪里 (路径), 用的是哪一层的折叠, 派发在那里是什么.
2. **定理**: `NA.read W.T⁺ʷ ≼ NA.read W.TΛ` (或 `≼ NA.read (W.Tw 3)`), 无前提. 若只能对 `T⁺ʷ` 的某个链点或某一段做到, 交那一段, 并把已证的界 (`Xε≼ʷ` 等) 中能搬的那些搬到 `TΛ` 上.
3. **做不过去时**: 给出确切的缺口: 两边折叠在哪一处不同 (派发保留与折叠的差别, 或层号嵌入的问题), 缺的引理的 Agda 类型; 有编译的反例 (例如 `Tw 3` 里对应的那一处派发折叠而 `T⁺ʷ` 里保留) 就交.

只要下界 (作者 2026-11-11 的原则).

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K; 堆到 6G 仍耗尽 (先按手册 §4.2). 没有编译的否定时只写 "未走通".

#### 先读什么

`AGENTS.md` 全篇 (特别是 Agda 一节, 文字预算, 结论的写法); `probes/Survey/EBOHandbook.md` §4.1 到 §4.5 与 §5.4. 折叠: `YiDlFold.lagda.md`, `YiLamFold.lagda.md` (只检索 `Lw`, `Lw-Ω̂`, `lgl→Lw`, `Kfk`, `nrmk`, `witU`); 块 `YiNextCore.lagda.md` (`upT`, `tw`, `Λ`); 读回 `YiNextAcc.lagda.md` (`read`, `plus≽`, `_⊴_` 一节); 转运先例 `YiNextValFin.lagda.md`, `YiDlVRel.lagda.md`, `YiDlVBtbo.lagda.md`; `YiShpEps.lagda.md` 的 `Lv1` 与 `fold1` (第 1 层的读回关系). 查签名用检索, 大文件不要整篇读.

#### 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiInto` (模块名 `OCF.Lean.YiInto…`). 都是验收文件, 文首标 "验收文件". 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提.
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 堆墙多出在比较具体闭项的地方: 陈述逐字写, 不用别名; 经非单射的头求解的隐式参数显式写出 (手册第 4 节).
- 仓库文件里不写本机路径. 不要把仓库整个拷到临时目录.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽. 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块; 另有两路也在编译.
- 你的临时目录: `<实验目录>/agents/into`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 过程要求: 读完上面的文件后尽快动手, 第一个文件在 20 分钟内写出并编译; 每次回复都要有工具调用, 不要在一次回复里只思考.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 回报格式 (只在回报里交一次)

1. 判决: 做到第几步; 一段话说对目标意味着什么 (`T⁺ʷ ≼ TΛ` 成立没有; 哪些界搬到了 `TΛ` 上; `TΛ` 已证的最高下界).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断).
4. 办法.
5. 第一个障碍: 精确到引理与位置, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 回报原文

#### 1 判决

我做完了第 2 步，第 3 步没有用上。`T⁺ʷ ≼ TΛ` 现在是编译定理，没有前提。

对目标意味着什么：读法 ψ₀(Ω_{Ω+1}) 的闭项 `T⁺ʷ` 原样出现在塔的第 3 项 `Tw 3` 的计算里。这里的"原样"指定义相等，`at-T⁺ʷ` 用 `refl` 证明。到那里的路是沿折叠的观察项往下走九步。所以不需要第九次审查 (d1) 说的那条引理：Ω 结点层号上的层号嵌入下折叠单调。燃料搜索派发 `dl` 对嵌入是否单调，这条证明不碰。

搬到 `TΛ` 上的界：`T⁺ʷ` 已证的六条下界全部搬过去了，同时也搬到了 `Tw 3` 上。
- `TΛ` 已证的下界里，按读法最高的是 `Xε≼TΛ`。参照 `Xε` 读作 ψ₀(Ω_Ω+ε_{Ω₁+1})，这个读法是判断，不是定理。
- 带逐项一致证明的参照里最高的是 `X₁₂≼TΛ`，即 ψ₀(Ω_Ω+Ω₁·2)，依据 `YiShpOneLab.X₁₂-label`。
- 此前 `TΛ` 的最高下界是 `aboveΛ : L.suc D.BTBOᴵ ≼ NA.read W.TΛ`。
- 这些都只是下界，没有上界，也没有同值。

#### 2 文件表

| 文件 | 代码行 (代码块内非空行) / 全文行 | 冷编译退出码 | 常驻内存峰值 | 用时 |
|---|---|---|---|---|
| `probes/OCF/Lean/YiIntoTw3.lagda.md` | 65 / 101 | 0 | 1.70 GB | 9.2 s |
| `probes/OCF/Lean/YiIntoBounds.lagda.md` | 37 / 65 | 0 | 1.61 GB | 9.4 s |

冷编译前我只删了这两个模块自己的 `.agdai`，路径写的是字面全路径。两份日志里都只有本模块的 `Checking` 行。检索 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、`--cubical`、`--irrelevant-projections`、`Funext`，结果为 0。选项行是 `--safe --without-K --lossy-unification`。两个文件文首都标了"验收文件"，文件里不含本机路径。

#### 3 定理表

除特别说明，以下都在 `YiIntoTw3`，档位都是编译定理。

| 名字 | 逐字陈述 | 白话 |
|---|---|---|
| `T⁺ʷ≼Tw3` | `NA.read W.T⁺ʷ ≼ NA.read (W.Tw 3)` | `T⁺ʷ` 不高于塔的第 3 项 |
| `T⁺ʷ≼TΛ` | `NA.read W.T⁺ʷ ≼ NA.read W.TΛ` | `T⁺ʷ` 不高于 `TΛ` |
| `at-T⁺ʷ` | `W.Ψ zero (lw′ (desc path₃ (st (tw 3) (Lw-tw 3) (λ _ → fold)))) (dx (desc path₃ (st (tw 3) (Lw-tw 3) (λ _ → fold)))) G.top ≡ W.T⁺ʷ` | 下降终点就是 `T⁺ʷ`，证明是 `refl` |
| `ly-T⁺ʷ` | `ly (desc path₃ (st (tw 3) (Lw-tw 3) (λ _ → fold))) ≡ suc (tw 2)` | 终点的层号是 `suc (tw 2)` |
| `ly-fin2` | `ly (desc (1 ∷ 0 ∷ 0 ∷ 0 ∷ []) (st (tw 3) (Lw-tw 3) (λ _ → fold))) ≡ upT (suc (suc zero))` | 第 4 步后到层号 `upT (fin 2)` |
| `keep₅` | `W.dl (suc zero) (tw 2) (G.top , tt , inj₁ tt) ≡ keep (inj₁ tt) refl` | 第 5 步链点用到的派发在根位置保留 |
| `ly-top2` | `ly (desc (1 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ []) (st (tw 3) (Lw-tw 3) (λ _ → fold))) ≡ up (suc zero) (plus (suc zero) G.top G.top)` | 第 8 步后到层号 `up 1 (top + top)`，它的 `top` 支是 `suc (tw 2)` |
| `desc≼` | `∀ ns s {ℓ} {X : L.Ordᶜ ℓ} → X ≼ NA.read (W.Ψ zero (lw′ (desc ns s)) (dx (desc ns s)) G.top) → X ≼ NA.read (W.Ψ zero (lw′ s) (dx s) G.top)` | 沿任意路径下降，目标层 0 的读回不升 |
| `child≼` | `∀ {k} (V : Lw k) x n {ℓ} {X : L.Ordᶜ ℓ} → X ≼ NA.read (W.Ψ zero (lw′ (child V x n)) (dx (child V x n)) G.top) → X ≼ NA.read (W.Ψ zero V x G.top)` | 下降一步，读回不升 |
| `ΩΩ+1≼TΛ` (Bounds) | `L.ψ⁰ (L.suc (L.Ω S2.ℓ₀)) ≼ NA.read W.TΛ` | ψ₀(Ω_Ω+1)，参照由 `S2.ts-label` 验收 |
| `χ₁≼TΛ` (Bounds) | `S2.χ 1 ≼ NA.read W.TΛ` | ψ₀(Ω_Ω+Ω₁)，参照由 `S2.χ1-label` 验收 |
| `X₁₂≼TΛ` (Bounds) | `X₁₂ ≼ NA.read W.TΛ` | ψ₀(Ω_Ω+Ω₁·2)，参照由 `X₁₂-label` 验收 |
| `Xω≼TΛ` (Bounds) | `Xω ≼ NA.read W.TΛ` | 读作 ψ₀(Ω_Ω+Ω₁·ω)，读法是判断 |
| `X²≼TΛ` (Bounds) | `X² ≼ NA.read W.TΛ` | 读作 ψ₀(Ω_Ω+Ω₁²)，读法是判断 |
| `Xε≼TΛ` (Bounds) | `Xε ≼ NA.read W.TΛ` | 读作 ψ₀(Ω_Ω+ε_{Ω₁+1})，读法是判断 |
| `ΩΩ+1≼Tw3` … `Xε≼Tw3` (Bounds) | 同上六条，右边换成 `NA.read (W.Tw 3)` | 同样的界落在 `Tw 3` 上 |

#### 4 办法

1. **一步下降 `child`。** 它作用在公共上界 `Lw` 上（"公共上界"指折叠沿它走的层号结构）。
   - 遇到 Ω 结点层号 `wΩ V w`，取第 `n` 个链点 `W.ptsΩ k g V n` 那一支，即 `V (co …) (lw …)`，派发取 `λ r → x (co … , lw … , r)`。
   - 遇到 ℕ 极限层号 `wl V s`，取第 `n` 个分量。
   - `w0` 和 `ws` 不动。
2. **`child≼` 的证明。** 目标层 0 上 `Way zero j` 只有 `fold`，因为 `Pre zero = ⊥`。所以按 `rootW` 的值分情形 (`ΩT₀`)，`ΩT` 就是链的部分和的极限，再用 `YiDlVBtbo.psum≽` 与 `≼l` 收尾。
3. **迭代。** `desc` 和 `desc≼` 沿一个 `List ℕ` 迭代下降。
4. **主定理。** 主定理是 `desc≼ path₃ … (≼-refl (NA.read W.T⁺ʷ))`。检查器自己算出下降的终点，并判定它与 `T⁺ʷ` 定义相等。两边的公共上界只在第 0、1 层的 `T.Legal` 证明上不同，那里是 `⊤`，按 η 相等。所以不需要转运，也不需要互模拟。

**位置 (第 1 步)。** `path₃ = 1 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []`，从 `Tw 3` 出发：
- 第 1 步：`Tw 3` 的第 1 个链点 `top + Tw 2`。
- 第 2 到 4 步：三次取 ℕ 极限的第 0 项，到层号 `upT (suc (suc zero))`。
- 第 5 步：它的第 1 个链点，是第 1 层的 `top` 加上 `tw 2` 的顶折到第 1 层。这里的派发 `dl 1 (tw 2)` 在根 `(top, tt, inj₁ tt)` 上保留 (`keep₅`)，得到第 1 层的结点 `G.lc (inj₁ tt) K`。
- 第 6、7 步：两次第 0 个链点。分支族 `Kfk zero` 在 `top` 处是同一个派发再保留一次。
- 第 8 步：一次 ℕ 极限的第 0 项，到层号 `up 1 (top + top)`。
- 第 9 步：它的第 0 个链点，层号是 `suc (tw 2)`，公共上界是 `ws (Lw-tw 2)`，派发是 `λ _ → fold`，这就是 `T⁺ʷ`。

路上所有折叠的目标层都是 0，观察项上的派发一直是常值 `fold`。

**修正简报里的一条判断。** 简报的判断是：`tw 3` 的 `suc top` 支 `upT (fin 2)` 的 `suc top` 支是 `suc (tw 2)`。层号上确实如此，但目标层 0 的折叠根本不走 `Kfk` 的分支族，只走链点。实际位置在 `upT (fin 2)` 的第 1 个链点之下，如上。

#### 5 第一个障碍

没有数学障碍。唯一的报错是撞名，改名后通过：
`[ClashingDefinition] Multiple definitions of lay. Previous definition at …/YiNextCore.lagda.md:39.15-18`
原因是记录字段 `lay` 与 `Lay` 的构造子重名，字段已改为 `ly`。

#### 6 偏离与事故

- 没有偏离：只新建了这两个文件，没改已有文件，只编译了自己的模块。
- 测内存时我用 `/usr/bin/time -l` 包了 agda 命令，退出码仍直接打印，没有经过管道。日志在 `<实验目录>/agents/into/` 下的 `cold-Tw3.log` 与 `cold-Bounds.log`。
- 判断（未编译）：即使第 5 步那处派发改成折叠，下降仍能到层号 `up 1 (top + top)`，只是路径的形状不同。所以这条结论看来不依赖 `keep₅`。我只手算过这种情形，没有编译。
