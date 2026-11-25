# 下一站闭项的值从 BTBO 往上 (YiAbove)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-12 00:55 至 01:30 |
| 工具调用 / agda 编译 (粗数) | 69 / 9 |
| token (usage 字段，按消息去重) | 输出 215254；新写入缓存的输入 701605；读缓存的输入 13824063；其余输入 110 |
| 写过的仓库文件 | `YiAboveCtx.lagda.md`, `YiAboveLost.lagda.md`, `YiAboveOne.lagda.md`, `YiAboveStep.lagda.md` |
| 文件前缀 | `YiAbove` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-12: 下一站闭项的值从 BTBO 往上返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | T⁺ 严格高过 BTBO，不低于 ψ₀(Ω_Ω+Ω₁) 的带标签参照（无前提）；ψ₀(Ω_Ω·2) 只有条件定理；lost 那一对被问到；四件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 作者的指示是 "朝着最终目标的关键路径走" (最终目标: 布劳威尔树上 ψ₀(Λ) 的合法闭项, 值不低于 EBO). 你这一路的任务是 **下一站的闭项 `T⁺` 的值从 BTBO 往上: 它的值是否高过 BTBO, 高到哪里**. 这决定下一站的保守派发掉不掉值, 是往塔的一切项推广折叠之前要知道的. 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇. 特别是 Agda 一节 (选项, 文字预算, 退出码, 堆; 函数外延只准作前提), "用记号验收强度", "中间站给界", "结论的写法".
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 与 §5.4.
3. **已闭合的锚点 (无前提)**: `probes/OCF/Lean/YiBtboLower.lagda.md` 全读 (`btbo⁺ : D.BTBOᴵ ≼ NA.read NT.T⁺`; 办法: 链上只带值序, 每步经累加规范化层号 `V2′` (在 `YiBtboV2`) 与主线一侧的 `V3m` 造到下一个链点的前驱嵌入, 再 `Ψ-emb`). 说明在 `probes/Survey/RR7-BtboLower.md`.
4. 被验收的闭项: `probes/OCF/Lean/YiNextTop.lagda.md` (`T⁺ = Ψ zero (vs V₂) (λ _ → fold) G.top`, 层号 `upT (suc (tw 2))`, 读法 ψ₀(Ω_{Ω+1}); `T⁺-form`, `T⁺-feedback`, `T⁺-term₀`: 第 0 项定义性地是 `T₃`, 读法 ψ₀(Ω_Ω) = BTBO), 折叠 `YiNextFold.lagda.md` 与 `YiNextBase.lagda.md` (`Lv` 多一种 `vΩ`), 读回 `YiNextAcc.lagda.md` (`read`, `T₃≼T⁺`), 已有的值 `YiNextValFin.lagda.md` (`T⁺-Ωω` 等). **有限测试**: `YiNextAccTest.lagda.md` 的 `lost`, `could` (同一支里保守派发丢掉的一对); 回报 `probes/Survey/Reports-2026-11-11/YiNext.md` §6 说丢失只在可数坐标那个方向, 上确界也许不受影响 (判断, 没有核对).
5. 参照 (都是验收侧, 允许导入): `probes/OCF/Align/Level.lagda.md` 的 `ψ⁰`, `Ω`, `toLevel`; `probes/OCF/Align/Stage2.lagda.md` (BTBO 之上 ψ₀(Ω_Ω+1), ψ₀(Ω_Ω·2) 的交替读法与它们带标签的代表; 注意 §1: `ψ⁰ (Ω BTBOᴸ)` 与 BTBO 是同一个不动点, 朴素代表不升值); `probes/OCF/Align/LambdaCountableTarget.lagda.md` (实际 EBO 参照 `E.EBO-tree`, 由记号的基本列生成); `OCF.Align.Value` (`_≼_`).
查签名用检索, 大文件不要整篇读.

#### 1 要交的, 分步; 每做成一步先交

1. **严格高过 BTBO 的一步**: 例如 `D.BTBOᴵ ≺ NA.read NT.T⁺` 或 `suc D.BTBOᴵ ≼ NA.read NT.T⁺` (用 `Value` 里现成的关系写; 选最便宜的能说明 "严格高过" 的陈述).
2. **一个 BTBO 之上的参照不高于 `read T⁺`**: 先 ψ₀(Ω_Ω+1), 再 ψ₀(Ω_Ω·2), 能做就继续往 ψ₀(Ω_{Ω+1}) (`T⁺` 的读法). 参照必须是有编译过的验收定理支持的树 (过基本列验收的带标签代表, 或记号基本列生成的 `EBO-tree` 一类), 写明用的是哪一个、它的验收定理叫什么. 参照只在验收文件里出现.
3. **若某一步做不过去**: 给出值停在哪里的编译事实 (例如一条上界, 或 "某参照 ≼ read T⁺ 推出某全知原则"), 或者把 `lost`/`could` 一类的有限测试推进成关于值的陈述. 没有编译的否定时只写 "未走通".

只要下界 (作者 2026-11-11: "只要证明 'BTBO是下界' 即可" 的同一原则): 选证法时不引入上界, 同值, 逐项精确; 有的话先找只用下界的证法.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K (可交显式前提的条件定理); 堆到 6G 仍耗尽 (先按手册 §4.2). 做不成的部分写成带确切类型的模块参数.

#### 2 过程要求

- 读完上面的文件后尽快动手: 第一个文件 (第 1 步) 在 20 分钟内写出并编译.
- 每写完一个文件就编译; 每次回复都要有工具调用, 不要在一次回复里只思考.

#### 3 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiAbove` (模块名 `OCF.Lean.YiAbove…`). 都是验收文件, 文首标 "验收文件". 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提, 用到它的定理在文首标 "条件".
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 堆墙多出在比较具体闭项的地方: 陈述逐字写, 不用别名; 沿良基证明算出的大参照树放 `opaque`; 经非单射的头求解的隐式参数显式写出 (手册第 4 节).
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块. 别的智能体也在编译, 不要动别人的文件.
- 你的临时目录: `<实验目录>/agents/above`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几步; 一段话说对目标意味着什么 (`T⁺` 的值是否高过 BTBO, 已证的最高下界写成 ψ₀(Ω_x), 保守派发掉不掉值).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 用到的参照与它的验收定理.
4. 办法: 与 `YiBtboLower` 相比新用到了什么.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 回报原文

#### 1 判决

我做完了第 1 步和第 2 步的第一档,又多走了一站 ψ₀(Ω_Ω+Ω₁)。ψ₀(Ω_Ω·2) 没有走通:我把它写成一条条件定理,前提只剩一条单步比较 `Stepᴳ`,这条前提没有证,也没有否定。第 3 步按要求把 `lost` 推进成编译过的陈述。

对目标意味着什么:
- **`T⁺` 的值严格高过 BTBO**(编译定理,无前提):`L.suc D.BTBOᴵ ≼ read T⁺`。
- **已证的最高下界是 ψ₀(Ω_Ω+Ω₁)**(编译定理,无前提,参照带标签)。它不是 ψ₀(Ω_x) 的形式,夹在 ψ₀(Ω_Ω) 与 ψ₀(Ω_{Ω+1}) 之间。
- **到 ψ₀(Ω_Ω+Ω₁) 为止,下界与保守派发无关**。这是读代码可以核对的事实,不是定理:这一站的证明只用到目标层 0 的折叠(那里本来没有能保留的位置)和目标层 `tw 2` 的 `Φ₂`(经 `Ω-keep`),没有出现目标层 ≥ 1 的折叠。
- **保守派发第一次起作用,是在层号 ≥ 1 的链上**。编译事实:`lost` 那一对确实被 `T⁺` 的值的计算问到(`asked`, `asked-form`, `asked-lost`)。这把 YiNext 回报里的判断换成了定理。
- **值掉不掉,仍是判断**。我的纸面分析:
  - 树在目标层 1 上的值都低于 EBO 的 ψ₁(Ω_Ω),所以树自己的 "ψ₀(Ω_Ω+Ω₂)" 子项低于 EBO 的 ψ₀(Ω_Ω+Ω₂)。
  - 更高层号的分支 (Ω_{k+2}) 可能补回来,所以 `T⁺ ≥ ψ₀(Ω_Ω·2)` 仍可能成立。
  - 这与 `Value.D3-question`(静态前缀与 EBO 的穿透是否同值)是同一类开放问题,都没有核对。

#### 2 文件表

都在 `probes/OCF/Lean/`,都是验收文件。代码行是 agda 代码块里的非空行。冷编译时只删了这 4 个接口(字面路径),每个日志只有自己那一行 `Checking`。

| 文件 | 代码行 | 冷编译退出码 | 常驻峰值 |
|---|---|---|---|
| YiAboveOne.lagda.md | 33 | 0 | 1.68G |
| YiAboveCtx.lagda.md | 91 | 0 | 1.69G |
| YiAboveLost.lagda.md | 39 | 0 | 1.63G |
| YiAboveStep.lagda.md | 64 | 0 | 1.77G |

检索 `postulate`, `TERMINATING`, `NO_POSITIVITY`, `trustMe`, `irrelevant-projections`, `--cubical`, 洞, `Funext`, 本机路径:命中 0。选项行都是 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。

#### 3 定理表

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `bt₃` | `D.BTBOᴵ ≼ NA.read NT.T₃` | `YiBtboLower.btbo` 经 `T₃≅` 搬到下一站 | One | 编译定理 |
| `s⊑` | `Cp zero (succ zero NT.T₃) NT.T⁺` | `T₃` 的 ω 倍是 `T⁺` 的第一位置 | One | 编译定理 |
| `above` | `L.suc D.BTBOᴵ ≼ NA.read NT.T⁺` | 严格高过 BTBO | One | 编译定理 |
| `ΩΩ+1` | `L.ψ⁰ (L.suc (L.Ω S2.ℓ₀)) ≼ NA.read NT.T⁺` | 不低于 ψ₀(Ω_Ω+1) | One | 编译定理 |
| `topᶜ` | `∀ m {k} (V : Lv k) x ξ → Cp m G.top (Ψ m V x ξ)` | 任意派发下,`top` 是一切折叠值的第一位置(含 `vΩ`) | Ctx | 编译定理 |
| `term₁` | `chain (tw 2) NT.Φ₂ 1 ≡ G.lc p₀ gK` | 根链第 1 点是 `p₀` 上的结点 | Ctx | 编译定理 (`refl`) |
| `ctx` | `∀ {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ ξ → b ≡ NA.read ξ → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) S2.σ₁ y) ≼ NA.read (Ψ₀ (gK ξ))` | 上下文引理:可数的 y 不超过坐标 ξ,则 ψ₀(Ω_Ω+y) 不超过这一支的折叠 | Ctx | 编译定理 |
| `χ₁≼` | `S2.χ 1 ≼ NA.read NT.T⁺` | 不低于 ψ₀(Ω_Ω+Ω₁) | Ctx | 编译定理 |
| `χ₁-top`, `χ₁-d1` | `S2.χ 1 ≼ NA.read (Ψ₀ (gK G.top))`;`S2.χ 1 ≼ NA.read (d 1)` | 根链第 1 点的第 0 支,以及结点链的第 1 点,已不低于 ψ₀(Ω_Ω+Ω₁) | Step | 编译定理 |
| `FromStep.T2≼` | 模块参数 `(f : ℕ → L.Ordᶜ L.zero) (lf : Lab (L.lim f) S2.t2) (step : ∀ k m → f k ≼ NA.read (d m) → f (suc k) ≼ NA.read (Ψ₀ (gK (d (suc m)))))`;结论 `L.lim f ≼ NA.read NT.T⁺` | 记号基本列的单步比较,推出 ψ₀(Ω_Ω·2) 的带标签树不高于 `T⁺` | Step | 条件定理 |
| `T2≼ᴳ` | `Stepᴳ → GL.T2ᴸ ≼ NA.read NT.T⁺`,其中 `Stepᴳ = ∀ k m → GL.χ k ≼ NA.read (d m) → GL.χ (suc k) ≼ NA.read (Ψ₀ (gK (d (suc m))))` | 参照取 GoodL 的 ψ₀(Ω_Ω·2),只剩 `Stepᴳ` | Step | 条件定理 |
| `asked` | `NA.read (Ψ₀ N₂) ≼ NA.read NT.T⁺` | 位置 `s₂`(层号 1)上的结点在 `T⁺` 的第一位置里 | Lost | 编译定理 |
| `asked-form` | `Ψ₀ N₂ ≡ G.lim (λ n → Ψ₀ (Bs₂ (chain (suc zero) (λ ζ → Ψ (suc zero) NT.V₂ (cmp NT.V₂ s₂) (Bs₂ ζ)) n)))` | 它的折叠走层号 1 的链,派发用 `cmp V₂ s₂` | Lost | 编译定理 (`refl`) |
| `asked-lost` | `Ψ (suc zero) NT.V₂ (cmp NT.V₂ s₂) (Bs₂ G.top) ≡ G.lim (λ n → Ψ (suc zero) NT.V₂ (cmp NT.V₂ s₂) (B′ (chain zero (λ η → Ψ zero NT.V₂ (cmp NT.V₂ s₂′) (B′ η)) n)))` | 链第 1 点要算的项里,`s₂′` 上的结点被折成 ℕ-极限(`lost`);`could` 说它本可保留 | Lost | 编译定理 (`refl`) |

**前提的可满足性.**
- `lf` 由 `GL.T2-label` 填上:`GL.T2ᴸ ≡ L.lim GL.χ` 是 `refl`,编在 `T2≼ᴳ` 里。
- `Stepᴳ` 没有实例。它成立与否是判断。

**用到的参照与验收定理.**

| 参照 | 读法 | 验收定理 |
|---|---|---|
| `D.BTBOᴵ` | ψ₀(Ω_Ω) | 与 `N.BTBOᴵ` 定义性相同,`Label.BTBO-label` |
| `S2.ψ⁰ (suc (Ω ℓ₀))` | ψ₀(Ω_Ω+1) | `S2.ts-label` |
| `S2.χ 1 = ψ⁰ K₀` | ψ₀(Ω_Ω+Ω₁) | `S2.χ1-label` |
| `GL.T2ᴸ` | ψ₀(Ω_Ω·2),只在条件定理里 | `GL.T2-label` |

#### 4 办法(与 `YiBtboLower` 相比)

- 没有用 `PEmb`, `V2′`, `V3m`,只用 `btbo` 作起点。
- 新用到四件:
  1. `topᶜ`:对新块(含 `vΩ`)证 `top` 是任意派发下一切折叠值的第一位置。
  2. `up≼`:层号 `tw 2` 上的第一位置经 `Ψ-cp`、`cp⊑ⁿ`、`⊑→≼` 变成值序。全程只用第一位置,不用值单调。
  3. `ctx`, `ctx₀`:Stage2 的 `Ctx₀` 在值上的对应,写法仿 `YiNextAcc.Ψ₀⊴Φ₀`,对可数 y 的 `≼` 推导归纳。后继一步靠 `sucK`、`Kf` 的结构和 `add-cp` 走到 ω 倍;坐标 `top` 单独处理(`topStep`)。
  4. 让参照的链 `S2.ch` 与结点 `p₀` 的链 `d` 同步,用 `ψ⁰≅ψ` 与 `plus≽`。

#### 5 第一个障碍

- 没有检查器报错。障碍出在数学上。
- 缺的引理就是 `Stepᴳ`(确切类型见上表)。它在 k = 0 时已要求 `GL.χ 1` = ψ₀(Ω_Ω+Ω_{ψ₀(Ω_Ω+Ω₁)}) ≼ `read (Ψ₀ (gK (d (suc m))))`,这个参照已高于 ψ₀(Ω_Ω+Ω₂)。
- 所以缺的是:层号 ≥ 1 的位置上的结点、带 Ω_Ω 前缀时,折叠值的下界。比较的两边是:

| | 参照(EBO) | 树(保守派发) |
|---|---|---|
| ψ₁(Ω_Ω) | Ω₁-共尾(穿透) | `Ψ 1 V₂ fold G.top` 是静态对角 `G.lim (λ n → Ψ 1 (V (co pₙ)) fold G.top)`(`ΩT` 在 `x p₀ = fold` 处) |
| 层号 1 链的第 1 点 ψ₁(Ω_Ω+Ω₁) | Ω₁-共尾 | ℕ-极限(`asked-lost`) |

- 判断:同层号直接比较多半不成立,需要错位比较(树的层号 k+2 对参照的层号 k)。
- 还没有可用的关系:一边是带 Ω̂ 前缀的高层 Level 树(GoodL 的 `Goodᴸ`/`forceᴸ` 族),一边是 `Raw (tw 2)`,两者之间没有现成的、类似 `YiNextAcc._⊴_` 的关系。

#### 6 偏离与事故

- 两次 `ClashingDefinition`:`Br` 与 `YiNextBase.Br` 撞名,`pts` 与 `YiNextBase.pts` 撞名。改名为 `Bs₂`, `stp` 后通过。
- 一次 macOS `sed` 不认 `\b`,替换没有生效,改用 Edit 完成。
- **一处范围外的写入,请复核:** 为确认导入 `GoodL` 不会重编共享接口(它的 `.agdai` 是 11-02 的,比依赖的 `Stage2` 旧),我在自己的临时目录里拷了一份仓库(probes, src, 库文件,约 2.4G),在拷贝里编了一个测试文件 `YiAboveT2Inst.agda`。
  - 结果:`GoodL` 没有重编。拷贝里只重编了 `OCF.BTBO`,因为我没有拷仓库根目录的 `_build`。
  - 之后才在仓库里导入 `GoodL`,编译日志只有自己模块的 `Checking` 行。
  - 拷贝已删。
- 没有改动已有文件,没有提交,没有碰 `src/`、`archive/` 或别的路的文件。

日志都在 `<实验目录>/agents/above/`,冷编译的是 `cold-*.log`。
