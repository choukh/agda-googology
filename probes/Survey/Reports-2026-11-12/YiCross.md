# A 跨层的内部模拟与折叠单调 (YiCross)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-13 01:48 至 02:27 |
| 工具调用 / agda 编译 (粗数) | 38 / 13 |
| token (usage 字段，按消息去重) | 输出 227411；新写入缓存的输入 461315；读缓存的输入 4952707；其余输入 48 |
| 写过的仓库文件 | `YiCrossAdd.lagda.md`, `YiCrossIface.lagda.md`, `YiCrossInst.lagda.md`, `YiCrossKeepNeg.lagda.md`, `YiCrossMono.lagda.md`, `YiCrossReg.lagda.md` |
| 文件前缀 | `YiCross` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: A 跨层模拟与折叠单调返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 跨层单调是条件定理，有限层号上无前提；主线 Lw-tw 2 根见证上同层单调前提为假；六件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 作者 2026-11-13 的决定 (选项工具): 按第十一次路线审查的建议, 停掉按站往上的值工作 (停工, 不是否定), **先单独做 A: 跨层的内部模拟与折叠单调**, A 的接口定稿后另派一路在同一接口上写配对的否定. 你是 A. 主审会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 为什么做这件 (事实与审查者的判断, 先读 `probes/Survey/RR11-RouteOverview.md`)

- 最终目标: 读法 ψ₀(Λ) 的合法闭项 `TΛ` (已有, 合法无前提) 的序数值不低于 EBO 的参照树 (下界). 与记号有编译联系的值现在只有 BTBO 一站 (`btbo-TΛ` 配 `BTBO-label`).
- 审查者提出的整体策略里已有两块编译定理 (主审已移入仓库, 都在 `probes/OCF/Lean/`):
  - `YiMonoExit`: `exit`, `ebo-lower` (终点归约到对基本列封闭的一族).
  - `YiMono`: 块内部的同层模拟 `Sim` 与 `M.mono` (一致折叠对 `Sim` 单调, 对任意派发 `D`, 前提 `MW`); `YiMonoInst`: `sim→≼`, `Inst.mw2 : KeepMono … (witU zero) → MW (Lw-tw 2)`, `Inst.value2`; `YiMonoTower`: 无见证上界 `Lw-twⁿ`, `VΛⁿ` 上 `mono-tw`, `mono-Λ`, `value-Λ` 无前提.
- 同层的 `Sim` 不给: 跨孩子、跨层的比较 (`em 2 top` 对 `em 3 top` 不可导), 左加 (`η ⊑ θ + η` 在嵌入与 `top` 处不可导). 所以还推不出塔的相邻项比较与链的一步. 后面两路 (B: 派发在规范域上完全, 验收站 ψ₀(Ω_Ω·2); C: 记号直连试点) 都要跨层的这一块.

#### 要交的 (审查者的规格; 你可以改设计, 但要在回报里说清改了什么, 为什么)

0. **接口先行.** 先写 `probes/OCF/Lean/YiCrossIface.lagda.md`: 跨层模拟 `Simʰ : Raw K → Raw K′ → Set` (审查者的草图: 嵌入透明, `top` 展开成结点或部分和, 任一支可上移), 前提 `Compat x x′` (左边保留处右边也保留) 写成记录, 以及 `monoʰ` 的陈述写成一个类型 (例如 `MonoH : Set`). 按 AGENTS 的当前最佳实践: 律里出现的每一对下标都带字面公共上界的证据; 量化域先取带证据的读回域 (塔 `tw n`, Λ 的规范构造), 不取一切合法树. 接口编译通过且你认为定稿 (以后只增不改) 时, 用 SendMessage 给 `main` 发一行 (文件名与 "接口定稿"), 然后继续; 配对否定的那一路会建在这个文件上.
1. **`monoʰ`**: 对任意派发 `D` 的一般折叠 (`YiDlFold.Fold`), 由 `Compat` 与 `Simʰ ξ ξ′` 推出 `Simʰ (Ψ m V x ξ) (Ψ m′ V′ x′ ξ′)` (或你认为合适的一般形). 先在无见证的上界 (`YiMonoTower` 的 `Lw-twⁿ`, `VΛⁿ`) 上无前提, 再看主线带见证的上界.
2. **回归**: 由它重新推出已编译的 `YiIntoTw3.T⁺ʷ≼TΛ`, `YiLamVBtbo.Tw≼TΛ` (主线上), 以及左加. 能在主线上做最好; 只在无见证的折叠上做成时说明.
3. **`KeepMono`** 在主线 `Lw-tw 2` 的根见证上 (`YiMonoInst.mw2` 的前提), 量化域取合法下标: 证, 或交编译的反例. 连续两条同形的退化反例就停下来查量化域 (AGENTS).
4. 做不过去时: 给出确切的缺口 (缺的引理的 Agda 类型, 检查器报错原文), 并说清它在关系一侧还是派发一侧.

值定理一律对派发 `D` 参数化写, 派发的性质作显式前提 (台账 P8). 关系只在块内部, 不经参照框架 `OCF.Align.Level`, 不读记号. 只要下界.

#### 已知的事实 (编译) 与判断

- 合法性对任意派发成立: `YiDlFold.Fold.Ψ-lgl`.
- 现派发 `dl` 在源层号字面是 ℕ 极限时一律折叠: `YiDlLost` 的 `dl-lim`, `not-full`. 处处完全的派发推出 LPO: `YiUniNegCmp.cmp-full→lpo`, `YiUniNegStep.step-full→lpo`. 保留行的分支族取 "诚实" 折叠值不合法: `YiUniNegKeep.honest-keep→⊥` (与 `KeepMono` 相邻).
- 判断 (RR9 §3 (c)): 现主线派发对层号嵌入不单调 (`dfin` 只在目标字面有限时保留), 所以 `Compat` 在主线派发上可能不成立; 这正是配对否定那一路要查的, 你不必证它对 `dl` 成立.

#### 先读什么

`AGENTS.md` (Agda 一节, 当前最佳实践里 "律带公共上界" 与 "量化域先取带证据的读回域", 文字预算, 结论的写法); `probes/Survey/RR11-RouteOverview.md`; `probes/Survey/EBOHandbook.md` §4.1 到 §4.5 与 §5.4; `YiMono*` 四件全读; 块的可读版 `YiReadCore.lagda.md` (原版 `YiNextCore`); `YiLamFold.lagda.md` (`Lw`, `Wit`, `witU`, `Kfk`, `nrmk`, `Lw-tw`, `Ψ`, `Ψ-lgl`); `YiDlFold.lagda.md`; `YiNextBase` (`Ψn`, `Way`, `Ext`) 与 `YiNextAcc` (`read`, `_⊴_`) 检索要用的名字; `YiIntoTw3`, `YiLamVBtbo` 里两条回归定理的证明形状. 查签名用检索, 不整篇读大文件.

#### 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiCross` (模块名 `OCF.Lean.YiCross…`). 都是验收文件, 文首标 "验收文件". 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞 (写入文件时也不要留洞), `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提.
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由. 一次性的试验放你的临时目录, 用纯 `.agda` (选项行要加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 堆墙多出在比较具体闭项的地方: 陈述逐字写, 不用别名; 大参照树放 `opaque`; 经非单射的头求解的隐式参数显式写出 (手册第 4 节).
- 仓库文件里不写本机路径. 不要把仓库整个拷到临时目录.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G (之后会有另一路同时编译). 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽. 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块.
- 你的临时目录: `<实验目录>/agents/cross`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- **停下的条件**: 同一处两次重新设计仍过不了检查器; 需要函数外延或 K; 堆到 6G 仍耗尽 (先按手册 §4.2). 没有编译的否定时只写 "未走通".
- 过程要求: 读完上面的文件后尽快动手, 接口文件在 30 分钟内写出并编译; 每次回复都要有工具调用, 不要在一次回复里只思考.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 回报格式 (只在回报里交一次)

1. 判决: 做到第几步; 一段话说对目标意味着什么 (有没有跨层的单调; 在主线还是只在无见证的折叠上; `KeepMono` 的结果).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断).
4. 办法, 与审查者规格的差别, 翻译账 (每条规则来自树侧的什么需要).
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 中途消息（主审发给这一路）

转录时间戳 2026-11-13 02:24 (UTC)：

主审收到接口更正, 已转告配对否定那一路 (前缀 YiCompatDl, 它只导入 YiCrossIface). 从现在起 YiCrossIface 请只增不改; 若非改不可, 先用 SendMessage 告诉主审改什么、为什么, 再改. 回报里把这次改动 (TopR 的 Ω 行, c-pts → c-obs) 和理由写进 "偏离与事故".

## 回报原文

### A 路回报: 跨层的内部模拟与折叠单调 (前缀 YiCross)

#### 1 判决

做到第 1 步的条件定理, 第 3 步的编译否定, 第 2 步的回归 (但回归没有用到 `monoʰ`).

- **跨层的单调有了, 是条件定理.** `monoʰ : MonoH D` 对任意派发 `D` 编译通过: 由 `Compat` (派发的一族配置对与封闭律) 和 `KeepRow` (Ω 结点层号两边的根都保留时, 分支族对相关下标单调) 推出 `Simʰ k k′ ξ ξ′ → Simʰ m m′ (Ψ m V x ξ) (Ψ m′ V′ x′ ξ′)`。它直接写在主线的折叠 `YiDlFold.Fold D` 与带见证的 `Lw` 上, 不区分有无见证。
- **前提可满足, 但已填的实例只到有限层号.** 无前提 (任意 `D`) 的实例有两个: 左边源层是第 0 层而右边任意 (`Zero.mono₀`); 两边都是有限层号, 层号可以不同, 保留行在内 (`Fin.mono-fin`)。ℕ 极限层号与 Ω 结点层号 (`tw 2` 起) 上 `Compat` 是派发的性质, 未证未否定; 那是配对否定那一路的对象。
- **`KeepMono` 在主线 `Lw-tw 2` 的根见证上不成立**, 对任意 `D` 有编译的否定 (`no-keep`, `no-MW2`)。反例的下标是 `suc zero ⊑ suc top`, 合法且不含极限; 外部派发是 `self (tw 2)`, 目标层 `tw 2`, 这正是 `T⁺ʷ` 的内层折叠 (`T⁺ʷ-form` 是 `refl`)。所以 `YiMonoInst.mw2`, `value2` 的前提是假的。失败的机制在关系一侧: 同层 `Sim` 的结点规则要位置相同, 而 `self` 把两支的保留结点放在 `tw 2` 的不同位置上。这不否定跨位置的 `Simʰ`。
- **对目标**: 塔的相邻项与链的一步在 Ω 结点层号上仍推不出。缺两样: (a) `Compat` 在 `tw 2` 以上对主线派发是否成立; (b) `KeepRow`, 即根保留行的分支族 `Kfk ∘ nrmk` 的单调。

#### 2 文件表

都在 `<仓库>/probes/OCF/Lean/`, 都标 "验收文件"。六个文件删自己的接口后按依赖次序冷编译, 每个日志里只有自己的 `Checking` 行; 禁用构造检索为 0, 本机路径检索为 0。

| 文件 | 代码行 | 冷编译退出码 | 常驻内存峰值 |
|---|---|---|---|
| `YiCrossIface.lagda.md` | 132 | 0 | 0.42 G |
| `YiCrossAdd.lagda.md` | 228 | 0 | 0.50 G |
| `YiCrossMono.lagda.md` | 96 | 0 | 0.47 G |
| `YiCrossInst.lagda.md` | 172 | 0 | 3.06 G |
| `YiCrossKeepNeg.lagda.md` | 86 | 0 | 0.39 G |
| `YiCrossReg.lagda.md` | 47 | 0 | 1.63 G |

#### 3 定理表

| 名字 | 陈述 (逐字) | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `M.monoʰ` | `monoʰ : MonoH D`, 其中 `MonoH = (S : Compat) → KeepRow S → ∀ {m k m′ k′} {V : Lw k} {x : Ext m k} {V′ : Lw k′} {x′ : Ext m′ k′} → Compat.C S V x V′ x′ → ∀ {ξ ξ′} → Simʰ k k′ ξ ξ′ → Simʰ m m′ (Ψ m V x ξ) (Ψ m′ V′ x′ ξ′)` | 一般折叠对跨层模拟单调 | YiCrossMono | 条件定理 (前提 `Compat`, `KeepRow`) |
| `add-monoʰ` | `∀ {M M′} k k′ (B : Bld M k) (B′ : Bld M′ k′) → BB M B′ → BN B B′ → ∀ {x x′} → Simʰ M M′ x x′ → ∀ {a a′} → Simʰ k k′ a a′ → Simʰ M M′ (add k B x a) (add k′ B′ x′ a′)` | 一般层的加法对两个参数单调, 覆盖全部十二条规则 | YiCrossAdd | 编译定理 |
| `plus-monoʰ`, `succ-monoʰ`, `psum-monoʰ`, `ΨN-nnʰ`, `ΨN-bbʰ`, `ΩT-nnʰ` | 见文件 | 结点两行: 同为保留 (两个结点, 位置任意) 或同为折叠 (链逐点相关) | YiCrossAdd | 编译定理 |
| `Zero.mono₀` | `∀ {m m′ k′} (x : Ext m zero) (V′ : Lw k′) (x′ : Ext m′ k′) → Simʰ m m′ G.top G.top → ∀ {ξ ξ′} → Simʰ zero k′ ξ ξ′ → Simʰ m m′ (Ψ m w0 x ξ) (Ψ m′ V′ x′ ξ′)` | 左边是第 0 层的树, 右边任意层, 任意上界, 任意派发 | YiCrossInst | 编译定理, 任意 `D` |
| `Fin.mono-fin` | `∀ {m k m′ k′} {V : Lw k} {V′ : Lw k′} → FL V → FL V′ → (x : Ext m k) (x′ : Ext m′ k′) → Simʰ m m′ G.top G.top → (∀ r r′ → lev k r ≡ lev k′ r′ → WayR (x r) (x′ r′)) → ∀ {ξ ξ′} → Simʰ k k′ ξ ξ′ → Simʰ m m′ (Ψ m V x ξ) (Ψ m′ V′ x′ ξ′)` | 两个有限层号之间的单调, 外部派发在层号相等的位置对上同向 | YiCrossInst | 编译定理, 任意 `D` |
| `Fin.self-fin` | `FL V → ∀ {ξ ξ′} → Simʰ k k ξ ξ′ → Simʰ k k (Ψ k V (self k) ξ) (Ψ k V (self k) ξ′)` | 派发 `self` 时保留行在内 | YiCrossInst | 编译定理 |
| `Fin.value-fin` | `FL V → FL V′ → ∀ {ξ ξ′} → Simʰ k k′ ξ ξ′ → NA.read (Ψ zero V (λ _ → fold) ξ) ≼ NA.read (Ψ zero V′ (λ _ → fold) ξ′)` | 有限层号之间的值序 | YiCrossInst | 编译定理 |
| `simʰ→≼` | `∀ {a b : R} → Simʰ zero zero a b → NA.read a ≼ NA.read b` | 出口 | YiCrossInst | 编译定理 |
| `la₀`, `ladd₀` | `la₀ : ∀ {M} {a : Raw M} {y : R} z → Simʰ M zero a y → Simʰ M zero a (plus zero z y)`; `ladd₀ : ∀ θ η → Simʰ zero zero η (plus zero θ η)` | 左加, 只在目标是第 0 层时 | YiCrossInst | 编译定理 |
| `top-refl` | `∀ K → Simʰ K K G.top G.top` | 每层的顶自相关 | YiCrossInst | 编译定理 |
| `Neg.no-keep` | `KeepMono (λ η l → lgl→Lw zero tt w0 η l) (witU zero) → ⊥` | `mw2` 的前提为假 | YiCrossKeepNeg | 编译定理 (否定), 任意 `D` |
| `Neg.no-MW2` | `MW (Lw-tw 2) → ⊥` | 同上 | YiCrossKeepNeg | 编译定理 (否定) |
| `Neg.no-refl` | `Sim (tw 2) (Ψ (tw 2) (Lw-tw 2) (self (tw 2)) G.top) (Ψ (tw 2) (Lw-tw 2) (self (tw 2)) G.top) → ⊥` | 主线这个配置上 `top` 的像在同层 `Sim` 里不自相关 | YiCrossKeepNeg | 编译定理 (否定) |
| `Reg.Tw⊑TΛ`, `Reg.Tw≼TΛʰ` | `∀ n → NA.read (Ψ zero (Lw-tw n) (λ _ → fold) G.top) ≼ NA.read (Ψ zero VΛ (λ _ → fold) G.top)` | `Tw≼TΛ` 的回归, 任意 `D`, 带见证的上界 | YiCrossReg | 编译定理 |
| `T⁺ʷ⊑TΛ`, `T⁺ʷ≼TΛʰ` | `NA.read W.T⁺ʷ ≼ NA.read W.TΛ` | `YiIntoTw3.T⁺ʷ≼TΛ` 的回归, 主线 `dl` | YiCrossReg | 编译定理 |

#### 4 办法, 与规格的差别, 翻译账

**办法.** `Simʰ K K′` 对层号对双重递归定义 (位置先沿左边走到叶, 再沿右边)。规则十二条: `zS sS wS lR lL bR` 同 `Sim`; `nN` 的两个位置任意; `eL`, `eR` 使嵌入透明; `tT` 带证据 `TopR`; `cR` (落在允许的孩子的顶之下就在本层的顶之下); `t0` (第 0 层的顶读作 1)。`monoʰ` 是对 (左上界, 右上界, 推导) 的一条归纳, 不按站。

**与审查者规格的差别.**
1. **`WayR` 只收同为保留或同为折叠.** 左折叠右保留没有收。它要把链点那一支上移 ("任一支可上移"), 而这条作为输入规则对右折叠的行不成立: 折叠只取链上的下标, 任意下标的那一支可以更高 (判断, 没有编译的反例)。
2. **`nN` 要两个位置的层号字面相等, 另带顶相关.** 只要顶相关时, 层号 2 上结构派发 `cmpw (ws (ws w0))` 在位置对 `(p₁ , p₀)` 上左保留右折叠, 对角配置进不了任何 `Compat` (纸面推导, 没有留成文件)。
3. **`Compat` 是一族配置对加封闭律, 不是逐对的记录.** 派发的同向要对内层派发 `cmpw` 遗传成立, 逐对的记录说不出这件事。
4. **没有 "`top` 展开成结点 / 部分和" 的规则.** 分支族 `Kfk` 对展开不是不变的 (`Kfk T top = T top`), 加上会使 `KeepRow` 更难。后果: 左加只在目标是第 0 层时成立; 后继层号的 `top` 处左加推不出 (判断)。
5. **回归没有用到 `monoʰ`.** 两条回归的目标层都是第 0 层, 那里没有结点, 只用 `la₀` 与 `refl₀`。它们是在块内部重新推出的 (不经 `NA.plus≽`), 在主线带见证的上界上。

**翻译账.** 没有读记号, 没有经参照框架。每条规则的来源:
- `nN` 跨位置: `self` 把同一层的结点放到不同位置 (`no-refl`)。
- 层号相等: `cmpw` 的保留条件由位置的层号决定 (`Fin.ck`, `Fin.cf`)。
- `t0`: `add zero B x top = suc x`。
- `cR` 只许后继的孩子与 ℕ 极限的第 0 个孩子: 第 `n` 个孩子的顶在折叠后是部分和的一项, 要目标层上的左加; Ω 结点层号上 `x + top = suc x`, 所以不许。
- `c-obs`: 链点由公共上界与派发决定, 不是关系内部的量。

#### 5 第一个障碍

**(a) 关系一侧, `KeepRow.c-keep` (根保留行).** 它要对一切相关的下标 `η ⊑ η′` 有 `Kfk k T η ⊑ Kfk k′ T′ η′`。对推导归纳时, `sS` 一步要 `T (suc a) ⊑ T′ (suc b)`, 即两支的层 `g (nrmk a)` 与 `g′ (nrmk b)` 的顶相关。缺的引理:

```agda
nrmk-mono : ∀ {k k′ η η′} → Simʰ k k′ η η′ → Simʰ k k′ (nrmk k η) (nrmk k′ η′)
up-top : ∀ {η η′ : R} → Lgl zero η → Lgl zero η′ → Simʰ zero zero η η′ → Simʰ (up zero η) (up zero η′) G.top G.top
```

两条都没有检查器报错, 因为没有写进文件; 纸面判断是都不成立:
- `nrmk` 把 ℕ 极限换成部分和, `lL` 的推导跟不过去。常值极限 `lim (λ _ → suc zero) ⊑ suc zero`, 归一后左边是 ω。这是退化的合法下标, 按 AGENTS 读作量化域太宽: `nN` 与 `c-keep` 对一切下标量化, 没有限制到合法或归一的下标。
- `up-top` 在 `η = suc (suc zero)`, `η′ = lim` (有限数列) 上推不出: `cR` 只许 ℕ 极限的第 0 个孩子。

**(b) 派发一侧, `Compat` 在 `tw 2` 以上.** 要 `c-way`, `c-cmp` 对 `cmpw (wl …)` (带 `shiftw` 搬运) 与 `cmpw (wΩ …) = D …` 成立, 即派发在层号相等的位置对上同向。对 `dl` 未证未否定。

#### 6 偏离与事故

- **接口在第一次 "定稿" 通知后改过一次**, 随即发了更正, 主审已转告配对否定那一路 (前缀 YiCompatDl)。改动两处:
  1. `TopR` 的 Ω 结点层号一行, 由 "下标层相等 × 顶相关 × 一切相关合法下标上分支层的顶相关" 改为只留前两项。
  2. `Compat` 的字段 `c-pts` (链点下一步的派发封闭) 换成 `c-obs` (两边第 `n` 个链点那一支的顶相关)。

  理由: 原第三项要 `up-top` 那样的性质对一切相关下标成立, 按上面 (a) 的分析 `tw 2` 的顶不自相关, 以 `tw 2` 为目标层的配置进不了任何 `Compat`。这条理由是纸面判断, 没有编成定理。
- **过错在我**: 第一次通知时只在有限层号的实例上填过, 没有先在 `tw 2` 上试 `c-top`, 违反了 "规范实例都通过才定稿"。现在 `tw 2` 及以上仍然没有填过的实例; 接口此后只增不改, 非改不可先发消息。
- 定稿前另有两次设计修改, 都在通知之前: `nN` 加层号相等的证据; Ω 行由整行假设改为折叠行结构递归加保留行假设。
- `YiCrossKeepNeg` 只导入 `YiMono`, 不导入 `YiCrossIface` (两者的构造子同名)。
- 没有碰已有文件, 没有提交; 临时目录里只有编译日志。
