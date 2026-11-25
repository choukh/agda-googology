# A¬ 同一接口上的配对否定：主线派发与 Compat (YiCompatDl)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-13 02:21 至 02:52 |
| 工具调用 / agda 编译 (粗数) | 39 / 7 |
| token (usage 字段，按消息去重) | 输出 201791；新写入缓存的输入 401693；读缓存的输入 5484923；其余输入 64 |
| 写过的仓库文件 | `YiCompatDlLPO.lagda.md`, `YiCompatDlLoss.lagda.md`, `YiCompatDlNeg.lagda.md` |
| 文件前缀 | `YiCompatDl` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: A¬ 配对否定返回并复核; 第十一批合读 (主审)” 一节 |
| 主审复核后的一句结论 | 接口在塔与 Λ 上不可满足：对任意派发推出 LPO，对主线派发矛盾；三件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 作者 2026-11-13 的决定 (选项工具): 先做 A (跨层的内部模拟与折叠单调), **A 的接口定稿后派一路在同一接口上写配对的否定 (A¬)**. 你是 A¬. A 仍在跑 (另一个执行方, 前缀 `YiCross`), 它的接口已定稿. 主审会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 接口 (已定稿, 只读, 不改)

`probes/OCF/Lean/YiCrossIface.lagda.md` 全读. 要点:
- `Simʰ K K′`: 两层的树之间的模拟 (十二条规则; 结点规则 `nN` 带两位置层号相等与顶相关两条证据).
- `WayR`: 两个派发同为保留 (`kk`) 或同为折叠 (`ff`); 左保留右折叠、左折叠右保留都不收.
- `Compat D` (记录): 一族配置对 `C V x V′ x′` 及封闭律 `c-top`, `c-way`, `c-cmp`, `c-self`, `c-Ls`, `c-Ll`, `c-LΩ`, `c-Rs`, `c-Rl`, `c-RΩ`, `c-root`, `c-pts`. 尤其 `c-way`: 配置对里, 层号字面相等且顶相关的两个位置上, 派发必须 `WayR`; `c-root`: Ω 结点层号的根的派发必须 `WayR`.
- `KeepRow S`: 两边的根都保留时保留行的分支族对相关下标单调.
- `MonoH D = (S : Compat) → KeepRow S → C V x V′ x′ → Simʰ ξ ξ′ → Simʰ (Ψ m V x ξ) (Ψ m′ V′ x′ ξ′)`; A 已在 `YiCrossMono` 里证了 `monoʰ : MonoH D` (对任意 D), 并在 `YiCrossInst` 里给了有限层号上的实例 (`Zero.S₀`, `Fin.Sᶠ`). 这些文件 A 还可能在改, 你只读、只导入 `YiCrossIface` (如需 `monoʰ` 也可导入 `YiCrossMono`, 但它若被 A 改动导致你编译失败, 改为只依赖接口).
- A 的判断: ℕ 极限层号与 Ω 结点层号上, 主线派发 `dl` 是否满足 `Compat` 与 `KeepRow`, 未证未否定, 是你这一路的对象.

#### 要交的 (按优先)

主线派发是 `YiDlFold` 的 `dl` (`open Fold dl public`; `TΛ = Ψ zero VΛ (λ _ → fold) G.top`).

1. **对 `dl` 的 `Compat`, 在规范读回域上**: 回归要用的配置对来自塔的相邻项与 Λ (例如 `Lw-tw n` 对 `Lw-tw (suc n)`, `Lw-tw n` 对 `VΛ`, 外部派发取 `λ _ → fold` 一类). 二选一给出编译结果:
   - (正) 一族 `C` 含这些配置对, 对 `dl` 满足全部封闭律 (那么 `Compat` 对 `dl` 在这个域上成立);
   - (负) 编译定理: 任何 `S : Compat dl` 都不能含某个具体配置对. 典型的证法: 沿封闭律走到两个层号字面相等、顶相关的位置, 那里 `dl` 一边保留一边折叠, 于是 `¬ WayR`, 与 `c-way` (或 `c-root`) 矛盾. 交出那一对位置与那条 `¬ WayR` (保留/折叠错位的编译实例).
2. **错位是不是真损失** (若第 1 步是负的): 在那个配置对上, 能不能找到 `Simʰ ξ ξ′` 而 `¬ Simʰ (Ψ …) (Ψ …)` (折叠后确实不相关), 或者 `NA.read` 上的值也比不上. 这一步说明否定是数学上的, 还是只说明接口太窄. 做不到时如实写.
3. `KeepRow` 对 `dl` 在同一域上 (只在第 1、2 步之后、有余力时做). 主线 `tw 2` 根见证上同层的 `KeepMono` 由 A 在做, 你不做.

**读法规则 (AGENTS)**: 反例对象不在规范读回域内的否定, 读作 "谓词太宽", 不读作数学障碍; 连续两条同形的退化反例就停下来查量化域. 前提要可满足: 否定定理的每个前提给实例. 否定写成编译过的定理; 有限样本的测试明确标为测试.

#### 已知的事实 (编译) 与判断

- `YiDlLost` 的 `dl-lim` (源层号字面是 ℕ 极限时 `dl` 一律折叠), `couldP`, `lostP`, `not-full`; `YiDlFold` 的 `dl` 定义与 `dfin`.
- 处处完全的派发推出 LPO: `YiUniNegCmp.cmp-full→lpo`, `YiUniNegStep.step-full→lpo` (只否定处处完全).
- 判断 (`probes/Survey/RR9-OmegaOmega2.md` §3 (c)): 现主线派发对层号嵌入不单调 (`dfin` 只在目标字面有限时保留).
- 第十一次路线审查: `probes/Survey/RR11-RouteOverview.md` (为什么要这条否定).

#### 先读什么

`AGENTS.md` (Agda 一节, 当前最佳实践 "律带公共上界, 构造与否定配对" 与 "量化域先取带证据的读回域", 结论的写法, 文字预算); `probes/Survey/EBOHandbook.md` §4.1 到 §4.5 与 §5.4; `YiCrossIface` 全读; `YiDlFold.lagda.md` 全读; `YiDlLost.lagda.md`; `YiLamFold.lagda.md` 里的 `Lw`, `Wit`, `witU`, `Lw-tw`, `VΛ`, `cmpw`, `rootW` (检索); 块的可读版 `YiReadCore.lagda.md` (原版 `YiNextCore`). 查签名用检索, 不整篇读大文件.

#### 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiCompatDl` (模块名 `OCF.Lean.YiCompatDl…`). 都是验收文件, 文首标 "验收文件". 中文 literate Agda (`.lagda.md`). 不改任何已有文件 (包括 A 的 `YiCross*`), 不碰 `src/`, `archive/`.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞 (写入文件时也不要留洞), `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提.
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由. 一次性的试验放你的临时目录, 用纯 `.agda` (选项行要加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 堆墙多出在比较具体闭项的地方: 陈述逐字写, 不用别名; 大参照树放 `opaque`; 经非单射的头求解的隐式参数显式写出 (手册第 4 节).
- 仓库文件里不写本机路径. 不要把仓库整个拷到临时目录.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G (A 也在编译). 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽. 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要删或重编 A 的模块.
- 你的临时目录: `<实验目录>/agents/compatneg`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- **停下的条件**: 同一处两次重新设计仍过不了检查器; 需要函数外延或 K; 堆到 6G 仍耗尽 (先按手册 §4.2). 没有编译的否定时只写 "未走通".
- 过程要求: 读完上面的文件后尽快动手, 第一个文件在 25 分钟内写出并编译; 每次回复都要有工具调用, 不要在一次回复里只思考.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 回报格式 (只在回报里交一次)

1. 判决: 第 1 步是正还是负 (或未走通); 一段话说对目标意味着什么 (`dl` 在规范域上能否给跨层单调; 若不能, 错位在哪个位置, 是不是真损失).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断); 否定定理的每个前提给实例.
4. 办法; 反例对象是否在规范读回域内.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 中途消息（主审发给这一路）

转录时间戳 2026-11-13 02:36 (UTC)：

主审转告: 接口 YiCrossIface 在你派出前后被 A 改了一处并重新定稿 (A 说全链冷编 0), 请按现在磁盘上的文件建, 若你已读过旧版请重读这两处: (1) `TopR` 在 Ω 结点层号上的一行, 原来是 "下标层相等 × 顶相关 × 一切相关合法下标上分支层的顶相关", 现在只留前两项 (A 说原第三项使 tw 2 的顶不自相关, 以 tw 2 为目标层的配置进不了任何 Compat); (2) `Compat` 的字段 `c-pts` 换成 `c-obs` (两边第 n 个链点那一支的顶相关). 其余不变. 若你已有文件因此编译失败, 按新接口改你自己的文件即可, 不改接口.

## 回报原文

#### A¬ 回报 (前缀 `YiCompatDl`, 按 11-13 重新定稿后的 `YiCrossIface` 建; 我的文件只用到 `c-LΩ`, `c-Ll`, `c-Rl`, `c-cmp`, `c-way`, `TopR` 和 `c-obs` 的改动对它们没有影响)

##### 1. 判决

第 1 步是负的, 有编译定理, 无前提。

- **对 `dl`**: 任何 `S : Compat dl` 都不含下列配置对, 外部派发任意 (含 `λ _ → fold`):
  - 塔的任意两项 `(Lw-tw (2+n), Lw-tw (2+j))`, 包括相邻项和自身;
  - `(Lw-tw (2+n), VΛ)`;
  - `(VΛ, VΛ)`。

  所以在规范读回域上, `dl` 经这个接口给不出跨层单调。
- **对一切派发 `D`**: `Compat D` 只要含上面任一配置对, 就推出 LPO (`YiCompatDlLPO`)。所以问题不在 `dl` 本身: 接口的封闭律逼出了一个完全的派发, 触及壁垒。

**错位的位置。**
- 左边: 沿 `c-LΩ` 进 `tw 2` 型的支 `ω+2`, 公共上界是结构的 `ws (ws _)`。
- `c-cmp` 用的一对位置 (层号 ω+1): 左边 `inj₁ tt`, 右边 `r₃ = (1, tt, (ω+2, _, inj₁ tt))`。
- `c-way` 用的一对位置 (层号 ω): 左边 `inj₂ (inj₁ tt)`, 右边 `q₃ = (1, tt, (ω+2, _, inj₂ (inj₁ tt)))`, 都在 `tw 3` 的顶层。
- 结果是左边结构派发保留, 右边 `dl` 折叠, 两者不满足 `WayR` (`mis`)。

**是不是真损失 (第 2 步)。**
- 在内层 ω+1 上是真的: 相关的输入 (`sim-in`) 给出不相关的输出 (`not-out`, 编译定理)。方向正是 `MonoH` 要的方向。
  - 折叠的输出与 `top` 互相 `Simʰ`;
  - 保留的输出严格在 `top` 之上 (`top-below`)。
  - 所以 `MonoH` 的结论在 `c-LΩ` 强迫进入每个 `Compat` 的那个内层配置上确实为假, 排除这个配置不是 `c-way` 写得太严。
- 在第 0 层没有找到损失: 一对外层输入的内层链经过这个配置, 两边分支取常值, 第 0 层的输出逐字相等 (`eq0`, 有限测试)。第 0 层的值上不相关的输入没有找到。
- 读法 (判断): 这是接口归纳假设一层的数学障碍, 没有显示成最终序数值的损失。

**判断 (未编译, 可修订)。** 修补不能靠换派发 (LPO 定理对一切 `D` 成立)。可以考虑两个方向, 给作者定:
- 改接口: 不让 `c-LΩ` 单边下降, 或让 `nN`/`c-cmp` 的位置对带字面公共上界的证据, 不只是层号相等;
- 改折叠: 让嵌入支里的内层派发与顶层对应位置上的 `D` 一致。

第 3 步 `KeepRow` 没有做: 没有 `S` 含这些配置对, 在这个域上它是空的。

##### 2. 文件表

三个文件都放在 `probes/OCF/Lean/`, 都是验收文件。删除自己的接口后依次冷编译, 退出码都是 0, 每个日志只有本模块一行 `Checking`, 每个约 2 秒。

| 文件 | 代码行 / 总行 | 退出码 | 常驻内存峰值 |
|---|---|---|---|
| `YiCompatDlNeg.lagda.md` | 135 / 207 | 0 | 425 MB |
| `YiCompatDlLPO.lagda.md` | 108 / 162 | 0 | 434 MB |
| `YiCompatDlLoss.lagda.md` | 61 / 113 | 0 | 402 MB |

检索 `postulate`, `TERMINATING`, `NO_POSITIVITY`, `trustMe`, 洞, `--irrelevant-projections`, `--cubical`, 本机路径, 结果都是 0。

##### 3. 定理表

`Neg` 第 4 节在 `module _ (S : Compat dl)` 内, `LPO` 第 3 节在 `module _ (D : ∀ k K → Ext k K) (S : Compat D)` 内, 所以这些定理的外层前提就是 `S`, `LPO` 文件里还有 `D`。

| 名字 | 陈述 (逐字) | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `no-tw` | `∀ n j {m m′} {x : Ext m (tw (suc (suc n)))} {x′ : Ext m′ (tw (suc (suc j)))} → C (Lw-tw (suc (suc n))) x (Lw-tw (suc (suc j))) x′ → ⊥` | 塔的任意两项不能成配置对 | Neg | 编译定理 |
| `no-Λ` | `∀ n {m m′} {x : Ext m (tw (suc (suc n)))} {x′ : Ext m′ Λ} → C (Lw-tw (suc (suc n))) x VΛ x′ → ⊥` | 塔项对 Λ 不能成配置对 | Neg | 编译定理 |
| `no-ΛΛ` | `∀ {m m′} {x : Ext m Λ} {x′ : Ext m′ Λ} → C VΛ x VΛ x′ → ⊥` | Λ 对自身也不行 | Neg | 编译定理 |
| `kill` | `∀ {K} {V : Lw K} {K′} {V′ : Lw K′} → PR V → PR V′ → IsWΩ V′ → ∀ {m} {x : Ext m K} {m′} {x′ : Ext m′ K′} → C V x V′ x′ → ⊥` | 两边都能沿支走到 `tw 2` 型、右边顶层是 `wΩ` 时排除 | Neg | 编译定理 |
| `core` | `∀ {m} {y : Ext m (tw 2)} {K′} {V′ : Lw K′} {m′} {x′ : Ext m′ K′} → IsWΩ V′ → (r′ q′ : Pre K′) → lev K′ r′ ≡ suc Ωω → lev K′ q′ ≡ Ωω → C (Lw-tw 2) y V′ x′ → ⊥` | 错位的核心论证 | Neg | 编译定理 |
| `mis` | `WayR (cmpw (lgl→Lw zero tt w0 ω2 ωR-lgl) (inj₁ tt) (inj₂ (inj₁ tt))) (cmpw (Lw-tw 3) r₃ q₃) → ⊥` | 相邻项上错位的那一对派发 | Neg | 编译定理 |
| `left-keep` | `cmpw (lgl→Lw zero tt w0 ω2 ωR-lgl) (inj₁ tt) (inj₂ (inj₁ tt)) ≡ keep (inj₁ tt) refl` | 左边保留 | Neg | 有限测试 (`refl`) |
| `right-fold` | `cmpw (Lw-tw 3) r₃ q₃ ≡ fold` | 右边折叠 | Neg | 有限测试 (`refl`) |
| `S∅` | `Compat dl` | 空族实例 | Neg | 编译 |
| `lpo-tw` | `∀ n j {m m′} {x : Ext m (tw (suc (suc n)))} {x′ : Ext m′ (tw (suc (suc j)))} → C (Lw-tw (suc (suc n))) x (Lw-tw (suc (suc j))) x′ → LPO` | 对任意 `D`, 含塔的配置对就推出 LPO | LPO | 编译定理 |
| `lpo-Λ` | `∀ n {m m′} {x : Ext m (tw (suc (suc n)))} {x′ : Ext m′ Λ} → C (Lw-tw (suc (suc n))) x VΛ x′ → LPO` | 塔项对 Λ 同上 | LPO | 编译定理 |
| `lpo-ΛΛ` | `∀ {m m′} {x : Ext m Λ} {x′ : Ext m′ Λ} → C VΛ x VΛ x′ → LPO` | Λ 对自身同上 | LPO | 编译定理 |
| `base` | `(t : (ℕ → Bool) → Pre K′) → (∀ α → lev K′ (t α) ≡ Tβ α) → (r′ : Pre K′) → lev K′ r′ ≡ Ωω → C (Lw-tw 2) y V′ x′ → LPO` | 核心: 逼右边的派发判定 α | LPO | 编译定理 |
| `strict` | `∀ α n → Dn zero (hα α n) (hα α (suc n))` | 探针序列严格递增, 不退化 | LPO | 编译定理 |
| `sim-in` | `Simʰ (suc (suc Ωω)) (tw 3) ξL ξR` | 错位配置上输入相关 | Loss | 编译定理 |
| `not-out` | `Simʰ (suc Ωω) (suc Ωω) (Ψ (suc Ωω) VL (cmpw VL (inj₁ tt)) ξL) (Ψ (suc Ωω) (Lw-tw 3) (cmpw (Lw-tw 3) r₃) ξR) → ⊥` | 输出不相关 | Loss | 编译定理 |
| `rev-out` | 与 `not-out` 两端互换的 `Simʰ` | 反方向相关 | Loss | 编译定理 |
| `R⊑top`, `top⊑R` | 右边输出与 `G.top` 两个方向的 `Simʰ` | 折叠输出与 `top` 互相 `Simʰ` | Loss | 编译定理 |
| `top-below` | `Dn (suc Ωω) G.top (Ψ (suc Ωω) VL (cmpw VL (inj₁ tt)) ξL)` | `top` 是保留输出的严格第一位置 | Loss | 编译定理 |
| `swap-ok` | 互换左右 (左边 `Lw-tw 2` 用 `dl` 折叠, 右边结构派发保留) 后输出的 `Simʰ` | 左折叠右保留时这一对仍相关 | Loss | 有限测试 |
| `sim₀` | `Simʰ (tw 2) (tw 3) ξ₀ ξ₀′` | 外层一对输入相关 | Loss | 编译定理 |
| `eq0` | `Ψ zero (Lw-tw 2) (λ _ → fold) ξ₀ ≡ Ψ zero (Lw-tw 3) (λ _ → fold) ξ₀′` | 常值分支时第 0 层输出相等 | Loss | 有限测试 |

**前提的实例。**
- `S : Compat dl`: 用 `S∅` (空族, 编译)。A 的 `YiCrossInst.Zero.S₀ D` 是非空实例, 我没有导入。
- 外部派发 `x`, `x′`: 取 `λ _ → fold`。
- LPO 定理里的 `D`: 取 `dl`。
- 配置对属于 `C`: 这正是被否定的那一条。
- 判断: LPO 在 `--safe` 下不可证 (仓库惯例), 所以 LPO 版读作 "推出 LPO", 和 `cmp-full→lpo` 同一档。

##### 4. 办法; 反例对象在不在规范读回域内

**`dl` 的论证。**
1. 沿 `PR` 路径走: 塔的第 2+n 项沿第 1 支走 n 步到 `Lw-tw 2`, 由 `lift` 对 n 归纳给出。
2. 用 `c-LΩ` 进支 `ω+2`。
3. `c-cmp` 取层号 ω+1 的一对位置, 顶相关由新写的 `ʰ→Q`, `ʰ→P` 从层号得到 (是 `P→ʰ` 的逆)。
4. `c-way` 取层号 ω 的一对位置: 左边 `cmpw (ws _) (inj₁ tt) (inj₂ _) = keep`, 右边 `cmpw (wΩ …) = dl`, 由 `dl-lim` 得折叠, 与 `WayR` 矛盾。

**LPO 版。** 同样的路径, 改进支 `suc (lim (hα α))`。`hα α` 在 α 遇到真值后从 n 跳到 ω+n+2, 所以 `Tβ α` 有层号 ω 的槽位当且仅当 α 有真值。`c-way` 逼右边的 `D (Tβ α) _` 在有真值时保留, 于是判定 α。

**是否在规范读回域内: 是。**
- 配置对就是 `Lw-tw`, `VΛ`。
- 走过的支是 1, ω+2, `suc (lim (hα α))`, 都是合法树, 极限严格递增 (`strict`), 不用退化结点。
- 支上的公共上界都是 `lgl→Lw` / `Lw-Ω̂` 的规范读回。
- 判断: 起作用的量化来自接口自己的律: `c-LΩ` 让左边单边进支而右边留在顶层, `c-cmp`/`c-way` 只凭层号相等配对位置, 位置对之间没有字面公共上界。

##### 5. 第一个障碍

第 2 步在第 0 层没有走通 (未走通, 不是否定)。缺的引理:

```agda
Σ (Raw (tw 2)) λ ξ₀ → Σ (Raw (tw 3)) λ ξ₀′ → Simʰ (tw 2) (tw 3) ξ₀ ξ₀′ ×
  (Simʰ zero zero (Ψ zero (Lw-tw 2) (λ _ → fold) ξ₀) (Ψ zero (Lw-tw 3) (λ _ → fold) ξ₀′) → ⊥)
```

或者同一对输入在 `NA.read` 上 `≼` 不成立。分支是常值时两边相等 (`eq0`)。判断: 需要分支依赖 Ω_ω 下标; 那时两边输出是 ψ 塌缩的大树, 比较要序数分析, 本路没有做。没有检查器报错。

##### 6. 偏离与事故

- 派出前后接口改过一次, 我按磁盘上的现行版本重读并建文件, 没有编译失败。
- 除接口外只导入了非 A 的模块: `YiDlFold`, `YiDlLost`, `YiUniNegBase`, `YiUniIf`, `YiNextTower`, `YiLamFold`。没有导入 `YiCrossMono` 或 `YiCrossInst`。
- 只新建了这三个文件, 删除接口时只删了它们自己的 `.agdai`。日志在 `<实验目录>/agents/compatneg/`。
- 没有提交。
