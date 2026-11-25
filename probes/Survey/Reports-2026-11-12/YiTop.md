# F3 规范域内的 E2 与 F2 去掉 Pos (YiTop)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-13 06:37 至 07:17 |
| 工具调用 / agda 编译 (粗数) | 65 / 21 |
| token (usage 字段，按消息去重) | 输出 259192；新写入缓存的输入 473767；读缓存的输入 13915781；其余输入 120 |
| 写过的仓库文件 | `YiTopBlock.lagda.md`, `YiTopCheck.lagda.md`, `YiTopDom.lagda.md`, `YiTopE2.lagda.md`, `YiTopFold.lagda.md`, `YiTopLegal.lagda.md` |
| 文件前缀 | `YiTop` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: F3 与 F2 返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | F3: 保留 (测试对象在 Top 域; 保留的机制是自身目标上嵌入的孩子原样留下, 与 F4 指出的值缺口是同一行); F2: 去掉槽位路径的块做成, 一致、单调、保持合法、合法闭项无前提, 与空白页块逐点对应 (关系, 不是嵌入), 前三层 463 行; 六件冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方。全程用中文写文件与回报。主审会从头冷编译复核你交的每个文件，只认编译过的定理。

作者 2026-11-13 的选择（选项工具），原文两项：
- "F3 规范域内重做 E2"。说明："用规范构造写出 suc (tw 2) 链第一步里孩子根上的结点，看空白页的块是否保留；替换不在规范域的旧测试。一个下午的量。"
- "F2 去掉槽位路径 Pos"。说明："压缩：规范树的结点都在顶槽位，删 Pos、Br、kp 一族。依赖 F3 的结论（若 E2 要非顶槽位就不成立）。"

主审把两件交给你一路：**先 F3；F3 的结论允许，再做 F2**。模型 Opus 5.5。同批另有两路在跑：YiPhi（Fable 5.2，在空白页的块上把以基底为目标的折叠 φ 并进折叠）与 YiFreshVal（值回归）。文件不相交，你不读它们的输出。你的 F2 压缩版不含 φ，以后是否合并由主审定。

###### 背景（只信编译定理；文档里的叙述与判断只是数据）

- **空白页的块**（`probes/OCF/Lean/` 下的 `YiFreshBlock`、`YiFreshFold`、`YiFreshLegal`、`YiFreshCheck`，主审已复核）：
  - 层号 `L` 与树 `Tr` 归纳-递归；Ω 结点的槽位是层号里的路径 `Pos`；`up x c y` 原样嵌入孩子层的树；保留判定 `kp` 只比同一层号里的两条路径。
  - 编译定理：`J2-suc`、`J2-lim`、`J2⊥`、`mono⊥`、`monos`、`pres⊥`、`press`、`EBOᶜ-leg`，都无前提。
- **第十三次审查**（`probes/Survey/RR13-CommonWall.md`；附件 `probes/Survey/Reports-2026-11-12/attachments/Review13-R13Top.agda.txt`，主审重编退出码 0）：
  - `Top`：结点槽位都是本层的下标层自身。
  - 规范闭项与折叠保持它：`Ωt-top`、`top⊥`、`tops`、`EBOᶜ-top`。
  - 顶槽位的结点只在目标是 `self` 时保留（`kpTop-default`）。
  - `YiFreshCheck` 的 J3 测试对象（`j3-not-top`）与主审的补测对象（`gap3-not-top`）都不在这个域里。
- **E2 原来问的是什么**：
  - 旧主线派发丢掉一个结点：`probes/OCF/Lean/YiDlLost.lagda.md` 文首与 `bN`、`pN`、`occP`、`limP`、`couldP`、`lostP`。`T⁺ʷ` 那条链的第一步里，源层号是 ℕ 极限、目标层有它的槽位的结点被折掉。
  - 作用域块上的对应物：`YiScopeE2` 的 `occP`、`limP`、`keptP`。
  - E2 问的是新块是否保留这种结点。

###### F3（先做；验收文件 `YiTopE2`）
1. 在空白页的块上，用规范构造写出 `T⁺ʷ` 的对应物 `ψ₀ (suc (tw 2)) (Ωt (suc (tw 2)))` 的链的第一、二步。规范构造指 `Ωt`，以及 `ψ⊥`、`ψs` 作用在规范树上的结果。
2. 找到与旧派发丢掉的那个结点对应的结点：源层号是 ℕ 极限一类、目标层有它的场合，例如审查者说的 "链第一步里孩子 ξ 根上的那个结点"。用有限测试（`refl`）判断它是否保留；能做的话，tw 3 的对应情形也测。
3. 写出测试对象在 `Top` 域内的证明。可以把附件 `R13Top` 的定义搬进你的文件，改成 literate；要导入的话，只能导入仓库模块。
4. **判决写在文首**：保留、不保留、做不出，或 "规范域里没有这种结点"（要非顶槽位才出现）。做完**立刻**用 SendMessage 给 `main` 发一行：判决加文件名。
5. 判决是 "不保留"、"做不出"，或 "规范域里没有这种结点而又需要非顶槽位" 时，停下交回报，不做 F2。

###### F2（F3 判决为 "保留"，且测试对象都在顶槽位时做；新文件，成品候选）
1. `YiTopBlock`、`YiTopFold`、`YiTopLegal`：去掉 `Pos`、`Br`、`at`、`fromBr`、`toBr`、`kp` 一族。Ω 结点只在顶槽位，分支是本层下标层的树；折叠在目标路径是 `self` 时保留，其余照空白页的折叠。
2. 重证 `J2-suc`、`J2-lim`、`J2⊥` 的对应物，单调，保持合法，以及读法 ψ₀(Λ) 的闭项合法，都无前提。
3. 验收文件 `YiTopCheck`：一条从 YiTop 的树到空白页的树的嵌入，并证它与折叠交换（至少对 `ψ⊥`，能做到 `ψs` 更好），说明压缩没有改变折叠。做不到时如实写。
4. 行数对比：前三层各多少。口径：代码块里非空、非注释的行，含模块头与导入。空白页原块是 102、124、312。

###### 先读什么
- `AGENTS.md` 全篇。
- 空白页四个文件全读。
- 附件 `Review13-R13Top.agda.txt` 全读。
- `probes/Survey/RR13-CommonWall.md`。
- `YiDlLost.lagda.md` 文首与 `bN` 附近（检索）；`YiScopeE2.lagda.md` 文首。
- `probes/Survey/EBOHandbook.md` §4.1 到 §4.5。

查签名用检索，不整篇读大文件。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiTop`（模块名 `OCF.Lean.YiTop…`）。不改任何已有文件，不碰 `src/`、`archive/`。
- 块、折叠、合法性的文件是成品候选：不导入记号、参照框架与旧块（可以导入 `YiFresh*`），用 `python3 probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 检查，退出码 0 才算干净。验收文件文首标 "验收文件"。
- 中文 literate Agda（`.lagda.md`）。每个模块文首不超过 5 行；代码之间的文字只写范围与不显然的定义理由。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。无关参数可以用。函数外延只准作验收文件里的显式前提。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 6G（另两路也在编译）。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。日志落文件，只看首个错误附近。
  - 不用 `--ignore-interfaces`。要冷编译只删你自己模块的接口（`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`），写字面的精确路径，不用通配，不用变量拼路径。
  - 大的规范树放 `opaque`，陈述逐字写（手册 §4）。
- 临时目录：`<实验目录>/agents/top`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不写 `/tmp` 的别处，不装包，不提交，不推送。
- **停下的条件**：F3 判决不允许 F2；同一处两次重新设计仍过不了检查器；需要函数外延或 K；6G 仍耗尽。没有编译的否定时只写 "未走通"。
- **过程要求**：读完上面的文件后尽快动手，第一个文件在 30 分钟内写出并编译；每次回复都要有工具调用，不要在一次回复里只思考。
- **结束前自查**：每个文件删自己的接口后冷编译，退出码 0，日志里只有你自己模块的 `Checking` 行；检索禁用构造为 0；成品候选的 importclosure 退出码 0。

###### 回报格式（只在回报里交一次）
1. 判决：F3 的结果（保留与否，测试对象在不在 `Top` 域）；F2 做到哪里；一段话说对目标意味着什么。
2. 文件表：文件、代码行数、冷编译退出码、常驻内存峰值、是否成品候选（importclosure 结果）。
3. 定理表：名字、逐字的陈述、一句白话、文件、档（编译定理 / 有限测试 / 判断）。
4. 办法：F3 找的是哪个结点、为什么它是旧派发丢掉那个的对应物；F2 删了什么，折叠哪几行变了。
5. 第一个障碍：精确到引理，附检查器报错原文（若有）。
6. 偏离与事故。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 1 判决

**F3: 保留.** 旧派发丢掉的那类结点, 在空白页的块的规范构造里保留, 测试对象都在 `Top` 域 (只用顶槽位). tw 3 同样保留. 已按简报用 SendMessage 给 main 发了一行 (判决 + `YiTopE2`).
- 依据分三档:
  - 编译定理 `keep-suc`: 后继层号结点的链步, 源里的一切结点都原样保留.
  - 有限测试: `ψ₀ (suc (tw 2)) (Ωt (suc (tw 2)))` 里的具体结点, 见 `occP`, `limP`, `couldP`, `keptP`, `kept-branch`; tw 3 的同名测试带 `³`.
  - Top 域证明: `*-top`.
- 对照 (有限测试): 同样条件的结点 (下标层为 ℕ 极限, 目标层有它的槽位) 也出现在 k 侧, 即 `Ωₗ` 层号根结点的链步里. 那里它随整个孩子被折到第 0 层 (`occK`, `couldK`, `stepK`, `ι-noΩ`), 是第十三次审查已知的 k 侧回退, 不在旧派发丢结点的那个位置上.
  - 判断: 要在 k 侧保留这种结点, 最直接的写法是用非顶槽位. 若以后 F1 (φ) 那样做, F2 的块写不出这种结点. 这条风险没有编译结论.

**F2: 做完.** 文件 `YiTopBlock`, `YiTopFold`, `YiTopLegal`, `YiTopCheck`, 全部冷编译通过, 都无前提.
- 删掉了 `Pos`, `Br`, `at`, `fromBr`, `toBr`, `kp`, `posW`, `legFrom`, `Good`, `kp-ind`.
- 重证了 J2 的对应物, 单调, 保持合法, 以及读法 ψ₀(Λ) 的闭项 `EBOᶜ` 合法.
- `YiTopCheck` 证了 YiTop 与空白页之间的一个**对应关系 (不是函数嵌入)**: 它对 `ψ⊥` 与 `ψs` 都保持, 塔, Λ, Ω 树和 `EBOᶜ` 都相互对应.

**对目标意味着什么.** 在规范域上, 空白页的块不会重犯旧派发丢结点的错误. 机制来自树侧结构: 后继孩子的链步经 J2-suc 进入孩子层, 目标是 self, `up` 原样保留. 规范树只需要顶槽位 (`Top` 不变量, 编译事实), 由此逼出 F2 的压缩, 前三层少 75 行 (−14%). 这是纯压缩, 没有新增来自记号的规则, 翻译账上是零. 尚开着的是 k 侧回退 (F1/YiPhi 的对象); 那里若需要非顶槽位, 会与 F2 冲突 (判断).

#### 2 文件表

行数口径: 代码块里非空, 非注释的行, 含模块头与导入; 用同一脚本复算空白页原块, 得 102/124/312, 与简报一致. 内存列是 `+RTS -s` 报的 "total memory in use", 不是严格的常驻内存峰值, 原因见 §6.

| 文件 (`probes/OCF/Lean/`) | 行数 | 冷编译退出码 | 内存 | 成品候选 / importclosure |
|---|---|---|---|---|
| `YiTopBlock.lagda.md` | 69 (原 102) | 0 | 232 MiB | 是, 0 (闭包本地 1) |
| `YiTopFold.lagda.md` | 101 (原 124) | 0 | 235 MiB | 是, 0 (本地 2) |
| `YiTopLegal.lagda.md` | 293 (原 312) | 0 | 508 MiB | 是, 0 (本地 3) |
| `YiTopCheck.lagda.md` | 264 | 0 | 1229 MiB | 验收文件, 0 |
| `YiTopE2.lagda.md` | 189 | 0 | 293 MiB | 验收文件, 0 |
| `YiTopDom.lagda.md` | 142 | 0 | 364 MiB | 验收文件 (搬自 R13Top), 0 |

- 前三层合计 463 行, 原块 538 行.
- 冷编译: 只删了自己六个模块的 `.agdai`, 每个文件单独编译; 日志里没有 YiTop 以外的 `Checking` 行.
- 禁用构造检索结果为 0: postulate, TERMINATING, NO_POSITIVITY, trustMe, 洞, K, `--cubical`, funext, 本机路径都没有. 唯一的编译指示是 OPTIONS 行 `--safe --without-K --lossy-unification`.

#### 3 定理表

全部是编译定理或有限测试, 无前提. 陈述逐字.

**`YiTopE2` (验收)**

| 名字 | 陈述 | 白话 | 档 |
|---|---|---|---|
| `keep-self` | `(ℓ : L) (B : Base ℓ) (t : Tr ℓ) {m : L} {q : Pos m} → Node ℓ t m q → Node ℓ (ψs ℓ B ℓ self t) m q` | 目标是 self 时, 树里一切结点 (含嵌入孩子里的) 都在输出里 | 编译定理 |
| `keep-suc` | `(a : L) (B : Base (suc a)) (x : Tr (suc a)) (y : Tr a) {m : L} {q : Pos m} → Node a y m q → Node a (ψs (suc a) B a (ins self) (up x tt y)) m q` | 后继层号结点的链步保留源里的一切结点 | 编译定理 |
| `ι-noΩ` | `(j : L) (a : Tr zero) {m : L} {q : Pos m} {g : Br m q → Tr m} → Occ j (ι j a) m (Ω q g) → ⊥` | ι 的像里没有任何结点 | 编译定理 |
| `T⁺-form` | `ψ₀ (suc (tw 2)) (Ωt (suc (tw 2))) ≡ lim (cum (λ n → ψ⊥ (suc (tw 2)) (B₀ _) (up zero tt (suc (γ n)))))` | 外层链的形状 | 有限测试 |
| `γ-1`, `γ-2` | `γ 1 ≡ next (Ωt (tw 2))`; `γ 2 ≡ next (ψs (tw 2) (B₀ _) (tw 2) self (γ 1))` | 外层链的第一, 二步 | 有限测试 |
| `γ₁₀`, `fold-Ωt₂` | `cp 0 (γ 1) ≡ Ωt (tw 2)`; `ψ⊥ (tw 2) (B₀ _) (Ωt (tw 2)) ≡ lim (cum (λ m → ψ⊥ (h₁ (δ m)) (dW (tw 1) h₁ (B₀ _) (δ m) zero) (Ωt (h₁ (δ m)))))` | γ₁ 的第 0 分量, 以及它根结点的链 δ | 有限测试 |
| `δ-1`, `lvN` | `δ 1 ≡ Ωt (tw 1) + ι (tw 1) Tw₁`; `g₂ 0 ≡ suc LN` | δ₁ 处的孩子沿 0, 0 分量是后继层号 | 有限测试 |
| `reach` | `cp 0 (cp 0 (ψ⊥ (tw 2) (B₀ _) (G0 (δ 1)))) ≡ ψ⊥ (suc LN) BN (Ωt (suc LN))` | 折叠真的走到孩子根上的结点 N, 底就是 BN | 有限测试 |
| `N-fold`, `η-1`, `η-2` | `ψ⊥ (suc LN) BN (Ωt (suc LN)) ≡ lim (cum (λ n → ψ⊥ (suc LN) BN (up zero tt (suc (η n)))))`; `η 1 ≡ next (Ωt LN)`; `η 2 ≡ next (ψs LN (dS LN BN zero) LN self (next (Ωt LN)))` | N 的链与它的前两步 | 有限测试 |
| `occP` | `Node (suc LN) (up zero tt (suc (η 1))) (chL LN c₀) (inj₁ (inj₁ tt))` | 第二步的源里有这个结点 | 有限测试 |
| `limP` | `Σ (ℕ → L) λ f → at (chL LN c₀) (inj₁ (inj₁ tt)) ≡ lim f` | 它的下标层是 ℕ 极限 | 有限测试 |
| `couldP` | `Σ (Pos LN) λ p → at LN p ≡ at (chL LN c₀) (inj₁ (inj₁ tt))` | 目标层 LN 有它的槽位 | 有限测试 |
| `keptP`, `kept-branch` | `Node LN (η 2) (chL LN c₀) (inj₁ (inj₁ tt))`; `proj₁ keptP ≡ proj₁ occP` | 输出里有它, 分支与源里相同 | 有限测试 |
| `occK`, `couldK`, `stepK` | `Node (tw 2) (G0 (δ 1)) (chL LN c₀) (inj₁ (inj₁ tt))`; `Σ (Pos (tw 1)) λ p → at (tw 1) p ≡ at (chL LN c₀) (inj₁ (inj₁ tt))`; `st0 (δ 1) ≡ Ωt (tw 1) + ι (tw 1) (ψ₀ (h₁ (δ 1)) (Ωt (h₁ (δ 1))))` | k 侧: 同一结点在源里, tw 1 有它的槽位, 链步把整个孩子折到第 0 层 | 有限测试 |
| `γ-top`, `δ-top`, `BN-top`, `η-top`, `src-top`, `node-top`, `srcK-top` | 例 `(n : ℕ) → Top LN (η n)`, `Top (suc LN) (up zero tt (suc (η 1)))` | 测试对象都在 Top 域 | 编译定理 |
| tw 3 一组 | `lvN³ : g₃³ 0 ≡ suc LN³`; `reach³ : cp 0 (cp 0 (cp 0 (ψ⊥ (tw 3) (B₀ _) (G0³ (δ³ 1))))) ≡ ψ⊥ (suc LN³) BN³ (Ωt (suc LN³))`; `occP³`, `limP³`, `couldP³`, `keptP³`, `kept-branch³` (与上面同形, 名字带 ³); `src³-top` | tw 3 同样保留 | 有限测试 / Top 证明 |

`YiTopDom` 是 `R13Top` 的原样搬移: `Top`, `Ωt-top`, `top⊥`, `tops`, `kpTop-default`, `EBOᶜ-top`, `gap3-not-top`, `j3-not-top`, 编译定理.

**`YiTopLegal` (成品候选)**

| 名字 | 陈述 | 白话 |
|---|---|---|
| `mono⊥` | `(ℓ : L) (B : Base ℓ) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → zero ⊢ ψ⊥ ℓ B x ◃ ψ⊥ ℓ B y` | 到第 0 层的折叠单调 |
| `monos` | `(ℓ : L) (B : Base ℓ) (j : L) (v : j ≤ ℓ) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → j ⊢ ψs ℓ B j v x ◃ ψs ℓ B j v y` | 带目标的折叠单调 |
| `pres⊥` | `(ℓ : L) (B : Base ℓ) → LegB ℓ B → (x : Tr ℓ) → Leg ℓ x → LN zero (ψ⊥ ℓ B x)` | 折叠保持合法且非零 |
| `press` | `(ℓ : L) (B : Base ℓ) → LegB ℓ B → (j : L) (v : j ≤ ℓ) (x : Tr ℓ) → Leg ℓ x → LN j (ψs ℓ B j v x)` | 同上, 带目标 |
| `tw-leg`, `Λ-leg`, `EBOᶜ-leg` | `(n : ℕ) → LegL (tw n)`; `LegL Λ`; `Leg zero EBOᶜ` | 塔, Λ, ψ₀(Λ) 的闭项合法 |

**`YiTopCheck` (验收)**

| 名字 | 陈述 | 白话 |
|---|---|---|
| `J2-suc` | `(a : L) (B : Base (suc a)) (j : L) (w : j ≤ a) (x : Tr (suc a)) (y : Tr a) → ψs (suc a) B j (ins w) (up x tt y) ≡ ψs a (base (ψ⊥ (suc a) B x) (λ j′ w′ → ψs (suc a) B j′ (ins w′) x)) j w y` | J2, 后继层 |
| `J2-lim` | 同形, ℕ 极限层 | J2, ℕ 极限层 |
| `J2⊥` | `(ℓ : L) (B : Base ℓ) (x : Tr ℓ) (c : Ch ℓ) (y : ChT ℓ c) → Σ (Base (chL ℓ c)) λ B′ → (b⊥ B′ ≡ ψ⊥ ℓ B x) × (ψ⊥ ℓ B (up x c y) ≡ ψ⊥ (chL ℓ c) B′ (chT ℓ c y))` | 到第 0 层的 J2, 对一切层号 |
| `rel⊥` | `(ℓ : L) (ℓ′ : F.L) (r : Lr ℓ ℓ′) (B : Base ℓ) (B′ : G.Base ℓ′) → RelB ℓ ℓ′ r B B′ → (x : Tr ℓ) (x′ : F.Tr ℓ′) → Rel ℓ ℓ′ r x x′ → Rel zero F.zero refl (ψ⊥ ℓ B x) (G.ψ⊥ ℓ′ B′ x′)` | 对应的输入, ψ⊥ 给出对应的输出 |
| `rels` | `… → RelB ℓ ℓ′ r B B′ → {j : L} {j′ : F.L} {w : j ≤ ℓ} {w′ : j′ G.≤ ℓ′} {q : Lr j j′} → Wr r w w′ q → (x : Tr ℓ) (x′ : F.Tr ℓ′) → Rel ℓ ℓ′ r x x′ → Rel j j′ q (ψs ℓ B j w x) (G.ψs ℓ′ B′ j′ w′ x′)` | 同上, 对 ψs, 目标路径也对应 |
| `tw-rel`, `Λ-rel`, `Ωt-rel` | `(n : ℕ) → Lr (tw n) (F.tw n)`; `Lr Λ F.Λ`; `(ℓ : L) (ℓ′ : F.L) (r : Lr ℓ ℓ′) → Rel ℓ ℓ′ r (Ωt ℓ) (G.Ωt ℓ′)` | 塔, Λ, Ω 树对应 |
| `EBO-rel` | `Rel zero F.zero refl EBOᶜ GL.EBOᶜ` | 两边 ψ₀(Λ) 的闭项在第 0 层逐点相同 |

`Rel` 只把顶槽位结点对到空白页的顶槽位结点 (`inj₁ tt`, `inj₁ (inj₁ tt)`). 在第 0 层, `Rel` 按定义就是布劳威尔树的逐点相同.

#### 4 办法

**F3 找的是哪个结点.**
- 沿折叠实际走到的路径: 外层链 γ₁ = `next (Ωt (tw 2))` → 第 0 分量 `Ωt (tw 2)` → 它根结点的链 δ (在 tw 1 层) 的第 1 点 → 那里的孩子层号是 ℕ 极限 → 沿 0, 0 分量到后继层号 `suc LN`, 其中 `LN = tw 1 ⊕ ↑ (tw 1) (Ωt (tw 1))` → 根结点 N.
- N 的链在 LN 层. 第二步的源里含 `Ωt LN`; 在分支 `c₀ = suc ω₀` 的孩子 `chL LN c₀` 的根上, 有一个下标层为 ℕ 极限, 且是 LN 的槽位的结点.
- 为什么它是旧派发丢掉那个的对应物: 旧块 (`YiDlLost`) 与作用域块 (`YiScopeE2`) 里, 那个结点都在 "γ₁ 里, 孩子根上 (后继孩子层号) 的结点 N" 的链第一步的源里, 下标层是 ℕ 极限, 目标层 LN 有它的槽位. 两者的链从 Ω 树起; 空白页的链从 0 起, 第一步输出 `next (Ωt LN)` (底), 所以对应的源在第二步.
- 保留的机制: N 的链步是 J2-suc, 进入孩子层, 目标 self; 这时 `up` 原样保留, 孩子里的结点一个不丢. `keep-suc` 把这一点写成对一切后继层号结点的定理.

**F2 删了什么.**
- 块: 删 `Pos`, `Pos⁼`, `Br`, `Br⁼`, `at`, `at⁼`, `fromBr`, `fromBr⁼`, `toBr`, `toBr⁼`. 加 `Hd` (层号有没有顶槽位: 后继与 `Ωₗ` 为 ⊤) 与 `Bt` (分支类型, 即下标层的树). `T` 的结点从 `Ω : (p : P) → (B p → T) → T` 改成 `Ω : S → (B → T) → T`. `↑` 的 Ω 行按层号分两行.
- 折叠: 删 `kp`, `kp⁼`, `posW`, 以及两处 `where step`. 变了的行:
  - `ψ⊥ ℓ B (Ω s g)` 改用 `stp ℓ B s g` 与起点 `z₀ ℓ s`.
  - `ψs` 的 Ω 行拆成 `ψs ℓ B _ self (Ω s g) = Ω s (λ z → ψs ℓ B ℓ self (g z))` 与默认的链.
  - 新增 `stp` (后继层: `ins self`; `Ωₗ` 层: `ink self`) 与 `z₀`.
  - `Ωt` 的槽位 `inj₁ tt`, `inj₁ (inj₁ tt)` 换成证据 `tt`.
  - `up` 各行, 加法, 底, `eqℕ` 都没变.
- 合法性: 删 `legFrom`, `Good`, `kp-ind`. `LegBr` 换成 `LegI`. 新增 `z₀-leg`, `stp-leg`, `dfLN`. `monos` 与 `press` 的 Ω 行按目标路径拆开.

#### 5 第一个障碍

都已解决, 没有未走通的地方.
1. `YiTopLegal` 的 `monos`: 我写了一个兜底的 `monos ℓ B j v ◃w = ◃l zero`. 每个子句按自己写出的模式检查, 路径 v 不展开, 所以 `ψs` 不归约. 报错原文:
   `lim _f_420 != ψs ℓ B j v (Ω s g) of type T (Hd j) (Bt j) (Ch j) (ChT j) when checking that the expression ◃l zero has type j ⊢ ψs ℓ B j v (g (z₀ ℓ s)) ◃ ψs ℓ B j v (Ω s g)`
   改法: 把 `ins`, `ink`, `inb` 分开写, `inl` 写成荒谬子句.
2. 同一文件: 我把 `pres⊥ ℓ B hB` 作为高阶参数传给辅助引理 `chain-LN`. 报错原文:
   `Termination checking failed for the following functions: stp-leg, chain-LN, pres⊥, press`
   改法: 链的部分直接写进 `pres⊥` 的 Ω 行; `press` 的 Ω 行改用互递归的 `dfLN`, 它直接调用 `press` 本身.

#### 6 偏离与事故

- **多一个文件 `YiTopDom`**: 是 `R13Top` 的 literate 搬移, 验收文件, 前缀符合. 简报允许把 R13Top 的定义搬进我的文件, 我单列成文件, 由 `YiTopE2` 导入.
- **`YiTopCheck` 交的是关系, 不是函数嵌入**: 简报允许做不到时如实写. 理由 (判断, 没有编译): `Ωₗ k h` 的分支定义域 `Tr k → L` 在层号里是逆变的. 函数嵌入需要一个从空白页的树回到 YiTop 树的投影, 还要证这个投影是左逆, 而后者要用函数外延. 改用关系 `Lr`/`Rel`/`Wr`: 本块一侧按结构递归, 空白页一侧用等式给出头构造子, 不需要外延.
- **编号差异 (判断, 读定义)**: 作用域块的 `tw 2 = Ω̂ (sucᴸ zero)`, 根分支是第 0 层的树; 空白页的 `tw 1` 才是这样. 所以简报指定的 `ψ₀ (suc (tw 2)) …` 在塔里比作用域块的 `T⁺ʷ` 高一格. 我按简报做了 tw 2 与 tw 3, 没有做 `suc (tw 1)`.
- **内存口径**: `/usr/bin/time -l` 被沙箱拦下 (`sysctl kern.clockrate: Operation not permitted`), 表里的内存是 GHC `+RTS -s` 的 "total memory in use", 不是严格的常驻内存峰值.
- 探路用的 Agda 交互求值 (只在我的临时目录里) 打印过一行 `~/.agda/libraries` 的过期路径错误, 不影响编译.
- 试验文件都在 `<实验目录>/agents/top`. 没有改已有文件, 没有提交.
