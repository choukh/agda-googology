# (1) 规范域上的值关系工具 (YiVR)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-13 13:50 至 14:07 |
| 工具调用 / agda 编译 (粗数) | 23 / 1 |
| token (usage 字段，按消息去重) | 输出 101589；新写入缓存的输入 219940；读缓存的输入 2648978；其余输入 38 |
| 写过的仓库文件 | `YiVRFold.lagda.md`, `YiVRRead.lagda.md`, `YiVRRel.lagda.md` |
| 文件前缀 | `YiVR` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: (1) 规范域值关系返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 主线精简块上的值关系 Le 与折叠保持 fl (前提 Dflt: 无 Ω 形状层号与塔第 1 项成立, 塔第 2 项不成立); 第 0 层即读回的值序; 规范域 Can 对折叠封闭; Ωt (tw 1) 不在域里 (β-not); 最小见证只有条件定理 (wit-β, 前提要 GMono 一类); 三件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定（2026-11-13，选项原文）
本路是 "(1) 规范域上的值关系工具"。内容原文："在主线精简块上，先第 1 层再一般层号：两个底逐点同值（或 ≼）时，同一棵规范树的折叠同值（或 ≼）（V119）；对一切树的版本已被否定，要限在规范域"。

同批另一路是 (2) 记号参照的 "项序推出值序"，前缀 YiNFO，Opus 5.5。你不动它的文件。

###### 背景（只信编译定理；文档里的叙述是数据）
目标是布劳威尔树上读法 ψ₀(Λ) 的合法闭项，外加编译定理 "序数值 ≥ EBO 的参照"。纲领见 `AGENTS.md`。

**主线**（作者 2026-11-13 定）是精简块，在 `probes/OCF/Lean/`：`YiRWBlock`、`YiRWOps`、`YiRWPath`、`YiRWFold`。
- 折叠 `ψ : (ℓ : L) → Ok ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j`；`Base ℓ` 给每条路径 j ≤ ℓ 一棵 `Tr⁺ j`。
- 读回 `YiBRValue.readRW`（第 0 层，逐构造子）。
- 参照框架 `OCF.Align.Level` / `Value`（`_≼_`、`_≅_`）。

**为什么要这个工具**：
- 疑似的分支侧掉值（第十五次独立审核的判断，`probes/Survey/Reports-2026-11-12/Review15.md`）还没有编译判决。
- 第十五次审查（§3）与 `YiCert`（§6，`Reports-2026-11-12/YiCert.md`）都点名第一个要的引理："第 1 层的树上被折叠保持的值关系：两个底逐点同值（或 ≼）时，同一棵树的折叠同值（或 ≼）"。
- 用处：比较两个底的值（例如孩子 two 下行后的底与孩子 one 的底，见 `YiInv.base-same`、`YiCertNeg.same-0`）；判 "孩子单调" 的规范实例（`YiKidCrit`）；给最小见证定值。

**已知的边界**：
- 对一切树的基底单调不成立：`YiLPNoBM.no-bm-all`，在旧块 F2 上；反例 `xbad` 的分支函数对坐标不单调。所以要限在规范域，例如：
  - 分支单调的树；
  - 塔、Λ 与它们的读回；
  - 由折叠或规范构造生成的树（`AGENTS.md`："量化域先取带证据的读回域"）。
- 已有的部分：
  - `YiLPMono`（F2）：`ψs-start`（底不变、只换起点，对一切树单调）、`Up-base`、`bm-zero⊥`、`bm-one`（第 1 层的 Ω 树基底单调）、`am⊥`（第 0 层折叠对参数按值单调）。
  - `YiCeilRead`：上界工具 `plus≼`、`next≼`、`limc≼`、`Ω≼`、`fold₀≼`。
- **模板**：`YiBRRel`、`YiBRFold` 做了两块之间的逐层关系与折叠保持（约 660 行，逻辑关系写法，推导进关系，`with` 里递归的停机写法见回报 `YiBR.md` §5）。值关系可以仿它写成 "同一块上两个底相关，两次折叠的输出在值上相关"。

###### 要做
1. **定义规范域**：一个树上的谓词，例如分支单调、或由规范构造生成。要求：
   - 塔各项、Λ 的 Ω 树、最小见证 `up β two (Ωt 2)`、`YiInv` 的链 `zz` 在域里；
   - 对折叠的输出封闭，至少对第 1 层。
2. **值关系，第 1 层**：在主线精简块上证：第 1 层的规范树 x，两个底 B、B′ 在各条路径上逐点值相等（`≅`），则 `ψ … B … x` 与 `ψ … B′ … x` 的读回 `≅`；`≼` 版同理。
   - 先做第 1 层（层号 1 = `nd sS (λ _ → zero)` 一类），再做一般层号；做不到一般层号就交第 1 层与第一个挡住的引理。
   - 目标与起点 β 也可以一起随底变。
3. **一个用例**：用它证 "孩子 two 下行后的底与孩子 one 的底给出同值的折叠"，即 `YiInv.base-same` / `YiCertNeg.same-*` 在值上的版本；或在精简块上给 `YiKidCrit` 的规范域版补一个新的实例。
4. 写清量化域与前提的可满足性（实例）。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiVR`（模块名 `OCF.Lean.YiVR…`）。不改任何已有文件，不碰 `src/`、`archive/`。读回、参照框架用到的文件是验收文件，文首标明；纯树侧的关系与引理尽量导入闭包干净。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的标 "条件"（本路尽量不用）。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
- 临时目录：`<实验目录>/agents/vr`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器（停机）；需要函数外延或 K（作前提除外）；8G 仍耗尽。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：值关系做到哪一层；规范域的定义与封闭性；用例的结果；对纲领与目标的意义。列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存、importclosure。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 回报：(1) 规范域上的值关系工具（前缀 YiVR）

##### 1. 判决

**对纲领与目标的意义。** 主线精简块上有了一个树侧的值关系 `Le`，导入闭包干净，不引用记号和读回。折叠对一切满足前提 `Dflt` 的层号保持它，这是编译定理。它把 F2 上的 `bm-zero⊥`、`bm-one`、`am⊥` 统一成一条，并搬到了主线块。但 "疑似的分支侧掉值" 仍没有判决：塔第 1 项的 Ω 树不在这个关系的自相关域里，原因是关系不比较不同孩子的嵌入。对左边是 `Ωt (tw 1)` 的最小见证，本路只有条件定理。

**值关系做到哪一层。**
- 关系 `Le ℓ x y`（`YiVRRel`）：零、后继、ℕ 极限按值前序的规则；Ω 结点是函数式的（`w≼w`：相关的分支给相关的树）；右边变大只沿第一分支（`≼w`）；嵌入只比同一个孩子（`u≼u`）。第 0 层上它就是 `readRW` 的 `Value._≼_`（`le→≼`、`≼→le`，两个方向）。
- 折叠保持 `fl`（`YiVRFold`）：对一切层号 ℓ，前提 `Dflt ℓ`。底、起点 β、树三者同时可变，目标层 j 与路径 w 任意。对 (层号, 推导) 递归，检查器一次通过，没有用 `with` 的技巧。
- `Dflt ℓ` 只在 Ω 形状处有内容：分支侧一行用默认底，要它自相关。
  - 成立：不含 Ω 形状的层号（含第 1 层，`Dflt-noΩ`）、塔第 1 项（`Dflt-tw1`）。
  - 不成立：塔第 2 项（`Dflt-tw2-not`，编译否定）。读作关系太窄。
- 第 1 层：底的关系只剩第 0 层分量，所以陈述只用读回（`fold₁-≼`、`fold₁-≈`）。

**规范域与封闭性。** `Can ℓ x = Le ℓ x x`，即分支函数遗传地单调。
- 在域里：第 0 层的一切树（`refl₀`）；不含 Ω 形状的层号的 Ω 树（`Ωt≼`，含 `Ωt 1`、`Ωt 2`）；后继形状层号的 Ω 树（`ΩtS≼`）。
- 对折叠的输出封闭：`can-fold`，对一切 `Dflt` 层号。
- 不在域里：`Ωt (tw 1)`（`β-not`，编译否定）。所以简报要求的 "塔各项、Λ 的 Ω 树、`up β two (Ωt 2)`、链 `zz` 在域里" 没有做到。
- 链 `zz` 只有条件定理 `zz-can`，前提是孩子 two 的底自相关。

**用例。**
- 用例一（塔第 1 项，左边是第 0 层树 a 的嵌入）：a、a′ 值序相关时，孩子 two 的两个底相关（`base-two`），最小见证形状 `up (ι a) two (Ωt 2)` 的折叠读回 `≼`（`wit-≼`）。实例是两棵不同文而同值的树 `ωa`、`ωb`（`ωa≢ωb`、`ωa≈ωb`），折叠同值（`wit-ω`）。
- 用例二（左边是零）：孩子 c 里按 `Le` 不高于某个 `zn c n + 1` 的树，嵌入后的值不高于孩子 c+1 的 Ω 树嵌入后的值（`kid-suc`，对一切 c）；孩子 c 的 Ω 树是其中之一（`kid-Ω`）。它没有装进 `YiKidCrit.KidMono`，因为只对 c′ = c+1、x = 零。
- `YiInv.base-same` 的值版没有另做：主线块上 `YiKidRW.base-sameᴿ` 已是 `refl`。

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| 关系不比较不同孩子的嵌入，`Ωt (tw 1)` 不自相关 | `YiVRRel.β-not` | 编译否定（关系太窄） |
| `Dflt (tw 2)` 不成立，`fl` 在塔第 2 项以上用不上 | `YiVRFold.Dflt-tw2-not` | 编译否定（关系太窄） |
| `K.Bc two ⊴ K.Bc two` 是否成立没有判决，`zz-can`、`wit-β` 的前提可满足性未知 | `YiVRRead` 末节 | 未证，未否定 |
| 结论是 `≈ᵛ`（两个方向的 `≼`），不是逐构造子的 `≅` | `fold-≈`、`fold₁-≈` | 偏离简报 |
| 底的关系不含 `self` 路径上的分量 | `YiVRFold._⊴_` | 定义选择；"折叠不读该分量" 是读代码的判断，`fl` 编译通过说明保持定理不需要它 |
| `Le` 的传递性没有证；高层的自反只对规范域成立 | `YiVRRel` | 未做 |
| `Λ` 上没有任何结论 | — | 未做 |

##### 2. 文件表

| 文件 | 总行 / 代码行 | 冷编退出码 | 内存 | importclosure |
|---|---|---|---|---|
| `<仓库>/probes/OCF/Lean/YiVRRel.lagda.md` | 223 / 146 | 0 | 381 MiB | 0 命中，OK |
| `<仓库>/probes/OCF/Lean/YiVRFold.lagda.md` | 273 / 199 | 0 | 406 MiB | 0 命中，OK |
| `<仓库>/probes/OCF/Lean/YiVRRead.lagda.md` | 225 / 142 | 0 | 2075 MiB | FAIL：验收文件，经 `OCF.Align.Value` 碰到 `GoodL`、`Omega2`、`Stage2` |

- 三个接口删掉后从 `YiVRRead` 冷编，日志里的 `Checking` 行只有这三个模块。
- 检索 `postulate`、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、洞、`--cubical`、`irrelevant-projections`、`Funext`、本机路径：0 命中。
- 没有用函数外延和 K。
- 日志在 `<实验目录>/agents/vr/`。

##### 3. 定理表

全部是编译定理，除标 "条件" 与 "陈述" 的以外无前提。

| 名字 | 陈述（逐字） | 白话 | 文件 |
|---|---|---|---|
| `fl` | `(ℓ : L) (o : Ok ℓ) → Dflt ℓ → (B B′ : Base ℓ) → B ⊴ B′ → (j : L) (w : j ≤ ℓ) (β β′ : Tr⁺ j) → Le j (proj₁ β) (proj₁ β′) → {x x′ : Tr ℓ} → Le ℓ x x′ → Le j (proj₁ (ψ ℓ o B j w β x)) (proj₁ (ψ ℓ o B′ j w β′ x′))` | 底、起点、树都相关时，折叠输出相关 | YiVRFold |
| `infl` | `(ℓ : L) (o : Ok ℓ) (B : Base ℓ) (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) (x : Tr ℓ) {a : Tr j} → Le j a (proj₁ β) → Le j a (proj₁ (ψ ℓ o B j w β x))` | 折叠不低于起点，对一切树与底 | YiVRFold |
| `can-fold` | `(ℓ : L) (o : Ok ℓ) → Dflt ℓ → (B : Base ℓ) → B ⊴ B → (j : L) (w : j ≤ ℓ) (β : Tr⁺ j) → Can j (proj₁ β) → (x : Tr ℓ) → Can ℓ x → Can j (proj₁ (ψ ℓ o B j w β x))` | 规范域对折叠输出封闭 | YiVRFold |
| `fl₁` | `(B B′ : Base L1) → B ⊴ B′ → (j : L) (w : j ≤ L1) (β β′ : Tr⁺ j) → Le j (proj₁ β) (proj₁ β′) → {x x′ : Tr L1} → Le L1 x x′ → Le j (proj₁ (ψ L1 (tt , λ _ → tt) B j w β x)) (proj₁ (ψ L1 (tt , λ _ → tt) B′ j w β′ x′))` | 第 1 层的 `fl` | YiVRFold |
| `Dflt-noΩ` / `Dflt-tw1` | `(ℓ : L) → NoΩ ℓ → Dflt ℓ` / `Dflt (tw 1)` | 前提的实例 | YiVRFold |
| `Dflt-tw2-not` | `Dflt (tw 2) → ⊥` | 前提在塔第 2 项不成立 | YiVRFold |
| `B₀⊴-noΩ` / `B₀⊴-tw1` | `(ℓ : L) → NoΩ ℓ → B₀ ℓ ⊴ B₀ ℓ` / `B₀ (tw 1) ⊴ B₀ (tw 1)` | 默认底自相关 | YiVRFold |
| `Up≼` | `∀ {ℓ} (j : L) (d : Dn ℓ j) (b b′ : Tr⁺ ℓ) → Le ℓ (proj₁ b) (proj₁ b′) → {y y′ : Tr j} → Le j y y′ → Le ℓ (proj₁ (Up j d b y)) (proj₁ (Up j d b′ y′))` | 上折保持关系 | YiVRRel |
| `Ωt≼` | `(ℓ : L) → NoΩ ℓ → Can ℓ (proj₁ (Ωt ℓ))` | 无 Ω 形状层号的 Ω 树在域里 | YiVRRel |
| `refl₀` | `(x : Tr zero) → Can zero x` | 第 0 层的树都在域里 | YiVRRel |
| `β-not` | `Can (tw 1) (proj₁ (Ωt (tw 1))) → ⊥` | 塔第 1 项的 Ω 树不在域里 | YiVRRel |
| `le→≼` / `≼→le` | `{x y : Tr zero} → Le zero x y → readRW x V.≼ readRW y` / `(x y : Tr zero) → readRW x V.≼ readRW y → Le zero x y` | 第 0 层上关系就是读回的值序 | YiVRRead |
| `fold-≼` | `(ℓ : L) (o : Ok ℓ) → Dflt ℓ → (B B′ : Base ℓ) → B ⊴ B′ → (w : zero ≤ ℓ) (β β′ : Tr⁺ zero) → readRW (proj₁ β) V.≼ readRW (proj₁ β′) → {x x′ : Tr ℓ} → Le ℓ x x′ → readRW (proj₁ (ψ ℓ o B zero w β x)) V.≼ readRW (proj₁ (ψ ℓ o B′ zero w β′ x′))` | 读回对底、起点、树单调 | YiVRRead |
| `fold-≈` | `(ℓ : L) (o : Ok ℓ) → Dflt ℓ → (B B′ : Base ℓ) → B ⊴ B′ → B′ ⊴ B → (w : zero ≤ ℓ) (β β′ : Tr⁺ zero) → readRW (proj₁ β) ≈ᵛ readRW (proj₁ β′) → (x : Tr ℓ) → Can ℓ x → readRW (proj₁ (ψ ℓ o B zero w β x)) ≈ᵛ readRW (proj₁ (ψ ℓ o B′ zero w β′ x))` | 两个底同值则同一棵规范树的折叠同值 | YiVRRead |
| `fold₁-≼` | `(B B′ : Base L1) → ((w : zero ≤ L1) → readRW (proj₁ (B zero w)) V.≼ readRW (proj₁ (B′ zero w))) → (w : zero ≤ L1) (β β′ : Tr⁺ zero) → readRW (proj₁ β) V.≼ readRW (proj₁ β′) → {x x′ : Tr L1} → Le L1 x x′ → readRW (proj₁ (ψ L1 o₁ᴸ B zero w β x)) V.≼ readRW (proj₁ (ψ L1 o₁ᴸ B′ zero w β′ x′))` | 第 1 层，前提只用读回 | YiVRRead |
| `fold₁-≈` | 同上，把 `V.≼` 换成 `≈ᵛ`，树取 `(x : Tr L1) → Can L1 x` | 第 1 层的同值版 | YiVRRead |
| `base-two` | `(a a′ : Tr zero) → readRW a V.≼ readRW a′ → Bw a ⊴ Bw a′` | 孩子 two 的两个底相关 | YiVRRead |
| `wit-≼` | `(a a′ : Tr zero) → readRW a V.≼ readRW a′ → readRW (proj₁ (ψ₀ (tw 1) o₁ (wit a))) V.≼ readRW (proj₁ (ψ₀ (tw 1) o₁ (wit a′)))` | 见证形状的折叠对左边单调 | YiVRRead |
| `wit-ω` | `readRW (proj₁ (ψ₀ (tw 1) o₁ (wit ωa))) ≈ᵛ readRW (proj₁ (ψ₀ (tw 1) o₁ (wit ωb)))` | 不同文而同值的两个左边给同值 | YiVRRead |
| `rhs-form` | `(c : Tr zero) → ψ₀ (tw 1) o₁ (up zero (suc c) (proj₁ (Ωt (h₁ (suc c)))) (proj₂ (Ωt (h₁ (suc c))))) ≡ limc⁺ (λ n → ψ₀ (h₁ c) (proj₂ o₁ c) (suc (zn c n)))` | 孩子 c+1 的 Ω 树的折叠是孩子 c 一列折叠的部分和极限（`refl`） | YiVRRead |
| `kid-suc` | `(c : Tr zero) (y : Tr⁺ (h₁ c)) (n : ℕ) → Le (h₁ c) (proj₁ y) (suc (zn c n)) → readRW (proj₁ (ψ₀ (tw 1) o₁ (up zero c (proj₁ y) (proj₂ y)))) V.≼ readRW (proj₁ (ψ₀ (tw 1) o₁ (up zero (suc c) (proj₁ (Ωt (h₁ (suc c)))) (proj₂ (Ωt (h₁ (suc c)))))))` | 左边为零时孩子单调的一族实例 | YiVRRead |
| `kid-Ω` | `kid-suc` 取 y = `Ωt (h₁ c)`、n = 1 | 孩子 c 的 Ω 树不高于孩子 c+1 的 | YiVRRead |
| `zz-can`（条件） | `K.Bc two ⊴ K.Bc two → (n : ℕ) → Can (h₁ K.oneᴿ) (K.zzᴿ n)` | 链 `zz` 在域里；前提可满足性未知 | YiVRRead |
| `wit-β`（条件） | `(B′ : Base (h₁ two)) → K.Bc two ⊴ B′ → readRW (proj₁ (ψ₀ (tw 1) o₁ (up K.βᴿ two (proj₁ (Ωt (h₁ two))) (proj₂ (Ωt (h₁ two)))))) V.≼ readRW (proj₁ (ψ (h₁ two) (proj₂ o₁ two) B′ zero (z≤ (h₁ two)) K.b₁ (proj₁ (Ωt (h₁ two)))))` | 最小见证的值对孩子 two 的底单调；前提可满足性未知 | YiVRRead |
| `GMono`（陈述） | `(z z′ : Tr zero) → readRW z V.≼ readRW z′ → readRW (proj₁ (ψ₀ (h₁ z) (proj₂ o₁ z) (proj₁ (Ωt (h₁ z))))) V.≼ readRW (proj₁ (ψ₀ (h₁ z′) (proj₂ o₁ z′) (proj₁ (Ωt (h₁ z′)))))` | 未证，未否定 | YiVRRead |

前提可满足性：`Dflt` 有 `Dflt-noΩ`、`Dflt-tw1`；`B ⊴ B′` 有 `B₀⊴-noΩ`、`B₀⊴-tw1`、`base-two`；`Le ℓ x x′` 有 `Ωt≼`、`wit≼`、`ωa≈ωb`。只有 `zz-can` 与 `wit-β` 的前提没有实例。

##### 4. 第一个障碍

**缺的规则。** 关系里的 `u≼u` 只比同一个孩子 c 的两个嵌入。`Ωt (nd (sΩ k) h)` 的分支 c 是 `up zero c (Ωt (h c))`，自相关要对相关的 c、c′ 比较两个不同孩子层 `h c`、`h c′` 里的树。这需要两样本路没有的东西：
- 一个跨层的关系（`Tr (h c)` 对 `Tr (h c′)`）；
- 折叠对它的保持（`ψ (h c) …` 对 `ψ (h c′) …`，两边的证据、底、路径都不同）。

**落到塔第 1 项的具体引理。** `K.Bc two` 的第 1 层分量是结点 `z ↦ Ωt 1 + ι (ψ₀(h₁ z)(Ωt (h₁ z)))`。它自相关要 `GMono`：第 0 层的 z 按值变大时，`ψ₀(h₁ z)(Ωt (h₁ z))` 的读回不降。

判断（不是定理）：`GMono` 是 "`K.Bc two ⊴ K.Bc two`" 所需的那条引理。本路没有证 `GMono` 推出它，也没有证反向；这个判断来自手工展开 `kp` 与 `YiInv.seed-form` 的陈述。

没有碰到停机、函数外延、K 或堆的障碍。

##### 5. 偏离与事故

**偏离**
- 简报写 "读回 `≅`"。交的是 `≼` 与 `≈ᵛ`；逐构造子的 `≅` 版要另写一个结构关系，没有做。
- 底的关系 `_⊴_` 只对非 `self` 的路径要求。不这样写，`B₀ (tw 1)` 因 `self` 分量是 `Ωt (tw 1)` 而不自相关，塔第 1 项的用例就没有了。
- 规范域取 "自相关"（`Le ℓ x x`），不是 "由规范构造生成"。
- 关系多放了一条 `≼s`（右边加后继），省掉一条要用传递性的可容许规则。
- `YiVRRead` 末节的 `GMono` 是未证的陈述，按 `YiLPMono` 的先例放在文件里。

**事故**
- 编译经临时目录的 `ck.sh`，与简报命令相同，只多 `-s` 记内存，退出码不经管道。
- 三次类型错误（两处隐式参数未解），都已改。
- 没有改动已有文件，没有提交。

**没有读、只凭转述或陈述引用的**
- `Review15.md`、`YiCert.md`、`YiLPNoBM`、`YiCeilRead`、`YiBRFold`、`YiRWCheck`：没有读。
- `YiBR.md`：只读了 §5。
- `YiKidGen`：只读文首与 `plus≽` 一段；`kid-Ω`（左边为零）与它的 `Ωmono`（左边为 β）的关系没有核对。
- `YiKidRW` 的 `Bc`、`zzᴿ`、`βᴿ`、`b₁`、`plus≽`，以及 `YiBRValue.readRW`、`OCF.Align.Value`：用的是现有接口，没有重编它们。
