# (B) 终点的 Into：先试绕开 (YiEB)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-13 10:51 至 11:08 |
| 工具调用 / agda 编译 (粗数) | 47 / 9 |
| token (usage 字段，按消息去重) | 输出 91606；新写入缓存的输入 229986；读缓存的输入 5364196；其余输入 72 |
| 写过的仓库文件 | `YiEBBtbo.lagda.md`, `YiEBNoKG.lagda.md`, `YiEBShape.lagda.md` |
| 文件前缀 | `YiEB` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: (B) 终点的 Into 返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | btbo-EBO : D.BTBOᴵ ≼ read EBOᶜ, 无前提, 不经 Into; transfer/transferP; V102 部分成立, 还要起点条件 (no-KG 否定只带下界条件的对齐引理); 三件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定（2026-11-13，选项原文）
本路是 "(B) 终点的 Into：先试绕开"。内容原文："先核 EBOᶜ 各支的底是否满足值引理的下界条件，若成立就让每行直接对 EBOᶜ 的各支成立（V102）；不成立再攻 CoordMono（V101）"。

同批另三路，各自只新建文件，你不动它们的文件：
- (A) 冲塔第 2 项，前缀 YiT2，Fable 5.2；
- (C) F2 前 3 层从头精简重写，前缀 YiRW；
- (D) YiLPIface 的配对否定，前缀 YiLN。

###### 背景（只信编译定理；文档里的叙述是数据）
目标是布劳威尔树上读法 ψ₀(Λ) 的合法闭项，外加编译定理 "序数值 ≥ EBO 的参照"，只要下界。终点的出口已经归约到逐行：`YiRefTw2.endpoint : (Y : T₀) → (∀ k → Rt (hc-tower k) ≼ Y) → toL EBO-tree′ ≼ Y`，无前提。

主线合法块 F2，在 `probes/OCF/Lean/`：
- `YiLegBlock`：`Λ = lim tw`。
- `YiLegOps`：
  - `Ωt (lim g) = lim (cumΩ g) …`；
  - `cumΩ g (suc n) = up (cumΩ g n) (suc n) (Ωt (g (suc n))) …`。
- `YiLegFold`：`EBOᶜ = ψ₀ Λ Ev-Λ Rt-Λ (Ωt Λ)`；`twᶜ n = ψ₀ (tw n) (Ev-tw n) (Rt-tw n) (Ωt (tw n))`。
- `YiLPIface` 的 `J2⊥-lim`：
  `ψ⊥ (lim g) ε ρ B (up x n y e) ≡ ψ⊥ (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n x) y`。

值的部分：
- **读回与统一模拟**（(b)，`YiLSRead`、`YiLSFold`、`YiLSTw1`、`YiLSBtbo`）：
  - `lower : ∀ {ℓ i} (f : NL ℓ) (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Corr i ℓ → L.ψ⁰ (L.Ω i) ≼ read (ψ⊥ ℓ ε ρ B (Ωt ℓ))`，NL 是零、后继、ℕ 极限层号。
  - `OKB ℓ B = (zero ⊢ suc zero ⊴ b⊥ B) × ((j : LF) (w : j ≤ ℓ) → j ⊢ Ωt j ⊴ bs B j w)`；`ok-B₀`；`ok-dS`；`ok-dL : … → OKB (lim g) B → (n : ℕ) (t : Tr (lim g)) → OKB (g n) (dL g ε ρ B n t)`。
  - `btbo-tw1 : D.BTBOᴵ ≼ read (twᶜ 1)`。它经塔第 1 项的链点 `pt m`（层号 `h₁ x` 是 NL）与 `tw1-form : twᶜ 1 ≡ limc (λ n → G (pt n)) …` 证出；`V3` 对满足 `OKs` 的任意底 `Bb` 陈述。
- **(a) 的结果**（`YiLPInto`、`YiLPMono`、`YiLPNoBM`）：
  - `Into n = readᴸ (twᶜ n) ≼ᴸ readᴸ EBOᶜ`；`into-0` 是定理。
  - `into-coord : (n : ℕ) → CoordMono (tw n) … → Into (suc n)`，前提 `CoordMono` 未证未否定（台账 V101）。
  - `B₀⊴dL : (n : ℕ) (x : Tr Λ) → B₀ (tw n) ⊴ dL tw Ev-Λ Rt-Λ (B₀ Λ) n x`。
  - `chain-B₀`、`chain-B₁`：换底后回灌链的坐标不同。
  - `no-bm-all`：对一切树的基底单调不成立。
- 回报原文：`probes/Survey/Reports-2026-11-12/YiLS.md`、`YiLP.md`。

主审的判断（V102，未编译，请先挑战它）：值引理对满足下界条件的一切底成立，所以塔的每一行也许可以直接对 `EBOᶜ` 的各支证，不经 "塔第 n 项 ≼ 终点"。

###### 要做
1. **核形状**：用编译的等式（`refl` 或 J2 各条）写出 `EBOᶜ` 的读回是 `EBOᶜ` 各支的上确界。
   - 写清第 n 支是哪一棵树：层号 `tw n` 上 `Ωt (tw n)` 的折叠，底是 `dL tw Ev-Λ Rt-Λ (B₀ Λ) n x`。
   - 再证 `read EBOᶜ` 不低于每一支。
2. **核下界条件**：这些底满足 `OKB`，由 `ok-B₀ Λ` 与 `ok-dL` 推，或其他办法。
3. **BTBO 那一行对 `EBOᶜ`**：无前提证出 `D.BTBOᴵ ≼ read EBOᶜ`。
   - 难点在于塔第 1 项那一支的底不是 `B₀ (tw 1)`，链点会变（`chain-B₁`）。
   - 要把 `btbo-tw1` 的论证推广到满足下界条件的一般底：链点、`tw1-form`、`LOWER`、`V3F` 的对应物都对一般底陈述。
   - 证到第一个挡住的引理也算交付。
4. **一般的转移引理**：形如 "对每个 n，若某参照 X 对满足 `OKB` 的一切底都不高于层号 `tw n` 上 Ω 树的折叠，则 X ≼ read EBOᶜ"。这样以后塔各行都不需要 Into。陈述的具体形状由你定。
5. **只有绕开不成时**才去攻 CoordMono（V101），并报告第一个障碍。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiEB`（模块名 `OCF.Lean.YiEB…`）。不改任何已有文件，不碰 `src/`、`archive/`。值的文件是验收文件，文首标 "验收文件"。
- 树、折叠、合法性一行不改。**先验检查**（`AGENTS.md`）：若觉得要改折叠，先停下报告。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的标 "条件"。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 6G；若依赖 `YiLSRel`（冷编约 6.9G），用 8G。
  - 冷编只删自己模块的接口，写字面路径；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
  - 堆墙的写法见 `probes/Survey/EBOHandbook.md` 第 4 节。
- 临时目录：`<实验目录>/agents/eb`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；需要函数外延或 K（作前提除外）；堆仍耗尽。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：对纲领与目标意味着什么，再列关键路径上暴露的问题（表：问题、位置、档）；写明 V102 成立与否。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档（编译定理 / 条件定理 / 有限测试 / 判断）。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 判决

**对纲领与目标.** 终点闭项 `EBOᶜ`（F2 块里读作 ψ₀(Λ) 的那棵合法树）现在有一条无前提的编译下界：`btbo-EBO : D.BTBOᴵ ≼ read EBOᶜ`。证明直接取 `EBOᶜ` 的第 1 支，不经 Into，也不用 CoordMono。按记号读，`D.BTBOᴵ` 是 ψ₀(Ω_Ω)，这一读法是判断，依据是 `YiBtValBT` 的注释，本轮没有核。
- 树、折叠、合法性一行未改，新增的都是验收文件。闭项不引用记号；参照 `D.BTBOᴵ` 与已有的 `btbo-tw1` 是同一个。
- 这一步给终点出口立了一个无前提的锚点，不改变 "树自足" 的状况。到 EBO 下界还要塔的各行。

**V102 部分成立.**
- BTBO 那一行可以直接对 `EBOᶜ` 的支证（编译定理）。
- 但它不是 "满足下界条件的一切底" 都行：除了 `OKB`，还要起点条件 `Start`，即 Ω 结点链的起点 `bs B zero (ink self)` 与底分量 `b⊥ B` 逐点同形（`E`）。`lower` 确实对一切满足 `OKB` 的底成立，用到 `Start` 的只有对齐引理 `KG`。
- `no-KG` 编译证明了：有一个满足 `OKB` 的底，`KG` 对它不成立。所以 `Start` 不能从 `KG` 去掉。
- 结论 "BTBO ≼ 一切满足 `OKB` 的底上的折叠" 本身未证未否，是开放问题。
- 因为绕开成功，第 5 项 CoordMono（V101）没有去攻。

| 问题 | 位置 | 档 |
|---|---|---|
| `KG` 要 `Start`，`OKB` 推不出它；有满足 `OKB` 的底使 `KG` 不成立 | `YiEBBtbo.Btbo.KG`，`YiEBNoKG.no-KG` | 编译定理（否定的是这条引理，不是路线） |
| 只带 `OKB` 的 `transfer` 用不到 BTBO 这一行，要用带谓词的 `transferP` 加上 `Start` | `YiEBShape.transfer` / `transferP` | 编译定理 |
| 第 1 支的底上，链起点与底分量字面相等 | `YiEBBtbo.start-dB1≡`（`refl`） | 有限测试 |
| 第 2 支的链起点（在层号 `tw 1`）不是 `Ωt (tw 1)`：它是一个 Ω 结点，分支是 `Ωt (h₁ c)` 以 `next (Ωt (tw 1))` 为底的上折像，标准底的分支是 `up zero c …`。对 `B₀ (tw 2)` 按 `up` 分支写的第 2 行论证不能直接搬到第 2 支 | `YiEBShape.start-dB2` | 有限测试；推论是判断 |
| 第 n+1 支的底分量 `b⊥` 就是第 n 支本身 | `YiEBShape.b⊥-dB`（`refl`） | 有限测试 |

#### 文件表

代码行指代码块内的非空行。冷编都是先删掉自己模块的 `.agdai`，日志里只有本模块的 `Checking` 行。依赖 YiLSRel 的接口，堆上限用 8G。

| 文件 | 代码行 | 冷编退出码 | 最大驻留 / 占用 | 用时 |
|---|---|---|---|---|
| `probes/OCF/Lean/YiEBShape.lagda.md` | 61 | 0 | 0.72G / 1273MiB | 8s |
| `probes/OCF/Lean/YiEBBtbo.lagda.md` | 104 | 0 | 0.92G / 1558MiB | 10s |
| `probes/OCF/Lean/YiEBNoKG.lagda.md` | 55 | 0 | 0.86G / 1542MiB | 10s |

三个文件都检索过禁用构造（`postulate`、洞、`TERMINATING` 等编译指示、`trustMe`、`--cubical`、`--irrelevant-projections`）和本机路径，结果为 0；选项行只有 `--safe --without-K --lossy-unification`。

#### 定理表（全部是编译定理，无前提）

| 名字 | 陈述（逐字） | 白话 | 文件 |
|---|---|---|---|
| `EBO-lim` | `EBOᶜ ≡ lim (λ n → ψ⊥ Λ Ev-Λ Rt-Λ (B₀ Λ) (cumΩ tw n)) (…)`（`refl`） | 终点是各支的 ℕ 极限 | Shape |
| `branch-eq` | `(n : ℕ) → ψ⊥ Λ Ev-Λ Rt-Λ (B₀ Λ) (cumΩ tw n) ≡ br n` | 第 n 支是 `Fn n (dB n)`，`dB n = dL tw Ev-Λ Rt-Λ (B₀ Λ) n (pre n)` | Shape |
| `br≼` | `(n : ℕ) → read (br n) ≼ read EBOᶜ` | 每一支不高于终点 | Shape |
| `sup≼` | `(Y : T₀) → ((n : ℕ) → read (br n) ≼ Y) → read EBOᶜ ≼ Y` | 终点是各支的最小上界 | Shape |
| `EBO≅sup` | `read EBOᶜ L.≅ L.lim (λ n → read (br n))` | 读回等于各支读回的极限 | Shape |
| `ok-dB` | `(n : ℕ) → OKB (tw n) (dB n)` | 各支的底满足下界条件 | Shape |
| `b⊥-dB` | `(n : ℕ) → b⊥ (dB (suc n)) ≡ br n` | 第 n+1 支的底分量是第 n 支 | Shape（有限测试） |
| `transfer` | `(X : T₀) (n : ℕ) → ((B : Base (tw n)) → OKB (tw n) B → X ≼ read (Fn n B)) → X ≼ read EBOᶜ` | 某行对一切满足 `OKB` 的底成立，就对终点成立 | Shape |
| `transferP` | `(X : T₀) (n : ℕ) (P : Base (tw n) → Set) → P (dB n) → ((B : Base (tw n)) → OKB (tw n) B → P B → X ≼ read (Fn n B)) → X ≼ read EBOᶜ` | 同上，多带一个第 n 支的底满足的谓词 | Shape |
| `start-dB2` | `bs (dB 2) (tw 1) (ink self) ≡ Ω (inj₁ (inj₁ tt)) (λ c → Up (h₁ c) (down stop c) (next (Ωt (tw 1)) (Ωt-nz (tw 1))) _ (Ωt (h₁ c)))` | 第 2 支的链起点 | Shape（有限测试） |
| `Chain.form` | `Fn 1 B ≡ limc (λ n → G (pt n)) (λ n → G-nz (pt n))`（对一切 `B : Base (tw 1)`） | 一般底上的 `tw1-form` | Btbo |
| `Lemmas.LOWER` | `∀ m → L.ψ⁰ (L.Ω (κ m)) ≼ read (G (pt m))`（前提 `OKB (tw 1) B`） | 一般底上的 `LOWER` | Btbo |
| `Lemmas.V3F` | `∀ m → WT.Eb (ordᴰ (cp (pt m))) (read (G (pt m)))`（前提 `OKB`） | 一般底上的 `V3F` | Btbo |
| `Btbo.KG` | `(x : Tr zero) → read (K x) L.≅ read (G x)`（前提 `OKB`、`Start B`） | 链点与求和项对齐；唯一用到 `Start` 的地方 | Btbo |
| `Btbo.btbo-B` | `D.BTBOᴵ ≼ read (Fn 1 B)`（前提 `OKB (tw 1) B`、`Start B`） | 一般底上的 BTBO 下界 | Btbo |
| `start-dB1` / `start-dB1≡` | `Start (dB 1)` / `bs (dB 1) zero (ink self) ≡ b⊥ (dB 1)` | 第 1 支的底满足起点条件 | Btbo |
| `btbo-EBO`, `btbo-EBO′` | `D.BTBOᴵ ≼ read EBOᶜ` | 终点不低于 BTBO（`btbo-EBO′` 经 `transferP` 得出） | Btbo |
| `btbo-B₀` | `D.BTBOᴵ ≼ read (twᶜ 1)` | 标准底是一般陈述的一个实例 | Btbo |
| `ok-bad` | `OKB (tw 1) Bbad` | 反例底满足下界条件（底分量 ω，链起点 1） | NoKG |
| `no-start` | `Start Bbad → ⊥` | 反例底不满足起点条件 | NoKG |
| `no-GK` | `read (G zero) ≼ read (K zero) → ⊥` | 对反例底，`G 0` 不低于 ω+1，`K 0` 读成 ω | NoKG |
| `no-KG` | `read (K zero) L.≅ read (G zero) → ⊥` | `KG` 对反例底不成立 | NoKG（否定） |

#### 第一个障碍

BTBO 这一行对 `EBOᶜ` 没有障碍，已经做完。

对 V102 的原始说法（只靠 `OKB`），第一个挡住的引理是 `YiEBBtbo.Btbo.KG`，它已被 `no-KG` 否定。要对一切满足 `OKB` 的底证 `btbo-B`，必须换掉 `KG` 的用法。纸面判断（未编译）的一条出路是把 `b⊥` 换成链起点后比较，需要两条：
- ψs 的输出与底分量 `b⊥` 无关。这不是字面相等，要一个跨各层的树结构相等关系。
- ψ⊥ 对 `b⊥` 在值上单调。

当链起点大于底分量时，`shift` 还需要前驱包含（`⊑`），而 `⊑` 在 `suc` 下不保持，这一支更难。都没有做。

#### 偏离与事故，凭转述的东西

- **偏离**：多交了一个否定文件 `YiEBNoKG`（在本路前缀内），用来支撑 "`Start` 不能从 `KG` 去掉" 这一句。`start-dB2` 先在临时目录用纯 `.agda` 试过，再写进 `YiEBShape`。
- **事故**：第一次编译时 `/usr/bin/time -l` 被沙箱拦下，退出码 1 来自 `time`，不来自 agda。之后改用 `+RTS -s`，上表的数都来自冷编。
- **没有读、只凭检索或转述**：
  - `YiRefTw2.endpoint` 只检索了签名。它属于 YiFresh/YiUpLegal 块，`T₀` 来自 `YiFreshValRead`。我没有核那个 `T₀` 与 F2 的 `L.Ordᶜ L.zero` 是否相同，也没有核 BTBO 这一行与 `Rt (hc-tower k)` 各行的对应。所以 `btbo-EBO` 能否直接接进 `endpoint` 未核。
  - `D.BTBOᴵ` 读作 ψ₀(Ω_Ω) 只来自注释。
  - CoordMono 的定义、`YiLPNoBM` 文首以外的内容、台账 V101/V102 的原文，都没有读。
