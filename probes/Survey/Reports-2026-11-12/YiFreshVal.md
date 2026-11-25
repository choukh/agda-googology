# F4 空白页块上的值回归 (YiFreshVal)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-13 06:37 至 07:15 |
| 工具调用 / agda 编译 (粗数) | 67 / 8 |
| token (usage 字段，按消息去重) | 输出 229272；新写入缓存的输入 711339；读缓存的输入 9671692；其余输入 92 |
| 写过的仓库文件 | `YiFreshValGap.lagda.md`, `YiFreshValRead.lagda.md`, `YiFreshValTw1.lagda.md` |
| 文件前缀 | `YiFreshVal` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: F4 返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | BTBO 下界没有证出: 只有条件定理 btbo-tw1 (前提 LOWER, V3F 只在链点上, m = 0 是定理); 执行方与主审的纸面判断: LOWER 在 m = 1 不成立, 塔第 1 项远低于 BTBO; 原因在自身目标上嵌入的孩子原样保留 (self-add, self-Ω, G2-form 编译), 不在回退; 没有编译的上界, 只写未走通; 三件冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方。全程用中文写文件与回报。主审会从头冷编译复核你交的每个文件，只认编译过的定理。

作者 2026-11-13 的选择（选项工具）原文："F4 值的回归，先做 tw 1"。说明："证空白页的块上 ψ₀ (tw 1) 的闭项不低于 BTBO。那一站 k = 0，回退与 φ 都不起作用；过不了说明问题不在回退。"

模型 Opus 5.5。同批另有两路在跑：YiPhi（Fable 5.2，改空白页的折叠，在 k 侧链步上并进以基底为目标的折叠 φ）与 YiTop（规范域内的 E2 与压缩）。文件不相交，你不读它们的输出。你只用现有的 `YiFreshFold`。按第十三次审查的说法，k = 0 的层号上 φ 与原折叠相同；这是判断，你不需要依赖它。

###### 背景（只信编译定理；文档里的叙述与判断只是数据）

- **目标**：作者定 "只要证明 BTBO 是下界即可"，值的目标只要下界，不要求同值或上界。
- **空白页的块**（`probes/OCF/Lean/` 下的 `YiFreshBlock`、`YiFreshFold`、`YiFreshLegal`、`YiFreshCheck`，主审已复核）：
  - 层号 `L` 与树 `Tr` 归纳-递归；`tw 0 = zero`，`tw (suc n) = Ωₗ (tw n) (λ c → tw n ⊕ ↑ (tw n) c)`，`Λ = lim tw`。
  - `Ωt ℓ` 是每层的 Ω 树；`ψ₀ ℓ = ψ⊥ ℓ (B₀ ℓ)`；闭项 `EBOᶜ = ψ₀ Λ (Ωt Λ)` 合法（`EBOᶜ-leg`），值未证。
  - `Tr zero` 里没有 Ω 结点也没有 `up`（`Pos zero = ⊥`，`Ch zero = ⊥`），是普通的布劳威尔树。
- **已有的 BTBO 下界**（别的块上的，可作样板）：
  - `probes/OCF/Lean/YiBtboLower.lagda.md`：`btbo : D.BTBOᴵ ≼ read T₃` 与 `btbo⁺ : D.BTBOᴵ ≼ NA.read NT.T⁺`。经 `YiPEBase.btbo-embⁿ` 与嵌入 `EmbTⁿ`；链上的不变量只是值序。
  - 来历：`probes/Survey/RR7-BtboLower.md`（第七次审查，约 290 行的无前提证法）。
  - `probes/OCF/Lean/YiLamVBtbo.lagda.md`：旧主线块上 `btbo-Tw2 : D.BTBOᴵ ≼ NA.read (W.Tw 2)`，再到 `btbo-TΛ`。
  - `_≼_` 与布劳威尔树类型在 `probes/OCF/Align/Value.lagda.md`（检索）。

###### 要做（按次序，每做成一件先编译；验收文件，前缀 `YiFreshVal`）
1. **读回**：从空白页块的 `Tr zero` 到 `_≼_` 所用的树，写 `read`，并证它对 `next`、`cum`、`lim`、`+` 的基本性质（需要多少证多少）。
2. **定站**：
   - 先查清 `D.BTBOᴵ` 在哪个模块、怎样定义，以及已有证明里 BTBO 落在别的块塔的第几项（`T₃`、旧块 `Tw 2`）。
   - 判断空白页的 `ψ₀ (tw 1) (Ωt (tw 1))` 的读法，标成判断。空白页的 tw 1 是以全部可数树为分支的 Ω 结点层号，`Ωt (tw 1)` 读作 Ω_Ω 一类。
   - 若 tw 1 这一站的读法明显低于 BTBO，就改取空白页塔中够得着的最低一项（例如 `ψ₀ (tw 2) (Ωt (tw 2))`），在文首如实写明。那时 k ≠ 0，回退会起作用，结论的意义不同。
3. **证 `D.BTBOᴵ ≼ read (那个闭项)`**，无前提。做不到时交条件定理：前提写准，并给出可满足的实例。或者停在第一障碍。
4. 若做成，顺带一条 `read (那个闭项) ≼ read EBOᶜ`（空白页的塔各项不超过终点，可能要单调），得到 `D.BTBOᴵ ≼ read EBOᶜ`。做不到不强求。

###### 先读什么
- `AGENTS.md` 全篇。
- 空白页四个文件全读。
- `probes/Survey/RR7-BtboLower.md`。
- `YiBtboLower.lagda.md`、`YiPEBase.lagda.md` 的文首与 `EmbTⁿ`、`btbo-embⁿ` 的陈述（检索）。
- `YiLamVBtbo.lagda.md` 文首。
- `probes/Survey/EBOHandbook.md` §4.1 到 §4.5（堆墙：大参照树放 `opaque`，陈述逐字写，隐式参数显式写）。

查签名用检索，不整篇读大文件。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiFreshVal`（模块名 `OCF.Lean.YiFreshVal…`）。这些是验收文件，文首标 "验收文件"，可以导入记号与参照框架。不改任何已有文件，不碰 `src/`、`archive/`。
- 中文 literate Agda（`.lagda.md`）。每个模块文首不超过 5 行；代码之间的文字只写范围与不显然的定义理由。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞（写入文件时也不留洞）、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只准作显式前提，用到它的结论标 "条件"。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 6G（另两路也在编译）。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。日志落文件，只看首个错误附近。
  - 不用 `--ignore-interfaces`。要冷编译只删你自己模块的接口（`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`），写字面的精确路径，不用通配，不用变量拼路径。
- 临时目录：`<实验目录>/agents/freshval`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不写 `/tmp` 的别处，不装包，不提交，不推送。
- **停下的条件**：同一处两次重新设计仍过不了检查器；需要函数外延或 K（作前提除外）；6G 仍耗尽（先按手册 §4.2）。没有编译的否定时只写 "未走通"。
- **过程要求**：读完上面的文件后尽快动手，第一个文件在 30 分钟内写出并编译；每次回复都要有工具调用，不要在一次回复里只思考。
- **结束前自查**：每个文件删自己的接口后冷编译，退出码 0，日志里只有你自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：定在哪一站、为什么；BTBO 下界是无前提定理、条件定理还是未走通；一段话说对目标意味着什么。
2. 文件表：文件、代码行数、冷编译退出码、常驻内存峰值。
3. 定理表：名字、逐字的陈述、一句白话、文件、档（编译定理 / 条件定理 / 有限测试 / 判断）。
4. 办法：读回怎样写；从哪条已有证明搬了什么、改了什么。
5. 第一个障碍：精确到引理，附检查器报错原文（若有），以及缺的引理的 Agda 类型。
6. 偏离与事故。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 1. 判决

- **站定在 tw 1**：`Tw1 = ψ₀ (tw 1) (Ωt (tw 1))`，k = 0。我开工前按原意读它为 ψ₀(Ω_Ω)，量级与 BTBO 相当（判断），所以没有换站。
- **BTBO 下界没有证出来，只交了条件定理 `btbo-tw1 : LOWER → V3F → D.BTBOᴵ ≼ read Tw1`**。两条前提只在链点上陈述：
  - 链点的形状由 `Tw1-form` 给出（`refl`）：`Tw1` 是 `G (pt n)` 的部分和的极限，`pt (m+1) = 1 + G (pt m)`。`G x` 是 tw 1 的分支 x 那一层上的 ψ₀(Ω)。
  - 两条前提在 m = 0 是定理（`LOWER-0`，`V3F-0`）。
- **纸面判断：前提 `LOWER` 在 m = 1 不成立，所以这条条件定理很可能是空的，`Tw1` 远低于 BTBO。** 这只是判断，没有编译的上界，也没有经过独立审核，所以只能写"未走通"，不能写成路线已否定。
  - 第 2 层上，以第 1 层自身为目标的折叠对右加的 Ω 树只是加法：`self-add` 是编译定理，对任意底与任意后继层号成立。
  - 于是 `G 2` 里第 1 层的链点是 Ω₁·ω^k（`G2-form` 编译，`z₂-1` 是有限测试），`G 2` 约为 ψ₀(Ω₁·ω^ω) = ε_{ω^ω}。
  - 参照的 ψ⁰(Ω₂) 是 BHO：参照的 ψ₁ 对抬升上来的低层树是乘法，`ref-mul` 编译了 u = 1 这一支。
  - 编译定理 `LOWER⇒Ω₂` 说明 `LOWER` 推出 ψ⁰(Ω₂) ≼ `read (G (pt 1))`；而 `G (pt 1)` 的各块都在第 2、3、4… 层上（`h-pt1`、`G-pt1`），按上面的估计都远低于 BHO（判断）。
  - 对照：第 1 层够得着参照，`lower-1 : ψ⁰(Ω₁) ≼ read (G 1)` 是无前提定理，因为第 0 层的树里没有 `up`。缺口从第 2 层开始。
- **对目标的意义**（判断）：问题不在回退。原因是 `YiFreshFold` 的自身目标规则 `ψs ℓ B _ self (up x c y) = up (ψs ℓ B ℓ self x) c y`（孩子层的树原样保留、不被折叠），加上 `Ωt (suc a)` 的分支是 `up zero tt (suc c)`。这条规则不在 k 侧，所以按简报的说法 φ 也碰不到它（我没读 YiPhi）。旧主线 YiLean 够得着 BTBO，是因为它的加法把嵌入展开成目标层的结点（纸面对比）。粗估 `Tw1` 在 φ(3,0) 一带，把握很低；比较有把握的只是"`G 2` 与 `G (pt 1)` 都低于 BHO"。

#### 2. 文件表

| 文件 | 总行 / 代码行 | 冷编退出码 | 内存（RTS 统计：总占用 / 最大驻留） |
|---|---|---|---|
| probes/OCF/Lean/YiFreshValRead.lagda.md | 103 / 67 | 0 | 905 MiB / 525 MB |
| probes/OCF/Lean/YiFreshValTw1.lagda.md | 183 / 123 | 0 | 1398 MiB / 830 MB |
| probes/OCF/Lean/YiFreshValGap.lagda.md | 124 / 73 | 0 | 1485 MiB / 891 MB |

三个文件都删掉自己的 `.agdai` 后冷编，6G 堆，每份日志只有自己模块的 `Checking` 行。禁用构造与本机路径的检索都是 0。三个文件文首都标了"验收文件"。

#### 3. 定理表（档位全是编译定理，另注者除外）

**YiFreshValRead**（空白页第 0 层的读回 `read : Tr zero → T₀`，`T₀ = L.Ordᶜ L.zero`）
- `read-+ : (x y : Tr zero) → read (x + y) L.≅ (read x L.+ read y)` — 读回尊重加法。
- `read-ι : (x : Tr zero) → read (ι zero x) L.≅ read x`
- `plus≽ : (a : Tr zero) {y : T₀} (b : Tr zero) → y ≼ read b → y ≼ read (a + b)`；`plus≼`（左加数一侧）同形。
- `cum≽`；`limcum≽ : (F : ℕ → Tr zero) (n : ℕ) {y : T₀} → y ≼ read (F n) → y ≼ read (lim (cum F))`
- `next≽ : (b : Tr zero) {Y : T₀} → Y ≼ read b → L.lim (iterᴸ (Y L.+_) L.zero) ≼ read (next b)` — 参照的 ω 倍不超过 `next`。
- `◃⊑ : {x y : Tr zero} → zero ⊢ x ◃ y → read x L.⊑ read y`
- `HS-read : (x : Tr zero) → Leg zero x → L.HS (read x)` — 合法的树读回后有证书。

**YiFreshValTw1**
- `Tw1-form : Tw1 ≡ lim (cum (λ n → G (pt n)))`（`refl`）
- `pt-leg : ∀ m → Leg zero (pt m)`；`Mono-cp : (x : Tr zero) → Leg zero x → Mono (tr₀ (cp x))`
- `LOWER = ∀ m → L.ψ⁰ (L.Ω (κ m)) ≼ read (G (pt m))`；`V3F = ∀ m → WT.Eb (ordᴰ (cp (pt m))) (read (G (pt m)))`（这两条是定义，即前提）
- `LOWER-0`，`V3F-0` — m = 0 的实例。
- `shift : ∀ x (l : Leg zero x) → PEmb (L.toLevel (read (G x)) (HS-read (G x) (G-leg x))) (lvl (st x) (st-leg x))`
- `btbo-tw1 : LOWER → V3F → D.BTBOᴵ ≼ read Tw1` — **条件定理**；按判断，前提在 m = 1 不可满足。

**YiFreshValGap**
- `self-add : (a : LF) (B : Base (suc a)) (x : Tr (suc a)) → ψs (suc a) B (suc a) self (x + Ωt (suc a)) ≡ ψs (suc a) B (suc a) self x + Ωt (suc a)` — 自身目标的折叠对右加的 Ω 树是加法。
- `self-Ω : (a : LF) (B : Base (suc a)) → ψs (suc a) B (suc a) self (Ωt (suc a)) ≡ bs B (suc a) self + Ωt (suc a)`
- `G2-form : G (suc (suc zero)) ≡ lim (cum (λ k → next (ψ⊥ one (B₀ one) (z₂ k))))`，其中 `z₂ = iter (λ c → next (ψs one (B₀ one) one self c)) zero`
- `z₂-1 : z₂ 1 ≡ next (Ωt one)` — **有限测试**。
- `h-pt1 : hdL (h₁ (pt 1)) ≡ two`；`G-pt1 : hdT (G (pt 1)) ≡ G (suc (suc zero))`
- `ref-mul : L.lim (iterᴸ (Ω₁ L.+_) L.zero) ≼ L.ψ {k = L.suc L.zero} {ℓ = L.suc (L.suc L.zero)} L.zero (λ r → L.suc r) Ω₁` — 参照里 Ω₁·ω ≼ ψ₁(Ω₁)。
- `two⊑κ1 : L.suc (L.suc L.zero) L.⊑ᴵ κ 1`；`LOWER⇒Ω₂ : LOWER → L.ψ⁰ (L.Ω (L.suc (L.suc L.zero))) ≼ read (G (pt 1))`
- `G1-form`；`lower-1 : L.ψ⁰ (L.Ω (L.suc L.zero)) ≼ read (G (suc zero))` — 无前提。
- 判断（不是定理）：`G 2` 约为 ε_{ω^ω}，低于 ψ⁰(Ω₂)，所以 `LOWER 1` 不成立。

#### 4. 办法

- **读回**：`read` 与旧主线的写法同形，Ω 与 up 两种情形是荒谬模式。`HS-read` 经 `◃⊑` 从合法性得到。
- **链**：照搬 `YiBtboLower` 的骨架——值序不变量 `D.γ n ≼ read (pt m)`，`emb` 由 `PW₃ (V1 …)`、`PW₁ (V2′ …)`、`PW₂ (HS-read …) (V3F)`、`shift` 四段 `PEmb-∘` 复合，再接 `Ψ-emb`。
  - `shift` 用 `YiPEStep` 的 `PEmb-shift`、`toLevel-+`、`PEmb-≅ʳ`、`HS-≅`。
  - 改动只在三处：链点是 `1 + G`，不是旧的累加；起点取 `pt 1`，因为 `pt 0 = 0` 低于 D.γ 0 = 1；前提只在链点上陈述。
- `V3m` 的空白页版（`V3F`）我没有证。纸面方案：对底泛化，ℕ 极限情形用孩子的底 b⊥ = 前一块的值来分块；这只有在 `LOWER` 成立时才有用。
- `lower-1` 是第 0 层上的直接归纳（`ψ⁰-mono⁰`、`ψ⁰≅ψ`），参照的链与这里的链差一步。

#### 5. 第一个障碍

- **卡在 `LOWER` 的 m = 1 这一项**：`L.ψ⁰ (L.Ω (κ 1)) ≼ read (G (pt 1))`。按判断它是假的，不是缺一条证明。
- **在任何仿照 `YiLeanValRel/ValFold` 的模拟证明里，会卡在自身目标的 `up` 情形**。需要的引理形如：
  `SELF-UP : ∀ a (B : Base (suc a)) (x : Tr (suc a)) (y : Tr a) {i ℓ κ} (p : i L.<ᴵ ℓ) (σ : L.Simᴵ κ ℓ) {y′ : L.Ordᶜ κ} → Corr i (suc a) → RelF a y′ y → RelF (suc a) (L.ψ p σ y′) (up (ψs (suc a) B (suc a) self x) tt y)`
  - 取 a = 0、y′ = y = 1：左边是 Ω₁·ω，右边读作 Ω₁+1，所以这条引理在值上不成立（判断）。
- 没有检查器报错，因为这个障碍是数学上的，不是证明写不出来。
- 要把判断变成编译的否定，需要一条空白页对参照的上界模拟（第 1 层，含部分和的吸收），估计几百行；或者按规则送 Fable 5.2 独立审核。

#### 6. 偏离与事故

- **没有改取 tw 2**：缺口来自每个后继层号上都有的自身目标规则，换到 tw 2 并不绕开它（判断）。这件事已在文首如实写明。
- 第 3 步只交了条件定理，`V3F` 与 `LOWER` 都没证；第 4 步（`Tw1 ≼ EBOᶜ`）没做。
- 前提从"对一切合法的 x"收窄成"只在链点上"，因为证明只用到链点，前提更弱、定理更强。
- **事故**：第一次编译外面套了 `/usr/bin/time`，沙箱拦了 sysctl，退出码 1，但 agda 本身已经跑完。之后改用 `+RTS -s` 读内存，表里的数是 RTS 的统计，不是真正的常驻内存峰值。
- 一次性的试验文件 `GapTry.agda` 只放在临时目录 `<实验目录>/agents/freshval/` 里，内容已移入 `YiFreshValGap`。
- 没有改动任何已有文件，没有提交。

文件：
- <仓库>/probes/OCF/Lean/YiFreshValRead.lagda.md
- <仓库>/probes/OCF/Lean/YiFreshValTw1.lagda.md
- <仓库>/probes/OCF/Lean/YiFreshValGap.lagda.md
