# 现折叠上继续推小站 (YiStep)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-12 07:45 至 08:38 |
| 工具调用 / agda 编译 (粗数) | 90 / 24 |
| token (usage 字段，按消息去重) | 输出 300886；新写入缓存的输入 491620；读缓存的输入 24988984；其余输入 164 |
| 写过的仓库文件 | `YiStepDiag2.lagda.md`, `YiStepFold2.lagda.md`, `YiStepMain2.lagda.md`, `YiStepPfx.lagda.md`, `YiStepRel2.lagda.md`, `YiStepThree.lagda.md`, `YiStepTree.lagda.md` |
| 文件前缀 | `YiStep` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-12: 现折叠上继续推小站一路返回并复核; 第八批合读 (主审)” 一节 |
| 主审复核后的一句结论 | ψ₀(Ω_Ω+Ω₃) 只到条件定理（前提：第 2 层的 BTBO 链点）；第 2 层关系与折叠引理做成；七件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 作者的方针: "边重构边做, 只动值的前沿碰到的那块"; 你这一路是 **现折叠上继续推小站**: 把第 1 层关系的对角规则对结点参数化, 往 ψ₀(Ω_Ω+Ω₃), ψ₀(Ω_Ω+Ω_ω) 推, 直到派发开始折叠的那一站. 主审会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 背景 (事实)

- 现折叠: 燃料搜索的一致折叠 `probes/OCF/Lean/YiDlFold.lagda.md`; 闭项 `T⁺ʷ` (读法 ψ₀(Ω_{Ω+1})), `TΛ` (读法 ψ₀(Λ)); `YiIntoTw3.T⁺ʷ≼TΛ` 把 `T⁺ʷ` 上的界搬到 `TΛ`.
- 已证的最高下界: `YiSyncTwo.X₂≼TΛ : S2.X₂ ≼ NA.read W.TΛ` (参照读作 ψ₀(Ω_Ω+Ω₂), 读法是判断). 它用到: 第 1 层的读回关系 `YiSyncRel._⊴⁺_` (对角规则 `dg`, 门槛统一取 `top + Tw 2`), `YiSyncDiag.Diag` (静态对角线在 Ω₁ 结点 `ψ₁ top` 之下), `YiSyncFold` 的 `fold1⁺`, `Fold₁ᴾ`, 以及 `YiL1*` (第 1 层的 BTBO 下界 `base₁`), `YiShpEps` (`Lv1`, `fold1`), `YiShpSq`, `YiShpTwo`. 回报 `probes/Survey/Reports-2026-11-12/YiSync.md` §5 (判断): 规则只对前缀 `G₂` 与这一个 Ω₁ 结点陈述; 往上一站 (Ω₂·2, Ω₃) 大概要按新的结点与前缀重陈述门槛并给出新的对角定理; 能否对位置参数化没有试.
- 派发开始折叠的地方 (判断): 第九次审查 (`probes/Survey/RR9-OmegaOmega2.md` 问题 2) 估计到 ψ₀(Ω_Ω+Ω_{ω+1}) 为止被比较的目标层号 ≤ ω, 源层号有限, 现折叠在被问到的位置上完全; 第一处不一致大约在 ψ₀(Ω_Ω+Ω_{ω+2}) 或 ψ₀(Ω_Ω+Ω_{ω+1}²). 燃料搜索 `dl` 在源层号字面是 ℕ 极限时折叠 (`YiDlLost.dl-lim`).

#### 要交的, 分步; 每做成一步先交

1. **参数化**: 把对角规则与 `Diag`, `fold1⁺`, `Fold₁ᴾ` 一类的引理写成对目标层 k (至少 k = 1, 2, …) 与对应的 Ω_k 结点参数化的形式, 或写出一般的第 k 层读回关系; 先做 k = 2, 得到 ψ₀(Ω_Ω+Ω₃) 的参照 (照 `S2.X₂` 的写法, 例如 `L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σ (L.Ω 3))`) 不高于 `NA.read W.TΛ`.
2. **一切有限 n**: ψ₀(Ω_Ω+Ω_n) 对一切 n, 再到 ψ₀(Ω_Ω+Ω_ω) (n 的上确界).
3. **停在哪里**: 继续往上 (例如 ψ₀(Ω_Ω+Ω_{ω+1})), 第一个证不出的站给出编译事实: 用到的位置, 派发在那里保留还是折叠, 源层号与目标层号的形状. 说清停下是因为派发折叠还是因为关系一侧.

只要下界 (作者 2026-11-11 的原则). 参照的读法没有逐项一致证明时写成判断.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K; 堆到 6G 仍耗尽 (先按手册 §4.2). 没有编译的否定时只写 "未走通".

#### 先读什么

`AGENTS.md` (Agda 一节, "中间站给界", 文字预算, 结论的写法); `probes/Survey/EBOHandbook.md` §4.1 到 §4.5 与 §5.4; `YiSync*` 四个文件全读; `YiL1Base`, `YiL1Stmt`, `YiShpTwo`, `YiShpEps` 检索要用的名字; `YiDlLost` (`dl-lim`); 参照 `probes/OCF/Align/Level.lagda.md` (`ψ`, `ψ⁰`, `Ω`, `add`, `Simᴵ`), `Stage2.lagda.md` (`ℓ₀`, `X₂`, `σ₂`). 查签名用检索.

#### 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiStep` (模块名 `OCF.Lean.YiStep…`). 都是验收文件, 文首标 "验收文件". 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞 (写入文件时也不要留洞), `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提.
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 堆墙多出在比较具体闭项的地方: 陈述逐字写, 不用别名; 大参照树放 `opaque`; 经非单射的头求解的隐式参数显式写出 (手册第 4 节).
- 仓库文件里不写本机路径. 不要把仓库整个拷到临时目录.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽. 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块; 另有两路也在编译.
- 你的临时目录: `<实验目录>/agents/step`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 过程要求: 读完上面的文件后尽快动手, 第一个文件在 20 分钟内写出并编译; 每次回复都要有工具调用, 不要在一次回复里只思考.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 回报格式 (只在回报里交一次)

1. 判决: 推到了哪一站; 一段话说对目标意味着什么 (`TΛ` 已证的最高下界; 停在哪里, 原因).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档. 每个参照写明读法是否有逐项一致证明.
4. 办法: 参数化是怎么做的, 与 `YiSync` 相比新用到了什么.
5. 第一个障碍: 精确到引理与位置, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 回报原文

#### 1 判决

**只推到 ψ₀(Ω_Ω+Ω₃) 的条件定理，没有拿到无前提的新下界。**

- `TΛ` 已证的最高无前提下界没有变，仍是 `YiSyncTwo.X₂≼TΛ`（参照读作 ψ₀(Ω_Ω+Ω₂)，读法是判断）。
- 本路编译通过的最强结论是 `X₃≼ᵇ : Chain₂ → X₃ ≼ NA.read W.TΛ`。参照 `X₃ = L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σ₃ (L.Ω 3))` 读作 ψ₀(Ω_Ω+Ω₃)，读法是判断，没有逐项一致证明。
- 前提 `Chain₂` 说的是：参照的第 2 层静态对角线 ψ₂(Ω_{ℓ₀}) = lim F₂ 里，第 1 项起的每一项都落在树的 `K₂ (suc (ξ m))` 之下。它是 `YiSyncDiag.chain₁′` 在第 2 层的对应，可以叫第 2 层的 BTBO 链点。第 0 项 ψ₂(Ω₁) 已无前提证出（`F₂0⊴K`）。
- **前提能否满足，没有实例**。我判断它成立，依据只是类比：第 1 层的对应 `chain₁′` 是定理。
- 除这个前提外，第 2 层要的部件都编译通过了：关系 `⊴²`，目标层 2、1、0 的三条折叠引理，以及链上逐点 `e₃⊴γ₃`。

**停在哪里，原因是什么。** 停在 Ω₃，原因在关系一侧，不在派发。
- 用到的位置上派发都保留（编译事实，都是 `refl`）：`ψ₂-top`, `ψ₂-lc₀`, `ψ₂-lc₁`, `ψ₂-tp`, `ψ₂′-lc`, `ψ₂′-tp`, `ψ₁-lc₀`。目标层 1 在层号 1 的结点上折叠（`ψ₁-lc₁`），这是该折叠的情形。
- `Chain₂` 的链点 m = 0 的根位置（`refl`）：源层号是 ℕ 极限（`lim-src₀`），目标层是 2，派发折叠（`root-fold₂`）。层号不低于目标时，本来就该折叠。第 1 层同形的链点上派发同样折叠（`root-fold₁`），而 `chain₁′` 仍然成立。
- 第 2 步（一切 n 的 Ω_n，以及 Ω_ω）与第 3 步（Ω_{ω+1} 一带）都没有做。按同样的结构，每一站 Ω_{k+1} 都要一条第 k 层的 BTBO 链点（判断）。所以第九次审查估计的 "派发开始折叠的那一站" 这次没有走到：关系一侧先在 Ω₃ 停下了。

#### 2 文件表

都在 `probes/OCF/Lean/`。先删掉这 7 个文件的接口，再按依赖次序逐个冷编译。每个日志只有自己模块的 1 行 `Checking`，没有别的输出行。内存是 `/usr/bin/time -l` 量的常驻内存峰值。

| 文件 | 总行 / 代码行 | 冷编译退出码 | 内存峰值 |
|---|---|---|---|
| `YiStepTree.lagda.md` | 178 / 111 | 0 | 1.65 GB |
| `YiStepPfx.lagda.md` | 191 / 147 | 0 | 2.05 GB |
| `YiStepRel2.lagda.md` | 274 / 224 | 0 | 1.86 GB |
| `YiStepFold2.lagda.md` | 344 / 280 | 0 | 2.03 GB |
| `YiStepThree.lagda.md` | 40 / 27 | 0 | 1.83 GB |
| `YiStepDiag2.lagda.md` | 106 / 70 | 0 | 1.86 GB |
| `YiStepMain2.lagda.md` | 89 / 66 | 0 | 1.62 GB |

- 每个文件约 10 到 14 秒。
- 检索 `postulate`、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`irrelevant-projections`、`--cubical`、`{!`、洞 `?`、`Funext`、本机路径，结果都是 0。
- 选项行都是 `--safe --without-K --lossy-unification`。没有改任何已有文件。

#### 3 定理表

**记号。**
- `ψ₂ = W.Ψ L2 V2 (W.cmpw V2 s₃)`，`ψ₁` 取自 `YiShpSq`。
- `G₃ η = plus (tw 2) top (plus (tw 2) K₀ (gm₃ η))`，`K₀ = Kfk zero Tt (suc top)`。
- `γ₃ = chain L2 (ψ₂ ∘ G₃)`。
- `σ₃ q = L.lim 1 (L.lim 0 (L.lim 3 q))`，`σ₃′ q = σ₃ (L.suc q)`。
- `K₂ = Kfk zero Tψ₂`，`thr = plus zero top (W.Tw 2)`。

**档。**
- "定理"：编译定理，无前提。
- "条件"：编译定理，前提写在陈述里，或是模块参数。
- 凡含 `X₃` 的行另有一条判断：参照读作 ψ₀(Ω_Ω+Ω₃)。

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `Tt-s₃` | `Tt ssT ≡ G.lc s₃ gm₃` | 根链第 1 点的分支里有层号 2 的 Ω₃ 结点 | Tree | 定理 (`refl`) |
| `N₃-chain` | `Ψ₀ (G.lc s₃ G₃) ≡ G.lim (λ n → Ψ₀ (G₃ (γ₃ n)))` | 目标层 0 把它折成层号 2 的链 | Tree | 定理 (`refl`) |
| `ψ₂-top` | `ψ₂ G.top ≡ G.lc (inj₂ (inj₁ tt)) K₂` | 目标层 2 在根 `p₀` 上保留层号 0 | Tree | 定理 (`refl`) |
| `ψ₂-lc₁` | `∀ g → ψ₂ (G₃ (G.lc (inj₁ tt) g)) ≡ G.lc (inj₁ tt) (λ η → ψ₂ (G₃ (g η)))` | 层号 1 的结点保留（`ψ₂-lc₀`, `ψ₂-tp`, `ψ₂′-lc`, `ψ₂′-tp`, `ψ₁-lc₀` 同类；`ψ₁-lc₁`, `Ψ₀-lc₁` 给出折叠时的链） | Tree | 定理 (`refl`) |
| `N₃≼T` | `∀ {X : L.Ordᶜ L.zero} → X ≼ NA.read (Ψ₀ (G.lc s₃ G₃)) → X ≼ NA.read W.T⁺ʷ` | Ω₃ 结点在 `T⁺ʷ` 之下 | Tree | 定理 |
| `X₃-form` | `X₃ ≡ L.lim (λ n → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σ₃′ (e₃ n)))` | 参照的链 | Tree | 定理 (`refl`) |
| `X₃≼ᶜ` | `Sync₃ → X₃ ≼ NA.read W.TΛ` | 链上逐点的值推出 ψ₀(Ω_Ω+Ω₃) ≤ TΛ | Tree | 条件 |
| `P1.fold1ᴳ` | `∀ {X : T₁} {η} → X ⊴⁺ η → X L.≅ X → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σA X) ≼ NA.read (Ψ₀ (G η))` | `fold1⁺` 对分支族参数化 | Pfx | 条件（模块参数 `P : Pfx`） |
| `P1.Fold₁ᴳ` | `∀ {X : T₁} {η} → X ⊴⁺ η → X L.≅ X → L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σA X) ⊴⁺ ψ1 (G η)` | `Fold₁ᴾ` 参数化（`fold0ᴳ`, `Fold₀ᴳ`, `CtxAᴳ`, `Z⊴ᴳ` 同） | Pfx | 条件（同上） |
| `P₂`, `P₃′` | `P₂ : Pfx`，`P₃′ : Pfx` | 记录可满足：原来的 `G₂`，以及 Ω₃ 结点下的 `G₃′` | Pfx | 定理 |
| `_⊴²_` | `data _⊴²_ : ∀ {k} → L.Ordᶜ k → R₂ → Set`。规则 `z⊴ s⊴s ⊴s ⊴l l⊴ ⊴b₁ ⊴b₀ n1 t1 n0 n0′ e1 e0 u1 u0 dg ≅⊴`；其中 `n1 : ∀ {f : T₁ → T₂} {g : NA.R₁ → R₂} → (∀ (y : T₁) a → y ⊴⁺ a → y L.≅ y → f y ⊴² g a) → L.limᵢ {i = ℓ₁} L.zero f ⊴² G.lc (inj₁ tt) g`，`dg : ∀ {k} {F : ℕ → L.Ordᶜ k} {g : R → R₂} → (∀ n a → Cp zero thr a → F n ⊴² g a) → L.lim F ⊴² G.lc (inj₂ (inj₁ tt)) g` | 第 2 层的读回关系 | Rel2 | 定义 |
| `⊴²-cp`, `⊴²-+ˡ`, `⊴²-+ʳ` | `∀ {k} {x : L.Ordᶜ k} {η η′} → x ⊴² η → Cp L2 η η′ → x ⊴² η′`；`∀ θ {k} {x : L.Ordᶜ k} {η} → x ⊴² η → x ⊴² plus L2 θ η`；`∀ {k} {x : L.Ordᶜ k} {η} → x ⊴² η → ∀ η′ → x ⊴² plus L2 η η′` | 右边沿第一位置上移；左右加法 | Rel2 | 定理 |
| `add₂`, `suc-step²` | `∀ {x : T₂} {η} → x L.≅ x → x ⊴² η → ∀ {x′ : T₂} {η′} → x′ ⊴² η′ → (x L.+ x′) ⊴² plus L2 η η′`；`∀ {A : T₂} {β} → A L.≅ A → A ⊴² β → L.lim (iterᴸ (A L.+_) L.zero) ⊴² succ L2 β` | 加法上下文；ω 倍 | Rel2 | 定理 |
| `F2.Fold22` | `∀ {X : T₂} {η} → X ⊴² η → X L.≅ X → L.ψ (σ₃ L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σ₃′ X) ⊴² ψ₂ (G₃ η)` | ψ₂(Ω_Ω+X) 不高于 ψ₂(G₃ η) | Fold2 | 条件（模块参数 `Diag₂`） |
| `F2.Fold21` | `∀ {X : T₂} {η} → X ⊴² η → X L.≅ X → L.ψ (σB L.zero) (λ r → r) (L.add (L.Ω S2.ℓ₀) σ₃′ X) ⊴⁺ ψ₁ (G₃ η)` | 目标层 1 | Fold2 | 条件（同上） |
| `F2.fold2²` | `∀ {X : T₂} {η} → X ⊴² η → X L.≅ X → L.ψ⁰ (L.add (L.Ω S2.ℓ₀) σ₃′ X) ≼ NA.read (Ψ₀ (G₃ η))` | 目标层 0，值（部件 `Fold12 Fold02 Ctx2 Fold1²2 Fold0²2 Fold1²1 Fold0²1 fold1² fold0²` 同档） | Fold2 | 条件（同上） |
| `X₃≼ᵈ` | `Diag₂ᵀ → X₃ ≼ NA.read W.TΛ`，其中 `Diag₂ᵀ = L.ψ (σ₃ L.zero) (λ r → r) (L.Ω S2.ℓ₀) ⊴² ψ₂ G.top` | 前提只剩第 2 层的对角定理 | Three | 条件 |
| `F₂-form` | `∀ n → F₂ n ≡ L.ψ (σ₃ L.zero) (λ q → L.lim n q) (L.Ω (S2.ℓ₀ L.[ n ]ᴵ))` | 静态对角线的各项 | Diag2 | 定理 (`refl`) |
| `F₂0⊴K` | `∀ a → Cp zero thr a → F₂ 0 ⊴² K₂ a` | 第 0 项 ψ₂(Ω₁) 在门槛以上的一切分支之下 | Diag2 | 定理 |
| `chain→diag` | `Chain₂ → Diag₂ᵀ`，其中 `Chain₂ = ∀ n → Σ ℕ (λ m → F₂ (suc n) ⊴² K₂ (G.suc (ξ m)))` | 对角定理归约到第 2 层的 BTBO 链点 | Diag2 | 条件 |
| `X₃≼ᵇ` | `Chain₂ → X₃ ≼ NA.read W.TΛ` | 本路的最终结论 | Diag2 | 条件 |
| `lim-src₀`, `root-fold₂`, `root-fold₁` | `W.cmpw V2 s₃ (WL.nrmk zero (G.suc (ξ 0)) , WL.nrmk-lgl zero (G.suc (ξ 0)) , inj₁ tt) ≡ fold`（`root-fold₁` 把 `s₃` 换成 `s₂`）；`lim-src₀` 说该位置的 `lev` 是 `lim` | 链点根上源层号是 ℕ 极限，目标层 2 和 1 都折叠 | Diag2 | 定理 (`refl`) |
| `foldM₂` | `∀ (a : MT.R) (l : M.Lgl M.zero a) {κ} → Corr κ MT.⌜ a ⌝ → ∀ {ℓ} (p : L.suc (L.suc L.zero) L.<ᴵ ℓ) (σ : L.Simᴵ κ ℓ) → RelF (M.suc (M.suc M.zero)) (L.ψ p σ (L.Ω κ)) (MF.Ψ (M.suc (M.suc M.zero)) (MT.lv a l) (x₂ MT.⌜ a ⌝) M.G.top)` | 主线 `FOLD` 在目标层 2 上 | Main2 | 定理 |
| `R₂ᵗ` | `∀ a (l : Lgl zeroN a) → RR (M.suc (M.suc M.zero)) L2 (MF.Ψ (M.suc (M.suc M.zero)) (MT.lv (toM a) (toM-lgl a l)) (x₂ MT.⌜ toM a ⌝) M.G.top) (T₂ᵗ a l)` | 主线的树与一致折叠互模拟 | Main2 | 定理 |

#### 4 办法

**参数化。**
- **第 1 层**：`YiSyncFold` 的 `fold1⁺`, `Fold₁ᴾ` 与 `YiShpEps` 的 `fold0`, `ctxA` 改成对分支族记录 `Pfx` 参数化（模块 `P1`）。
  - 记录的字段：`top` 是第一位置，单调，后继，嵌入上的后继。
  - 原来靠定义性展开的地方改成字段：`nd0`, `nt0` 是目标层 0 上的链，`nd1`, `nt1` 是目标层 1 上的保留。
  - 用两个实例检验字段可满足：`G₂`（原情形）与 `G₃′`。
- **第 2 层**：没有写一般的第 k 层定义，只对 k = 2 写了具体的关系 `⊴²` 与三条折叠。

**与 `YiSync` 相比新用到的：**
1. `n1`, `t1` 的假设取 `y ⊴⁺ a` 并带 `y ≅ y`。原因是第 1 层的穿透用到 `tr⁻ (s≅ z≅)`，它与原树只有 `≅`（`≅-tr⁻`），要经 `⊴⁺` 的 `≅⊴` 换代表。
2. `plus L2 θ (em tt a)` 不再是嵌入，所以要单独写把 `⊴⁺` 与 `NA._⊴_` 搬到 θ 之上的规则（`emb₁`, `emb₀`, `emsh`）。
3. 加法分三层写：`add₂`, `add₁₂`, `add₀₂`，对应 Sim `σ₁₂`, `σ₀₂`（`x + up y` 会换 Sim）。
4. 新的反演引理：`upˡ⁻`, `upʳ⁻`, `u≅⁻`, `lᵢ≅⁻₁`, `lᵢ≅⁻₀`。
5. 层号 1 的结点在目标层 1 和 0 上折成层号 1 的链（`Node1`），链点关系由 `Fold21` 给出；层号 0 的结点用 `Node0`。
6. 层号 1、0 的嵌入经 `ψ-≅`, `ψ⁰-≅` 换 Sim（`σ₃″`, `σ₃‴` 换成 `σA`, `S2.σ₁`），交给 `P1 P₃′`。
7. `dg` 只放在 `R₂` 的层号 0 结点上，门槛仍是 `top + Tw 2`；层号 1 的结点不需要 `dg`。
8. `T⁺ʷ` 里的 Ω₃ 结点经 `c-d₃` 落在根链第 1 点之下，用到 `c-g`（照搬 `YiLamVLost`）与 `cT`。

**翻译账（判断）。** `n1`, `t1`, `n0`, `n0′` 的形状读自参照 `ψ` 在层号 1、0 上的穿透规则，属于 AGENTS 说的加深翻译的标志。`dg` 的门槛和 `≅⊴` 来自树侧折叠的需要。

#### 5 第一个障碍

**位置。** 缺的引理就是 `Chain₂`：

`Chain₂ = ∀ n → Σ ℕ (λ m → F₂ (suc n) ⊴² K₂ (G.suc (ξ m)))`

**编译事实。**
- 第 1 层的 `chain₁′` 是这样来的：主线 `FOLD`（`RelF 1`）、互模拟、`br₁` 换成 `NA._⊴_`、再加嵌入（`lower₁ᴱ`, `Fix01`, `fixQ`）。
- 在第 2 层，主线一侧与互模拟都编译通过（`foldM₂`, `R₂ᵗ`）。
- 断在把 `RelF 2` 换成 `⊴²` 的层号 1 结点规则。
  - 实验文件 `<实验目录>/agents/step/S6.agda`（不在仓库里）写了这一句：`br₂ θ (ndr {r = inj₁ _} {q = L.zero} (cs cz) h) (rc {r′ = inj₁ _} _ hh) = n1 (λ y a q t → br₂ θ (h y _ q) (hh _ a _))`
  - 检查器报错原文：
```
S6.agda:87.32-33: error: [UnequalTerms]
(y OCF.Lean.YiSyncRel.⊴⁺ a) !=<
((M.suc M.zero OCF.Lean.YiLeanValRel.Lvl.⊴ (λ _ → RelF M.zero))
 (OCF.Lean.YiLeanValRel.SLs M.zero (RelF M.zero)
  (OCF.Lean.YiLeanValRel.RelP M.zero))
 Data.Unit.Base.⊤ (OCF.Lean.YiLeanValRel.topS M.zero)
 (λ _ → Data.Empty.⊥) y _a_109)
when checking that the expression q has type
OCF.Lean.YiLeanValRel.SLs (M.suc M.zero) (RelF (M.suc M.zero))
(OCF.Lean.YiLeanValRel.RelP (M.suc M.zero)) (inj₁ x) y _a_109
```
- 走这条路缺的引理，Agda 类型是：

  `∀ {y : T₁} {a : NA.R₁} → y ⊴⁺ a → Σ (M.Raw (M.suc M.zero)) (λ a′ → RelF (M.suc M.zero) y a′ × RR (M.suc M.zero) (suc zero) a′ a)`

**判断（没有编译的否定，所以只写 "未走通"）。**
1. 上面这条引理一般不成立。`⊴⁺` 有对角规则 `dg`，例如 `Diag` 把 ψ₁(Ω_{ℓ₀}) 放到 `ψ₁ top` 之下；`RelF 1` 没有对角规则，YiL1 回报正是因此才加了 `dg`。
2. 也不能把 `n1` 的假设缩到 `RelF 1` 的像上。`Fold21` 与 `fold2²` 要把这个假设用到链点 c n = iter (ψ₁(Ω_Ω + f ·)) Ω₁ 上，而 c n ⊴⁺ δ n 要经 `Diag`（`Z1`），也就是经 `dg`。
3. 因此第 2 层的 BTBO 链点要一条新的折叠定理：在一致折叠一侧，对所有层号 ≥ 3 的层建立关系（BTBO 链点内部有层号 3 及以上的链，例如 ψ₂(Ω_m) 要经第 m−1 层的链），并且这些层上层号 1 的槽位用带 `dg` 的 `⊴⁺`。主线的 `RelF` 家族在层号 1 的槽位上不能借用。
4. 第 1 层没有遇到这个问题，因为那里槽位只有层号 0，假设是值 `y ≼ read a`，两侧相同。

#### 6 偏离与事故

- 多交了两个文件，都在前缀内：`YiStepDiag2` 把对角定理归约到链点并证出第 0 项；`YiStepMain2` 是主线在目标层 2 上的一半。
- 一次编译错误，已修好。`YiStepFold2` 第一版报 `NotInScope N.hm`，原因是模块参数不会作为模块内容导出。改成直接写递归调用。
- 修改方式：自己的文件用 python 字符串替换和 Edit 工具改的。
- 试验做法：用纯 `.agda` 的实验文件 `S1` 到 `S7` 查形状、找错误。另用 `agda --interaction` 的 `Cmd_compute_toplevel` 求了几个范式（例如 `ψ₂ top` 与参照在结点上的穿透形状）。这些都在 `<实验目录>/agents/step/`，不进仓库。
- 编译命令外面加了 `/usr/bin/time -l` 量内存；退出码是 agda 自己的，没有经过管道。
- 没有用 `--ignore-interfaces`。只删过自己 7 个模块的接口，用的是字面路径。没有碰已有文件、`src/`、`archive/`。
- 简报的第 2、3 步没有做，因为第 1 步没有拿到无前提的定理；理由见 §1 与 §5。

文件都在 `<仓库>/probes/OCF/Lean/`：
- `YiStepTree.lagda.md`
- `YiStepPfx.lagda.md`
- `YiStepRel2.lagda.md`
- `YiStepFold2.lagda.md`
- `YiStepThree.lagda.md`
- `YiStepDiag2.lagda.md`
- `YiStepMain2.lagda.md`

冷编译日志在 `<实验目录>/agents/step/`，文件名是 `cold-YiStep*.log`。
