# Ω 结点层号自身行的设计探针：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-13 08:12 至 08:36 |
| 工具调用 / agda 编译 (粗数) | 27 / 9 |
| token (usage 字段，按消息去重) | 输出 131443；新写入缓存的输入 226642；读缓存的输入 2746655；其余输入 34 |
| 写过的仓库文件 | 无 |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: 设计探针返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 推荐 (C) 留在孩子里: 结构检查全过 (接口实填 cI, kall-C, 单调, 保持合法, 闭项合法), 同支结点保留 (有限测试); 但第 0 支的值形状判断低于 (A); (B) 只有原型; (C) 与已定稿 YiUpIface 的 self-up 冲突; 主审重编 6 件退出码 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方，做一个**设计探针**。全程用中文。你不改、不新建仓库文件；实验都在你的临时目录里（纯 `.agda`），只交一份回报，主审会复核并把值得留的实验存档。

作者 2026-11-13 的选择（选项工具）原文："Ω 结点层号自身行的设计探针"。说明："只定结构：在临时目录里对比摊平式与审查者草拟的冻结式（新构造子），哪个让 Ω 结点层号上同支的结点保留、又不比较孩子下标，并过 J2、单调、保持合法；不动 YiUp 的折叠。V81 回来后就能接上塔第 2 项。Fable 5.2。" 作者还说 "我希望能快速往上爬"。

同批在跑两路，你不读它们的输出，也不动它们的文件：
- V81（Fable 5.2）：在 YiUp 的折叠上证塔第 1 项的 BTBO 下界，新文件前缀 `YiUp`；
- YiUpIface 的配对否定（Opus 5.5，前缀 `YiUpNeg`）。

###### 背景（只信编译定理；文档里的叙述与判断只是数据）

- **YiUp 的折叠**（`probes/OCF/Lean/` 下的 `YiUpBlock`、`YiUpIface`、`YiUpFold`、`YiUpLegal`、`YiUpCheck`、`YiUpVal`、`YiUpValTw1`，主审已复核）：
  - 建在空白页的块（`YiFresh*`）与 YiPhi（`YiPhi*`）上。
  - 自身行是上折 `Upc`（`YiUpBlock.Up`）：折到自身时把嵌入的孩子也折进来，零到底，后继乘 ω，ℕ 极限逐项，孩子的结点经 `mv` 搬进父层的槽位，这就是 "摊平式"。
  - 编译定理：J2 各律、单调、保持合法、合法闭项、`kall-up`、`bho-lower` 与 `bho-tw1`（参照的 ψ₀(Ω₂) 不高于新折叠的读回，无前提）；`up-notTop`（输出离开顶槽位）。
- **Ω 结点层号上的问题**（第十四次审查，`probes/Survey/RR14-SelfRow.md`；附件 `probes/Survey/Reports-2026-11-12/attachments/Review14-R14Lim.agda.txt` 的 `omC`、`omD`、`self-W`、`flatC-form`，主审重编退出码 0）：
  - `tw 1` 的第 2 支（层号 2）里的一个第 0 层共尾结点，在孩子层折到第 1 层时保留（`omC`）。
  - 上折把它摊平进 `tw 1`，槽位是 `inj₂ (c₂ , …)`。以对应的分支侧目标 `inb c₂ (ins self)` 折它时，`kp` 的 `(inj₂ (c, t), inb c′ w)` 一行走默认，尽管两个 `c₂` 字面相同（`omD`）。
  - 要让它保留就得判定同支。
- **已编译的边界**（不能要求的）：
  - `YiPhiNegB.wdec`、`wdecα`：分支侧 "同支交给孩子、异支回退" 弱判定合法规范下标的字面相等；`wlpo`：加函数外延得 WLPO。
  - `YiPhiNegB.viaE→dec`：经由算出的同支证据，就判定字面相等。
  - `YiPhiNegKSem.fullSem→lpo`、`YiUniNegStep.step-full→lpo`：按层号的 "能保留处都保留" 推出 LPO。
  - `probes/OCF/Barrier.lagda.md`：下标不能有三歧。
- **审查者草拟的冻结式**（RR14 §2 问题 4 (B)，未编）：
  - 在 Ω 结点层号上不摊平，加一个构造子 `ex : T → (c : C) → D c → T`，读作 x·ω^(↑y)，把上折留成数据，孩子保持嵌入。
  - 折叠要一个 "指数模式"：底的变换对孩子树 y 递归。结点与目标同在孩子 c 里时，用孩子层的 `kp` 比路径，同支由 "身在孩子 c 里" 给出，不判定。
  - 代价估计：第 1 层多一个构造子，`◃` 多两条；第 2 层折叠约翻倍，底变成高阶；停机靠 (y, x) 的字典序，未验证。

###### 要做（每做成一件先编译）
1. **最小模型**：在临时目录里写一个只含 zero、suc、lim 与 Ω 结点层号（`Ωₗ`，至少能表示 `tw 1`、`tw 2`）的小块，或直接导入 YiUp 的模块。在上面分别实现：
   - (A) 摊平式自身行，即现在的 YiUp；
   - (B) 冻结式（`ex` 构造子加指数模式的折叠）；
   - 你能想到的第三种：要求不比较孩子下标，不用 `wdec`、`fullSem` 一类被否定的东西。
2. **对每种写法编译检查**：
   - (a) `omD` 那种配置：同支的结点在以后以分支侧目标折叠时是否保留（有限测试）；
   - (b) J2 各律（照 `YiUpIface` 的陈述，`refl` 或命题等式）；
   - (c) 单调（无前提为好）与保持合法；
   - (d) 塔与读法 ψ₀(Λ) 的闭项合法，或至少 `tw 2` 一项；
   - (e) 停机由检查器接受（`--safe`）；
   - (f) 若可能，一条值的形状测试：对照 YiUp 在 `tw 2` 一站链的第一、二步，看哪种不低于 (A)。
3. **判决**：推荐哪一种接进 YiUp，写出接入的改动清单（第 1 到 3 层各改什么，估行数），以及 V81 的模拟要为它加哪些情形。

###### 先读什么
- `AGENTS.md` 全篇。
- `YiUpBlock`、`YiUpFold`、`YiUpIface` 全读；`YiUpLegal` 的结构（检索）；`YiPhiBlock`（路径、`Ev`）与 `YiPhiFold`（`kp` 的 `Ωₗ` 六行）。
- 附件 `Review14-R14Lim.agda.txt` 全读；`probes/Survey/RR14-SelfRow.md`。
- `YiPhiNegB` 文首与 `wdec`、`J2-Ωb`、`Ωb-off` 的陈述（检索）。
- 已发表的 `src/OCF/BTBO.lagda.md` 的折叠（只读，检索）。

查签名用检索，不整篇读大文件。

###### 规则
- **不改、不新建仓库文件。** 实验只放临时目录 `<实验目录>/agents/omega`（先 mkdir），用纯 `.agda`，选项行 `{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns #-}`。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes -i <你的临时目录> <你的临时目录>/<文件>.agda > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 另有两路在编译，堆上限 6G，同时只跑一个 agda。
  - 不用 `--ignore-interfaces`，不删任何仓库里的 `.agdai`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。日志落文件，只看首个错误附近。
- 不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、K、`--irrelevant-projections`、`--cubical`；函数外延只能作前提。
- 不比较孩子下标，没有按层号字面判等的派发；不要求下标的三歧。
- 不在临时目录之外写文件，不 `rm` 临时目录之外的东西，不 `pkill`，不装包，不提交。
- **停下的条件**：同一处两次重新设计仍过不了检查器；需要函数外延或 K；6G 仍耗尽。没有编译的否定时只写 "未走通"。
- **过程要求**：读完上面的文件后尽快动手，第一个文件在 30 分钟内写出并编译；每次回复都要有工具调用，不要在一次回复里只思考。

###### 回报格式（只在回报里交一次）
1. 判决：推荐的写法；三种写法在 (a) 到 (f) 上各自的结果（表，标档）；一段话说对 "往上爬" 意味着什么。
2. 文件表：临时文件、代码行数、退出码。
3. 定理表：名字、逐字的陈述、一句白话、文件、档（编译定理 / 条件定理 / 有限测试 / 判断）。
4. 接入 YiUp 的改动清单与行数估计；V81 的模拟要加的情形。
5. 第一个障碍（若有）：精确到引理，附检查器报错原文。
6. 偏离与事故。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

### 回报: Ω 结点层号自身行的设计探针 (Fable 5.2)

临时目录 (下称 `<实验目录>`): `<实验目录>/agents/omega`。仓库文件未改、未新建。

#### 1 判决

**推荐第三种写法 (C)，但它不是在各项上都不低于 (A)**：它通过了 (a) 到 (e) 的全部结构检查，单步的值在第 0 支上低于 (A)（判断，见下）。

- **对纲领与目标**：三种写法都不比较孩子下标，不用 `wdec`、`fullSem`，不要求三歧，不触壁垒。
- **(C) 的块改动为零**：`YiFreshBlock` 与 `kp` 都不动。它来自树侧的要求（同支信息由 "身在孩子里" 给出），没有读记号的规则。
- **(C) 与现接口冲突**：`YiUpIface.self-up` 对一切层号陈述为 `Upc`，(C) 在 Ω 结点层号上按设计不满足它。按 "定稿后只增不改"，接入要另开接口，这一点要作者定。

三种写法：

- **(A) 摊平式**：现在的 YiUp，不改。
- **(B) 冻结式**：只做了指数模式的折叠原型 `Ex`（只有 `ψs` 一半，不带 `ex` 构造子，不进互递归）。完整的 (B) 没有做。
- **(C) 留在孩子里**：Ω 结点层号的自身行写成 `up (ψs … self β x) c (selfC (h c) … y)`。孩子树 y 先做孩子层自己的自身折叠（底取孩子层的 Ω 树 `Ωt (h c)`），再原样嵌入。后继与 ℕ 极限层号仍是上折。上折走到 Ω 结点层号孩子里的 `up` 时停下，把那一段沿下行链加法地重新嵌入（`embD`）。

| 检查 | (A) 摊平 | (B) 冻结，指数模式原型 | (C) 留在孩子里 |
|---|---|---|---|
| (a) omD 配置 | 不保留：`omD`；深一层 `suc (tw 1)` 重现：`omD2-A`（有限测试） | 链步在孩子里做时保留：`scope-keeps`；自身目标输出父层结点，即第二遍摊平：`self-flat`（有限测试） | 保留，自身行做两遍后仍保留：`P-kept`、`omD-C`、`P-kept²`、`omD-C²`；深一层孙辈留在原处：`deep`（有限测试） |
| (b) J2 各律 | 已有 `YiUpCheck.upI`（主审已复核，本路只导入） | 未做 | `cI : YiPhiIface.Iface`，各律 `refl`，`J2-lim` 先用 `eqℕ-refl`；`kstep` 是 `refl`；`kall-C`（编译定理） |
| (c) 单调与保持合法 | 已有 `YiUpLegal` | 未做 | `mono⊥`、`monos` 无前提；`pres⊥`、`press` 前提同 YiUp（编译定理） |
| (d) 闭项合法 | 已有 | 未做 | `twᶜ-leg`（一切 n）、`EBOᶜ-leg`，无前提（编译定理） |
| (e) 停机 | 已有 | 原型被检查器接受 | 被检查器接受（Ω 行自身行按层号分三行写） |
| (f) 值的形状 | 基准：`f-A`、`suc-A` | 后继行是底的折叠迭代的部分和：`suc-B`（有限测试） | 第 0 支与 (A) 不同形：`f-C`、`f-C₀`、`f-C₁`、`br0-C`（有限测试） |

**关于值，只有形状测试，没有序的定理。** 以下是纸面判断：

- tw 2 一站链第一步的第 0 支折到第 0 层：(A) 是 "对 β, β+β, … 逐项折叠的极限"，(C) 是 "β 的折叠上做 1, 2, … 次 `next` 的极限"。按读法前者高于后者。
- 原因：(C) 把孩子部分加法地放在 x 的折叠旁边（读作 x′ + β′·ω^y），(A) 是 x′·ω^y。
- 反过来，(A) 在 omD 配置里把同一孩子里的结点提前折掉，(C) 不会。
- 两种损失哪个对 tw 2 的下界更要紧，本路没有测到。

**(B) 的三条发现**（前两条有限测试，第三条判断）：

- 指数模式要把底写成折叠族（高阶），原型里停机没有问题。
- 冻结项对自身目标再折一次，输出只能是父层槽位的结点（`self-flat`），所以 omD 配置推迟一遍后重现。要避免，自身行得写成 `ex (F b) c (selfC y)`，那与 (C) 同样丢乘法耦合。
- 若把 `ex` 的非自身行照 `up` 的行写，折到第 0 层的值在第 0 支上与 (C) 同形，也低于 (A)。所以 "加构造子而不做指数模式" 换不来值。

**对 "往上爬"**：

- V81 的塔第 1 项不受这次选择影响（判断）。理由：(C) 与 YiUp 的文本差别只有 Ω 结点层号的自身行与上折在 Ω 结点层号 `up` 处的一行；tw 1 的孩子层由第 0 层的树读出，不含 Ω 结点层号。这一点没有编译证明，`same0` 只是一个具体输入上的 `refl`。
- 塔第 2 项的链一上来就经过 tw 1 的自身行，所以这个选择在第 2 项的第一步就起作用。
- 若采用 (C)，第 2 项的模拟可以直接接上；先验的一条是 "(C) 的第一步是否还够得着参照树"。若够不着，退路是 (A)，并接受 omD 的损失；(B) 的完整版代价最高。

#### 2 文件表

都在 `<实验目录>`，纯 `.agda`。选项行在简报给的之外，除 `OmA` 都加了 `-W noUnsupportedIndexedMatch`（仓库库文件里本来就有）。禁用构造检索为 0：无 `postulate`、洞、`TERMINATING`、K、Funext。

| 文件 | 行数 | 退出码 | 内容 |
|---|---|---|---|
| `OmA.agda` | 70 | 0 | (A) 在 YiUpFold 上的 omD 配置 |
| `OmCFold.agda` | 105 | 0 | (C) 的折叠：`unT`、`embD`、`Up′`、`selfC`、`ψ⊥`、`ψs` |
| `OmCLegal.agda` | 277 | 0 | (C) 的单调、保持合法、闭项 |
| `OmCCheck.agda` | 177 | 0 | (C) 的接口实填、`kall`、自身行律、omD 测试、形状 |
| `OmBProto.agda` | 120 | 0 | (B) 指数模式原型 `Ex` 与测试 |
| `OmF.agda` | 74 | 0 | (A) 与 (C) 的形状对照，(A) 深一层的 omD |

#### 3 定理表

"编" 是编译定理，"测" 是有限测试。

| 名字 | 陈述（逐字） | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `mono⊥` | `(ℓ : L) (ε : Ev ℓ) (B : Base ℓ) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → zero ⊢ ψ⊥ ℓ ε B x ◃ ψ⊥ ℓ ε B y` | (C) 到第 0 层的折叠单调，无前提 | OmCLegal | 编 |
| `monos` | `(ℓ : L) (ε : Ev ℓ) (B : Base ℓ) (j : L) (v : j ≤ ℓ) (β : Tr j) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → j ⊢ ψs ℓ ε B j v β x ◃ ψs ℓ ε B j v β y` | (C) 到任意目标的折叠单调，无前提 | OmCLegal | 编 |
| `pres⊥` | `(ℓ : L) (ε : Ev ℓ) (B : Base ℓ) → LegB ℓ B → (x : Tr ℓ) → Leg ℓ x → LN zero (ψ⊥ ℓ ε B x)` | 保持合法且非零；前提可满足（`LegB₀`） | OmCLegal | 编 |
| `press` | `(ℓ : L) (ε : Ev ℓ) (B : Base ℓ) → LegB ℓ B → (j : L) (v : j ≤ ℓ) (β : Tr j) → LN j β → (x : Tr ℓ) → Leg ℓ x → LN j (ψs ℓ ε B j v β x)` | 同上，任意目标 | OmCLegal | 编 |
| `Up′-mono` | `∀ {ℓ} (j : L) (ε : Ev j) (d : Dn ℓ j) (b : Tr ℓ) {x y : Tr j} → j ⊢ x ◃ y → ℓ ⊢ Up′ j ε d b x ◃ Up′ j ε d b y` | 在 Ω 结点层号处停下的上折单调 | OmCLegal | 编 |
| `Up′-LN` | `∀ {ℓ} (j : L) (ε : Ev j) (d : Dn ℓ j) (b : Tr ℓ) → LN ℓ b → (y : Tr j) → Leg j y → LN ℓ (Up′ j ε d b y)` | 它保持合法且非零 | OmCLegal | 编 |
| `twᶜ-leg` | `(n : ℕ) → Leg zero (twᶜ n)` | 塔各项的闭项合法 | OmCLegal | 编 |
| `EBOᶜ-leg` | `Leg zero EBOᶜ` | 读法 ψ₀(Λ) 的闭项合法（只是合法，不是值） | OmCLegal | 编 |
| `cI` | `cI : PI.Iface` | (C) 实填 `YiPhiIface.Iface`：J2 八条、单调、保持、闭项、`kstep` | OmCCheck | 编 |
| `kall-C` | `KAll cI` | k 侧链步对一切孩子保留基底里的结点 | OmCCheck | 编 |
| `self-Ωₗ` | `… → ψs (Ωₗ k h) ε B (Ωₗ k h) self β (up x c y) ≡ up (ψs (Ωₗ k h) ε B (Ωₗ k h) self β x) c (ψs (h c) (proj₂ (proj₂ ε c)) (B₀ (h c)) (h c) self (Ωt (h c)) y)` | (C) 在 Ω 结点层号的自身行律；`self-suc`、`self-lim` 是上折两条 | OmCCheck | 编 |
| `P-kept` | `… → ψs (tw 1) ε₁ B (tw 1) self β (up x c₂ (P G)) ≡ up (ψs (tw 1) ε₁ B (tw 1) self β x) c₂ (Ω (inj₁ tt) (λ z → Ω (inj₂ (inj₁ tt)) (λ z′ → selfC two tt (G z z′))))` | 自身行后两层结点都还在孩子 `two` 里，槽位不变 | OmCCheck | 测 |
| `omD-C` | `(B′ : Base two) (β′ : Tr one) (G : Tr zero → Tr two) → IsΩ (ψs two tt B′ one (ins self) β′ (selfC two tt (nodeC G)))` | 外层结点的链步在孩子里做，第 0 层结点保留 | OmCCheck | 测 |
| `omD-C²` | `… → IsΩ (ψs two tt B′ one (ins self) β′ (selfC two tt (selfC two tt (nodeC G))))` | 自身行做两遍后仍保留 | OmCCheck | 测 |
| `deep` | `… → ψs (suc (tw 1)) ε₁ B (suc (tw 1)) self β (up X tt (up x c₂ (P G))) ≡ up (Up′ (tw 1) ε₁ (down stop tt) (ψs (suc (tw 1)) ε₁ B (suc (tw 1)) self β X) x) tt (up zero c₂ (selfC two tt (P G)))` | 深一层：孙辈没有被摊进 `suc (tw 1)` | OmCCheck | 测 |
| `fallback` | `… → ψs (tw 1) ε₁ B one (inb c₂ (ins self)) β (up X c₂ (nodeC G)) ≡ ψs (tw 1) ε₁ B one (inb c₂ (ins self)) β X + ι one (ψ⊥ two tt (B₀ two) (nodeC G))` | 界限：在 tw 1 层直接以分支侧目标折嵌入分支仍回退（该行与 YiUp 相同） | OmCCheck | 测 |
| `omD` | `(B : Base (tw 1)) (β : Tr one) (X : Tr (tw 1)) (G : Tr zero → Tr two) → IsLim (ψs (tw 1) ε₁ B one (inb c₂ (ins self)) β (Upc (tw 1) c₂ X (nodeC G)))` | (A)：摊平后以同支目标折，走默认（在 YiUpFold 上重现审查附件） | OmA | 测 |
| `omD2-A` | `… → IsLim (A.ψs (suc (tw 1)) ε₁ B one (ins (inb c₂ (ins self))) β (Upc (suc (tw 1)) tt X (up x c₂ (nodeC G))))` | (A) 的同一现象在 `suc (tw 1)` 重现 | OmF | 测 |
| `scope-keeps` | `(Bs : Base two) (Φ : Fam two) (β₀ : Tr one) (G : Tr zero → Tr two) → IsΩ (Ex two tt Bs Φ two stop one (ins self) β₀ (nodeC G))` | (B) 原型：链步以孩子层为根时结点保留 | OmBProto | 测 |
| `self-flat` | `… → exRow (tw 1) ε₁ B (tw 1) self β b c₂ (P G) ≡ Ω (inj₂ (c₂ , inj₂ (inj₁ tt))) (λ z → Ω (inj₂ (c₂ , inj₂ (inj₂ (inj₁ tt)))) (λ z′ → Ex … (G z z′)))` | (B) 原型：自身目标的输出是父层槽位的结点 | OmBProto | 测 |
| `f-A` | `(B : Base (tw 1)) → A.ψ⊥ (tw 1) ε₁ B (next β₁) ≡ lim (λ n → A.ψ⊥ (tw 1) ε₁ B (iter (β₁ +_) β₁ n))` | (A) 第 0 支到第 0 层的形状 | OmF | 测 |
| `f-C` | `(B : Base (tw 1)) → C.ψ⊥ (tw 1) ε₁ B (up β₁ zero (next (suc zero))) ≡ lim (λ n → C.ψ⊥ zero tt (dW zero (λ c → zero ⊕ ↑ zero c) ε₁ B zero β₁) (iter (suc zero +_) (suc zero) n))` | (C) 同一支的形状；`f-C₀`、`f-C₁` 给出前两项是 1、2 次 `next` | OmF | 测 |
| `step1-C`、`step1-A` | `stepC zero ≡ Ω (inj₁ (inj₁ tt)) (λ c → up (Ωt (tw 1)) c (selfC (h₁ c) (proj₂ (proj₂ ε₁ c)) (Ωt (h₁ c))))`；`stepA zero ≡ Ω (inj₁ (inj₁ tt)) (λ c → Up (h₁ c) (down stop c) (Ωt (tw 1)) (Ωt (h₁ c)))` | tw 2 一站链第一步在两种写法下的形状 | OmCCheck | 测 |

判断（未编译）：

- (C) 第 0 支的值低于 (A)。
- 链的极限处两者是否相同，没有测。
- tw 1 的折叠不经过改动的两行。
- (B) 完整版第 0 层一半要把底写成 `Base → Base` 的变换。
- (B) 后继行相邻项的 `◃` 得不到：它要折叠对底单调，而默认行输出 `lim (cum …)`，第一位置序下逐项 `◃` 推不出两个极限之间的 `◃`。原型里用 `cum` 绕开，合法性没有试。

#### 4 接入 YiUp 的改动清单（按 (C)）与行数估计

按仓库规则不改已有文件，用新文件取代 `YiUpFold`、`YiUpLegal`、`YiUpCheck`、`YiUpIface`。

- **第 1 层（块）**：`YiFreshBlock`、`YiPhiBlock` 零改动。`YiUpBlock` 保留 `chP`、`chBr`、`Dn`、`mv`、`mvBr`；新增 `unT`（3 行）与 `embD`（3 行）。`Up` 与 `Upc` 搬进折叠的互递归：多一个 `Ev` 参数，Ω 结点层号的 `up` 一行改写。
- **第 2 层（折叠）**：互递归里加 `Up′`（9 行）与 `selfC`（2 行）；自身行由 1 行变 4 行，按层号分三行，零层空行。代码约 81 → 105 行。`kp` 不改。
- **第 3 层（合法性）**：新增 `u-inc`、`u-mono`、`u-leg`、`embD-inc`、`embD-mono`、`embD-leg`（约 30 行）与 `selfC-nz`、`selfC-LN`（4 行）。`Up′-mono`、`Up′-LN` 并入 `monos`、`press` 的互递归。自身行的情形由 3 条变 9 条。总量与 `YiUpLegal` 相当（探针 277 行，原 277 行）。
- **接口**：`self-up` 要拆成三条，Ω 结点层号一条换成 `self-Ωₗ`。这与 "定稿后只增不改" 冲突，也影响在跑的配对否定 `YiUpNeg`，要作者定。其余字段陈述不变；`kall` 证明与原文同文。
- **值文件**：`YiUpVal`、`YiUpValTw1` 与 V81 的新文件要对新折叠重编。上折的引用多一个 `Ev` 参数；所用各行文本相同（判断），没有重编验证。

**V81 的模拟要加的情形**（接塔第 2 项时）：

1. Ω 结点层号自身行的输出 `up b c (selfC (h c) … y)`：模拟关系要有一条 "嵌入的孩子树已做过孩子层的自身折叠，底是该层的 Ω 树"。这一条用到的新东西是孩子层的 `ψs … self`。
2. 上折在 Ω 结点层号孩子的 `up` 处的 `embD` 输出，即 `up X c₀ (up zero c (selfC … y′))`，在孩子层号是 `tw 1 ⊕ suc …` 时出现。
3. 目标是 k 侧（`ink self`）时，上面两种输出都经 J2-Ωk 交给孩子层折叠，沿用已有情形。
4. 先验的一条：第一步 `stepC zero`（`step1-C`）是否不低于参照树的对应项。这是采用 (C) 还是退回 (A) 的判据。

#### 5 第一个障碍

没有阻断性的障碍。两处检查器拒绝：

- **(C) 的自身行经辅助函数 `selfRow ℓ ε c b y` 分派时停机检查失败**（一次，改回按层号直接写三行后通过）。报错原文：
  ```
  OmCFold.agda:32.1-103.87: error: [TerminationIssue]
  Termination checking failed for the following functions:
    selfC, selfRow, ψs
  Problematic calls:
    ψs (lim g) ε B j (inl n w) β (up x m y) | eqℕ m n
    ψs j ε (B₀ j) j self (Ωt j) y
    selfC (h c) (proj₂ (proj₂ ε c)) y
    selfRow ℓ ε c (ψs ℓ ε B ℓ self β x) y
  ```
  原因没有查清。
- **tw 1 上两个折叠的 `refl` 对照**在 c = 1 时不过（`UnequalTerms`）：两边底记录里各带自己的折叠闭包，语法不同。这不是值不同的证据。相等的证明要函数外延，没有做。

**(B) 的完整版没有做**：`ex` 构造子进 `T` 要把块、运算、合法性、折叠整套搬一遍（估 1000 行以上的拷贝加情形），本路只做了原型。写 "未走通"，不是否定。

#### 6 偏离与事故

- **(B) 没有按简报做成 "`ex` 构造子加指数模式的折叠"**，只有不带构造子的原型，(b)(c)(d) 未做。
- **(C) 里孩子层自身折叠的底取常量 `Ωt (h c)`**，没有用 x 折到孩子层的值。原因：`◃u` 的单调要 `zero ◃` 孩子部分，无前提时只有 `Ωt-nz` 可用；底依赖 x 时单调要带前提。这是一个设计取舍。
- **(f) 只到第一步**；第二步的范式没有算。
- **(A) 的 (b) 到 (e) 没有重证**，沿用主审已复核的 YiUp 模块。
- 同时只跑一个 agda，堆上限 6G，没有用 `--ignore-interfaces`，没有删仓库的 `.agdai`。临时目录里留有各文件的 `.agdai` 与 `.log`。
