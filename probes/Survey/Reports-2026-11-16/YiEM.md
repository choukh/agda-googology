# 替身码域加嵌入码（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-17 03:57 至 04:44 |
| 工具调用 / agda 编译 (粗数) | 68 / 25 |
| token (usage 字段，按消息去重) | 输出 261251；新写入缓存的输入 755055；读缓存的输入 15178969；其余输入 120 |
| 写过的仓库文件 | `YiEMChain.lagda.md`, `YiEMNeg.lagda.md`, `YiEMRead.lagda.md`, `YiEMSync.lagda.md` |
| 文件前缀 | `YiEM` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 主审 8G 冷编 4 件全部退出 0，禁用构造 0，三件不读记号的导入闭包干净；扩展码 Read⁺，同步对象各来源的块都在码域里（way-sync、schema-sync）；现行替身不按块的码换基（seen≠code），要按码换基须改定义 |

## 简报原文

你的完整任务简报在 `<实验目录>/briefs/b77/YiEM.md`。先用 Read 工具完整读它，再逐条照做（含其中的 "规则" 与 "回报" 两节）。在仓库根目录 `<仓库>` 下工作。只新建你前缀的文件，不改任何已有文件。全程用中文。最后一条消息就是你的回报。

## 回报原文

#### YiEM 回报（替身码域加嵌入码，Opus 5.5）

##### 1. 判决

**这对纲领与目标意味着什么**
- 树、折叠、合法性的定义都没有动。新文件四个，三个不读记号，导入闭包为 0（`YiEMRead`、`YiEMChain`、`YiEMNeg`）；`YiEMSync` 是验收文件，闭包里有记号模块。
- 嵌入码取自树自己的 `emb` 与 `upz`，以及偏移的结构，没有读记号的基本列。闭包定理对变量 a、b 和路径 w 陈述，与阶段无关（`way-at`、`schema-at`）。
- 块一侧的结论（编译，按来源列出）：同步对象偏移里，way 行嵌入交下去的块都在扩展码域里，Ω 树的分支块与部分和块也在。三个证据实例逐字相同：`oᴱ ≡ oₛ`、`oᶻ ≡ oₛ` 都由 `refl` 得到。
- 但现行 `BS.ψ` 的 `seen` 一支并不按块的码换基。在 `yₑ` 那一格，`seen` 与按 `yₑ` 的码换基得到的树不同（`seen≠code`，编译否定）。要让折叠按码换基，折叠必须拿到块的码，而树不带码，这需要改定义。按规则，我停在这里，交作者定。

**各步到哪一步**
- 第 0 步完成，是编译定理。`yₑ` 在 `Domain⁺` 里，码是 `em tt (old omega)`；新码合法（读出是 `Tr⁺`，`fold⁺` 用的证据与 `fold` 相同）；第一位置关系经 `fold⁺` 保持。
- 第 1 步：按来源的闭包是编译定理，对一切链点 m（变量）成立。"到达 seen 的块只来自下表这几类" 是判断。chain m 上 seen 实际在哪些结点触发，未查。
- 第 2 步：没有找到到达 seen 而不在码域里的块。码域外的三类块都写成了编译否定，它们会不会到达 seen 是判断。找到的来源都不碰 V149 的方向反变，这也是判断。
- 第 3 步：代价与翻译账见下。

**覆盖表**（块的来源 × 在不在 `Domain⁺`）

| 块的来源 | ω 那一格（`YiBCReach`） | 真实链点 `a₁ (chain m)`，m 任意（证据 oₛ = oᴱ = oᶻ） | 档 |
|---|---|---|---|
| Ω 树在 Ω 形状结点上的分支块 `Ωt (h c)`。c 任意，含保留分支的变元，以及作孩子编号的回灌输出 | 在 | 在 | 编译：`omega-any`、`omega-sΩ` |
| Ω 树在 ℕ 极限结点上的部分和块 | 在 | 在 | 编译：`omega-sL`、`Lim.block-lim` |
| way 行嵌入的块（偏移里任一 ℕ 极限结点，任意 m 和 n） | 在（`yₑ-in`、`cell-emb`） | 在（`way-sync`、`Lim.way-lim`、`first-lim`；验收 `wayᴱ`、`wayᶻ`） | 编译 |
| 码树沿嵌入链的子块（到 Ω 形状结点时就是 seen 收到的块） | 在 | 在 | 编译：`code-in` 加 `schema-at`、`schema-sync` |
| 地板 `tw 1` 自身里的块（相对地板 `tw 0`） | — | 在。组合由同一组定理给出，`ev-tw` | 编译（零件）；组合是判断 |
| 上折输出作块 | 不在（`no-up-code⁺`、`up∉`）；到达 seen：判断为否（自身目标的嵌入行是上折，`self-row`） | 同左 | 否定是编译；到达是判断 |
| 嵌入进地板 | 不在（`floor-emb∉`）；`Ok⊕` 证据给的 way 路径都在偏移里（`way-at`） | 同左 | 编译 |
| 带非 Ω 树分支函数的块 | 不在（`odd∉`）；后继层 Ω 树的槽位只在自身目标下保留（`sS-keep`、`sS-keepᵘ`） | 同左 | 否定是编译；到达是判断 |
| 回灌输出在后继形状层作块 `suc c` | 后继层没有换基行；折进 c 之后遇到的块属于上面几类 | 同左 | 判断 |
| 证据不是 `Ok⊕` 形时 | 未查 | 未查 | — |
| seen 实际在哪些结点触发 | 已知（`reach`） | 未查 | — |

**问题表**

| 问题 | 位置 | 档 |
|---|---|---|
| `yₑ` 在扩展码域里 | `YiEMChain.yₑ-in` | 编译 |
| 码对沿偏移内路由嵌入后仍是码对 | `YiEMRead.emb-pre`、`cp-emb`、`way-in`、`way-at` | 编译 |
| 链点从第 1 个起都是 ℕ 极限，m 任意 | `YiEMChain.Feed.chain-L`、`chain-lim` | 编译 |
| 两个实例的证据就是读回证据 | `YiEMSync.oᴱ≡oₛ`、`oᶻ≡oₛ` | 编译（验收） |
| 现行 seen 与按码换基不同 | `YiEMChain.seen≠code` | 编译否定 |
| 到达 seen 的块只有上表几类 | — | 判断 |
| seen 在 chain m 上的触发位置 | — | 未查 |
| 从树恢复码是否可能 | — | 判断（未编译） |

**代价与翻译账**
- 代价：四个文件共 635 行，其中代码 398 行。码本身（定义加基本定理）约 40 行代码，闭包约 100 行，其余是链点实例与否定。YiBC 估的是 50 到 150 行，对应码本身加闭包。
- 新定义：`Read⁺`（按偏移分型）、`em`、`read⁺`、`source⁺`、`Domain⁺`、`fold⁺`；证明用的辅助：`pre`、`CP`、`downO`。
- 读自记号的：无。
- 由树的要求逼出的：
  - `em c` 就是 way 行里 `emb` 的一步 `upz`。
  - 码按偏移分型，是因为换基 a ↦ j 时 `j ⊕ nd s h` 的孩子集仍是 `Ch s`，同一个码才能在新地板上读出。
  - 允许任意孩子 c，是因为 `Ok⊕` 证据的路由是任意的 `⊑` 路径。
- 脚手架：只在证明里，没有进折叠（`BS.ψ` 没改）。
- 没有加深翻译的标志。提供信息的部分：对结构参数的一步定理 `way-at`、`schema-at`；四条否定划出码域外的块，以及现行 seen 与按码换基的差。

##### 2. 文件表

| 文件 | 总行 / 代码行 | 冷编退出码 | 记号 |
|---|---|---|---|
| `probes/OCF/Lean/YiEMRead.lagda.md` | 227 / 142 | 0 | 不读记号，闭包 0 |
| `probes/OCF/Lean/YiEMChain.lagda.md` | 183 / 106 | 0 | 不读记号，闭包 0 |
| `probes/OCF/Lean/YiEMNeg.lagda.md` | 182 / 120 | 0 | 不读记号，闭包 0 |
| `probes/OCF/Lean/YiEMSync.lagda.md` | 43 / 30 | 0 | 验收文件，闭包含记号 |

- 冷编时删掉自己的四个 `.agdai`，按依赖序 6G 逐个编，每个日志只有自己模块的 `Checking` 行。
- 禁用构造与本机路径的检索结果都是 0。
- 临时文件在 `<实验目录>/work/YiEM/`：`YiEM0.agda` 到 `YiEM4.agda`，都退出 0。

##### 3. 定理表

**YiEMRead**（编译定理，不读记号）
- 定义：
  - `data Read⁺ : L → Set`，构造子 `old : ∀ {b} → Read → Read⁺ b` 与 `em : ∀ {s h} (c : Ch s) → Read⁺ (h c) → Read⁺ (nd s h)`
  - `read⁺ : (a : L) {b : L} → Read⁺ b → Tr⁺ (a ⊕ b)`
  - `Domain⁺ : ∀ {k h} (S : Schema k h) c → Tr (h c) → Set`
  - `fold⁺ : ∀ {k h} (S : Schema k h) c → Read⁺ (offsets S c) → (j : L) → Ok j → floor S ≤ j → Tr⁺ j → Tr⁺ j`
- `in-old : ∀ {k h} (S : Schema k h) c {y : Tr (h c)} → Domain S c y → Domain⁺ S c y`
  白话：旧码域含在新码域里。
- `omega-row⁺ : ∀ {k h} (S : Schema k h) c j oj u β → fold⁺ S c (old omega) j oj u β ≡ seen S j oj u β c`
  白话：`seen` 就是 `old omega` 的换基。
- `omega-any : ∀ {k h} (S : Schema k h) c → Domain⁺ S c (proj₁ (Ωt (h c)))`
  白话：Ω 树块对任何证据、任何孩子都在码域里。
- `omega-sL : (a : L) (g : ℕ → L) → Ωt (a ⊕ nd sL g) ≡ limc⁺ (λ n → upz n (read⁺ a {g n} (old omega)))`；`omega-sΩ` 同形
  白话：Ω 树的子块是同一地板上的旧码。
- `code-in : {k : L} (a : L) (h : Tr k → L) (oa : Ok a) (v : k ≤ a) (ob : (c : Tr k) → OkO a (h c)) (c : Tr k) (d : Read⁺ (h c)) → Domain⁺ (schema a h oa v ob (λ _ → refl)) c (proj₁ (read⁺ a d))`
  白话：`rbO` 给的证据下，码域就是 `read⁺ a` 的像。
- `em-step : ∀ {s h} (c : Ch s) {d e : Read⁺ (h c)} → PointStep⁺ d e → PointStep⁺ {nd s h} (em c d) (em c e)`；`old-step`
  白话：嵌入码保持第一位置关系。
- `fold-step⁺ : ∀ {k h} (S : Schema k h) c d e j oj u β → PointStep⁺ d e → j ⊢ proj₁ (fold⁺ S c d j oj u β) ◃ proj₁ (fold⁺ S c e j oj u β)`
  白话：第一位置关系经换基折叠保持。
- `emb-pre : (a : L) {b b′ : L} (w : b ⊑ b′) (o : Ok (a ⊕ b′)) (d : Read⁺ b) → emb (a ⊕ b′) o (wk (⊕⊑ a w)) (read⁺ a d) ≡ read⁺ a (pre w d)`
  白话：沿偏移内的一段路由嵌入，码对仍是码对。
- `emb-∙ : (ℓ : L) (o : Ok ℓ) {i j : L} (v : i ≤ j) (w : j ⊑ ℓ) (y : Tr⁺ i) → emb ℓ o (v ∙ wk w) y ≡ emb ℓ o (wk w) (emb j (downOk ℓ o j (wk w)) v y)`
  白话：沿复合路径的嵌入可以分两段做。
- `cp-emb : (a : L) {b b′ : L} {u : a ⊕ b ≤ a ⊕ b′} → CP a u → (o : Ok (a ⊕ b′)) (d : Read⁺ b) → Σ (Read⁺ b′) λ d′ → emb (a ⊕ b′) o u (read⁺ a d) ≡ read⁺ a d′`
  白话：沿 `from0` 形的复合路由嵌入，码对仍是码对。
- `ok-down : (a : L) {b′ b : L} (w : b′ ⊑ b) (oa : Ok a) (ob : OkO a b) → downOk (a ⊕ b) (Ok⊕ a b oa ob) (a ⊕ b′) (wk (⊕⊑ a w)) ≡ Ok⊕ a b′ oa (downO a w ob)`；`rb-down` 同形
  白话：`Ok⊕` 证据与 `rbO` 证据沿偏移降下去，形状不变。
- `way-in : (a : L) (g : ℕ → L) (w : (n : ℕ) → g n ⊑ g (suc n)) (m n : ℕ) (d : Read⁺ (g m)) → WayIn a (g m) (g n) d (way (λ i → a ⊕ g i) (λ i → wk (⊕⊑ a (w i))) m n)`
  白话：`Ok⊕` 形路由上，way 行把码对嵌成码对。
- `way-at : (a : L) {b : L} (g′ : ℕ → L) (w : nd sL g′ ⊑ b) (oa : Ok a) (ob : OkO a b) (m n : ℕ) (d : Read⁺ (g′ m)) → WayIn a (g′ m) (g′ n) d (way (λ i → a ⊕ g′ i) (proj₁ (downOk (a ⊕ b) (Ok⊕ a b oa ob) (a ⊕ nd sL g′) (wk (⊕⊑ a w)))) m n)`
  白话：偏移里任一 ℕ 极限结点上都是这样。
- `schema-at : (a : L) {b : L} (k : L) (h : Tr k → L) (w : nd (sΩ k) h ⊑ b) (ra : Rb a) (oa : Ok a) (ob : OkO a b) → proj₁ (rb⊑ (a ⊕ b) (rbO a b ra oa ob) (⊕⊑ a w)) ≡ just (schema a h oa (proj₁ (proj₁ (downO a w ob))) (proj₂ (downO a w ob)) (λ _ → refl))`
  白话：偏移里任一 Ω 形状结点的换基证据，地板都是 a。

**YiEMChain**（编译定理，不读记号）
- `yₑ-in : Domain⁺ S₁ zero yₑ`
  白话：YiBCReach 那一格的块在码域里。
- `cell-emb : emb (G 1) (proj₂ oω 1) (self ∙ proj₁ oω 0) (Ωt (G 0)) ≡ read⁺ (tw 1) {Lω.offs 1} (em zero (em tt (old omega)))`
  白话：那一格 way 行交下的整棵树是码对。
- `seen≠code : (oj : Ok (G 0)) (β : Tr⁺ (G 0)) → seen S₁ (G 0) oj (lift (tw 1) one) β zero ≡ fold⁺ S₁ zero (em tt (old omega)) (G 0) oj (lift (tw 1) one) β → ⊥`
  白话：现行 seen 不是按 `yₑ` 的码换基。这是编译否定，依据 `obs-seen` 的结果是 `hl`、`obs-code` 的结果是 `hΩ`。
- `ev-chain : (d : Tr zero) → proj₂ oₛ d ≡ Ok⊕ (tw 1) (↑ (tw 1) (gₛ d)) (Ok-tw 1) (OkO↑ (tw 1) (tw 1) (Ok-tw 1) self (gₛ d))`；`rb-chain`、`ev-tw` 同类
  白话：链孩子的两种证据都是读回形。
- `way-sync : (g′ : ℕ → L) (w : nd sL g′ ⊑ ↑ (tw 1) (proj₁ (Ωt (tw 1)))) (m n : ℕ) (e : Read⁺ (g′ m)) → WayIn (tw 1) (g′ m) (g′ n) e (way (λ i → tw 1 ⊕ g′ i) (proj₁ (downOk (tw 1 ⊕ ↑ (tw 1) (proj₁ (Ωt (tw 1)))) oₛ (tw 1 ⊕ nd sL g′) (wk (⊕⊑ (tw 1) w)))) m n)`；`schema-sync`
  白话：同步对象偏移的每个结点上，闭包都成立。
- `Feed.chain-L : (m : ℕ) → IsL (chain (suc m))`；`chain-lim`
  白话：现行链从第 1 个点起都是 ℕ 极限，o 与 B 任意。
- `Lim.route-lim : (n : ℕ) → proj₁ (proj₂ oₛ d) n ≡ wk (⊕⊑ (tw 1) (wᶜ n))`；`Lim.row-lim`；`Lim.way-lim`
- `Lim.first-lim : (o : Ok (tw 1 ⊕ offs 1)) → emb (tw 1 ⊕ offs 1) o (self ∙ wk (⊕⊑ (tw 1) (wᶜ 0))) (Ωt (tw 1 ⊕ offs 0)) ≡ read⁺ (tw 1) (pre (wᶜ 0) (old omega))`
  白话：对 ℕ 极限链点 `lim f a`（f 任意），顶层第一个 way 块是码对。

**YiEMNeg**（编译否定，不读记号）
- `no-up-code⁺ : (a b : L) (e : a ⊕ b ≡ two) (d : Read⁺ b) → proj₁ (subst Tr⁺ e (read⁺ a d)) ≡ proj₁ lifted → ⊥`；`up∉`
  白话：上折输出不在码域里。
- `floor-emb∉ : (a : L) (o : Ok a) {k : L} (w : k ≤ a) (y : Tr⁺ k) → Step w → (d : Read⁺ zero) → proj₁ (read⁺ a d) ≡ proj₁ (emb a o w y) → ⊥`
  白话：嵌入进地板的树不是码。
- `odd∉ : (a b : L) (e : a ⊕ b ≡ one) (d : Read⁺ b) → proj₁ (subst Tr⁺ e (read⁺ a d)) ≡ odd → ⊥`
  白话：分支函数不是 Ω 树那一个的块不在码域里。
- 行的形状，`refl`：`sS-keep`、`sS-keepᵘ`、`self-row`。
- 前提可满足：实例 `two₀`、`one₀`、`step₁`。

**YiEMSync**（编译定理，验收文件）
- `oᴱ≡oₛ : SY.oᴱ ≡ oₛ`、`oᶻ≡oₛ : SY.oᶻ ≡ oₛ`
  白话：两个实例在同步对象上的证据就是读回证据。
- `chainᴱ-lim`、`chainᶻ-lim`
  白话：`YiSYReduce` 两个实例的链从第 1 个点起都是 ℕ 极限。
- `wayᴱ`、`wayᶻ`
  白话：两个实例下，链点顶层 way 行把码对嵌成码对。

##### 4. 第一个障碍

- **覆盖方向：** 没有撞到编译的障碍。剩下两件：来源穷尽是判断；证据不是 `Ok⊕` 形时未查。
- **把码域用进折叠的方向：** 障碍是 `YiEMChain.seen≠code`。现行 `BS.ψ` 的 seen 一支对一切块都用 `old omega`，在 `yₑ` 上与按码换基不同。
  - 要按码换基，折叠必须拿到块的码。树不带码，也没有从树恢复码的函数。
  - 我的判断是：在一般情形下认出 `Ωt` 要比较分支函数，这一点未编译。
  - 让码随树或随证据携带，是改定义（改块，或加证据字段），所以停下交作者。
  - 档：工程上，即定义的选择，挡住了；数学上是否挡住（能否从树恢复码）未编译。

##### 5. 偏离、事故与未读的东西

**偏离**
- `Read⁺` 按偏移分型，嵌入码 `em c` 允许任意孩子，不只是 YiBC 建议的 "第一孩子"。理由：换基时这样是结构性的；`Ok⊕` 路由可以经过 ℕ 极限结点的任意孩子 n。
- `Read⁺` 里没有作用在嵌入码上的 `plus`、`next`、`limit`，混合码写不出来。找到的来源用不到它们。

**事故**
- `seen≠code` 第一次用 `with … | ()` 写，6G 下堆耗尽，退出 251。没有原样重跑：先用临时文件 `YiEM4` 定位，原因是 `with` 抽象上下文里的 eq 时把两棵树整个规范化了。改成辅助函数 `hl≢hΩ` 后通过。
- 没有跑 `--profile`，没有量峰值内存。

**没读，只凭简报转述**
- `EBOHandbook` 的 4.2、4.6 节，以及 Bedrock 性能手册。只用了简报里的规则名 H-6、C-9、S-1。
- `Review18`；YiBL*、YiSV*、YiFI*、YiQD、YiZS、AuditE 的内容。

**读过**
- 台账 V149、V158、V287、V290 到 V297 各条。
- `Reports-2026-11-16/YiBC.md` 的回报部分。
- YiBS*、YiBC*、YiRW*、YiRKChain、YiSYReduce、YiKSDesc（σ、okl）的源码。

## 简报正文（子智能体读的文件，本机路径换成占位）

### 任务：替身码域加嵌入码（前缀 YiEM，临时目录 <临时目录>）

你在 Agda 研究仓库 `<仓库>` 上工作，全程用中文。执行方 Opus 5.5。这是工程一路；只在新文件里写候选，不改已有定义。同批另三路与你互不导入。

#### 作者的决定与背景（2026-11-17）
- 作者已关闭现行折叠上同步对象那一步链步（台账 V287），依据是两份先读定义的 Fable 5.2 封存审核。**主线定义不动**；改树、折叠、合法性只在新文件里做候选；换基进主线由作者定。
- 第七十七批作者选四路（选项原文）："替身值的后继一步 StepS (Recommended), 按读回域的充分性与参照出口 (Recommended), 替身码域加嵌入码 (Recommended), Fable 先读定义审查换基候选"。前缀 `YiZS`（Fable 5.2）、`YiQD`（Opus 5.5）、`YiEM`（Opus 5.5），以及审查 E 路（Fable 5.2，只在临时目录），互不导入。
- **换基候选的现状（第七十五、七十六批，主审冷编复核过；都在 `probes/OCF/Lean/`）**：
  - 换基折叠 `YiBSFold`（`BS.ψ`；换基行在 `route` 落在地板之上时对一切孩子 c 同形：在 `j ⊕ offsets S c` 上重建 Ω 树经 `seen` 沿 `lift` 朝原目标折，原孩子树只进低层尾项，`YiBLFold.row-reb`）；证据 `YiBSBase`（`Schema`、`split`、`rbO`、`rb-tw`、`seen`）；替身码 `YiBSRead`（`Read`、`read`、`Domain`）；核 `YiRBSib`。
  - 证据覆盖（`YiBCCover`）：读回域上处处满（`full-sync`、`Chain.full-chain`、`full-kl`、`full-kl-child`、`full-rbO`、`full-↑`、`rb-row`、`full-row`）；变量层号上给不出（`YiBCNeg.no-sync`，谓词太宽）；嵌入块到达换基行而不在码域里（`YiBCReach.reach`、`yₑ∉`，ω 代替链点；`YiBCNeg.emb∉read`、`∉dom`）。`YiBCSync.a₁-eq`、`chain-eq`：`YiRKChain` 的副本与原定义逐字相等。
  - 律（`YiBLIface`、`YiBLFold`，不读记号）：换基律 `RebAt`、嵌入律 `EmbLaw`、出口 `OutR`；`SuffR.keepAll`、`sys→low`、`SuffRA`；换基折叠满足树一侧全部律（`rebᴮ`、`keepᴮ`、`keepᴬ`、`fallᴬ`、`monoᴬ`、`monoᴮ`）；`lowᴮ`、`lowᵗ`（LowKeep，前提只剩参照一侧：`OutR`、辅助系统的 `Out`、`Gen⁺`、`Weak`、`Lim`、`Node`）；`ev-cp`、`nodeE-cp`（目标槽位副本由 `lift` 实填）；`top-noEv`、`main-noEv`（替身自己孩子层号的槽位、主系统孩子槽位不保留）。YiBL 判断的下一处障碍：(1) 主系统 `OutR.nodeE` 在 ℓ 层孩子槽位上只能走链，而 `SuffR` 对一切树陈述，要改成按读回域陈述；(2) 辅助系统 `Out.nodeE` 走链一支要 `∀ k → Φ s (g (z k)) ⊴ Φ s (nd p g)`，对部分和极限在 k ≥ 1 处可能不成立。底层接口 `YiFIIface`（`Suff.keepAll`、`sys→low`、`Out`）与 `YiAbsG*`。
  - 值（`YiSV*`）：替身对偏移沿字面路径单调（`YiSVMono.Mono.mono-path`、`seen-mono`、`seen◃`，不读记号；与 `YiLTLift.upS`、`upL` 同形，未合并）；目标孩子 ω 时非零各支承载 ψ_ω(Ω_{ω+1})（`YiSVOmega.branch-nz`、`seen-ω`，参照关系 `YiHCLim.Lim.Mω`）；顶结点承载 ψ_ω(Ω_{Ω₁}) ⇐ 后继一步 `YiSVRed.Red.StepS`（`top-red`、`branch-red`、`liftC`），`StepS` 的结论在 η ≤ ω+1 成立（`step-low`），η = ω+2 处缺 "目标层之上两层" 的保持（`ℓ₊` 上折到自身的保持，`YiHCOmega.Tω.upB` 一类；跨两层的下折保持，`YiBSFam.LF` 在 ℕ 极限底座上的对应物）；字面延伸 ω 的分支要 ω+ω 一类 ℕ 极限层号上的关系族（`YiHCLim.Lim` 只要有限孩子 `fn (d n)`）。
  - 比较表一路的否定：`YiRKCell.no-ωᵉ`、`YiCTCall.cell`、`YiDGDiag.ColW.wdecα`、`YiDGCell.cell→wdecα`。
- 主线现状：第一档成品已完成；终点无条件值 ψ₀(Ω_Ω+ψ₁(Ω_ω)+ω)（`YiFYRef.target-low`）；里程碑 ψ₀(Ω_{Ω₂}) 未达到。

#### 本路的问题
`YiBCReach`：ω 代替链点时，嵌入块 `yₑ` 到达换基行的 `seen` 一支（`reach`），不在替身码域 `YiBSRead.Domain` 里（`yₑ∉`）；码读出的树顶不是嵌入（`YiBCNeg.read-not-up`），沿非平凡路径嵌入的树顶是嵌入（`emb-up`）。YiBC 估：给 `Read` 加一个 "沿第一孩子嵌入" 的码约 50 到 150 行，不覆盖上折（`YiBSUpNeg`）与回灌输出作块的情形。

#### 要做的（按序）
0. **最小检查**：在新文件里写扩展的码 `Read⁺`（含嵌入码）、`read⁺`、`Domain⁺`，先让 `yₑ` 在 `Domain⁺` 里（编译）。说明扩展码在折叠与 `seen` 下的解释（`YiBSRead` 的 `source`、`fold` 一类），证新码合法、第一位置关系经折叠保持（仿 `YiBSRead` 已有的定理）。不成立就停下回报。
1. **真实链点**：不用 ω 代替，在 `a₁ (chain m)`（`YiSYReduce` 的原定义；变量 m，或 m = 1、2，闭项放 `opaque`）上查：到达换基行 `seen` 一支的块都在 `Domain⁺` 里吗。给出覆盖表（块的来源 × 在 / 不在 / 未查）。
2. 不在的块，写清来源（上折、回灌输出作块、带任意分支函数的块）与是否碰到 V149 的方向反变；能写成编译否定的写成否定。
3. 交代价与翻译账。

#### 规则（主审写给内部子智能体，必须照做）
- **先读** `AGENTS.md` 全文；性能问题先查 `probes/Survey/EBOHandbook.md` 4.2、4.6 节与 Bedrock 性能手册 `<Bedrock>/dev/cubical-agda-performance.md` 的 C-9（在变量上陈述、定义等式作假设、在唯一调用点实例化）、C-10（具体的站作 opaque 原子或模块参数）、S-1/S-3（重的构造在出生处封进 opaque，并在同一块里导出规格等式）、C-24、Q-1（`--profile=definitions`）、Q-23（量底价、二分）、H-6（251 之后不原样重跑）。
- **只新建文件**，放 `probes/OCF/Lean/`，用你的前缀（见上）。不改任何已有文件，不碰 `src/`、`archive/`，不碰别的前缀。中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行（判决与档位、做了什么、不否定什么、入口）；代码之间只写范围与不显然的理由。一次性的试验放你的临时目录，用纯 `.agda`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`（仓库 `.agda-lib` 另加 `--cubical-compatible --guardedness --hidden-argument-puns -W noUnsupportedIndexedMatch`；临时目录的纯 `.agda` 要把前三个也写上，否则报 `InfectiveImport`）。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径（写 `<实验目录>`、`<仓库>`）。
- **编译**（仓库根目录）：`agda +RTS -M6G -RTS --library-file=<库文件> -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`；临时目录的纯 `.agda` 另加 `-i <你的临时目录>`。退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 Agda 内部错误。报退出码不经过管道。同时只跑一个 agda，堆上限 6G（同批另有四路，外部广撒网也可能在编，机器共 64G；峰值超过 4G 先改形状）。不用 `--ignore-interfaces`，只删自己模块的 `.agdai`（在 `probes/_build/2.8.0.2/agda/OCF/Lean/` 下，写字面路径）。大的 `refl` 前加 `timeout 600`。
- **停下的条件**：退出 251 时不原样重跑，先按 C-9、C-10、S-1 改形状并定位（附 profile 或二分数据）；改过形状后同一上限仍撞墙才停。同一处两次重新设计仍过不了检查器也停。若某一步要改树、折叠或合法性的定义，停下回报。没有编译的否定时只写 "未走通"。
- **过程**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译。动手证一般形式之前先用临时文件检查前提可满足；已有引理先检索（`grep`）再写，不重证，搬来的证明在文首写明来源。查签名用检索，不整篇读大文件。
- 不在你的临时目录与你前缀的新文件之外写、删、移任何东西；不 `pkill`，不写 `/tmp`，不装包，不提交，不改 `probes/README.md`、`probes/LOG.md`、台账与留档。
- **两条已更正的事实**（不要再照旧说法写）：`YiMXNote.¬Mono` 否定的是记号一侧非标准形项的项序单调，**不是**树侧折叠的跨层单调（树侧跨层单调目前没有编译的否定）；`YiKWObjects.kept` 是新封装的对象，与 `YiC1Slot` 不透明块里的 `kept` 不是同一个。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造与本机路径为 0；文首标 "不读记号" 的文件用 `python3 probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 查导入闭包。

#### 回报（最后一条消息就是回报，主审会原样留档）
1. 判决：先说对纲领与目标意味着什么；各步到哪一步；问题表（问题、位置、档）。档分三种：编译定理、有限测试、判断。
2. 文件表：代码行、冷编退出码。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理；是数学上挡住还是工程上挡住。
5. 偏离与事故；没有读、只凭转述引用的东西。
不用 "只差"、"自然" 一类形容；判断与定理分开写。

