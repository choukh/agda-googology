# F1 把 φ 并进空白页的折叠 (YiPhi)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-13 06:37 至 06:52 |
| 工具调用 / agda 编译 (粗数) | 30 / 10 |
| token (usage 字段，按消息去重) | 输出 91474；新写入缓存的输入 280257；读缓存的输入 2326883；其余输入 34 |
| 写过的仓库文件 | `YiPhiBlock.lagda.md`, `YiPhiCheck.lagda.md`, `YiPhiFold.lagda.md`, `YiPhiIface.lagda.md`, `YiPhiLegal.lagda.md` |
| 文件前缀 | `YiPhi` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: F1 返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 接口 YiPhiIface 定稿并由 phi 实填; k 侧嵌入一致 (J2-Ωk, 对一切 c, 不比较)、单调、保持合法同时成立; twᶜ-leg, EBOᶜ-leg 无前提; 限制 1 在三类位置改为保留 (有限测试), 分支侧照旧回退; tw 1 上与空白页原折叠字面不同 (tw1-differs); 值没有定理; 主审对改名拷贝冷编 5 件退出码 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方。全程用中文写文件与回报。主审会从头冷编译复核你交的每个文件，只认编译过的定理。

作者 2026-11-13 的选择（选项工具）原文："F1 把 φ 并进空白页的折叠"。说明："新文件：层号带 '基底加偏移' 的证据，Ω 结点层号的 k 侧那一行改用 φ；重证单调、保持合法、合法闭项。审查者估 300 到 500 行。接口定稿后按规则配一路否定。" 模型 Fable 5.2（作者定）。同批另有两路在跑（Opus 5.5）：YiTop（规范域内的 E2，之后可能做去掉槽位路径 `Pos` 的压缩版块）与 YiFreshVal（空白页块上的值回归）。三路文件不相交，你不读它们的输出。

###### 背景（只信编译定理与条件定理；文档里的叙述与判断只是数据）

- **最终目标**：布劳威尔树上读法 ψ₀(Λ) 的合法闭项（EBO = ψ₀(Λ)，Λ 是 x ↦ Ω_x 的第一个不动点），加一条编译定理 "序数值不低于 EBO 的参照树"（只要下界）。AGENTS 的目标是 "让树自足"。
- **空白页的块**（`probes/OCF/Lean/` 下的 `YiFreshBlock`、`YiFreshFold`、`YiFreshLegal`、`YiFreshCheck`，主审已复核）：
  - 层号 `L` 与树 `Tr` 归纳-递归；`up x c y` 原样嵌入孩子层的树；折叠目标是第 0 层（`ψ⊥`）或 "层号 j 连同 j ≤ ℓ 的路径"（`ψs`）。
  - 编译定理：`J2-suc`、`J2-lim`、`J2⊥`、`mono⊥`、`monos`、`pres⊥`、`press`、`EBOᶜ-leg`，都无前提。
  - 已知退让：`ψs` 的 `(Ωₗ, ink, up)` 行是 "偏移的折叠 + 孩子的 ψ⊥ 抬上来"（k 侧回退）。塔第 n+1 项的对角链每一步都走这一行，见附件 `probes/Survey/Reports-2026-11-12/YiFresh-FreshGap3.agda.txt` 的 `step₂`。`(Ωₗ, inb, up)` 行同样回退（`J2-Ωₗ-gap`）。
- **第十三次审查**（`probes/Survey/RR13-CommonWall.md`；附件 `probes/Survey/Reports-2026-11-12/attachments/Review13-R13Base.agda.txt`、`Review13-R13Top.agda.txt`，主审重编退出码 0）：
  - `R13Base`：`φ : (a b : L) → Base (a ⊕ b) → Bt a → {j : L} → j ≤ a → Tr (a ⊕ b) → Tr j`，目标在基底 a 里。`J2φ-suc`、`J2φ-lim`、`J2φ-Ω` 都是 `refl`，`J2φ-Ω` 里分支 c 是变量，不比较。另有 `monoφ`、`pressφ`、`tw-split : tw (suc n) ≡ tw n ⊕ Ωₗ (tw n) (↑ (tw n))`（`refl`）、`J2k`、`new-step`（c = 0 时保留结点；原折叠 `old-step` 是 ℕ 极限）、`Tw′-leg`。
  - 审查者写明的限制：
    1. φ 对层号 `a ⊕ b`（b ≠ 0）上的结点一律折叠，包括下标层其实在基底里的那种，因为读回 `↑` 丢了槽位。审查者说，要保留就得对偏移树 `c : Tr a` 递归，而不是对 `↑c`。
    2. φ 只替换了最外一层链步，里面仍走 `ψs` 的回退。
    3. `Tw′-leg` 的合法性不依赖 φ。
  - `R13Top`：规范树的结点都在顶槽位（`Top`、`EBOᶜ-top`），顶槽位的结点只在目标是 `self` 时保留（`kpTop-default`）。
  - **分支侧 `(Ωₗ, inb, up)` 不在这一路的范围**：审查者判断，靠算出来的同支证据就会判定字面相等（`R13Diag.diag→dec`）。不要去比较孩子下标。

###### 要做（按次序，每做成一件先编译）

1. **接口 `YiPhiIface`（先写，只陈述，不证明；记录或类型）**，包括：
   - 新块与新折叠的类型：层号带 "基底加偏移" 的证据，或审查者的 `a ⊕ b` 写法，由你定。
   - 嵌入一致：后继、ℕ 极限、到第 0 层，以及 Ω 结点层号的 k 侧（对一切分支 c，不比较 c）。
   - 折叠单调；保持合法；塔各项、Λ 与读法 ψ₀(Λ) 的闭项合法。
   - 一条 "k 侧链步保留基底里的结点" 的陈述，对照 `new-step`。

   在 tw 1、tw 2、tw 3、Λ 上实填通过后，用 SendMessage 给 `main` 发一行 "YiPhiIface 接口定稿"，之后接口只增不改。主审会对同一接口另派配对否定。
2. **实现**（新文件，例如 `YiPhiBlock`、`YiPhiFold`、`YiPhiLegal`，成品候选）：
   - 把 φ 并进折叠，使里层也用它，不只最外一层链步；尽量解决限制 1。
   - 不比较孩子下标；没有按层号字面判等的派发；加法不打开 `up`。
   - 重证单调（无前提为好）、保持合法，以及塔、Λ 和读法 ψ₀(Λ) 的闭项合法，无前提。
3. **回归**（验收文件 `YiPhiCheck`）：
   - 原有 `J2-suc`、`J2-lim`、`J2⊥` 的对应物仍成立。
   - 塔第 2、3 项根结点的链步保留基底里的结点（有限测试，对照 `old-step`）。
   - 在 k = 0 的层号上（例如 tw 1 那一站）与空白页原折叠相同。
4. **行数**：前三层各多少。口径：代码块里非空、非注释的行，含模块头与导入。空白页原块是 102、124、312。

值不是这一路的任务，但不要做明显降低值的改动；有这种取舍时写进回报。

###### 先读什么
- `AGENTS.md` 全篇。
- 空白页四个文件全读。
- 附件 `Review13-R13Base.agda.txt`、`Review13-R13Top.agda.txt` 全读。
- `probes/Survey/RR13-CommonWall.md`。
- `probes/Survey/EBOHandbook.md` §4.1 到 §4.5。

查签名用检索，不整篇读大文件。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiPhi`（模块名 `OCF.Lean.YiPhi…`）。不改任何已有文件，不碰 `src/`、`archive/`。
- 块、折叠、合法性的文件是成品候选：不导入记号、参照框架与旧块（可以导入 `YiFresh*`），用 `python3 probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 检查，退出码 0 才算干净。验收文件文首标 "验收文件"。
- 中文 literate Agda（`.lagda.md`）。每个模块文首不超过 5 行；代码之间的文字只写范围与不显然的定义理由。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞（写入文件时也不留洞）、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。无关参数可以用。函数外延只准作验收文件里的显式前提。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 6G（另两路也在编译）。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。日志落文件，只看首个错误附近。
  - 不用 `--ignore-interfaces`。要冷编译只删你自己模块的接口（`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`），写字面的精确路径，不用通配，不用变量拼路径。
- 临时目录：`<实验目录>/agents/phi`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不写 `/tmp` 的别处，不装包，不提交，不推送。
- **停下的条件**：同一处两次重新设计仍过不了检查器；需要函数外延或 K；6G 仍耗尽（先按手册 §4.2）；需要比较孩子下标才能继续。没有编译的否定时只写 "未走通"。
- **过程要求**：读完上面的文件后尽快动手，第一个文件在 30 分钟内写出并编译；每次回复都要有工具调用，不要在一次回复里只思考。
- **结束前自查**：每个文件删自己的接口后冷编译，退出码 0，日志里只有你自己模块的 `Checking` 行；检索禁用构造为 0；成品候选的 importclosure 退出码 0。

###### 回报格式（只在回报里交一次）
1. 判决：接口是否定稿；合法闭项有没有；限制 1 到 3 各解决到哪里；一段话说对目标意味着什么。
2. 文件表：文件、代码行数、冷编译退出码、常驻内存峰值、是否成品候选（importclosure 结果）。
3. 定理表：名字、逐字的陈述、一句白话、文件、档（编译定理 / 条件定理 / 有限测试 / 判断）。
4. 设计与翻译账：每个新构造子与折叠行来自树侧的什么需要，哪些读自记号。
5. 第一个障碍：精确到引理，附检查器报错原文（若有），以及缺的引理的 Agda 类型。
6. 偏离与事故。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

### YiPhi 回报 (F1: 把 φ 并进空白页的折叠)

#### 1 判决

- **接口已定稿**: `YiPhiIface.Iface` 由 `YiPhiCheck.phi` 实填, 对一切带证据的层号成立; 已给 main 发过定稿通知。
- **合法闭项有**: `twᶜ n` (塔各项) 与 `EBOᶜ` (读法 ψ₀(Λ)), `twᶜ-leg`, `EBOᶜ-leg` 无前提。值没有定理。
- **回归第 3 项没有按字面通过**: tw 1 (k = 0) 上新旧折叠字面不同, 有编译的有限反例 `tw1-differs`。k 侧那一行对一切 k 都换成了孩子层的折叠, 没有按 k 是否为零分派。
- **做法与审查者的 `a ⊕ b` 写法不同**: 块 `L`, `Tr` 没有改。目标路径 `_≤_` 新增 "对一切孩子各给一条路径" 的构造子 `inlu`, `inu`; 层号证据 `Ev` 在 `Ωₗ k h` 处给每个孩子层一条路径 k ≤ h c。`Ev` 不是对一切层号可满足的, 折叠的量化域是带证据的层号; 塔与 Λ 的证据 `Ev-tw`, `Ev-Λ` 是闭项。

三条限制各到哪里:

1. **限制 1 (下标层在基底里的结点被折掉)**: 在三类位置上改为保留, 都不比较分支。
   - 槽位在孩子 c 里、目标在 k 侧: 目标沿证据路径搬进孩子 c 再比路径。
   - 槽位在 k 侧、目标在孩子里或对一切孩子给出: 槽位用 `psh` 沿证据路径搬进那个孩子 (后一种取第一个孩子, 是取定)。
   - 有限测试 `new-step₂′`, `new-step₃′`, `keep-suc` 通过; 原折叠同处是 ℕ 极限。
   - 仍折掉的 (读定义): 槽位与目标在两个指定的孩子里 (`inb`/`inj₂`, 不比较); 槽位在 k 侧而目标是 `ink w` 且 `kp⁼ k` 走默认的。没有 "该保留的都保留" 的定理。
2. **限制 2 (只换了最外一层链步)**: 折叠只有一对 `ψ⊥`/`ψs`, 每一层的 `(Ωₗ, ink, up)` 行都走证据路径交孩子 (`J2-Ωk`, `refl`, c 是变量)。仍回退的有三处:
   - `(Ωₗ, inb c′, up x c y)` 行, 按简报不在范围。
   - 不同号的 `(lim, inl n, up x m y)` 行。
   - 孩子的底 `bs` 仍经 `inb c` 取, 所以孩子里结点的链步的底会走上面的回退。
3. **限制 3 (闭项合法性不依赖 φ)**: 闭项就是新折叠本身。根结点的链步字面等于 `stepᴾ` (`step-is-root`, `refl`), 合法性由 `pres⊥`/`press` 经过新行得到。

**对目标的意义**: k 侧 "嵌入一致、单调、保持合法" 三者在同一个折叠里对一切带证据的层号同时成立, 塔与 Λ 的闭项合法。新增的路径构造子、证据、槽位搬运都由 "不比较分支也要把目标交给孩子" 这一树侧要求逼出, 没有读记号。距 EBO 下界仍缺值的定理; 新折叠在各站的值不低于原折叠是判断, 未证。

#### 2 文件表

都在 `<仓库>/probes/OCF/Lean/`。冷编译是删自己接口后按 Block, Iface, Fold, Legal, Check 的次序编, 日志里各只有自己模块的 `Checking` 行。

| 文件 | 代码行 | 冷编译退出码 | 内存 (RTS total / 最大驻留) | 成品候选 (importclosure) |
|---|---|---|---|---|
| `YiPhiBlock.lagda.md` | 110 | 0 | 240 MiB / 137 MB | 是 (0) |
| `YiPhiIface.lagda.md` | 65 | 0 | 284 MiB / 166 MB | 接口 (0) |
| `YiPhiFold.lagda.md` | 85 | 0 | 269 MiB / 140 MB | 是 (0) |
| `YiPhiLegal.lagda.md` | 211 | 0 | 619 MiB / 333 MB | 是 (0) |
| `YiPhiCheck.lagda.md` | 106 | 0 | 318 MiB / 183 MB | 验收文件 (0) |

- 禁用构造检索 0, 无本机路径, 无函数外延。
- **行数 (前三层, 含从 `YiFresh*` 复用的部分)**:

| 层 | 复用 | 新增 | 合计 | 空白页原块 |
|---|---|---|---|---|
| 块 | 102 (`YiFreshBlock` 全部) | 110 | 212 | 102 |
| 折叠 | 48 (运算, `Ωt`, `ι`, `eqℕ`) | 85 | 133 | 124 |
| 合法性 | 190 (序, `Leg`, 运算引理, `Ωt` 合法, `Good`, `LN`, 层号合法性) | 211 | 401 | 312 |
| 合计 | | | 746 | 538 |

- 口径变化: 路径、`posW`、`Base` 约 30 行原来算在折叠, 现在放在块里。

#### 3 定理表

`ε : Ev ℓ`, `B : Base ℓ`, `β : Tr j` 是偏移对当前目标的折叠。

| 名字 | 陈述 (逐字) | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `Ev-tw`, `Ev-Λ` | `(n : ℕ) → Ev (tw n)`; `Ev Λ` | 塔与 Λ 带证据 | Block | 编译定理 (闭项) |
| `phi` | `Iface` | 接口实填 | Check | 编译定理 |
| `J2-suc` | `ψs (suc a) ε B j (ins w) β (up x tt y) ≡ ψs a ε (dS a ε B x) j w (ψs (suc a) ε B j (ins w) β x) y` | 后继层嵌入一致 | Iface/Check | 编译定理 (`refl`) |
| `J2-lim` | `ψs (lim g) ε B j (inl n w) β (up x n y) ≡ ψs (g n) (ε n) (dL g ε B n x) j w (ψs (lim g) ε B j (inl n w) β x) y` | ℕ 极限层, 同号孩子 | 同上 | 编译定理 |
| `J2-limu` | `ψs (lim g) ε B j (inlu ws) β (up x n y) ≡ ψs (g n) (ε n) (dL g ε B n x) j (ws n) (ψs (lim g) ε B j (inlu ws) β x) y` | ℕ 极限层, 对一切 n | 同上 | 编译定理 (`refl`) |
| `J2-Ωk` | `ψs (Ωₗ k h) ε B j (ink w) β (up x c y) ≡ ψs (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) j (w ∙ proj₁ (proj₂ ε c)) (ψs (Ωₗ k h) ε B j (ink w) β x) y` | k 侧嵌入一致, c 是变量 | 同上 | 编译定理 (`refl`) |
| `J2-Ωu` | `ψs (Ωₗ k h) ε B j (inu ws) β (up x c y) ≡ ψs (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) j (ws c) (ψs (Ωₗ k h) ε B j (inu ws) β x) y` | 目标对一切孩子给出时一致 | 同上 | 编译定理 (`refl`) |
| `J2⊥-suc/lim/Ω` | 例: `ψ⊥ (Ωₗ k h) ε B (up x c y) ≡ ψ⊥ (h c) (proj₂ (proj₂ ε c)) (dW k h ε B c x) y` | 到第 0 层一致, 一切层号 | 同上 | 编译定理 (`refl`) |
| `mono⊥` | `(ℓ : L) (ε : Ev ℓ) (B : Base ℓ) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → zero ⊢ ψ⊥ ℓ ε B x ◃ ψ⊥ ℓ ε B y` | 单调, 无前提 | Legal | 编译定理 |
| `monos` | `(ℓ : L) (ε : Ev ℓ) (B : Base ℓ) (j : L) (v : j ≤ ℓ) (β : Tr j) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → j ⊢ ψs ℓ ε B j v β x ◃ ψs ℓ ε B j v β y` | 单调, 无前提 | Legal | 编译定理 |
| `pres⊥` | `(ℓ : L) (ε : Ev ℓ) (B : Base ℓ) → LegB ℓ B → (x : Tr ℓ) → Leg ℓ x → LN zero (ψ⊥ ℓ ε B x)` | 保持合法且非零 | Legal | 编译定理 (前提: 底合法非零; `LegB₀` 给实例) |
| `press` | `(ℓ : L) (ε : Ev ℓ) (B : Base ℓ) → LegB ℓ B → (j : L) (v : j ≤ ℓ) (β : Tr j) → LN j β → (x : Tr ℓ) → Leg ℓ x → LN j (ψs ℓ ε B j v β x)` | 同上, 一切目标 | Legal | 编译定理 (同上) |
| `twᶜ-leg` | `(n : ℕ) → Leg zero (twᶜ n)`, `twᶜ n = ψ₀ (tw n) (Ev-tw n) (Ωt (tw n))` | 塔各项闭项合法 | Legal | 编译定理, 无前提 |
| `EBOᶜ-leg` | `Leg zero EBOᶜ`, `EBOᶜ = ψ₀ Λ Ev-Λ (Ωt Λ)` | 读法 ψ₀(Λ) 的闭项合法 | Legal | 编译定理, 无前提 |
| `kstep` | `ψs (tw (suc n)) (Ev-tw (suc n)) B (tw n) (ink self) β (up x zero (Ω p g)) ≡ Ω p (λ z → ψs (tw n) (Ev-tw n) (dW (tw n) (λ c → tw n ⊕ ↑ (tw n) c) (Ev-tw (suc n)) B zero x) (tw n) self (ψs (tw (suc n)) (Ev-tw (suc n)) B (tw n) (ink self) β x) (g z))` | 一切 n: 第一个孩子里的结点在 k 侧链步下保留 (对照 `new-step`) | Iface/Check | 编译定理 (`refl`) |
| `step-is-root` | `stepᴾ n c ≡ ψs (tw (suc n)) … (posW (tw (suc n)) (inj₁ (inj₁ tt))) … (up zero c (Ωt (tw n ⊕ ↑ (tw n) c)))` | `stepᴾ` 就是折叠里根结点的链步 | Check | 编译定理 (`refl`) |
| `new-step₂`, `new-step₃` / `old-step₂`, `old-step₃` | `isΩ (stepᴾ 1 zero)`, `isΩ (stepᴾ 2 zero)` / `isLim (stepᴼ 1 zero)`, `isLim (stepᴼ 2 zero)` | 塔第 2, 3 项链步第一步: 新保留, 旧是 ℕ 极限 | Check | 有限测试 |
| `new-step₂′`, `new-step₃′` / `old-step₂′` | `isΩ (stepᴾ 1 (stepᴾ 1 zero))`, `isΩ (stepᴾ 2 (stepᴾ 2 zero))` / `isLim (stepᴼ 1 (stepᴼ 1 zero))` | 链的第二步 (孩子层是 `Ωₗ`, 下标层在基底里) 仍保留 | Check | 有限测试 |
| `keep-suc` / `old-suc` | `isΩ (ψs (tw 2) (Ev-tw 2) (B₀ _) (tw 1) (ink self) (Ωt (tw 1)) (up zero (suc zero) (Ω (inj₂ (inj₁ (inj₁ tt))) (λ _ → zero))))` / 旧折叠同处 `isLim` | 孩子层是后继, 非顶槽位在基底里的结点保留 | Check | 有限测试 |
| `same-2`, `same-ω` | 新旧 `ψ₀`/`ψs` 在层号 2 与 ω 的两棵闭树上 `≡` | 无 `Ωₗ` 的层号上样本相同 | Check | 有限测试 (弱) |
| `tw1-new`, `tw1-old` | 新: `… ≡ ψs (zero ⊕ ↑ zero c) … zero (self ∙ lift zero (↑ zero c)) (Ωt zero) y`; 旧: `… ≡ Ωt zero + ι zero (F.ψ₀ (zero ⊕ ↑ zero c) y)` | tw 1 上 k 侧那一步新旧各是什么 | Check | 编译定理 (`refl`) |
| `tw1-differs` | `ψs (tw 1) (Ev-tw 1) (B₀ _) zero (ink self) (Ωt zero) (up zero zero (suc zero)) ≢ F.ψs (tw 1) (F.B₀ _) zero (F.ink F.self) (up zero zero (suc zero))` | k = 0 上字面不同 (首项 1 对 1+1) | Check | 有限反例 |

`same-*` 弱的原因: 样本只能是不含 Ω 结点与 ℕ 极限的闭树; 含变量的项两边是不同的函数名, `refl` 比不了, 一般定理要函数外延。

判断 (未编译):
- `tw1-differs` 那一对的值相同 (lim(1,2,…) 对 lim(2,3,…))。
- 新行的值不低于原回退 (孩子带底 fold x 的折叠, 对 fold x + 孩子的 ψ₀)。
- 没有做会降低值的改动。

#### 4 设计与翻译账

都来自树侧, 没有读记号的基本列规则; 没有新构造子进 `L`/`Tr`。

- **`inu`, `inlu`**: `up x c y` 要交给孩子而不能问 c 是谁, 所以目标必须在每个孩子里各有一条路径。由 "不比较分支" (壁垒一侧的要求) 逼出。
- **`Ev`**: `(Ωₗ, ink, up)` 行要 k ≤ h c 的字面路径, 即 "每个孩子层字面含 k" (RR13 §2 的说法)。`EvO`, `Ev⊕`, `EvO↑`, `lift` 是为塔写出闭证据; `EvO↑` 对树递归, 用到槽位 `posW k p`, 对应审查者 "对偏移树递归而不是对 ↑c" 的提示。
- **`psh`, `pshBr`**: 槽位在 k 侧而目标在孩子里时, 把槽位搬进孩子再比路径, 服务限制 1。`inu`/`inlu` 处取第一个孩子是取定。
- **`ψs` 多一个参数 β**: 交给孩子时, 底必须是 x 对同一目标的折叠; 原来的 `bs` 经 `inb c` 取不到它。`Base.bs` 只剩给结点链步用。
- **`kp` 改为对层号递归, `Ωₗ` 六行**: 原来的三行默认里两行换成沿证据搬运后比较; "两个指定孩子" 一行仍默认。`(inj₁ t, inb c w)` 一行落在分支侧的保留判定上, 它不比较 c, 但动了简报说 "不在范围" 的区域附近, 请主审留意。
- **脚手架账**: 新增的 `Ev` 一族 (约 45 行) 是 J2 的 k 侧需要的; `psh` (约 16 行加证明 20 行) 是限制 1 需要的。没有为验收加字段。
- `LegB` 在 `YiPhiIface` 与 `YiPhiLegal` 各定义了一次 (逐字相同), 为了让接口先于实现编译。

#### 5 第一个障碍

没有过不了检查器的地方; 四个停下条件都没有触发。未做的一处 (不是未走通):

- **孩子的底在 "经证据路径的目标" 上仍是分支侧折叠。** 按定义, `bs (dW k h ε B c x) j w′ = ψs (Ωₗ k h) ε B j (inb c w′) (bs B j (inb c w′)) x`, 即使 `w′ = w ∙ proj₁ (proj₂ ε c)`。精确的值应是 `ψs (Ωₗ k h) ε B j (ink w) (bs B j (ink w)) x`。
- 后果: 孩子里结点的链步的底, 对 x 里别的分支的嵌入走 `(Ωₗ, inb, up)` 回退。
- 缺的东西: `pull : ∀ {j k a} → k ≤ a → j ≤ a → Maybe (j ≤ k)`, 把落在证据路径像里的目标拉回 k 侧; 加上它的归纳原理, 并把 `dW` 改用它。纸面上它不比较分支 (`inu es` 对 `inb c w` 取 `es c`), 两条都是 `inb` 时放弃; 未写未编。

#### 6 偏离与事故

- **偏离简报的 "与空白页原折叠相同"**: 见 §1 与 `tw1-differs`, 只交了 Ω-free 样本上的相同。
- **偏离审查者的 `a ⊕ b`**: `a ⊕ (k ⊕ d)` 与 `(a ⊕ k) ⊕ d` 不是定义相等, 递归不到里层 (纸面判断, 没有编译否定), 所以改用路径。`tw-split` 式的字面形状只在 `Ev-tw` 里经 `lift` 用到。
- **量化域收窄**: 折叠现在只对带 `Ev` 的层号定义。例如 `Ωₗ (suc zero) (λ _ → zero)` 没有证据 (读定义, 未写成定理)。
- **事故**: 第一次冷编译用 `/usr/bin/time -l` 量内存, 沙箱拒绝 `sysctl`, 循环里的退出码 1 是 `time` 的, 不是 agda 的。随即删自己五个接口, 改用 `+RTS -s` 重新冷编译, 表中数字出自这一次。
- 过程中 `YiPhiCheck` 有三次类型错误后修正 (含变量的 `refl` 比较; `fin` 层缺证据; `self ∙ v` 不是定义上的 `v`), 都在验收文件里。
- 没有改已有文件, 没有提交; 临时目录里只有日志。
