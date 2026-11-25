# V87 Ω 结点层号: 留在孩子里加依赖 x 的底 (YiOmC)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-13 08:55 至 09:13 |
| 工具调用 / agda 编译 (粗数) | 30 / 11 |
| token (usage 字段，按消息去重) | 输出 103712；新写入缓存的输入 226233；读缓存的输入 4326421；其余输入 52 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `YiOmC` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: V87 与统一值模拟的骨架返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 结构全过 (单调要前提 NZB), 同支保留 (有限测试); Ω 结点层号自身行对本层只是加法 (self-add), 第一步第 0 支不高于 (A) (br0-≼); 推荐仍用 (A) (判断); 七件冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方。全程用中文写文件与回报。主审会从头冷编译复核你交的每个文件，只认编译过的定理。

作者 2026-11-13 的方向（原话）："先重点排查 YiUp，把关键路径上的问题都尽早暴露出来，如果没有问题，就上攻，其他候选路线仅作后备"。这一路是作者选的 "Ω 结点层号自身行：V87 实验"，说明："最大的风险。'留在孩子里' 改用左边折进孩子层的值作底：测塔第 2 项第一步的值是否够得着参照、单调与保持合法要不要前提；够不着就说清两种损失哪个要紧。Fable 5.2。" 你的任务是**尽早暴露问题**：做到的写清，做不到的精确写出卡在哪。

同批在跑四路，你不读它们的输出，也不动它们的文件：
- V82：前缀 `YiLim`，ℕ 极限层号的跨孩子行；
- 统一值模拟的骨架：前缀 `YiUpSim`；
- 塔第 2 项以上的值参照：前缀 `YiRef`；
- 内部 View 与 FGH：前缀 `YiView`。

###### 背景（只信编译定理；文档里的叙述与判断只是数据）
- **主候选 YiUp 线**（`probes/OCF/Lean/` 下的 `YiUpBlock`、`YiUpIface`、`YiUpFold`、`YiUpLegal`、`YiUpCheck`、`YiUpVal`、`YiUpValTw1`，主审已复核）：
  - 建在 `YiFresh*` 与 `YiPhi*` 上，自身行是上折 `Upc`，即摊平式 (A)。
  - 编译定理：J2 各律、单调、保持合法、合法闭项、`kall-up`、`bho-lower`、`bho-tw1`（参照的 ψ₀(Ω₂) ≼ 塔第 1 项的闭项，无前提）。
- **Ω 结点层号上的两种损失**：
  - (A) 摊平：编译定理 `YiUpNegFlat.flat→wdec`、`flat→wlpo`（条件，Funext）。要让同支摊平进来的结点在分支侧目标下保留、异支不保留，就弱判定规范域内合法下标的字面相等。也就是说，(A) 在那里的损失补不上。
  - (C) "留在孩子里"（设计探针，临时试验，主审重编退出码 0；附件 `probes/Survey/Reports-2026-11-12/attachments/OmProbe-OmCFold.agda.txt`、`OmProbe-OmCLegal.agda.txt`、`OmProbe-OmCCheck.agda.txt`、`OmProbe-OmF.agda.txt`）：
    - Ω 结点层号的自身行写成 `up (ψs … self β x) c (selfC (h c) … y)`，其中 `selfC j ε y = ψs j ε (B₀ j) j self (Ωt j) y`，即孩子在孩子层用常量底 `Ωt (h c)` 折到自身。
    - 上折走到 Ω 结点层号孩子里的 `up` 时，经 `embD` 加法地重新嵌入。
    - 编译通过：接口实填、`kall-C`、单调、保持合法、闭项合法。同支保留是有限测试（`P-kept`、`omD-C`、`deep`）。
    - 判断：孩子部分与左边的折叠只是相加（x′ + β′·ω^y），(A) 是 x′·ω^y；塔第 2 项第一步第 0 支的值低于 (A)（形状测试 `f-A`、`f-C`）。
    - 探针取常量底，是为了无前提的单调：`◃u` 要孩子部分非零。
  - 留档：`probes/Survey/Reports-2026-11-12/OmProbe.md`、`YiUpNeg.md`；台账 `probes/Survey/IdeaLedger.md` 的 V83、V85、V87。

###### 要做（每做成一件先编译）
1. **(C′) = (C) 加依赖 x 的底**：Ω 结点层号的自身行里，孩子树 y 的自身折叠以 "x 的折叠折进孩子层的值" 作底，而不是常量 `Ωt (h c)`。目标是找回 x′·ω^y 的乘法耦合，同时保留同支。
   - 写法由你定，可以照 J2-Ωk 用层号证据的路径 k ≤ h c，把 x 的折叠搬进孩子层。不比较孩子下标。
   - 新文件，例如 `YiOmCFold`、`YiOmCLegal`，成品候选；可以导入 `YiFresh*`、`YiPhi*`、`YiUp*`，可以把附件里的定义搬进来改。
2. **结构检查**：接口各律（照 `YiPhiIface` 或另写一份 `YiOmCIface`；`YiUpIface.self-up` 在 Ω 结点层号上会不同，如实写）、单调、保持合法、合法闭项、`kall`。单调若要前提，写出最弱的前提，并在规范闭项上给出实例。
3. **决定性的值测试**（验收文件 `YiOmCVal`，可导入参照框架与 `YiUpVal`、`YiUpValTw1` 的工具）：
   - 塔第 2 项的链第一步，对照 (A) 与 (C)。形状测试是必做的；能做的话，证一条与参照比较的下界或不及。
   - 写明 (C′) 的第一步是否 "够得着参照的对应项"，以及 (A) 的损失与 (C′) 的损失各在哪一行。
4. **判决**：Ω 结点层号自身行推荐 (A)、(C) 还是 (C′)，以及推荐的依据（编译定理 / 有限测试 / 判断）。

###### 先读什么
- `AGENTS.md` 全篇。
- `YiUpBlock`、`YiUpFold`、`YiUpIface` 全读；`YiUpLegal`（检索）；`YiUpVal`、`YiUpValTw1`（检索 `At`、`lower2`、`S`）。
- 上面列的四个附件全读。
- `YiUpNegFlat` 文首与 `flat→wdec` 陈述。
- `probes/Survey/EBOHandbook.md` §4.1 到 §4.5。

查签名用检索，不整篇读大文件。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiOmC`（模块名 `OCF.Lean.YiOmC…`）。不改任何已有文件，不碰 `src/`、`archive/`。
- 成品候选不导入记号与参照框架，用 `python3 probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 检查。验收文件文首标 "验收文件"。
- 中文 literate Agda。每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只准作验收文件里的显式前提。
- 不比较孩子下标与层号；加法不打开 `up`。仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 6G（另有四路在编译）。
  - 冷编译只删你自己模块的接口，写字面路径；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
- 临时目录：`<实验目录>/agents/omc`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- **停下的条件**：同一处两次重新设计仍过不了检查器；需要函数外延或 K；6G 仍耗尽；需要比较孩子下标。没有编译的否定时只写 "未走通"。
- **过程要求**：读完后尽快动手，第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编译退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0；成品候选 importclosure 退出码 0。

###### 回报格式（只在回报里交一次）
1. 判决：推荐哪一种；(C′) 的结构检查与值测试结果；暴露出的关键路径问题，表：问题、位置、档。
2. 文件表：文件、代码行数、冷编译退出码、常驻内存峰值、是否成品候选。
3. 定理表：名字、逐字的陈述、一句白话、文件、档、用到的折叠行。
4. 设计与翻译账。
5. 第一个障碍：精确到引理，附检查器报错原文（若有）。
6. 偏离与事故。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 1. 判决

**推荐 Ω 结点层号的自身行仍用 (A) 上折;(C′) 与 (C) 只作后备,不建议替换。** (C′) 的结构检查全部通过,但值上有一处损失,依赖 x 的底补不回来。

依据分三档:

- **编译定理**
  - (C′) 的接口各律、`kall`、单调(带前提 `NZB`)、保持合法、塔各项与 Λ 的闭项合法都成立。
  - `bho-lower`、`bho-tw1` 对 (C′) 也成立(逐行移植,无前提)。tw 1 这一站用不到 Ω 结点层号的自身行,所以这条不区分 (A)、(C)、(C′)。
  - 塔第 2 项链第一步第 0 支折到第 0 层:(C′) 的输出的值 ≼ `β₁ + β₁` 的值 ≼ (A) 的输出 `next β₁` 的值(`below2`、`br0-≼`,对任意底 B;用 (C′) 的折叠取值与用 (A) 的折叠取值各一条)。只证了 "不高于",没有证严格。
  - Ω 结点层号上 (C′) 的自身行是加法(`self-add`、`Suc.F-add`,`refl`);(A) 是上折(`SucA.F-up`,`refl`)。
- **有限测试**
  - 同支结点留在孩子里,并在孩子层的链步下保留(`P-kept`、`omD`、`deep`)。
  - 塔第 2 项链第一步上,(C′) 的孩子的底化成常量 `Ωt (h₁ c)`(`step1`),第 0 支与 (C) 逐字相同(`br0-same`)。原因是这一步 x = 0 且底是规范底;x 非零时两者不同(`differ-C′`、`differ-C`)。
- **判断(纸面,未编译)**
  - 孩子部分的类型是 `Tr (h c)`,值到不了本层;当前目标的底 β 在 `Tr ℓ`,进不了孩子。所以 "x′·ω^y 的乘法耦合" 在 (C′) 里只能以 x 折进孩子层之后的值出现,对本层仍是 X + (小于本层 Ω 树的量)。
  - 后果在层号 tw 1 + 1(塔第 2 项的孩子 c = 1)的链 `z (k+1) = next (F (z k))` 上:
    - (C′):F(x + β₁) 的值是 F x + β₁,链点是 β₁·ω^k,极限约 β₁·ω^ω。
    - (A):F(x + β₁) 约 F x · β₁,链的极限约 ε_{β₁+1}。
  - 也就是 Ω 结点层号 ν 上,"Ω_{ν+1} 折到 ν" 这一步在 (C′) 少了 ε 跳跃;按 ψ₀(Ω₂) 的类比,这是值上要紧的损失。

**(C′) 的第一步够不够得着参照的对应项:未测到。** 本仓库已编译的参照下界只到 tw 1,第 2 项的参照不在我能导入的范围内(同批 `YiRef` 在做,我没有读)。能说的只有上面那条 "不高于 (A)"。

**两种损失各在哪一行:**

- (A) 的损失:`YiUpFold` 的自身行 `ψs ℓ ε B _ self β (up x c y) = Upc ℓ c …`,摊平后同支结点在分支侧目标 `inb c w` 下不保留(`YiUpNegFlat.flat→wdec`,补不上)。它对值的后果本路没有测。
- (C′) 的损失:`YiOmCFold` 的行 `ψs (Ωₗ k h) ε B _ self β (up x c y) = up (ψs … self β x) c (kid k h ε B c x y)`,同支保留,但对本层只是加法。
- 按上面的判断,(C′) 的损失直接落在值上,(A) 的损失落在结点保留上。所以推荐 (A);这个比较是判断,不是定理。

**暴露的关键路径问题**

| 问题 | 位置 | 档 |
|---|---|---|
| 依赖 x 的底在塔的 Ω 树闭项上不带进新东西:链第一步 x = 0、底是规范底,孩子的底化成 `Ωt (h₁ c)` | `YiOmCCheck.step1`、`kid-zero`、`br0-same` | `kid-zero` 是编译定理;`step1`、`br0-same` 是有限测试;"塔闭项上处处如此" 是判断 |
| Ω 结点层号的自身行对本层只是加法 | `YiOmCCheck.self-add`、`Suc.F-add` | 编译定理(`refl`) |
| 第一步第 0 支的值 (C′) 不高于 (A) | `YiOmCVal.ValC.br0-≼`、`ValA.br0-≼` | 编译定理(只有 ≼) |
| tw 1 + 1 的链在 (C′) 下极限约 β₁·ω^ω,(A) 下约 ε_{β₁+1} | `Suc.form-suc`、`F-add`、`F-next` 对 `SucA.F-up` | 形状是编译定理;值是判断 |
| `monos` 要前提 `NZB`(底的每个分量非零) | `YiOmCLegal.monos` | 编译定理(充分);"最弱" 未证,也没有 "无前提则不单调" 的否定 |
| 塔第 2 项没有可比较的参照 | — | 事实 |
| 上折 `Up′` 走到 Ω 结点层号孩子里的 `up` 时,底取 `B₀`,不是调用处的底 | `YiOmCFold.Up′` 的 `Ωₗ` 行 | 设计取定,未测别的写法 |

#### 2. 文件表

都在 `<仓库>/probes/OCF/Lean/`。冷编译是删掉自己七个接口后逐个编译,每个日志里只有自己模块的 `Checking` 行。

| 文件 | 代码行 | 冷编译退出码 | 常驻峰值 (RTS maximum residency / total in use) | 成品候选 |
|---|---|---|---|---|
| `YiOmCFold.lagda.md` | 90 | 0 | 137 MB / 266 MiB | 是 |
| `YiOmCLegal.lagda.md` | 314 | 0 | 320 MB / 572 MiB | 是 |
| `YiOmCIface.lagda.md` | 91 | 0 | 165 MB / 304 MiB | 是(接口) |
| `YiOmCConst.lagda.md` | 81 | 0 | 153 MB / 267 MiB | 否((C) 的对照折叠,取自附件) |
| `YiOmCCheck.lagda.md` | 180 | 0 | 180 MB / 325 MiB | 否(验收/测试) |
| `YiOmCVal.lagda.md` | 149 | 0 | 526 MB / 953 MiB | 否(验收) |
| `YiOmCValBho.lagda.md` | 299 | 0 | 986 MB / 1655 MiB | 否(验收) |

- `importclosure.py` 对 `YiOmCFold`、`YiOmCLegal`、`YiOmCIface`、`YiOmCConst` 退出码 0,禁用表命中 0。
- 禁用构造与本机路径检索为 0。

#### 3. 定理表

| 名字 | 陈述(逐字) | 白话 | 文件 | 档 | 用到的折叠行 |
|---|---|---|---|---|---|
| `monos` | `(ℓ : L) (ε : Ev ℓ) (B : Base ℓ) → NZB ℓ B → (j : L) (v : j ≤ ℓ) (β : Tr j) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → j ⊢ ψs ℓ ε B j v β x ◃ ψs ℓ ε B j v β y` | 折到目标 j 单调,前提是底的分量非零 | Legal | 定理 | 全部 |
| `mono⊥` | `(ℓ : L) (ε : Ev ℓ) (B : Base ℓ) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → zero ⊢ ψ⊥ ℓ ε B x ◃ ψ⊥ ℓ ε B y` | 折到第 0 层单调,无前提 | Legal | 定理 | `ψ⊥` 各行 |
| `nzs` | `(ℓ : L) (ε : Ev ℓ) (B : Base ℓ) → NZB ℓ B → (j : L) (v : j ≤ ℓ) (β : Tr j) → j ⊢ zero ◃ β → (x : Tr ℓ) → j ⊢ zero ◃ ψs ℓ ε B j v β x` | 底非零则折叠值非零,不要合法性 | Legal | 定理 | 全部 |
| `press` | `(ℓ : L) (ε : Ev ℓ) (B : Base ℓ) → LegB ℓ B → (j : L) (v : j ≤ ℓ) (β : Tr j) → LN j β → (x : Tr ℓ) → Leg ℓ x → LN j (ψs ℓ ε B j v β x)` | 保持合法且非零 | Legal | 定理 | 全部 |
| `twᶜ-leg` / `EBOᶜ-leg` | `(n : ℕ) → Leg zero (twᶜ n)` / `Leg zero EBOᶜ` | 塔各项与 Λ 的闭项合法 | Legal | 定理 | — |
| `nzB₀`、`nzS`、`nzL`、`nzW`、`nzLeg` | 如 `nzW : (k : L) (h : Tr k → L) (ε : Ev (Ωₗ k h)) (B : Base (Ωₗ k h)) → NZB (Ωₗ k h) B → (c : Tr k) (x : Tr (Ωₗ k h)) → NZB (h c) (dW k h ε B c x)` | 前提在规范底上成立,孩子的底继承,由底合法推出 | Legal | 定理 | — |
| `omI` | `omI : OI.Iface` | 接口实填(含 J2 各律、`kstep`、`self-suc`、`self-lim`、`self-Ω`、`U-Ω`、`kall`) | Check | 定理 | 全部 |
| `nz-tw`、`nz-Λ`、`nz-child` | `nz-tw : (n : ℕ) → NZB (tw n) (B₀ (tw n))` 等 | 单调前提在规范闭项上的实例 | Check | 定理 | — |
| `self-add` | `… → ψs (Ωₗ k h) ε B (Ωₗ k h) self β (up x c y) ≡ ψs (Ωₗ k h) ε B (Ωₗ k h) self β x + up zero c (kid k h ε B c x y)` | Ω 结点层号的自身行是右加 | Check | 定理 (`refl`) | 自身行 |
| `kid-zero` | `… → kid k h ε B c zero y ≡ ψs (h c) (proj₂ (proj₂ ε c)) (base (b⊥ B) (λ j w → bs B j (inb c w))) (h c) self (bs B (h c) (inb c self)) y` | x = 0 时孩子的底直接取自 B | Check | 定理 (`refl`) | 自身行 |
| `step1` | `stepC′ zero ≡ Ω (inj₁ (inj₁ tt)) (λ c → up β₁ c (ψs (h₁ c) (proj₂ (proj₂ ε₁ c)) (B₀ (h₁ c)) (h₁ c) self (Ωt (h₁ c)) (Ωt (h₁ c))))` | 第一步上底化成常量 | Check | 有限测试 | J2-Ωk、自身行 |
| `br0-C′`、`br0-same`、`br0-A`、`br1-A`、`br1-C′`、`br1-C` | 如 `br (stepC′ zero) zero ≡ up β₁ zero (next (suc zero))`;`br (stepA zero) zero ≡ next β₁` | 第 0、1 支的形状 | Check | 有限测试 | 同上 |
| `P-kept`、`P-down`、`omD`、`deep`、`fallback` | 如 `omD : … → IsΩ (ψs two tt B′ one (ins self) β′ (kid zero h₁ ε₁ B c₂ x (nodeC G)))` | 同支保留;没改的回退行 | Check | 有限测试 | 自身行、`Up′` |
| `differ-C′` / `differ-C` | `… ≡ up (next β) zero (next (next (suc zero)))` / `… ≡ up (next β) zero (next (suc zero))` | x 非零时 (C′) 与 (C) 不同 | Check | 有限测试 | 自身行 |
| `Suc.form-suc` | `ψ⊥ (suc (tw 1)) ε₁ B₂ (Ωt (suc (tw 1))) ≡ lim (cum (λ k → next (ψ⊥ (tw 1) ε₁ Bᵃ (z k))))` | tw 1 + 1 的链 | Check | 定理 (`refl`) | `ψ⊥` 结点行、J2-suc |
| `Suc.F-add` | `(x : Tr (tw 1)) → F (x + β₁) ≡ F x + Ω (inj₁ (inj₁ tt)) (λ c → up zero c (kid zero h₁ ε₁ Bᵃ c x (Ωt (h₁ c))))` | (C′):自身折叠把右加 β₁ 变成右加 | Check | 定理 (`refl`) | 自身行 |
| `SucA.F-up` | `(x : Tr (tw 1)) → F (x + β₁) ≡ Ω (inj₁ (inj₁ tt)) (λ c → Up (h₁ c) (down stop c) (F x) (Ωt (h₁ c)))` | (A):以 F x 为底上折 | Check | 定理 (`refl`) | (A) 自身行 |
| `Ω≽next` | `(ℓ : LF) (ε : Ev ℓ) (B : Base ℓ) → read (next (b⊥ B)) ≼ read (ψ⊥ ℓ ε B (Ωt ℓ))` | 任意层的 Ω 树的折叠值不低于底的 `next` | Val (`ValC`、`ValA`) | 定理 | `ψ⊥` 各行 |
| `below2` | `(B : Base (tw 1)) → read (ψ⊥ (tw 1) ε₁ B (up β₁ zero (next (suc zero)))) ≼ read (ψ⊥ (tw 1) ε₁ B (β₁ + β₁))` | (C′) 第 0 支的值不高于 β₁·2 的值 | Val | 定理 | `ψ⊥` 各行 |
| `br0-≼` | `(B : Base (tw 1)) → read (ψ⊥ (tw 1) ε₁ B (br (stepC′ zero) zero)) ≼ read (ψ⊥ (tw 1) ε₁ B (br (stepA zero) zero))` | 第一步第 0 支:(C′) 不高于 (A) | Val (`ValC`、`ValA` 各一条) | 定理 | 同上 |
| `f-A`、`f-C′`、`f-C′₀`、`f-C′₁`、`tw1-same0` | 如 `C′.ψ⊥ zero tt (ValC.D₀ B) (num 1) ≡ next (next (C′.ψ⊥ (tw 1) ε₁ B β₁))` | 第 0 层的形状;tw 1 链步 c = 0 上两个折叠相同 | Val | 有限测试 | — |
| `bho-lower` | `L.ψ⁰ (L.Ω I2) ≼ read (ψ₀ two tt (Ωt two))` | (C′) 在层号 2 上的 ψ₀(Ω₂) 下界 | ValBho | 定理 | 后继层自身行 (`Up′`) |
| `bho-tw1` | `L.ψ⁰ (L.Ω I2) ≼ read Tw1′`,`Tw1′ = ψ₀ (tw 1) (Ev-tw 1) (Ωt (tw 1))` | (C′) 的塔第 1 项闭项 ≽ 参照的 ψ₀(Ω₂) | ValBho | 定理 | 同上;用不到 Ω 结点层号自身行 |

#### 4. 设计与翻译账

- **(C′) 的自身行**:`up X c (kid k h ε B c x y)`,其中
  - `kid = ψs (h c) ε_c (dW … c x) (h c) self (ψs (Ωₗ k h) ε B (h c) (inb c self) (bs B (h c) (inb c self)) x) y`;
  - 孩子的底记录与 J2 各行相同;当前目标的底是 x 沿 `inb c self` 折进孩子层的值。
  - 递归都落在 x 或 y 上,停机检查直接通过。不比较孩子下标,加法不打开 `up`。
- **为什么底取 x 而不是 "X 再折一次"**:X 是折叠的输出,对它再折叠不是结构递归。β 在 `Tr ℓ`,同理不能折进孩子。在一致的调用里,B 的分量就是 "偏移折进各目标的值",所以取 `bs B`。
- **接口差异**:`YiUpIface.self-up` 在 Ω 结点层号上换成 `self-Ω`;上折成了接口字段 `U`,另列 `U-Ω`;`monos` 带 `NZB`。
- **翻译账**:
  - 没有新构造子,没有读自记号基本列的字段。
  - `kid` 的形状来自树侧(J2 的底加 "留在孩子里")。
  - 新增脚手架是 `NZB` 与 `nz*` 引理约 70 行,为合法性 (`◃u`) 所需,不是翻译带来的。
  - 验收只用了序数值 (`≼`) 与形状,没有用 `Lab`。

#### 5. 第一个障碍

- **值上的障碍(判断,无检查器报错)**:要证 "(C′) 在 tw 1 + 1 的链上够不着 ε_{β₁+1}" 需要 `Tr (tw 1)` 上的值语义或上界论证,本路没有。只编译了形状(`F-add` 对 `F-up`)和第 0 支的 ≼。未走通的精确位置:`Suc.z` 的链点在 (C′) 下折到第 0 层的上界引理。
- **检查器报错只有一处,已如实改写**:`br1-same : br (stepC′ zero) (suc zero) ≡ br (stepC zero) (suc zero)` 用 `refl` 不过,报 `[UnequalTerms] Up′ (tw 0 ⊕ ↑ (tw 0) zero) … ` —— 两边是 (C′) 与 (C) 各自的 `Up′`,是不同的函数,不是值不同的证据。改成两条同形的测试 `br1-C′`、`br1-C`。
- **单调前提的最弱性未证**:自反闭包版(分量为零或非零)要对输入加合法性前提,没有做。

#### 6. 偏离与事故

- 多交了三个简报没有逐字点名的文件:`YiOmCIface`(简报允许另写)、`YiOmCConst`(把附件的 (C) 搬进仓库作对照)、`YiOmCValBho`(把 `YiUpVal` 与 `YiUpValTw1` 第 3、6 节移植到 (C′);`btbo-tw1′` 条件定理没有移植)。
- `YiOmCCheck`、`YiOmCValBho` 导入了 `YiUpCheck`、`YiUpFold`、`YiFreshValTw1`(只读,作对照与工具)。
- 第一次冷编译用 `/usr/bin/time -l` 包着跑,沙箱里 `sysctl` 被拒,包装器退出码 1(agda 本身已完成)。随后删掉自己的七个接口,改用 `+RTS -s` 重跑,上表是这一次的结果。
- 没有改任何已有文件,没有提交;没有读同批四路的输出。
- 简报要的 "与参照比较的下界或不及" 只做到 tw 1(`bho-tw1`),塔第 2 项没有做。
- 临时目录(日志):`<实验目录>/agents/omc`
