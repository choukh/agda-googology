# YiUpIface 的配对否定 (YiUpNeg)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-13 08:12 至 08:37 |
| 工具调用 / agda 编译 (粗数) | 52 / 9 |
| token (usage 字段，按消息去重) | 输出 154916；新写入缓存的输入 274202；读缓存的输入 6518825；其余输入 76 |
| 写过的仓库文件 | `YiUpNegBound.lagda.md`, `YiUpNegFlat.lagda.md`, `YiUpNegSelf.lagda.md` |
| 文件前缀 | `YiUpNeg` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: YiUpIface 的配对否定返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | omD 写成编译定理: FlatKeep 加 FlatOff 对规范域内的下标弱判定字面相等 (flat→wdec), 加 Funext 得 WLPO (flat→wlpo), 经同支证据则可判定 (flatE→dec); upI 不满足 FlatKeep; 其余五行保留摊平后的结点 (flat-suc 等, 无前提); self-up 在零偏移上域外过宽 (self-zero); 三件冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方：对一份已定稿的接口写**配对否定**。全程用中文写文件与回报。主审会从头冷编译复核你交的每个文件，只认编译过的定理。

作者 2026-11-13 的选择（选项工具）原文："YiUpIface 的配对否定"。说明："把 omD 写成定理（摆平后要保留就得判定同支），查 self-up 律的量化域；不动折叠。Opus 5.5。" AGENTS.md 的规则："新路线派一路构造、一路对同一接口写否定，共用接口文件（定稿后只增不改）"。

同批在跑两路，你不读它们的输出，也不动它们的文件：
- V81（Fable 5.2）：在 YiUp 的折叠上证塔第 1 项的 BTBO 下界，新文件前缀 `YiUp`，不改已有的 YiUp 文件；
- Ω 结点层号自身行的设计探针（Fable 5.2，只在临时目录）。

###### 接口与实例（只信编译定理）
- **接口** `probes/OCF/Lean/YiUpIface.lagda.md` 的记录（已定稿）：字段照 `YiPhiIface.Iface`，另加：
  - 自身行律 `self-up : … → ψs ℓ ε B ℓ self β (up x c y) ≡ Upc ℓ c (ψs ℓ ε B ℓ self β x) y`，上折 `Up`、`Upc` 在 `YiUpBlock`；
  - 只增字段 `kall`（陈述取自 `YiPhiNegK.KAll`）。
- **实例** `YiUpCheck.upI`；实现在 `YiUpFold`、`YiUpLegal`（主审已冷编复核）。
- **背景**：
  - 第十四次审查 `probes/Survey/RR14-SelfRow.md`；附件 `probes/Survey/Reports-2026-11-12/attachments/Review14-R14Lim.agda.txt`。其中 `omC`、`omD` 是有限测试：上折把 Ω 结点层号孩子里的结点摊平进父层槽位 `inj₂ (c₂ , …)` 后，以分支侧目标 `inb c₂ …` 折它时走默认，尽管两个 c₂ 字面相同。审查者的判断是 "要保留就得判定同支"，没有写成定理。
  - 已知的编译否定：`YiPhiNegB` 的 `wdec`、`wdecα`、`wlpo`（条件：Funext）、`viaE→dec`；`YiPhiNegKSem.fullSem→lpo`；`YiUniNegStep.step-full→lpo`；`YiCtxNeg.diag1→dec`。

###### 要做（每条写成编译定理，或写明 "未走通"）
1. **把 omD 写成定理**：
   - 在这份接口（含 `self-up`）上，陈述 "摊平后同支的结点以后以分支侧目标折叠时保留" 这条加强，例如对一切 c，`Upc` 搬进 `inj₂ (c , …)` 的结点，在目标 `inb c w` 下输出以同一槽位为根。
   - 证明：它连同接口的律推出弱判定孩子下标的字面相等，仿 `YiPhiNegB.wdec`；或推出更强的不可能性；或者反过来给出满足它的实例。
   - 陈述要精确，并说明对象在不在规范域。规范域可用 `YiTopDom.Top` 或 `YiPhiNegDom` 的办法判断；注意上折的输出离开顶槽位（`YiUpCheck.up-notTop`），要说明你用的是什么规范域。
2. **self-up 律的量化域**：它对一切层号、一切孩子、一切底 β 陈述。查有没有退化输入（常值极限、不合法的树、不合法的底），使律说得过宽而实例只是碰巧满足；或者律推出不合理的东西（例如与 `fullSem` 一类相合）。按 AGENTS，"反例对象不在读回域内的否定，读作 '谓词太宽'"。
3. **上折与合法性**：`Up-mono`、`Up-LN`（`YiUpLegal`）的前提是否可满足；是否存在合法输入使上折的输出不合法（若有，是否在规范域内）。
4. **每条否定定理与条件定理的每个前提**，给一个实例或说明为何可满足（AGENTS："前提要可满足"）。

###### 先读什么
- `AGENTS.md` 全篇。
- `YiUpIface`、`YiUpBlock`、`YiUpFold` 全读；`YiUpCheck` 的 `upI`、`up-notTop`（检索）；`YiUpLegal` 的 `Up-mono`、`Up-LN`（检索）。
- 附件 `Review14-R14Lim.agda.txt` 全读。
- `YiPhiNegB`（`wdec` 的证明与探针）、`YiPhiNegDom`（规范域的写法）全读。
- `probes/Survey/EBOHandbook.md` §4.1 到 §4.5。

查签名用检索，不整篇读大文件。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiUpNeg`（模块名 `OCF.Lean.YiUpNeg…`），文首标 "验收文件（否定）"。不改任何已有文件，包括 YiUp 的文件。不碰 `src/`、`archive/`。
- 中文 literate Agda（`.lagda.md`）。每个模块文首不超过 5 行：判决与档位，否定的确切是什么，不否定什么。代码之间的文字只写范围与不显然的定义理由。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的结论标 "条件"。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 6G（另两路也在编译）。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。日志落文件，只看首个错误附近。
  - 不用 `--ignore-interfaces`。要冷编译只删你自己模块的接口（`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`），写字面的精确路径，不用通配，不用变量拼路径。**不要删 YiUp 或别人模块的 `.agdai`。**
- 临时目录：`<实验目录>/agents/upneg`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不写 `/tmp` 的别处，不装包，不提交，不推送。
- **停下的条件**：同一处两次重新设计仍过不了检查器；需要函数外延或 K（作前提除外）；6G 仍耗尽。没有编译的否定时只写 "未走通"。归到已知的墙之前，逐条核机制：有没有折叠，有没有值，失败的是哪个字段。
- **过程要求**：读完上面的文件后尽快动手，第一个文件在 30 分钟内写出并编译；每次回复都要有工具调用，不要在一次回复里只思考。
- **结束前自查**：每个文件删自己的接口后冷编译，退出码 0，日志里只有你自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：1 到 3 各得到什么（编译否定、有限测试、未走通）；一段话说这份接口的边界在哪里。
2. 文件表：文件、代码行数、冷编译退出码、常驻内存峰值。
3. 定理表：名字、逐字的陈述、一句白话、文件、档（编译定理 / 条件定理 / 有限测试 / 判断），对象在不在规范域。
4. 每条否定的前提的可满足实例。
5. 与已知否定的关系（逐条核机制）。
6. 偏离与事故。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 回报: YiUpIface 的配对否定 (执行方 Opus 5.5)

##### 1. 判决

**这对纲领与目标意味着什么.** omD 现在是编译定理，结论是 "要保留就得判定同支"。接口实例 `upI` 是摊平：自身行把孩子里的 Ω 结点搬进 Ωₗ 层的 `inj₂ (c , …)` 槽位（`Upc`）。设一个折叠满足两条：
- 加强 `FlatKeep`：以同支目标 `inb c w` 折叠摊平后的结点时，以孩子层保留判定给出的槽位为根；
- `FlatOff`：分支不同时不以任何槽位为根（`upI` 满足它）。

这样的折叠对塔第 3 项的一个合法下标 c₀ 与一切 c′ 弱判定 c₀ ≡ c′；加函数外延作前提，得 WLPO。探针在规范域内，所以这条读作数学障碍，不读作 "谓词太宽"。自身行律本身没有推出任何判定原则，它在域外说话的地方只有一处：零偏移。

- **第 1 项（omD）：编译定理。** 涉及：
  - `flat→wdec`, `flat→wdecα`；
  - `flat→wlpo`（条件定理：Funext）；
  - `flatE→dec`：经同支证据 E 派发时，字面相等可判定；
  - `up-not-flatKeep`：`upI` 不满足加强。

  边界是编译过的正面结果，无前提：`upI` 在后继层、ℕ 极限层（指定孩子、一切孩子）、Ωₗ 的下标层侧（`ink`）与一切孩子（`inu`）这五行都保留摊平后的结点。失败的只有 Ωₗ 的分支侧 `inb` 一行。

  另有一个有限测试 `chain-flat` 对 `chain-emb`：这一情形出现在 `upI` 自己的链步里，输入在 `Top` 内且合法。
- **第 2 项（self-up 的量化域）：编译定理。** `self-up` 对零偏移也陈述：
  - 对任一实例，若 x 以零偏移对自身折成零，则合法输入 `up x c (suc zero)` 的自身行输出是常值极限，不合法（`self-zero`；`upI` 取 x = zero 即满足前提）；
  - 旧自身行在同一输入上输出合法（`phi-legal`）；
  - 零偏移不是 "合法且非零"（`zero-not-LN`），`press` 本来就要求偏移合法非零，所以对象在规范域外，读作 "谓词太宽"；
  - 自身行律不读证据与底（`self-indep`）。

  律推出不合理的东西（如 `fullSem` 一类）：没有找到（判断）。依据是 `upI` 无前提地满足整个接口；接口若推出 LPO 或 WLPO，它们就能在 `--safe` 下证出。
- **第 3 项（上折与合法性）：编译定理。**
  - `Up-mono` 只有序的前提（`up-mono-inst`）。
  - `Up-LN` 的 "底合法且非零" 可以满足（底取 Ωt ℓ，`up-LN-inst`），也去不掉：零底的后继给出不合法输出（`up-zero-illegal`）。零底不在规范域。
  - 底合法且非零时，没有合法输入折出不合法输出（`Up-LN` 本身）。

**未走通（判断，未证）。**
- 只有 `FlatKeep`、没有 `FlatOff` 时，是否推出判定：接口里没有约束分支侧跨支折叠的律，我推不出反向那一侧。
- `FlatKeep ∧ FlatOff` 能否与完整的接口实例同时满足（以判定神谕为条件）：没有构造。估计要把折叠与合法性按带神谕的 `kp` 整段重写，约 400 到 500 行。判断可行，因为 `YiPhiLegal` 的证明经 `kp-ind`，而神谕那一行满足 `Good`。

##### 2. 文件表

三个文件都放在 `probes/OCF/Lean/`。冷编译的做法：只删自己的 `.agdai`，日志里只有本模块的 `Checking` 行。

| 文件 | 总行 / 代码行（非空） | 冷编译退出码 | 内存峰值 | 用时 |
|---|---|---|---|---|
| `YiUpNegFlat.lagda.md` | 303 / 180 | 0 | 337 MiB | 2.1 s |
| `YiUpNegBound.lagda.md` | 112 / 78 | 0 | 442 MiB | 2.4 s |
| `YiUpNegSelf.lagda.md` | 103 / 56 | 0 | 330 MiB | 2.0 s |

内存是 RTS 报告的 "total memory in use"，不是操作系统的常驻内存（原因见第 6 节）。禁用构造检索为 0：postulate、TERMINATING、NO_POSITIVITY、trustMe、REWRITE、洞、`--cubical`、`--irrelevant-projections`。本机路径检索为 0。选项行都是 `--safe --without-K --lossy-unification`。

##### 3. 定理表

**定义**（YiUpNegFlat）：
```agda
root⁼ a ε t w = kp⁼ a ε t w (λ q _ → just q) nothing
FlatKeepᶠ ψs = (k h ε B j c) (w : j ≤ h c) (β b) (p : Pos (h c)) (G) (q : Pos j)
  → root⁼ (h c) (proj₂ (proj₂ ε c)) (inj₂ p) w ≡ just q
  → Kept q (ψs (Ωₗ k h) ε B j (inb c w) β (Upc (Ωₗ k h) c b (Ω p G)))
FlatOffᶠ ψs = (k h ε B j) (c c′ : Tr k) (w : j ≤ h c′) (β b p G) → (c ≡ c′ → ⊥)
  → (q : Pos j) → Kept q (ψs (Ωₗ k h) ε B j (inb c′ w) β (Upc (Ωₗ k h) c b (Ω p G))) → ⊥
FlatEᶠ ψs = Σ E, (… c c′ …) → E k c c′ ≡ nothing → (q : Pos j) → Kept q (同上) → ⊥
```
`Kept` 取自 `YiPhiNegK`：`Kept p o = Σ G′, o ≡ Ω p G′`。`FlatKeep I = FlatKeepᶠ (Iface.ψs I)`，`FlatOff`、`FlatE` 同理。

探针的写法：
- `p₀ = zero , inj₂ (inj₂ (zero , inj₂ top₁)) : Pos (h₃ c₀)`；
- `node b = Upc (tw 3) c₀ b (Ω p₀ (λ _ → zero))`；
- `O I b c′ = Iface.ψs I (tw 3) (Ev-tw 3) (B₀ (tw 3)) (tw 1) (inb c′ (wc c′)) (Ωt (tw 1)) (node b)`；
- c₀, `h₃`, `wc`, `y₀` 取自 `YiPhiNegB`。

"域" 一列的说法见本节末尾。

| 名字 | 陈述（逐字或签名） | 白话 | 文件 | 档 | 域 |
|---|---|---|---|---|---|
| `up-never` | `… (c c′ : Tr k) (w : j ≤ h c′) … (q : Pos j) → Kept q (F.ψs (Ωₗ k h) ε B j (inb c′ w) β (Upc (Ωₗ k h) c b (Ω p G))) → ⊥` | `upI` 在分支侧目标下从不保留摊平进来的结点，对一切 c, c′ | Flat | 编译定理 | 一切输入 |
| `off-up`, `flatE-up` | `FlatOff upI`；`FlatE upI` | 实例满足回退与证据派发 | Flat | 编译定理 | — |
| `root-p₀` | `root⁼ (h₃ c₀) (proj₂ (proj₂ (Ev-tw 3) c₀)) (inj₂ p₀) (wc c₀) ≡ just top₁` | 孩子层的保留判定交出 top₁ | Flat | 编译（refl） | 域内 |
| `child-keeps` | `(B β G) → Kept top₁ (F.ψs (h₃ c₀) (proj₂ (proj₂ (Ev-tw 3) c₀)) B (tw 1) (wc c₀) β (Ω p₀ G))` | omC 的定理形式 | Flat | 编译定理 | 域内 |
| `flat-folds` | `(B β b q) → Kept q (F.ψs (tw 3) (Ev-tw 3) B (tw 1) (inb c₀ (wc c₀)) β (node b)) → ⊥` | omD 的定理形式 | Flat | 编译定理 | 域内 |
| `probe-self` | `F.ψs (tw 3) (Ev-tw 3) B (tw 3) self β (up zero c₀ y₀) ≡ node β` | 探针结点是自身行的输出 | Flat | 编译定理 | — |
| `probe-in` | `Top (tw 3) (up zero c₀ y₀) × Leg (tw 3) (up zero c₀ y₀) × LN (tw 3) (Ωt (tw 3))` | 输入在 Top 内且合法，偏移合法非零 | Flat | 编译定理 | — |
| `probe-notTop` | `Top (tw 3) (node β) → ⊥` | 摊平后的结点离开 Top | Flat | 编译定理 | — |
| `c₀-in`, `cα-in` | `Top (tw 2) c₀ × Leg (tw 2) c₀`；`∀ α → Top (tw 2) (cα α) × Leg (tw 2) (cα α)` | 下标在域内 | Flat | 编译定理 | — |
| `flat→wdec` | `(I : Iface) → FlatKeep I → FlatOff I → (c′ : Tr (tw 2)) → WDec (c₀ ≡ c′)` | 加强连同回退推出弱判定 | Flat | 编译定理 | 探针在域内 |
| `flat→wdecα` | `… → ∀ α → (∀ n → α n ≡ false) ⊎ (c₀ ≡ cα α → ⊥)` | 同上，落到 α | Flat | 编译定理 | 域内 |
| `flat→wlpo` | `Funext → (I : Iface) → FlatKeep I → FlatOff I → WLPO` | 加函数外延得 WLPO | Flat | 条件定理 | 域内 |
| `flatE→dec` | `(I : Iface) → FlatKeep I → FlatE I → (c′ : Tr (tw 2)) → Dec′ (c₀ ≡ c′)` | 经同支证据派发则可判定 | Flat | 编译定理 | 域内 |
| `up-not-flatKeep` | `FlatKeep upI → ⊥` | 实例不满足加强 | Flat | 编译定理 | 域内 |
| `keep-const`, `const-not-off` | 常值函数 ψc 在探针上以 top₁ 为根；`FlatOffᶠ ψc → ⊥` | 探针上的保留单独可满足 | Flat | 编译定理 | — |
| `keepᴱ`, `offᴱ`, `flatEᴱ` | `(E) → ((k c) → E k c c ≡ just refl) → FlatKeepᶠ (ψsᴱ E)`；`FlatOffᶠ (ψsᴱ E)`；`FlatEᶠ (ψsᴱ E)` | 给定同支判定，裸函数满足加强与回退 | Flat | 条件实例（不是接口实例） | — |
| `chain-self`, `chain-path`, `chain-flat`, `chain-emb` | tw 1, c₂ = 2：自身行输出是 `Ω s₁ (λ _ → Ω s₂ (λ _ → β))`；`posW (tw 1) s₁ ≡ inb c₂ (ins self)`；在那一链步下内结点不是结点，摊平前同一链步保留它 | omD 出现在 upI 自己的链步里 | Flat | 有限测试（单个样本，对一切底） | 输入在 Top 内且合法 |
| `kp-ind₂` | 同一条路径上两次调用 `kp` 走同一支 | 工具 | Bound | 编译定理 | — |
| `flat-suc`, `flat-lim`, `flat-limu`, `flat-ink`, `flat-inu` | 例：`root⁼ (g n) (ε n) (inj₂ p) w ≡ just q → Kept q (F.ψs (lim g) ε B j (inl n w) β (Upc (lim g) n b (Ω p G)))` | 其余五行，实例保留摊平后的结点，槽位相同 | Bound | 编译定理，无前提 | 一切输入 |
| `up-zero-illegal` | `∀ {ℓ} (j : L) (d : Dn ℓ j) → Leg ℓ (Up j d zero (suc zero)) → ⊥` | 零底的上折不合法 | Self | 编译定理 | 域外 |
| `zero-not-LN` | `∀ {j} → LN j zero → ⊥` | 零不是合法非零 | Self | 编译定理 | — |
| `self-zero` | `(I : Iface) (ℓ ε B x c) → Iface.ψs I ℓ ε B ℓ self zero x ≡ zero → Leg ℓ (Iface.ψs I ℓ ε B ℓ self zero (up x c (sucCh ℓ c))) → ⊥` | 律在零偏移上迫使输出不合法 | Self | 编译定理 | 域外 |
| `self-zero-up`, `phi-legal` | upI：输入合法且输出不合法；旧折叠：输出合法 | 对照 | Self | 编译定理 | 域外 |
| `self-indep` | 两组 x 的自身折叠相等 → 自身行输出相等（ε, B 可不同） | 律不读证据与底 | Self | 编译定理 | — |
| `up-mono-inst`, `up-LN-inst` | `Up-mono j d b ◃s`；`Leg j y → LN ℓ (Up j d (Ωt ℓ) y)` | 前提的实例 | Self | 编译定理 | — |

域的说法：所用的规范域是 "`YiTopDom.Top` 内合法输入的自身行像"，因为上折的输出离开顶槽位（`up-notTop`, `probe-notTop`）。
- 目标路径 `inb c′ (wc c′)` 由塔的证据路径构成；规范链步的目标也是 `inb c (…)`（`chain-path`）。
- c′ 取遍 `Tr (tw 2)`；`wdecα` 用到的 cα α 都在 `Top` 内且合法。

##### 4. 每条否定的前提的可满足实例
- `I : Iface`：`upI`。
- `FlatOff`, `FlatE`：`upI`（`off-up`, `flatE-up`）。
- `FlatKeep`：没有接口实例（`up-not-flatKeep`）。
  - 探针上的保留单独由常值函数满足（`keep-const`），它不满足 `FlatOff`（`const-not-off`）。
  - 加强与回退合起来，由 `ψsᴱ E` 满足（`keepᴱ`, `offᴱ`），前提是有一个对角上给 `just refl` 的同支判定 E。这个前提构造地给不出，这正是定理的内容；经典地（排中律加 UIP）可满足，这一句是判断。
- `Funext`：只在 `flat→wlpo` 里作显式前提。
- `self-zero` 的前提 `ψs … self zero x ≡ zero`：`upI`，x = zero，refl。
- `Up-LN` 的前提：底 Ωt ℓ（`Ωt-leg`, `Ωt-nz`）。

##### 5. 与已知否定的关系（逐条核机制）
- **`YiPhiNegB.wdec` / `wdecα` / `wlpo`.** 探针相同（tw 3, c₀, `h₃`, `wc`），结论形状相同。有折叠（目标 `inb`），没有值，观测的是输出的头部。差别有三处：
  - 那里的对象是嵌入的 `up x c y`（律 `J2-Ωb`），这里是摊平后的结点（`Upc` 的像）；
  - 那里的回退律 `Ωb-off` 是精确的回退式，这里的 `FlatOff` 只要求 "不以槽位为根"，更弱，所以定理更强；
  - 失败的字段是 `kp` 的 `kp (Ωₗ k h) … (inj₂ (c , t)) (inb c′ w) K d = d` 一行。

  审查报告 RR14 说这里 "位置对应 `wdec`"，那是判断；现在它是编译过的同一堵墙，从嵌入行搬到了摊平后的结点行。
- **`viaE→dec`, `YiCtxNeg.diag1→dec`.** `flatE→dec` 用同一条 `diag→dec`：c₀ 处必须给出证据。机制相同。
- **`YiPhiNegKSem.fullSem→lpo`, `YiUniNegStep.step-full→lpo`.** 不同。那两条是 "保留可否" 作为层号上的存在命题，推出 LPO；这里判的是一个分支下标（`Tr (tw 2)` 的树）的相等，推出 WDec/WLPO。不归到那堵墙。
- **壁垒定理.** 不涉及：没有 `Ordᴰ` 初始段，没有三歧性。
- **`YiPhiNegDom` 的证据量化过宽.** `flat-ink` 用的路径是 `w ∙ proj₁ (proj₂ ε c)`，所以摊平后的结点照样继承那条 "证据好坏不受律约束" 的问题。这是继承来的，没有另写定理。

##### 6. 偏离与事故
- 第一次编译用 `/usr/bin/time -l` 测常驻内存，沙箱拒绝 `sysctl`，`time` 退出 1；agda 本身已经检查完。之后改用 `+RTS -s`，所以表里的内存是 RTS 报告的总量，不是操作系统的常驻内存。
- `YiUpNegBound` 是否定的边界（正面结果），文首照简报写 "验收文件（否定）"，并注明它是正面。
- 删过的接口文件只有自己的三个 `.agdai`，用的是字面路径，没有用 `--ignore-interfaces`。没有改任何已有文件，没有写临时目录以外的地方，没有提交。
- 没有用临时 `.agda` 试验文件，三个文件直接写成 literate。日志在 `<实验目录>/agents/upneg/`（`cold-Flat.log`, `cold-Bound.log`, `cold-Self.log`）。

文件：
- <仓库>/probes/OCF/Lean/YiUpNegFlat.lagda.md
- <仓库>/probes/OCF/Lean/YiUpNegBound.lagda.md
- <仓库>/probes/OCF/Lean/YiUpNegSelf.lagda.md
