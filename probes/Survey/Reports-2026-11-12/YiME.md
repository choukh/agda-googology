# (c) 值接口的记号直连实例 (YiME)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | <synthetic>, claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-13 09:58 至 10:25 |
| 工具调用 / agda 编译 (粗数) | 35 / 8 |
| token (usage 字段，按消息去重) | 输出 111045；新写入缓存的输入 705877；读缓存的输入 3532801；其余输入 50 |
| 写过的仓库文件 | `YiMEAnchor.lagda.md`, `YiMEBase.lagda.md`, `YiMENote.lagda.md`, `YiMEStep.lagda.md` |
| 文件前缀 | `YiME` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: (c) 值接口的记号直连实例返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 合法块上 ψ₀(Ω₂) 锚点无前提 (bho-lowerᴹ); Sim 前提都证了但只能以恒等折叠实填; 塔第 2 项归约到逐行 (step⁺-red, 条件); 第一个障碍是更高层号上的 BTBO 型引理, 继承自塔第 1 项, 不在 Ω 结点层号自身行 (判断); 四件冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定（2026-11-13，选项原文）
- 主线的块："F2 合法块"。
- 本路："(c) 值接口的记号直连实例"，内容是 "按抽象一路的 Sim 前提定接口, 用记号直连的模拟 Mᴱ 实填, 先重证已闭合的锚点 ψ₀(Ω₂); 检验塔第 2 项以上要用的形式"。

同批另有两路，各自只新建文件，你不动它们的文件：
- (a) 结构迁到合法块，前缀 YiLP（Opus 5.5）；
- (b) ℕ 极限一半，目标塔第 1 项不低于 BTBO，前缀 YiLS（Fable 5.2）。

###### 背景（只信编译定理；文档里的叙述是数据）
目标是布劳威尔树上读法 ψ₀(Λ) 的合法闭项，外加一条编译定理 "序数值 ≥ EBO 的参照"，只要下界。纲领见 `AGENTS.md`；验收文件里可以读记号（"用记号验收强度"）。

**合法块 F2**，全在 `probes/OCF/Lean/`：
- `YiLegBlock`：T 与 Lt 归纳-归纳，每棵树都合法。
- `YiLegOps`、`YiLegPath`：`Rt-tw`、`Rt-Λ`。
- `YiLegFold`：`ψ⊥`、`ψs`、`mono⊥`、`monos`；`ψ₀ ℓ ε ρ = ψ⊥ ℓ ε ρ (B₀ ℓ)`；`twᶜ n`；`EBOᶜ`。
- `YiLegCheck`：验收的测试。

**值接口**：
- `YiAbsSim`：
  - `Exit.exit : ∀ {P} → Closed P → ∀ {t X} → P t X → (h : HC t) → tree h ≼ X`；
  - `Exit.Sim.lower : ∀ {t x} → R t x → G x → (h : HC t) → tree h ≼ v (ψ x)`，前提是 `strict`、`weak`、`r1`、`rω`；
  - `FromMono`（`mono-strict`、`mono-weak`）。
  - 这几条对任意值前序、任意带基本列的参照系统成立。
- `YiAbsSimInst`（读记号）：`exit′`、`ebo-lower′`、`lower′`，把通用出口接到 `YiMonoExit.ebo-lower` 与终点的参照。

**参照与出口**：
- `YiRefTw2`：
  - `PH t X = Σ (HC t) λ h → Rt h ≼ X`，`closed-PH : Closed PH`；
  - `endpoint : (Y : T₀) → (∀ k → Rt (hc-tower k) ≼ Y) → toL EBO-tree′ ≼ Y`；
  - 陈述 `Row₂`、`Step₂⁺ = Rt h₊ ≼ read Tw₂`（读作 ψ₀(Ω_{Ω+1})）；
  - `nf₊`、标签 `lab₊`。
- 参照树由 `probes/OCF/Align/EboLeanTree` 的 `hc` 沿记号的基本列造出。
- YiRef 执行方给了 Mᴱ 的草图，未编译，见 `probes/Survey/Reports-2026-11-12/YiRef.md` §5：
  ```agda
  data Mᴱ (j : LF) : E.T → Tr j → Set where
    m0 : ∀ {t x} → cof t ≡ c0 → Mᴱ j t x
    m1 : ∀ {t x} → cof t ≡ c1 → Mᴱ j (pred t) x → Mᴱ j t (suc x)
    mω : ∀ {t f} → cof t ≡ cω → (∀ n → Mᴱ j (fsn t n) (f n)) → Mᴱ j t (lim f)
    mΩ : ∀ {t ν p g} → cof t ≡ cΩ ν → (∀ {s c} → Mᴱ (at j p) s c → Mᴱ j (fsT t s) (g (fromBr j p c))) → Mᴱ j t (Ω p g)
    mw : ∀ {t x x′} → Mᴱ j t x → j ⊢ x ◃ x′ → Mᴱ j t x′
  ```
  它是对旧块写的；合法块的构造子带推导（lim 带步进），要相应改，由你定。
- 已闭合的锚点在旧 YiUp 折叠上：`YiUpVal.bho-lower : L.ψ⁰ (L.Ω I2) ≼ read (ψ₀ two tt (Ωt two))`，参照框架是 `OCF.Align.Level`。
- 参照框架 `OCF.Align.Level` 的层号没有 Ω 结点层号，加构造子会碰 `dec→WLPO`（YiRef 判断），所以塔第 2 项以上要记号直连。

###### 要做
1. **定接口**：把 `Sim` 的前提落到合法块与记号参照上。R 取记号直连的 Mᴱ 一类关系，按块的层号索引，形状由你定。写出它满足 `Sim` 的哪几条前提，各条的证明或缺口。
2. **重证锚点**：在合法块上，用这套接口证出 "读作 ψ₀(Ω₂) 的记号参照 ≼ 合法块上对应闭项的 read"，即 `bho-lower` 的对应物；或证到第一个挡住的引理。
   - 参照用记号项与 `HC` 推导经 `Rt`（`toL ∘ tree`）给出；要不要另外接到 `L.ψ⁰ (L.Ω I2)`，由你定。
3. **检验形式**（可选，做不到就报告）：朝 `Step₂⁺`（ψ₀(Ω_{Ω+1}) ≼ 塔第 2 项的闭项）走。这是越过 Ω 结点层号自身行的最小一站，用来检验关键路径的第 3 步：Ω 结点层号用摊平式 (A) 时丢掉的同支结点，对下界要不要紧。回报第一个挡住的引理，并写清它是否落在 Ω 结点层号的自身行上。

###### 注意
- 实测的堆墙：YiRef 给具体的参照树另起名字再比较，检查器沿 `hc-tower` 的良基证明展开，6G 耗尽。写法：只用 `Rt` 作用在推导上，引理对一般的推导陈述，再代入具体推导；大参照树放 `opaque`。另见 `probes/Survey/EBOHandbook.md` 第 4 节。
- 合法块的树里含推导：形状相同、推导不同的两棵树不相等；含极限的树要比较时可能要改用关系（判断）。
- 基底单调由 (a) 在做；若需要，写成显式前提，交条件定理。
- **先验检查**（作者 2026-11-13 采纳为工作规则，见 `AGENTS.md`）：若要给折叠新写一行或换写法，先查目标是指定孩子的还是一致的、孩子下标有没有证据函数、有没有按存在性保留。对上 `YiAbsObs`/`YiAbsFrame` 的 `obs→dec` 一族的前提就不写。本路原则上不改折叠。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiME`（模块名 `OCF.Lean.YiME…`）。不改任何已有文件，不碰 `src/`、`archive/`。读记号的文件是验收文件，文首标 "验收文件"。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的标 "条件"。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G。
  - 冷编只删自己模块的接口，写字面路径；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
- 临时目录：`<实验目录>/agents/me`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；需要函数外延或 K（作前提除外）；8G 仍耗尽。没有编译的否定时只写 "未走通"。归到已知的墙之前，逐条核机制。
- **过程要求**：第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：对纲领与目标意味着什么，再列关键路径上暴露的问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档（编译定理 / 条件定理 / 有限测试 / 判断）；值的下界写成 ψ₀(Ω_x)，x 用 Ω 的算术。
4. 接口：R 的逐字定义，`Sim` 各条前提的状态。
5. 第一个障碍，精确到引理；若做了第 3 件，写清障碍是否落在 Ω 结点层号的自身行上。
6. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 中途消息（主审发给这一路）

转录时间戳 2026-11-13 10:18 (UTC)：

主审：刚才网络与认证出错（API 403），你的任务被中途打断。作者已重新登录，请从断点接着做，简报与规则不变。
- 你已写出 YiMEBase、YiMEAnchor、YiMENote、YiMEStep 四个文件。先看 <你的临时目录>/agents/me/ 里的日志，确认最后一次编译的状态：YiMEStep.log 是最后写的一份。
- 断开时可能有一个 agda 进程还在跑。重新编译前先确认它的日志已经写完，或者已经结束；同时只跑一个 agda，堆 8G。
- 做完后按简报的格式回报。

Address this before completing your current task.

转录时间戳 2026-11-13 10:22 (UTC)：

主审：作者重新登录了，请从断点接着做，简报与规则不变。
- 你已写出 YiMEBase、YiMEAnchor、YiMENote、YiMEStep 四个文件。先看 <你的临时目录>/agents/me/ 的日志，确认最后的编译状态：YiMEStep.log 是最后一份。
- 断开时可能有 agda 进程还在跑，先确认它已结束；同时只跑一个 agda，堆 8G。
- 做完后按简报的格式回报。

Address this before completing your current task.

## 回报原文

###### 回报: YiME（值接口的记号直连实例）

##### 1. 判决

**对纲领与目标。** 这一路只在验收层（第 4 层）加了关系与定理，没有改树、折叠、合法性，不触壁垒（只比较记号项，不比较块的层号）。

- 锚点已在合法块上重证：`bho-lowerᴹ` 是无前提的编译定理，参照是记号沿基本列造的树，不经 `OCF.Align.Level`。值的下界：`ψ₀ two tt tt (Ωt two)` 不低于 ψ₀(Ω₂)。
- 这是 "记号引导的验收"，不算树自足：关系 `Mᴰ` 的构造子形状读自记号的 `cof`/`pred`/`fsn`/`fsT`。
- 塔第 2 项一站（`Step₂⁺`）未走通，没有编译的否定。交了条件归约 `step⁺-red` 和形状测试。
- 中途一次 API 403 中断，按主审指示核对日志后续做；断点处最后一次编译已结束（退出 42，名字歧义），没有残留进程的迹象（沙箱里 `pgrep` 不可用，依据是日志完整且命令已同步返回）。

**关键路径上暴露的问题**

| 问题 | 位置 | 档 |
|---|---|---|
| `Sim` 的 "ψ 是折叠、源层是单棵高层树" 的形式填不上。规则 4 把 ψ₀(b+1)[n] 写成和 ψ₀(b)·n，和不是单棵源树的折叠。实填只能取 ψ = 恒等、S₁ = S₀ = `Tr zero`；折叠保持不在 `Sim` 的前提里，而在 "闭项与记号项有 `M⁰`" 的证明里。 | `YiMEBase.lower⁰` | 定义事实 + 判断 |
| `Step₂⁺` 的第 0 行就是 BTBO 那一行，落在层号 `h₂ (c₂ 1) = tw 1 ⊕ ↑c₁` 上；c₁ 是 Ω 结点层号自身行（`Upc`）的输出。所以这一站包含一条比 (b) 路目标（BTBO ≼ 塔第 1 项）层号更高的 BTBO 型引理。 | `YiMEStep`：`row₀-btbo`、`row-form`、`c₁-form`、`lev₁-form` | 条件定理 + 有限测试 |
| 关系 `Mᴰ` 是带松弛的 "记号 ≤ 树"（`mz`、`mw`）。层号是固定数字时（锚点）够用。孩子下标是回灌的折叠输出时（Ω 结点层号的 `up` 行，层号 `h c`），树的层号只是不低于记号下标，要补 "行的值对孩子下标沿 `◃` 单调"。 | 所缺引理见 §5 | 判断（未编译） |
| 记号 "保留/折叠" 由 `cmpᵀ (ν+1) u` 定，块由路径 `kp` 定。松弛下二者可以不一致：记号折叠而块保留时，`Mᴰ` 里没有可用的构造子（第一位置序只给第一分支）。 | `Mᴰ` 的 `mΩ`、`mL` | 判断 |
| 摊平式丢掉的同支结点（`kp … (inj₂ (c , t)) (inb c′ w) = d`，c′ = c 时也折叠）不在第一个障碍上。它要等到把含自身行输出的 `tw 1` 层的树朝孩子层目标折叠时才进入。 | `drop-same`（定义的展开）；"何时进入" 是纸面追踪 | 测试 + 判断 |

##### 2. 文件表

都在 `<仓库>/probes/OCF/Lean/`，验收文件，文首各 3 行。删自己四个接口后按依赖顺序冷编，每份日志只有自己模块的一行 `Checking`。

| 文件 | 总行 | 代码行 | 冷编退出码 | 内存（RTS 报告的 total in use） |
|---|---|---|---|---|
| `YiMEBase.lagda.md` | 227 | 160 | 0 | 1252 MiB |
| `YiMENote.lagda.md` | 83 | 51 | 0 | 246 MiB |
| `YiMEAnchor.lagda.md` | 284 | 204 | 0 | 1259 MiB |
| `YiMEStep.lagda.md` | 138 | 80 | 0 | 1167 MiB |

每个约 2 到 8 秒。禁用构造与本机路径检索为 0（`postulate`、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`--cubical`、`irrelevant-projections`、洞）。没有用函数外延或 K。

##### 3. 定理表

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `lower⁰` | `∀ {t x} → M⁰ t x → (h : HC t) → Rt h ≼ read x` | 第 0 层有关系就有值的下界；由 `YiAbsSimInst.lower′` 实填得出 | Base | 编译定理 |
| `r1⁰` | `∀ {t x} → M⁰ t x → cof t ≡ c1 → Σ (Tr zero) λ x′ → M⁰ (pred t) x′ × ⊤ × (suc x′ ⊴ x)` | `Sim` 的 r1 | Base | 编译定理 |
| `rω⁰` | `∀ {t x} → M⁰ t x → cof t ≡ cω → ∀ n → Σ (Tr zero) λ x′ → M⁰ (fsn t n) x′ × ⊤ × (x′ ⊴ x)` | `Sim` 的 rω | Base | 编译定理 |
| `strict⁰` / `weak⁰` | `⊤ → suc x ⊴ y → O.suc (read x) ≼ read y` / `⊤ → x ⊴ y → read x ≼ read y` | `Sim` 的两种步 | Base | 编译定理 |
| `Gen.m-add` | `∀ {p b s y} → M (p ∷ []) b → M s y → M (p ∷ s) (b + y)` | 和对加法，对一切层的签名 | Base | 编译定理 |
| `Gen.m-next` | `∀ {t p b} (nz : Lt S zero b) → cof t ≡ cω → (∀ n → fsn t n ≡ replicate n p) → M (p ∷ []) b → M t (next b nz)` | 规则 4 对 `next` | Base | 编译定理 |
| `Gen.m-right`、`m-cum`、`m-zl`、`pos⁰` | 见文件 | 右加、部分和极限、"零到底" 推到一切输入、非零的树在 1 之上 | Base | 编译定理 |
| `At.PF` | `∀ {a x} → M¹ a x → M¹ (ψ₁ᵗ a) (F x)` | ψ₁(a) 对折到自身 | Anchor | 编译定理（对满足三条的任意底） |
| `At.QH` | `∀ {a x} → M¹ a x → M⁰ (ψ₀ᵗ a) (H x)` | ψ₀(a) 对折到第 0 层的树；结点处规则 6 的 γ-链对回灌链（`chain`） | Anchor | 同上 |
| `At.VW` | `∀ {a x} → M¹ a x → M⁰ (ψ₀ᵗ a) (W x)` | ψ₀(a) 对底折叠 | Anchor | 同上 |
| `At.lowerM` | `M⁰ t₂ (ψ⊥ two tt tt B₂ (Ωt two))` | 对任意满足三条的底 B₂ | Anchor | 编译定理 |
| `bho-M` | `M⁰ t₂ (ψ₀ two tt tt (Ωt two))` | 取 `B₀ two` | Anchor | 编译定理，无前提 |
| **`bho-lowerᴹ`** | `(h : HC t₂) → Rt h ≼ read (ψ₀ two tt tt (Ωt two))`，其中 `t₂ = ψ₀ᵗ (E.Ωs (natT 1))` | 合法块上闭项的值 ≥ ψ₀(Ω₂)（只有下界） | Anchor | 编译定理，无前提 |
| `nf₂`、`h₂` | `NF t₂`、`HC t₂`（`h₂ = hc nf₂ (c∷ c[])`） | 推导存在，上一条不是空话 | Anchor | 编译定理 |
| `Lev.Mᴸ` | `(j : L) → E.T → Tr j → Set`，对层号递归，参数 `Ix : L → E.T → Set` | 一切层号上的关系；检查器接受 | Step | 定义（编译） |
| `step⁺-red` | `(∀ n → M⁰ (ψ₀ᵗ (γ₊ n)) (row (suc n))) → Step₂⁺ᴸ`，`Step₂⁺ᴸ = (h : HC t₊) → Rt h ≼ read (twᶜ 2)` | ψ₀(Ω_{Ω+1}) 一站归约到逐行的 `M⁰` | Step | 条件定理，前提未证 |
| `row₀-btbo` | `M⁰ (E.EBOψ 2) (row 1) → (h : HC (E.EBOψ 2)) → Rt h ≼ read (twᶜ 2)` | 第 0 行给出 ψ₀(Ω_Ω) ≼ 塔第 2 项 | Step | 条件定理，前提未证 |
| `form₂`、`row-form`、`c₁-form`、`lev₁-form`、`drop-same`，`ψ₀ᵗ (γ₊ 0) ≡ E.EBOψ 2` | 都是 `refl` | 形状 | Step | 有限测试 / 定义的展开 |

- 前提可满足性：`At` 的三条由 `B₀ two` 满足（`Mβ₀`、两个 `m1 refl mz`）。
- `step⁺-red` 与 `row₀-btbo` 的前提没有实例，也没有否定。
- `Step₂⁺ᴸ` 里的 `twᶜ` 是合法块（`YiLegFold`）的，不是 `YiRefTw2.Step₂⁺` 用的旧块；`t₊` 与 `YiRefTw2.t₊` 同一个项。

##### 4. 接口

R 的逐字定义（`YiMEBase`）：
```agda
data Mᴰ (S : Sg) (Low : (p : P S) → E.T → B S p → Set) (Chd : (c : C S) → E.T → D S c → Set)
        (Nu : P S → E.T → Set) : E.T → T S → Set where
  mz : ∀ {x} → Mᴰ S Low Chd Nu [] x
  m1 : ∀ {t x} → cof t ≡ c1 → Mᴰ S Low Chd Nu (pred t) x → Mᴰ S Low Chd Nu t (suc x)
  mL : ∀ {t x} → cof t ≡ cω → (∀ n → Mᴰ S Low Chd Nu (fsn t n) x) → Mᴰ S Low Chd Nu t x
  mΩ : ∀ {t ν p g} → cof t ≡ cΩ ν → Nu p ν
     → (∀ η c → Low p η c → Mᴰ S Low Chd Nu (fsT t η) (g c)) → Mᴰ S Low Chd Nu t (Ω p g)
  mU : ∀ {t s x c y e} → Mᴰ S Low Chd Nu t x → Chd c s y → Mᴰ S Low Chd Nu (t ++ s) (up x c y e)
  mw : ∀ {t x x′} → Mᴰ S Low Chd Nu t x → Lt S x x′ → Mᴰ S Low Chd Nu t x′

M⁰ = Mᴰ (Sig zero) (λ ()) (λ ()) (λ ())
M¹ = Mᴰ (Sig one) Low¹ (λ _ → M⁰) Nu¹     -- Low¹ (inj₁ _) = M⁰；Nu¹ _ ν = ν ≡ []
```

与 YiRef 草图的差别：
- `mL` 不严格：基本列逐项不高于同一棵 x，不带下标对齐。块的链比记号的 γ-链晚一步，逐项对齐的 `mω` 填不上。
- `mz` 对任意 x。
- 多一个 `mU`：记号的和对着 `up`。
- `mΩ` 带槽位允许的共尾下标 `Nu`。
- 合法块的 `lim` 带步进，但 `mL` 不读 `lim`，所以不受影响。
- 低层关系作参数，高层实例对层号递归（`Lev.Mᴸ`），避开正性问题。

`Sim` 各条前提的状态。实填：S₁ = S₀ = `Tr zero`，ψ = 恒等，v = `read`，G = ⊤，`x ⇝ˢ y := suc x ⊴ y`，`x ⇝ y := x ⊴ y`，R = `M⁰`。

| 前提 | 状态 |
|---|---|
| `strict` | 证了（`strict⁰`） |
| `weak` | 证了（`weak⁰`） |
| `r1` | 证了（`r1⁰`，对推导反演） |
| `rω` | 证了（`rω⁰`） |
| `FromMono` | 没有用。严格步取 "后继在下" 的形式，不要第一位置序的值严格性 |

缺口不在 `Sim` 的前提里，在高层：
- 高层的 R（`Mᴸ`）要一个 "层号对记号下标" 的关系 `Ix`。后继层号上是字面的；Ω 结点层号与 ℕ 极限层号上没有给出。
- 折叠保持（`PF`/`QH`/`VW` 的一般层号版）只在第 1 层证了。

##### 5. 第一个障碍

**精确到引理。** `step⁺-red` 的前提在 n = 0 是：
```agda
M⁰ (E.EBOψ 2) (row 1)
-- row 1 ≡ ψ⊥ (h₂ (c₂ 1)) … (dW (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (B₀ (tw 2)) (c₂ 1) zero) (Ωt (h₂ (c₂ 1)))   （row-form, refl）
```
即 ψ₀(Ω_Ω) 不高于层号 `h₂ (c₂ 1)` 上 Ω 树的底折叠，底是 `dW` 造的，不是 `B₀`。

用 `mL` 展开后要的是下面这条（判断，未编译；A 是我起的名字）：

> **A**：对一切 `M⁰ η c`（c 是可数树，η 是记号项），有 `M⁰ (ψ₀ᵗ (E.Ωt η)) (…层号 tw 1 ⊕ L_c 上 Ω 树的底折叠与到第 0 层的折叠…)`，对满足下界条件的一切底。

对 `M⁰ η c` 归纳时各情形（都是判断）：
- `mw`（c ◃ c″）：要行的值对孩子下标沿 `◃` 单调。第 0 层只有 `◃s`（层号 a 对 `suc a`）与 `◃l`（`g n` 对 `lim g`，带换底）两种生成步。后一种是 ℕ 极限层号的行，即 (b) 路与 V81 的范围，并且要 (a) 路的基底单调。
- `m1`（c = suc c′）：要锚点的 `PF`/`QH`/`VW` 在一般层号上成立，前提是层号与记号下标的对应足够精确，使 `kp` 的保留与 `cmpᵀ` 一致。带松弛的 `M⁰ η c` 不给这个。
- 同一条引理在 `tw 1` 上（层号 `h₁ c`，不带 `tw 1 ⊕`）就是 (b) 路的目标。所以 `Step₂⁺` 的第一个障碍继承自塔第 1 项，不是塔第 2 项新出的。

**是否落在 Ω 结点层号的自身行上：不在。**
- 第一个障碍在 Ω 结点层号的 `up` 行：孩子下标 c 是回灌的折叠输出，层号 `h c` 随之而变。具体是 `ψ⊥ (Ωₗ k h) … (up x c y e)` 与 `ψs (Ωₗ k h) … (ink w) … (up x c y e)` 两行。
- 自身行只出现在它的输入里：`c₂ 1` 是自身行的输出（`c₁-form`），它被读成层号（`lev₁-form`），没有在这一步被折叠。
- 摊平式丢掉的同支结点那一行，这一步没有进入。纸面追踪（判断）：
  - 它第一次进入，是在层号 `suc X`（X 是 Ω 结点层号）的链把 X 上的自身行输出再朝某个孩子层目标折叠的时候（目标路径含 `inb`）。
  - 那里记号在分支下标小于目标时保留结点，块一律折叠，块的子值低于记号的对应子项。
  - 这对整体下界要不要紧，这一路没有得到判决。

**与已知结果的关系。** 我没有把 A 的 `mw` 情形归到 "跨层单调接口被否定" 那堵墙。那条否定的陈述我没有读，只在记忆索引里见到一句；A 只对 Ω 树这一棵、只沿 `◃s`/`◃l` 两种步，量化域不同，要逐条核对后才能归类。

##### 6. 偏离与事故

- 事故：
  - 一次 API 403 中断（见 §1）。
  - 类型错误三次：`P` 与块的字段重名；辅助引理改名时误伤；`Rt` 歧义。都已改。
  - `/usr/bin/time -l` 在沙箱里因 `sysctl` 被拒而返回 1，那一轮的退出码不算；随后改用 `+RTS -s` 重新冷编，四个都是 0。
  - 没有堆耗尽。
- 偏离：
  - 没有接到 `L.ψ⁰ (L.Ω I2)`（简报许可由我定）。
  - 多建了 `YiMENote`，把记号一侧的展开等式单放。
  - 锚点文件里 `Pu`/`Qu`/`Vu` 三个同形引理各写了一遍，没有抽象。
  - 第 3 件只做到条件归约与形状测试，引理 A 没有写成编译的 `Set`，也没有尝试证明。
- 没有读、只凭转述引用的：
  - `YiAbsObs`/`YiAbsFrame` 的 `obs→dec` 一族（本路没改折叠）。
  - `EBOHandbook.md` 第 4 节。
  - V81 的原文与 `YiUpValTw1`。
  - "跨层单调接口被否定" 的定理。
  - (a)、(b) 两路的文件。
  - "`twᶜ 2` 读作约 ψ₀(Ω_{Ω_{Ω+1}})" 取自 YiRef 回报，是那里的判断。
- 规则遵守：只新建了四个 `YiME*` 文件；没有改已有文件，没有碰 `src/`、`archive/`，没有删别人的接口，没有提交。

文件路径：
- `<仓库>/probes/OCF/Lean/YiMEBase.lagda.md`
- `<仓库>/probes/OCF/Lean/YiMENote.lagda.md`
- `<仓库>/probes/OCF/Lean/YiMEAnchor.lagda.md`
- `<仓库>/probes/OCF/Lean/YiMEStep.lagda.md`
- 日志：`<实验目录>/agents/me/`
