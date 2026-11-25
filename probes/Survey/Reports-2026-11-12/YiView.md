# 内部 View 与 FGH (YiView)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-13 08:55 至 09:29 |
| 工具调用 / agda 编译 (粗数) | 64 / 15 |
| token (usage 字段，按消息去重) | 输出 141695；新写入缓存的输入 279548；读缓存的输入 11829971；其余输入 116 |
| 写过的仓库文件 | `YiViewFGH.lagda.md`, `YiViewInst.lagda.md`, `YiViewRead.lagda.md`, `YiViewVal.lagda.md`, `YiViewWf.lagda.md` |
| 文件前缀 | `YiView` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: 内部 View 与 FGH 返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | View 对一切层号、一切合法对象, 无前提 (brwView); 部分良基 (wf, vrec); FGH 接到闭项, 与参照框架逐点相等 (FGH-read); 值的 Ω 坐标是块的低层树 (V92 待作者看); 五件冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方。全程用中文写文件与回报。主审会从头冷编译复核你交的每个文件，只认编译过的定理。

作者 2026-11-13 的方向（原话）："先重点排查 YiUp，把关键路径上的问题都尽早暴露出来，如果没有问题，就上攻，其他候选路线仅作后备"。这一路是作者选的 "内部 View 与 FGH（纲领第 1 条）"，说明："在 YiUp 的块上写内部 View（每个对象看成零、后继、ℕ 极限或 Ω 极限，嵌入与结点都要分解），证值上一致；并把 FGH 接到闭项上。这是纲领的硬要求，越早暴露越好。Opus 5.5。"

同批在跑四路（`YiLim`、`YiOmC`、`YiUpSim`、`YiRef`），你不读它们的输出，也不动它们的文件。

###### 纲领第 1 条（AGENTS.md 原文，作者 2026-11-05 的解释）
"中间层若不直接用布劳威尔树，必须有布劳威尔树的 View，作为最终定义的验收标准。中间层可以比布劳威尔树多（差、坐标、世界等额外信息），不能比它少。View 指内部 View，值上一致：每个对象 x 可以看成零、后继（x = y + 1）、ℕ-极限（相邻项按目标树自己的合法性步进，即第一位置；不要求按值严格递增，那会推出 LPO，见 `BrwViewNeg.strict→LPO`）或 Ω-极限（按低层合法树分支的 g），其中 y、f n、g c 仍是同一类型的对象，可以像布劳威尔树一样递归；x 的值与对应构造子作用在各部分的值上互相 `≼`。"

###### 背景（只信编译定理）
- **主候选 YiUp 线的块**：空白页的块 `probes/OCF/Lean/YiFreshBlock.lagda.md`。层号 `L` 与树 `Tr` 归纳-递归；树的构造子有 zero、suc、lim、Ω（槽位是层号里的路径 `Pos`），以及 `up x c y`，读作 x + ↑y，y 是孩子层的树原样嵌入。
  - 合法性在 `YiFreshLegal`：第一位置序 `_⊢_◃_`，`Leg`。
  - 折叠在 `YiUpFold`，第 0 层的树是普通布劳威尔树。
  - 闭项 `EBOᶜ`（`YiUpLegal`）合法无前提。
  - 读回 `YiFreshValRead.read : Tr zero → L.Ordᶜ L.zero`。
- **已有的 View 定义**：`probes/OCF/Align/BrwViewDef.lagda.md`。记录 `Sig` 与 `BrwView`，一个对一切层、一切高度通用的定义；四种读法 零 / 后继 / ℕ 极限（相邻项 `Stp`）/ Ω 极限（种类 `Kd`、坐标 `Cd`）；值一致是四条 ≈。还有 `BrwView.lagda.md`、`BrwViewNeg.lagda.md`（`strict→LPO`）、`BrwViewOne`、`BrwViewLift` 等，作样板。
- **FGH**：`src/OCF/BTBO.lagda.md` 的 `FGH : Ord₀ → ℕ → ℕ`（只读）；`probes/OCF/Align/EboLeanTree.lagda.md` 的 `fgh-EBO′`。

###### 要做（每做成一件先编译）
1. **值**：View 要 "值上一致"，所以先要每层树的值。
   - 定一个值的读法：每层的 `Tr ℓ` 读进某个序数树类型，与 `_≼_` 可比；第 0 层就是 `read`。高层可以借 `OCF.Align.Level` 的 `Ordᶜ`，或 `BrwViewDef` 的 `Sig` 所要的值类型。
   - 写清 `up x c y` 的值：是 x 的值加上 y 的值抬上来的值。
2. **View**（新文件，例如 `YiViewDef`、`YiViewInst`；块一侧的定义尽量是成品候选，不导入记号）：对一切层号 ℓ 与一切合法的 `x : Tr ℓ`，给出四种读法之一，各部分仍是同一类型的合法对象。
   - zero、suc、lim、Ω 直接给出。
   - `up x c y` 要按 y 分解。y 是零时，合法性要求孩子非零，说明怎样处理；y 是后继，就是 `suc (up x c y′)`；y 是极限，就是逐项；y 是 Ω 结点，就是父层槽位 `chP` 上的 Ω 极限，分支是 `up x c (g z)`；y 是嵌套的 `up`，递归处理。
   - ℕ 极限读法的相邻项要按目标树自己的第一位置步进（`◃`），不要求值严格递增。
   - 尽量接到 `BrwViewDef` 的记录上（给出 `Sig` 实例与 `BrwView` 实例）；接不上就如实写原因，另写一个等价的陈述。
3. **值上一致**：每一种读法，x 的值与对应构造子作用在各部分的值上互相 `≼`（或 ≈）。逐条编译。做不到的写清卡在哪一条，例如 `up` 的 Ω 极限读法要 "x + sup = sup (x + ·)"。
4. **FGH**：在第 0 层的树上定义（或借用）FGH，接到 YiUp 的 `EBOᶜ` 上，得到一个闭的 `ℕ → ℕ` 函数，写一条有限测试（如 n = 0, 1）。
5. **尽早暴露问题**：哪一条与纲领冲突或做不到，精确写出。

###### 先读什么
- `AGENTS.md` 全篇（纲领 1 与 "布劳威尔树的 View"）。
- `YiFreshBlock` 全读；`YiFreshLegal` 的 `_⊢_◃_` 与 `Leg`；`YiUpBlock` 的 `chP`、`mv`；`YiFreshValRead` 全读。
- `BrwViewDef`、`BrwView` 全读；`BrwViewNeg` 文首；`BrwViewLift` 文首。
- `src/OCF/BTBO.lagda.md` 的 `FGH`（检索）；`EboLeanTree` 的 `fgh-EBO′`（检索）。

查签名用检索，不整篇读大文件。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiView`（模块名 `OCF.Lean.YiView…`）。不改任何已有文件，不碰 `src/`、`archive/`。
- 块一侧的 View 定义尽量是成品候选，用 `python3 probes/Survey/scripts/importclosure.py OCF.Lean.<模块>` 检查。导入参照框架的文件是验收文件，文首标 "验收文件"。
- 中文 literate Agda。每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只准作验收文件里的显式前提。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 6G。
  - 冷编译只删自己模块的接口，写字面路径；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
- 临时目录：`<实验目录>/agents/view`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- **停下的条件**：同一处两次重新设计仍过不了检查器；需要函数外延或 K；6G 仍耗尽。没有编译的否定时只写 "未走通"。
- **过程要求**：读完后尽快动手，第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编译退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：View 做到哪里；值上一致做到哪几条；FGH 是否接上；暴露出的关键路径问题，表：问题、位置、档。
2. 文件表：文件、代码行数、冷编译退出码、常驻内存峰值、是否成品候选。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 设计：值的读法怎样定，`up` 的分解怎样写。
5. 第一个障碍：精确到引理，附检查器报错原文（若有）。
6. 偏离与事故。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 1. 判决

**View 已完整做出，对一切层号、一切合法对象成立，无前提**（编译定理）。块一侧的四个文件都是成品候选，导入闭包里没有记号模块。结论是：纲领第 1 条（布劳威尔树的 View）在 YiUp 的块上不构成障碍。

- **View**：`YiViewInst.brwView` 是 `BrwViewDef` 意义下的一个记录，下标取 `Ix = L`，对一切层号一次给出。
  - 每个合法的 `x : Tr ℓ` 读作零、后继、ℕ 极限或 Ω 极限之一，各部分都是同层的合法对象。
  - `up x c y` 按 y 的 View 分解，嵌套的 `up` 由对 y 的递归处理。
- **值上一致**：四种读法都是 x 的值与构造子作用在部分的值上互相 `≼`。
  - zero、suc、lim、Ω 四种直接读出的情形是字面相同（`≈-refl`）。
  - `up` 的四种情形经 `F≈` 与 `val-upz` 得到。"x + sup = sup (x + ·)" 在值的加法 `⊹` 里按定义成立，不需要另证。
- **超出简报的三件**（都无前提）：
  - 部分良基，可以沿 View 递归（`wf`、`parts⊆`、`vrec`）。
  - ℕ 极限的相邻项在树自己的 `◃` 里也步进（`objStep`）。
  - 抬升不改值（`emb-≈`，跨层的 `≼`）；块不比布劳威尔树少（`incl`）；块的加法的值就是值的加法（`val-+`）。
- **FGH 已接上**：`fgh = FGH EBOᶜ : ℕ → ℕ` 是闭项。有限测试只有 `fgh 0 ≡ 0`（`refl`）。`FGH EBOᶜ 1 ≡ 2` 是定理 `FGH-1` 的实例，不是测试。在验收文件里证了 `L.FGH (read x) n ≡ FGH x n`。

**暴露出的关键路径问题**

| 问题 | 位置 | 档 |
|---|---|---|
| 目标树 `V ℓ` 的 Ω 坐标是块自己的低层树 `Tr k`（含 `up`），不是低层的值 `V k`。合法性不要求分支函数 g 尊重值，所以把坐标换成值，上确界可能变（与 BTBO 的 `limᵢ` 同类）。作者若要求坐标也是纯四构造子的树，需要改 `L` 的 `Ωₗ`，也就是改块。 | `YiViewVal.V` | 判断（未编译反例） |
| 值的第一位置序 `◁` 不是严格的，所以 "孩子读作零" 不能从值排除。`mapUp` 在这种情形改用 x 自己的 View（`reidx`）。我认为合法树里这一支不会走到，但没有证。 | `YiViewInst.mapUp` 的 `vz` 行 | 前半是定理（构造本身），后半是判断 |
| 合法的退化结点（如分支全为零的 Ω 结点，值 ≈ 0）被读作 Ω 极限，不出错。按 `Leg` 的定义它合法，但我没有写成编译定理。 | `YiFreshLegal.Leg` | 判断 |
| `Leg (up …)` 的第三个分量 "孩子非零" 在 View 里没有用到（`view` 的模式是 `_`）。它只在部分的合法性里出现，而那里由 `zl` 从部分自身的合法性得到。 | `YiViewInst.view` | 代码事实 |
| 用 `refl` 求 `fgh 1`，240 秒没有算完（临时目录试验，退出码 124）。陈述写成 `fgh 1 ≡ 2` 时，检查器会经别名 `fgh` 把两边求值，180 秒没有完成，我中止了。改成逐字写 `FGH EBOᶜ 1 ≡ 2` 后，检查只需几秒。 | `YiViewFGH` | 工程（有限测试） |
| 第 0 层的 `FGH x 0` 和 `FGH x 1` 只由树的头部决定，所以测试只说明闭项能在检查器里求值到底，不反映强度。 | `YiViewFGH` | 定理（`FGH-1`）加说明 |

本路没有回答的事：`val` 与折叠 ψ 之间的关系、EBOᶜ 的值的上下界、值相同的树 FGH 是否相同。

#### 2. 文件表

均在 `probes/OCF/Lean/` 下。内存是 GHC RTS 的 "total memory in use"：沙箱拦了 `/usr/bin/time -l` 和 `ps`，拿不到操作系统的常驻内存峰值。

| 文件 | 代码行（agda 块里非空非注释） | 冷编译退出码 | 内存 | 成品候选 |
|---|---|---|---|---|
| `YiViewVal.lagda.md` | 244 | 0 | 889 MiB | 是（导入闭包干净） |
| `YiViewInst.lagda.md` | 108 | 0 | 818 MiB | 是（干净） |
| `YiViewWf.lagda.md` | 140 | 0 | 909 MiB | 是（干净，闭包 20 个模块） |
| `YiViewFGH.lagda.md` | 40 | 0 | 867 MiB | 是（干净） |
| `YiViewRead.lagda.md` | 51 | 0 | 1431 MiB | 否，验收文件（导入 `OCF.Align.Value`；`importclosure` 判 FAIL，作正对照） |

自查情况：
- 每次冷编译前删掉自己五个模块的 `.agdai`，日志里只有自己模块的 `Checking` 行。
- 禁用构造检索为 0：postulate、TERMINATING、NO_POSITIVITY、trustMe、洞、K、`--irrelevant-projections`、funext 都没有。
- 仓库文件里没有本机路径。

#### 3. 定理表（全部是编译定理，无前提）

| 名字 | 陈述（逐字） | 白话 | 文件 |
|---|---|---|---|
| `brwView` | `BrwView SigY Tr (λ {i} x → val i x) (λ {i} x → Leg i x)` | 每层每个合法对象都有四种读法之一，值一致 | Inst |
| `view` | `(ℓ : L) (x : Tr ℓ) → Leg ℓ x → VW ℓ (val ℓ x)` | 上一条的函数本体 | Inst |
| `mapUp` | `(ℓ : L) (c : Ch ℓ) (x : Tr ℓ) → Leg ℓ x → VW ℓ (val ℓ x) → {v : V (chL ℓ c)} → VW (chL ℓ c) v → VW ℓ (val ℓ x ⊹ emb ℓ c v)` | 孩子的 View 给出 `up x c y` 的 View | Inst |
| `val-upz` | `(ℓ : L) (c : Ch ℓ) (x : Tr ℓ) (y : Tr (chL ℓ c)) → val ℓ (upz ℓ c x y) ≡ val ℓ x ⊹ emb ℓ c (val (chL ℓ c) y)` | `up` 部分的值 | Inst |
| `parts⊆` | `(ℓ : L) (x : Tr ℓ) (h : Leg ℓ x) {t : Tr ℓ} → Part (view ℓ x h) t → Pt ℓ t x` | View 的部分都在部分关系里 | Wf |
| `wf` | `(ℓ : L) (x : Tr ℓ) → Acc ℓ x` | 部分关系良基 | Wf |
| `vrec` | `(ℓ : L) (P : Tr ℓ → Set) → ((x : Tr ℓ) (h : Leg ℓ x) → ((t : Tr ℓ) → Part (view ℓ x h) t → Leg ℓ t → P t) → P x) → (x : Tr ℓ) → Leg ℓ x → P x` | 沿 View 递归 | Wf |
| `objStep` | `(ℓ : L) (x : Tr ℓ) (h : Leg ℓ x) → ObjStep (view ℓ x h)` | ℕ 极限读法的相邻项按树的 `◃` 步进 | Wf |
| `≼-trans` | `∀ {ℓ₁ ℓ₂ ℓ₃} {a : V ℓ₁} {b : V ℓ₂} {c : V ℓ₃} → a ≼ b → b ≼ c → a ≼ c` | 跨层值前序可传递 | Val |
| `emb-≈` | `(ℓ : L) (c : Ch ℓ) (v : V (chL ℓ c)) → emb ℓ c v ≈ v` | 抬升不改值 | Val |
| `valCh-≈` | `(ℓ : L) (c : Ch ℓ) (y : ChT ℓ c) → valCh ℓ c y ≈ val (chL ℓ c) (chT ℓ c y)` | `up` 里孩子部分的值就是孩子的值 | Val |
| `val-mono` | `(ℓ : L) {x y : Tr ℓ} → ℓ ⊢ x ◃ y → val ℓ x ◁ val ℓ y` | 树的第一位置推出值的第一位置 | Val |
| `val-leg` | `(ℓ : L) (x : Tr ℓ) → Leg ℓ x → LegV ℓ (val ℓ x)` | 合法树的值合法 | Val |
| `val-incl` / `incl-leg` | `∀ {ℓ} (v : V ℓ) → val ℓ (incl v) ≈ v` / `∀ {ℓ} (v : V ℓ) → LegV ℓ v → Leg ℓ (incl v)` | 块不比布劳威尔树少 | Val |
| `val-+` | `∀ {ℓ} (x y : Tr ℓ) → val ℓ (x + y) ≈ val ℓ x ⊹ val ℓ y` | 块的加法就是值的加法 | Val |
| `FGH-val` | `(x : Tr zero) (n : ℕ) → FGHᵥ (val zero x) n ≡ FGH x n` | 树与值的 FGH 相同 | FGH |
| `FGH-1`, `fgh-1` | `(x : Tr zero) → FGH x 1 ≡ 2`；`FGH EBOᶜ 1 ≡ 2` | n = 1 处恒为 2 | FGH |
| `test₀` | `fgh 0 ≡ 0`（`refl`） | **有限测试** | FGH |
| `read-val` | `(x : Tr zero) → read x L.≅ readV (val zero x)` | 第 0 层的值就是 `read` | Read（验收） |
| `≼→ᴸ` / `≼←ᴸ` | `{v w : V zero} → v ≼ w → readV v ≼ᴸ readV w` / `(v w : V zero) → readV v ≼ᴸ readV w → v ≼ w` | 第 0 层值前序与参照框架的 `≼` 互相蕴涵 | Read（验收） |
| `FGH-read` | `(x : Tr zero) (n : ℕ) → L.FGH (read x) n ≡ FGH x n` | 参照框架的 FGH 与本块的 FGH 逐点相等 | Read（验收） |

#### 4. 设计

**值的读法**
- 每层的值类型 `V ℓ` 只有 zero、suc、lim、`Ω p (Br ℓ p → V ℓ)` 四种构造子，就是去掉 `up` 的 `Tr ℓ`。第 0 层上它与 `Tr zero` 一一对应，经 `readV` 与 `read` 结构互模拟。
- 没有借用 `Level.Ordᶜ`：它的下标是可数的 `Ordᴵ`，放不下以 `Tr k` 为分支的 `Ωₗ`。
- 值前序 `≼` 与 `OCF.Align.Value` 同形：Ω 结点取合法坐标（`LegBr`）上的上确界，两边层号各自独立（跨层）。
- 步进 `Stp` 取 `V` 自己的第一位置序 `◁`，与树的 `◃` 同形，只少 `up` 的两条；不要求值上严格递增。

**`up` 的值**
- `val ℓ (up x c y) = val ℓ x ⊹ valCh ℓ c y`。
- `⊹` 对右边按结构递归，在 Ω 结点上逐分支相加。
- `emb ℓ c` 把孩子层的值抬进本层：槽位沿 `chP` 搬，分支用 `chBr` 换型。

**`up` 的分解（`mapUp`，对孩子 y 的 View 分情形）**
- y 读作零：用 x 自己的 View 经 `reidx` 搬到 `val x ⊹ emb v` 上。
- y 读作后继 y′：部分是 `upz x c y′`。
- y 读作 ℕ 极限 f：部分是 `upz x c (f n)`，步进由 `⊹-mono◁` 与 `emb-mono◁` 得到。
- y 读作 Ω 极限：种类是 `chP ℓ c p`，部分是 `upz x c (g (chBr z))`。
- `upz x c t`：t 是零构造子时取 x，否则取 `up x c t`，所以部分总是合法的。
- 嵌套的 `up`：`view` 在 `up` 行按层号的形状读出孩子（三行，与 `Up` 同），对 y 递归，所以不需要上下文或拉链结构。

#### 5. 第一个障碍

数学上没有障碍。所有定义第一次或改一处就通过了检查器。
- 唯一的编译错误是 `YiViewFGH` 导入 `V` 时没有带上构造子：`zero is not a constructor of the datatype V`，一行修好。
- 工程上的障碍是 `fgh 1` 的求值，见第 1 节表格。

#### 6. 偏离与事故

- **文件**：简报举例 `YiViewDef`、`YiViewInst`；我写成 Val、Inst、Wf、FGH、Read 五个文件，都在 `YiView` 前缀下，只新建，没有改任何已有文件。
- **记录**：记录直接复用 `BrwViewDef`，没有另写等价陈述。
- **改过的设计**：中途把值前序改成跨层，并把签名从 "每层一个" 改为 `Ix = L` 的单一记录，为的是能陈述 `emb-≈`。改后五个文件全部冷编译重验。
- **临时目录试验**（纯 `.agda`）：两次超时（退出码 124），文件留在 `<实验目录>/agents/view/scratch/ViewFGHTry.agda`。
- **中止的编译任务**：一次后台 agda 编译（`fgh-1` 经 `fgh` 别名的那次）用 `TaskStop` 停掉了。沙箱禁用 `ps`，我无法确认那个 agda 进程已经退出。
- **没有做的事**：翻译账不在本路范围（不爬站），没有写。没有提交。
