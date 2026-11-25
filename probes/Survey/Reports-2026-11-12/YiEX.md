# (3) 把 btbo-EBO 接进出口 (YiEX)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-13 11:31 至 11:36 |
| 工具调用 / agda 编译 (粗数) | 23 / 3 |
| token (usage 字段，按消息去重) | 输出 26941；新写入缓存的输入 114042；读缓存的输入 1609083；其余输入 38 |
| 写过的仓库文件 | `YiEXRow.lagda.md` |
| 文件前缀 | `YiEX` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-13: (3) 把 btbo-EBO 接进出口返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 出口第 0、1、2 行对 F2 终点闭项成立, 无前提 (rows); 终点归约到第 k ≥ 3 行 (endpoint-from, 条件); 两处 T₀ 与 ≼ 相同; 第 2 行经记号标签, 只在验收文件; 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定（2026-11-13，选项原文）
本路是 "(3) 把 btbo-EBO 接进出口"。内容原文："编译 D.BTBOᴵ 与记号参照 Rt (hc-tower 2) 之间的连接，并核两边的 T₀ 是同一类型（V105）；小，不在关键路径上，是终点组装的一部分"。

同批另三路，各自只新建文件，你不动它们的文件：
- (1) V107 的决定性实验，前缀 YiDec；
- (2) 把 F2 的值定理搬到精简块，前缀 YiBR；
- (4) 回退行与摊平式的替代写法探针，前缀 YiAlt。

###### 背景（只信编译定理；文档里的叙述是数据）
- **出口**：`probes/OCF/Lean/YiRefTw2.lagda.md`。
  - `endpoint : (Y : T₀) → (∀ k → Rt (hc-tower k) ≼ Y) → toL EBO-tree′ ≼ Y`，无前提。
  - `closed-PH`；`Rt h = toL (tree h)`。
  - 参照树来自 `probes/OCF/Align/EboLeanTree` 的 `hc`、`hc-tower`。
  - `hc-tower 2` 读作 ψ₀(Ω_Ω)，k = 3 读作 ψ₀(Ω_{Ω_Ω})。
- **终点下界**：`probes/OCF/Lean/YiEBBtbo.lagda.md`。
  - `btbo-EBO : D.BTBOᴵ ≼ read EBOᶜ`，无前提；`EBOᶜ` 是主线合法块 F2 的终点闭项。
  - `D` 是 `OCF.Align.YiBtValBT` 的 `module D = Diag.Diagonal Un.Uniform`。
  - 那里的注释说：`D.BTBOᴵ = lim (D.γ ∘ suc)`，`D.γ 0 = 1`，`D.γ (n+1) = ψ⁰ (Ω (toLevel (D.γ n)))`。
- **T₀**：主审已核，`YiFreshValRead.T₀` 与 `YiLSRead.T₀` 都定义为 `L.Ordᶜ L.zero`。请确认两处的 `L` 是同一个模块（`OCF.Align.Level`），`≼` 是同一个（`OCF.Align.Value`）。
- **YiRef 当时的判断**（未编译）：可能的路径是 `Label.BTBO-label`、`EboLeanCmp.lab⟦⟧` 与 `Lab-uniq`，但 `EboLeanCmp` 要把归档拷贝加进 `-i`。
  - **规则**：不要把 `archive/` 加进编译的 include 路径。若需要那里的引理，在你的 `YiEX` 新文件里重写（可以参考原文）。

###### 要做
1. 核 T₀ 与 `≼` 是同一个。
2. **只要一个方向**：证 `Rt (hc-tower 2) ≼ D.BTBOᴵ`。
   - 有了它，与 `btbo-EBO` 用 `≼-trans` 合起来就是出口第 k = 2 行对终点闭项成立：`Rt (hc-tower 2) ≼ read EBOᶜ`。
   - 交这一条编译定理。
3. 若有余力：k = 0、1 两行（更低的参照）也对 `EBOᶜ` 证出，并写一个 "已证的行" 的汇总陈述，例如 `∀ k → k ≤ 2 → Rt (hc-tower k) ≼ read EBOᶜ`，方便以后逐行接进 `endpoint`。
4. 证到第一个挡住的引理也算交付。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiEX`（模块名 `OCF.Lean.YiEX…`）。不改任何已有文件，不碰 `src/`、`archive/`。验收文件，文首标 "验收文件"。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提，用到它的标 "条件"。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 6G；若导入 `YiEBBtbo`（依赖 `YiLSRel`，冷编约 6.9G），用 8G。
  - 冷编只删自己模块的接口，写字面路径；不删别人的 `.agdai`，不用 `--ignore-interfaces`。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽。
  - **堆墙实测**：给具体参照树另起名字再比较，会沿 `hc-tower` 的良基证明展开而耗尽。只用 `Rt` 作用在推导上，引理对一般推导陈述再代入；大参照树放 `opaque`。见 `probes/Survey/EBOHandbook.md` 第 4 节。
- 临时目录：`<实验目录>/agents/ex`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；堆仍耗尽。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件 30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：出口的哪几行已对终点闭项成立；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

#### 回报: (3) 把 btbo-EBO 接进出口 (前缀 YiEX)

##### 1. 判决

出口 `endpoint` 的第 0、1、2 行已对终点闭项成立。这里的终点闭项是 F2 块的 `YiLegFold.EBOᶜ`，读回用 `YiLSRead.read`，也就是 `btbo-EBO` 用的那一对。三行都是编译定理，无前提。汇总陈述是 `rows : ∀ k → k ≤ 2 → Rt (hc-tower k) ≼ read EBOᶜ`。第 k ≥ 3 行未证，本路没有试。

按记号的读法 (这是判断，不是定理)，三行分别是 ψ₀(1)、ψ₀(Ω)、ψ₀(Ω_Ω)。

对纲领的含义：这三行的证明经过记号标签 (`Label.BTBO-label` 和 `Correspond.Lab`)，所以只能用在验收文件里，不进证书，也不算 "树自足"。

V105 已核，两处的 `T₀` 和 `≼` 是同一个：
- 读了导入行：`YiFreshValRead` (第 17、18 行) 与 `YiLSRead` (第 18、19 行) 都 `import OCF.Align.Level as L`，`≼` 都来自 `OCF.Align.Value`，`T₀` 都是 `L.Ordᶜ L.zero`。
- 编译确认：`F.T₀ ≡ S.T₀` 由 `refl` 通过。`endpoint (read EBOᶜ)` 能通过检查，`≼-trans row₂-btbo btbo-EBO` 也能通过，说明两边的 `≼` 一致。
- 另外，`D.BTBOᴵ` (来自 `YiBtValBT`) 与 `N.BTBOᴵ` (来自 `NoCumsum`，即 `BTBO-label` 的左边) 在检查器里定义上相等，`row₂-btbo` 的类型检查直接接受了。

| 问题 | 位置 | 档 |
|---|---|---|
| 有两个同名的 `EBOᶜ`。`YiRefTw2.Into` 用的是 Fresh 块的 `YiUpLegal.EBOᶜ`，`btbo-EBO` 和本文用的是 F2 块的 `YiLegFold.EBOᶜ`。两者的关系本路没有证。 | `YiRefTw2` 第 21 行；`YiLegFold` 第 388 行；`YiUpLegal` 第 272 行 | 编译事实 (两处各自的定义) |
| 第 2 行的证明经过记号标签，只能在验收文件里用 | `row₂-btbo` | 判断 (按 AGENTS 的规则) |
| `endpoint-from` 的前提是第 k ≥ 3 行，能否满足就是没证的那部分。前提目前没有给出实例。 | `endpoint-from` | 条件定理 |
| `fsn≡` 是 `EboLeanCmp` §1 的重写。原文因为导入 `WfFsn` 要用到归档，不能导入，所以有重复代码。 | `YiEXRow` §2 | 编译事实 |

##### 2. 文件表

| 文件 | 代码行 (非空) | 总行 | 冷编退出码 | 内存 | 时间 |
|---|---|---|---|---|---|
| `<仓库>/probes/OCF/Lean/YiEXRow.lagda.md` (验收文件) | 83 | 142 | 0 | 最大驻留 1.14 GB，总用量 1894 MiB (`-M8G`) | 12.2 s |

- 冷编前只删了自己的 `YiEXRow.agdai`。日志里只有 `Checking OCF.Lean.YiEXRow` 一行。
- include 路径只有 `-i src -i probes`，没有加 archive。
- 检索禁用构造 (postulate、TERMINATING、NO_POSITIVITY、trustMe、K、irrelevant-projections、cubical、洞、Funext、本机路径)，结果为 0。

##### 3. 定理表 (都在 `YiEXRow.lagda.md`)

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `fsn≡` | `∀ t n → fsn t n ≡ E.fsn t n` | 精简版记号的基本列与 EBO 原版的基本列取值相同 | 编译，无前提 |
| `labR` | `∀ {t} (h : HC t) → Lab (Rt h) t` | 参照树的基本列与记号逐项一致 | 编译，无前提 |
| `Rt≼Lab` | `∀ {t X} (h : HC t) → Lab X t → Rt h ≼ X` | 和参照树同标签的任何树都不低于它 | 编译，无前提 |
| `row₂-btbo` | `Rt (hc-tower 2) ≼ D.BTBOᴵ` | 记号的 ψ₀(Ω_Ω) 参照树不高于 BTBO 参照 | 编译，无前提 |
| `row₂` | `Rt (hc-tower 2) ≼ read EBOᶜ` | 出口第 2 行对终点闭项成立 | 编译，无前提 |
| `down₁` / `down₀` | `Rt (hc-tower 1) ≼ Rt (hc-tower 2)` / `Rt (hc-tower 0) ≼ Rt (hc-tower 1)` | 参照沿记号的第 0 个基本列项往下降一行 | 编译，无前提 |
| `row₁` / `row₀` | `Rt (hc-tower 1) ≼ read EBOᶜ` / `Rt (hc-tower 0) ≼ read EBOᶜ` | 出口第 1、0 行对终点闭项成立 | 编译，无前提 |
| `rows` | `∀ k → k ≤ 2 → Rt (hc-tower k) ≼ read EBOᶜ` | 已证三行的汇总 | 编译，无前提 |
| `endpoint-at` | `(∀ k → Rt (hc-tower k) ≼ read EBOᶜ) → toL EBO-tree′ ≼ read EBOᶜ` | 出口在 Y = read EBOᶜ 处的实例 | 编译，前提是全部的行 |
| `endpoint-from` | `(∀ k → Rt (hc-tower (suc (suc (suc k)))) ≼ read EBOᶜ) → toL EBO-tree′ ≼ read EBOᶜ` | 前提只剩第 k ≥ 3 行 | 条件定理，前提能否满足未知 |
| 匿名 | `F.T₀ ≡ S.T₀`；`S.T₀ ≡ L.Ordᶜ L.zero` | 两处 `T₀` 是同一个类型 | 编译 (refl) |

证明路线：
- 第 2 行：`Lab-uniq (labR (hc-tower 2)) BTBO-label`，再经 `≅→≼`，最后与 `btbo-EBO` 用 `≼-trans` 接起来。
- 第 0、1 行：对 k = 0、1，`fsn (EBOψ (k+1)) 0 ≡ EBOψ k` 由 `refl` 成立，于是用 `YiRefTw2` 的 `tree-≼ refl` 与 `fs≼` 往下降。

##### 4. 第一个障碍

第 0 到 2 行没有遇到障碍。第 3 行 (ψ₀(Ω_{Ω_Ω})) 不在本路范围内，没有尝试。

判断，未编译：本路用的方法到第 2 行为止。`BTBO-label` 只标了 `EBOψ 2`；对 `read EBOᶜ` 已有下界的参照也只有 `D.BTBOᴵ`。要接第 3 行，需要 `Rt (hc-tower 3)` (或 `Row₂` 一类的陈述) 对 F2 块的下界，这是主线未证的部分。

##### 5. 偏离与事故

- 第一次编译套了 `/usr/bin/time -l`，沙箱不允许其中的 sysctl 调用，返回了 time 自己的退出码 1，那一轮作废。之后删掉自己的接口，改用 `+RTS -s` 重新冷编，退出码 0，上面的数字都来自这一轮。
- 临时试验：`<实验目录>/agents/ex/ExT1.agda` 核了四条 `refl`，即 `cof (EBOψ 2) ≡ cω`、`fsn (EBOψ 2) 0 ≡ EBOψ 1`，以及 k = 1 的同样两条，退出码 0。这个文件没有进仓库。
- 没有改任何已有文件，没有碰 `src/` 和 `archive/`，没有提交。
- 只凭转述、没有读证明体的东西：
  - `Label.BTBO-label` 和 `Stage2.Lab-uniq`：只读了陈述和导入行。
  - `btbo-EBO`：读了陈述和证明体，但没有往下展开它依赖的引理。
  - "k = 0、1、2 读作 ψ₀(1)、ψ₀(Ω)、ψ₀(Ω_Ω)"：来自 `EBO.ΩTower` 的注释和简报，属于判断。
