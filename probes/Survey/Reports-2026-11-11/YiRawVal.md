# 新折叠的值下界 (YiRawVal)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-11 05:21 至 05:38 |
| 工具调用 / agda 编译 (粗数) | 37 / 9 |
| token (usage 字段，按消息去重) | 输出 106479；新写入缓存的输入 272630；读缓存的输入 5905860；其余输入 66 |
| 写过的仓库文件 | `YiRawVal2.lagda.md`, `YiRawVal3.lagda.md`, `YiRawVal3Base.lagda.md`, `YiRawValBase.lagda.md`, `YiRawValTw3.lagda.md` |
| 文件前缀 | `YiRawVal` (在 `probes/OCF/Align/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 新折叠的值下界一路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 新折叠的闭项 n ≤ 3 的下界是定理；塔的第 3 项的闭项不低于参照的 ψ₀(Ω₃)；没有发现掉值；五件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库> = <仓库>) 的一路执行方, 任务是 "给写在第 K 层的树上的新折叠接值的下界定理". 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

### 0 先读什么

1. `AGENTS.md` 全篇. 特别是: "用记号验收强度" 与 "中间站给界, 终点对 EBO 验收" (序数值验收; 中间站给下界即可); Agda 一节 (选项, 文字预算, 退出码, 堆; Funext 只准作前提); "结论的写法".
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 (编译与内存, 堆墙的对策) 与 §5.4. `probes/Survey/Reports-2026-11-11/README.md` 的 §2; 再读同目录 `YiLvVal.md` 的回报原文 (上一轮值下界一路怎么做的, 卡在哪).
3. 代码 (都在 `probes/OCF/Align/`, 模块名 `OCF.Align.<名>`; 都已定稿, 可以导入, 不许编辑):
   - **范例, 先读懂**: `YiLvValBase` (`⟨_⟩`, `Ψ`, `γ`, `reference-row`, 记录 `Interface`, `FromInterface.theorem`, `interface₀`, `lower₀`, `lower₁`, `read-plus`, `suc-lower`, `one≼fold`), `YiLvVal2` (逐点前序 `_⊴_`, `interface₁`, `lower₂`), `YiLvVal3Base`, `YiLvVal3` (`_⊴₂_`, `interface₂`, `lower₃`; 编译它要 6G), `YiLvValFin`. 它们验收的是**上一轮写在 `LF` 上的折叠**的闭项 `YiLvFoldFin.foldᶠ n`: n ≤ 3 时参照的 ψ₀(Ω_n) ≼ 读回的 `foldᶠ n`.
   - **被验收的对象 (本任务)**: 写在 `Raw K` 上的新折叠. `YiRawFoldBase` (`Ext`, `psum`), `YiRawFold` (`Ψ`, `Φᵐ`, `Φ`, `own`, `ownT`, 各行都是 `refl`: `zero-row`, `suc-row`, `lim-row`, `em-rowˢ`, `top-rowˢ`, `top-as-node`, `keep-row`, `fold-row`, `next-additive`), `YiRawFoldInst` (`closed K pl L = Φ K pl L base top`, `closedᵐ`, `closed-row`, `closed-feedback`, `fin-zero : closed (fin 0) tt tt ≡ foldᶠ 0`), `YiRawFoldTw3` (`T₃ᵐ`, `T₃ᵐ-term`, `T₃ᵐ-feedback`, `T₃ᵐ-term₀`).
   - 旧折叠 (对照): `YiLvFold` (模块 `Fold`), `YiLvFoldFin` (`foldᶠ`, `wayᵇ`, `complete-fin`), `YiLvFoldAdd` (`plus`, `copies`, `successor`), `YiLvFoldBase` (`nodeAt`, `Chain`).
   - 参照一侧: `OCF.Align.Level`, `OCF.Align.Value` (`≼`), `YiIrrFoldValue` (`read`).
   查签名用检索, 大文件不要整篇读.

### 1 这一步是什么, 为什么要做

乙线上一轮把折叠改写在 `Raw K` 上, 塔的第 3 项有了合法闭项 `T₃ᵐ` (读法 ψ₀(Ω_Ω)), 派发处处完全. 但编译事实是: 闭项合法不携带强度信息; 新折叠目前**没有任何值定理**. 已有的值下界 (n ≤ 3) 验收的是旧折叠 `foldᶠ`. 新旧两个折叠在有限层号上的关系只有 n = 0 字面相等; 其余没有比 (逐字相等要函数外延).

本任务: 让新折叠有值的下界定理. 只要下界 (参照 ≼ 读回的闭项), 不要上界, 不要同值.

### 2 目标, 分步; 每步先交再往下

1. **n = 1.** `L.ψ⁰ (L.Ω ⟨ 1 ⟩) ≼ read (closed (fin 1) _ _)` (`closedᵐ` 的版本若相同或更容易, 一并交). 最便宜, 先做.
2. **n = 2, 3.** 同样的陈述. 两条路任选其一, 选便宜的:
   - (i) 直接验收: 把 `YiLvVal*` 的办法 (每层一个接口, 链点之间的关系) 搬到新折叠的行上. 有限层号上没有极限, 所以部分和一行不出现; 新折叠的结点行经 `ΨN`, `Ψn` 归约到与旧折叠相同的 `nodeAt`, `Chain`.
   - (ii) 过桥: 证 `read (foldᶠ n) ≼ read (closed (fin n) _ _)` (值上的比较, 不是字面相等; 两边同构造子逐项比), 再接 `lower₂`, `lower₃`. 若这座桥能对一切 n 证出, 它本身就是重要结果: 以后旧折叠的一切值定理都自动搬到新折叠.
3. **`T₃ᵐ`.** 由 `T₃ᵐ-term₀` (第 0 项是 `Φᵐ (suc zero) tt tt base top`) 得 `T₃ᵐ` 不低于 ψ₀(Ω₁) 的参照. 再往上: 对 n = 2, 3, 证参照的 ψ₀(Ω_n) ≼ `read T₃ᵐ` (办法: 链的第 1 点之后的坐标已经很大, 找出有限层号的闭项到某一项的第一位置或值上的 `≼`; `YiRawFoldUp.Φᵐ-below` 只对极限处取第 0 支的路径成立, 注意). 做不到就交到哪一步算哪一步, 写明缺的引理的类型.

部分进展也算: 做到第 2 步就已经是可以汇报的结果.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要 Funext 或 K 才能证 (可交显式前提的条件定理, 另给不带它的最强结果); 堆到 6G 仍耗尽 (先按手册 §4.2 的对策: 陈述逐字写, 大参照树放 `opaque`, 隐式参数显式写出; 文件拆小). 约化: 把缺的引理写成带确切类型的模块参数, 其余条件地证出来并编译.

不要为了让值定理好证而改折叠: 被验收的对象就是 `YiRawFoldInst.closed`, `closedᵐ` 与 `YiRawFoldTw3.T₃ᵐ`. 发现它的值低于读法, 那是重要结果: 写成编译过的定理交回, 不要自己修.

注意: 同时有别的路在研究新折叠里极限层号处的部分和一行能否换掉. 你的定理若依赖那一行 (第 3 步可能碰到), 在回报里指明是哪一条依赖它.

### 3 规则

- **只新建文件**, 前缀 `YiRawVal`, 放 `probes/OCF/Align/`, 中文 literate Agda (`.lagda.md`). 都是验收文件, 文首标 "验收文件"; 允许导入带记号闭包的 `Value` 与旧验收文件. 不改任何已有文件 (含 README, LOG, RESULTS, AGENTS), 不碰 `src/`, `archive/`. 同时在跑的另四路用前缀 `YiOmFold`, `YiOmNeg`, `YiPsum`, `YiLvAll`, 不要动它们的文件, 也不要依赖它们.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. Funext 只准作显式前提, 用到它的定理在文首标 "条件".
- **文字预算** (AGENTS Agda 一节): 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件. 一次性的试验放你的临时目录, 用纯 `.agda`.
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Align/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Align/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块.
- 你的临时目录: `<实验目录>/agents/rawval`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几步, 一段话说对纲领与目标意味着什么 (新折叠的哪些读法变成了定理).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断).
4. 办法: 走的是直接验收还是过桥; 哪些引理是从范例原样搬的, 哪些是新的; 哪些定理依赖部分和一行.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
强度写 ψ₀(Ω_x), 标明是定理还是读法; 下界不写成同值; 不用 "只差", "自然" 一类形容.

## 回报原文

#### 1 判决

我做完了第 1、2、3 步，走的是直接验收，没有过桥。

- **有限层号。** 对 n = 0, 1, 2, 3，"新折叠的 `closed (fin n)` 与 `closedᵐ (fin n)` 不低于参照的 ψ₀(Ω_n)" 现在是编译定理。这是下界，不是同值。
- **`T₃ᵐ`。** "不低于 ψ₀(Ω₁)、ψ₀(Ω₂)、ψ₀(Ω₃)" 是编译定理。它的读法 ψ₀(Ω_Ω) 仍然只是读法：目前的定理只到 ψ₀(Ω₃) 这一档下界。

对纲领的意义：
- 新文件都是验收文件，没有改折叠，被验收的就是 `YiRawFoldInst.closed`、`closedᵐ` 和 `YiRawFoldTw3.T₃ᵐ`。
- 没有发现新折叠在哪一步比读法掉值。
- 新折叠在上述各点第一次有了值定理，不再只有 "合法" 一条。
- 新折叠与旧折叠 `foldᶠ` 之间仍然没有值上的比较，桥没有做，见第 4 节。

#### 2 文件表

都在 `probes/OCF/Align/`。每个文件只删自己的 `.agdai`，按依赖顺序冷编译，每份日志里只有本模块一行 `Checking`。

| 文件 | 代码行 / 总行 | 退出码 | 常驻内存峰值 (`-M6G`)，用时 |
|---|---|---|---|
| `YiRawValBase.lagda.md` | 114 / 162 | 0 | 1.25G，6s |
| `YiRawVal2.lagda.md` | 167 / 218 | 0 | 1.31G，7s |
| `YiRawVal3Base.lagda.md` | 136 / 163 | 0 | 1.54G，8s |
| `YiRawVal3.lagda.md` | 274 / 334 | 0 | 1.86G，10s |
| `YiRawValTw3.lagda.md` | 20 / 40 | 0 | 1.44G，7s |

检索 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`--irrelevant-projections`、`--cubical`、本机路径，都是 0 处。Funext 唯一的命中是 Base 文首的 "没有 Funext"。五个文件的选项行都是 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。

#### 3 定理表

记号：`⟨ n ⟩ = L.natᴵ n`，`Ψ M` 是参照一侧目标层 M 的折叠，两者都取自 `YiLvValBase`。`N.Ψ` 是 `YiRawFold.Ψ`。

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `lower₀` / `lower₀ᵐ` | `L.ψ⁰ (L.Ω ⟨ 0 ⟩) ≼ read (closed (fin 0) tt tt)` (ᵐ 版换成 `closedᵐ`) | 不低于 ψ₀(Ω₀) | Base | 编译定理 |
| `lower₁` / `lower₁ᵐ` | `L.ψ⁰ (L.Ω ⟨ 1 ⟩) ≼ read (closed (fin 1) tt tt)` (ᵐ 版换成 `closedᵐ`) | 不低于 ψ₀(Ω₁) | Base | 编译定理 |
| `lower₂` / `lower₂ᵐ` | `L.ψ⁰ (L.Ω ⟨ 2 ⟩) ≼ read (closed (fin 2) tt tt)` (ᵐ 版同) | 不低于 ψ₀(Ω₂) | Val2 | 编译定理 |
| `lower₃` / `lower₃ᵐ` | `L.ψ⁰ (L.Ω ⟨ 3 ⟩) ≼ read (closed (fin 3) tt tt)` (ᵐ 版同) | 不低于 ψ₀(Ω₃) | Val3 | 编译定理 |
| `T₃ᵐ-Ω₁` | `L.ψ⁰ (L.Ω ⟨ 1 ⟩) ≼ read T₃ᵐ` | 第 0 项就是 `closedᵐ (fin 1)` | Tw3 | 编译定理 |
| `T₃ᵐ-Ω₂` | `L.ψ⁰ (L.Ω ⟨ 2 ⟩) ≼ read T₃ᵐ` | 走第 1 项、第 0 支、第 0 支 | Tw3 | 编译定理 |
| `T₃ᵐ-Ω₃` | `L.ψ⁰ (L.Ω ⟨ 3 ⟩) ≼ read T₃ᵐ` | 走第 1 项、第 0 支、部分和第 1 项 | Tw3 | 编译定理 |
| `FromInterface.theorem` / `theoremᵐ` | `L.ψ⁰ (L.Ω ⟨ suc M ⟩) ≼ read (closed (fin (suc M)) (fin-plain (suc M)) (fin-legal (suc M)))` (ᵐ 版同)；模块参数 `(M : ℕ) (I : Interface M)` | 第 M 层有接口，则 fin (M+1) 有下界 | Base | 条件定理 |
| `interface₀/₁/₂` | `Interface 0`、`Interface 1`、`Interface 2` | 条件定理的前提在 M ≤ 2 时成立 | Base / Val2 / Val3 | 编译构造 |
| `one≼` | `∀ k pl Lg (x : Ext B.zero k) ξ .l .nb → V.𝟏 ≼ read (N.Ψ B.zero k pl Lg x ξ l nb)` | 目标层 0 的输出不低于 1，对一切层号 | Base | 编译定理 |
| `X₁-keeps`、`X₂-keeps₁/₀/₀′`、`Y₁-folds`、`Y₁-keeps`、`Y₁-in` | 如 `wayOf Y₁ (inj₁ tt) ≡ fold`、`inS Y₁ ≡ X₁` (都是 `refl`) | 字面层号上的派发结果 | Val2 / Val3Base / Val3 | 有限测试 |

`Interface M` 与 `YiLvValBase.Interface` 同四个字段，折叠换成新的：
- `step` 的被验收一侧是 `N.Ψ (fin M) (fin M) (fin-plain M) (fin-legal M) (N.ownT (fin M) …) η l nb`。
- `lower` 对目标第 0 层的一切外部派发 `y : Ext B.zero (fin M)` 写。

#### 4 办法

我走的是直接验收，没有做第 (ii) 条的桥，原因是逐层搬接口更便宜。

**原样导入、没有重证的：**
- 逐点前序 `_⊴_`、`_⊴₂_`。
- 一切加法、前缀、搬运引理：`⊴-+ˡ`、`⊴₂-+ˡ`、`suc-step(₂)`、`TR₁`、`tr⁻≼`、`Ω⊴top`、`Ω₂⊴top`。
- `δ₁`、`δ₁-self`、`lᵢ≅⁻`、`up≅⁻`、`plus≽`、`suc-lower`、`Ψ₀≼ψ⁰`。

这些都与折叠无关。

**改写在新折叠行上的：** `Ω⊴Φ(₀)`、`Ψ₀⊴Φ(₀)`、`Ψ₁⊴Φ`、`fold-lower`、`Ω₂⊴ψ₂*`、`B₀/B₁/B₂`、`Ω₁⊴ψ₁`、`C₀/C₁/C₂`、`D`。证明逐子句与范例同形，有两处变化：
- `Dom` 与 `up` 的定义域参数换成无关的 `l`、`nb`，分支的证据取 `proj₂ (proj₂ (proj₂ (proj₂ l)))` 等。
- 链用 `Chain` 模块和结点数据记录直接写：`NodeChain`、`NodeChain0`、`Chain1`、`fold1⊴`、`fold1≼`。

**新的引理：**
- `Ψn-first`、`ΨN-first`、`one≼`、`fold₀`：目标第 0 层上 `Way zero _` 没有保留 (`keep ()`)，所以对一切外部派发都走链行。
- 新折叠的链里推进用 `gk`，由 `own` 派发；观察用 `gm`，由 `low` 或别的派发。两者值相同，但不是定义性相等。所以结点处的两条下界分开给，`Interface.lower` 也对一切外部派发写。
- 派发的字面事实 (有限测试)：
  - `Y₁ = own 2 (inj₁ tt)` 在目标层 1 上折叠层号 1 的结点，保留层号 0 的结点。
  - `inS Y₁ ≡ X₁ = ownT 1`，所以进孩子以后就是 `YiRawVal2` 的那一套。
  - `X₂ = ownT 2` 在规范槽位上全部保留，与旧的 `wayᵇ` 同。

**`T₃ᵐ` 的证明 (`T₃ᵐ-Ω₃ = ≼l 1 (≼l 0 (≼l 1 (plus≽ … lower₃ᵐ)))`)：**
- 第 1 项的层号是 `read0 (1 + closedᵐ (fin 1))`。
- 它第 0 支的第 0、1 支字面是 `fin 2`、`fin 3`。这一点由检查器的定义性比较接受，没有单独写成 `refl` 行。
- 那两支的 `Plain`、`Legal` 是 `⊤` 的元素，靠 eta 化成 `tt`，外部派发是全折叠。所以那两支就是 `closedᵐ (fin 2) tt tt`、`closedᵐ (fin 3) tt tt`。

**依赖部分和一行的定理：**
- `T₃ᵐ-Ω₂`、`T₃ᵐ-Ω₃` 依赖它：两次经过 `Φᵐ-lim-row`，用到 `psum` 的第 0 项是第 0 支、第 1 项是 `plus` 第 0 支加第 1 支。
- 判断：若这一行换成各支的极限，只需把 `plus≽` 那一步去掉。
- `one≼` 的 `(lim f) (mix w) top` 子句也读这一行，但有限层号的定理都不经过这个子句。
- `T₃ᵐ-Ω₁` 与全部 `closed`/`closedᵐ (fin n)` 的定理都不依赖它：有限层号上没有这一行。

#### 5 第一个障碍

在已交的范围内没有碰到停下的条件，没有检查器报错需要报告。下一步缺的引理：

- **一切有限 n。** 缺 `∀ M → Interface M` (类型是 `YiRawValBase.Interface`)。
  - 判断，未测：会遇到上一路 (c) 同类的问题，即变量层号上 `wayOf (N.ownT (fin M) …) r` 不化简。新派发是对位置的 `ccompare`，要另写化简引理。
  - 有了它，`FromInterface` 立刻给出全部 n。
- **`T₃ᵐ` 往上。**
  - 缺上面那条，以及第 1 项第 0 支的第 n 支等于 `closedᵐ (fin (n+2))` 的命题等式 (对变量 n 要搬运层号)。
  - 合起来可以得到不低于 ψ₀(Ω_ω)。这仍远低于读法 ψ₀(Ω_Ω)。
  - 要更高的下界，还缺极限层号以上 `closedᵐ` 的值定理。这会用到部分和一行。

#### 6 偏离与事故

- **简报没要求的：** `closedᵐ` 版本 (每个 n 都交了)，以及 n = 0。
- **临时探针：** 我写了一个纯 `.agda` 的探针 `<实验目录>/agents/rawval/t/RawTest.agda`，核对派发化简，不进仓库。
- **编译：** 编译中途有两次退出 42，都是我自己的类型错误，改后通过。一次是记录字段的隐式参数顺序，一次是一个用不到的定义 `Own₁` 的类型写错。
- **内存：** 五个文件的内存峰值都在 2G 以下 (测到的)。旧的 `YiLvVal3` 要 6.59G；我判断原因是这里没有 `Dom`、`up` 的计算，但没有专门测过。
- **没动的：** 没改任何已有文件，没碰 `src/`、`archive/`，不依赖 `YiOmFold`、`YiOmNeg`、`YiPsum`、`YiLvAll`，没有提交。
