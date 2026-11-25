# B5D：W4 的 BTBO 下界（Opus 5.5）：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-18 02:11 至 02:53 |
| 工具调用 / agda 编译 (粗数) | 68 / 1 |
| token (usage 字段，按消息去重) | 输出 232042；新写入缓存的输入 452199；读缓存的输入 18489621；其余输入 134 |
| 写过的仓库文件 | 无 |
| 文件前缀 | `WV` (在 `probes/OCF/Lean/`) |
| 主审复核后的一句结论 | 未拿到 BTBO 下界，按止损暂停（无否定）：编译无前提的下界只有 twᶜ 1 ≽ BTBO 基本列第 1 项 ω 与 ψ₀(Ω₁)（经 src 等价），twᶜ 1 ≽ Level 参照 ψ⁰ X*（读作 ψ₀(Ω₁²)，判断），W4 的 ψ₀(Ω₂) 闭项 ≽ ψ⁰(Ω₁·ω)（读法）；卡在 E 的 ex 行进入第二阶（It）；W4 的 LOWER 必须包含 E、It 对一切阶的值定理（旧 YiLSFold 是为无 ex 的折叠写的）；四个文件主审删接口 6G 冷编退出 0，附件 attachments/B5D-* |

## 简报原文

请严格按下面这份简报工作（简报全文，自足）。

### B5D：给新折叠 W4 重证 BTBO 下界（Opus 5.5）

目录 <实验目录>/math/B5D/，模块前缀 `WV`。

#### 背景

- 路线：作者定 "改定义 + 第 4 层经典数学"。构造性新折叠 W4（实验目录，`W4Fold`）已有塔的闭项 `twᶜ n` 与终点 `EBOᶜ : Tr zero`（Λ 上），但还没有任何值下界，旧定义上的 BTBO 下界不能当作 W4 的证据。外部审计 `probes/Survey/LEMAudit-2026-11-18.md` §3 方案 D 就是本路：给 W4 一个可报告的值基线。
- 旧定义上的 BTBO 下界可以参考：
  - `probes/OCF/Lean/YiSHAccept.lagda.md`：`btbo-low` 由 `BTBOFull.BTBO≈` 与 `YiMTValue.btbo-EBOᶻ` 复合而成；
  - `probes/OCF/Lean/YiMTValue.lagda.md`：`btbo-twᶻ`，塔每一项不低于 BTBO；
  - `probes/OCF/Lean/YiUpValTw1.lagda.md`：`bho-tw1`；
  - BTBO 的值与零层读回见 `src/OCF/BTBO.lagda.md`、`probes/OCF/Align/BTBOValBase`（`tr₀`）。
  先读这些的陈述与证明结构，选对 W4 最短的一条。
- W4 的结构：
  - 第 0 层禁挂起乘幂 `ex`，所以 `Tr zero` 是纯布劳威尔树；
  - 层号读回用带序结果代数上的迭代子；
  - 值在 `W4Val`；内部 View 在 `W4View`。
  - 设计与行律见 `probes/Survey/Reports-2026-11-16/B4W4.md`、`DefD1.md`、`RedefS2.md`。

#### 任务

1. 先选旧证明里一个非零的闭近似项（例如塔第 1 项或 BTBO 基本列的第 1、2 项），在 W4 的具体 `ψ₀` 上重证它的下界，并列出它经过 W4 的哪些行（`ex`、`E`、`It`、`upC`、自身行、回退行）。
2. 再推广到 BTBO 全量：目标 `BTBO 的零层树 ≼ EBOᶜ`（或 `≼ twᶜ n` 的上确界），值关系用旧证明同一种，以便与 `btbo-low` 对照。
3. 不改 W4 的定义。若发现非改不可，停下，写明理由与最小改动（AGENTS "第 4 层不反过来改前 3 层"）。

交付：BTBO 下界（编译）或停在第几项、卡在哪一行。

#### 公共约束（两路相同）

- 先读仓库 `<仓库>` 的 `AGENTS.md`（必须遵守）、`probes/Survey/EBOHandbook.md` §4（堆墙）与 §5。只信编译证据。
- 新折叠 W4 只在实验目录里：`<实验目录>/cl/W4/`（W4Block、W4Ops、W4Path、W4Fold、W4Val、W4View、W4Check、W4Contrast，纯 `.agda`）。W4Check 导入 S1Sharp，在 `<实验目录>/math/S1/`。只读，不改。
- 编译：仓库根目录，`agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes -i <实验目录>/cl/W4 -i <实验目录>/math/S1 -i <你的目录> <文件>`。每次只跑一个 agda；6G，单个大文件可以 8G。退出码不经管道：0 通过，42 类型错误（先看日志首行，`LibraryError` 是库文件问题），251 堆耗尽，124 超时。日志落你自己目录里的文件，只看首个错误附近。
- 选项行：`{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns #-}`。无 postulate、洞、编译指示，不开 K。排中律与函数外延只能作模块参数，结论标 "条件"。
- 只在你自己的目录里写，新模块名用你的前缀。不改仓库与 W4、S1 的任何文件；不 `rm` 别人的文件，不删别人的 `.agdai`，不 `pkill`，不写 `/tmp`，不装包，不提交。
- 止损：新代码约 1200 行以内；第一种写法不通可换一种再试；两种都不通就停，交回卡住的精确陈述与机制。
- 回报（你的最终消息就是回报原文，会逐字留档）：先说对纲领与目标意味着什么；再列新文件、关键定理的签名与档位（编译定理 / 条件定理 / 有限测试 / 纸面 / 判断）；最后说下一个必经缺口、位置与剩余距离，以及没读、只凭转述的东西。强度写 ψ₀(Ω_x)，x 用 Ω 的算术。不用 "决定性" 一类的说法，不用比喻。

## 回报原文

#### B5D 回报：W4 的 BTBO 下界（Opus 5.5）

##### 0. 结论与对纲领、目标的意义
- **结果：** 停在 BTBO 基本列第 2 项（BO = ψ₀(Ω_ω)）之前，没有拿到 BTBO 下界。
  - 第 1 项（ω）已在 `twᶜ 1` 上证出。
  - 第 2 项之下有三个近似项已在 W4 的具体 ψ₀ 上证出下界，都是编译定理，无前提。
  - 卡在 W4Fold 的 It 行（ex 行进入第二阶）。另外，要把一切有限层号与一切链点证完，需要一条对层号一致的 LOWER（定义见第 2 节）。
- **对纲领：**
  - 没有改 W4 的定义，没有发现非改不可的地方（第 4 层不反过来改前 3 层）。
  - 新文件全在实验目录。验收文件读 Level 参照、src 的 BTBO 和 `BTBOValMain`，属于第 4 层。
  - 没有用排中律或函数外延。没有 postulate、洞、编译指示，选项行照简报。
- **对目标（W4 的值基线）：**
  - 可报告的基线是 `twᶜ 1` ≽ Level 参照 ψ⁰ X*。X* 的值是 Ω₁·Ω₁，把这个界读作 ψ₀(Ω₁²) 是判断，不是定理。
  - W4 的 ψ₀(Ω₂) 闭项 ≽ ψ⁰(Ω₁·ω)。
  - 这两个界都远低于 BTBO = ψ₀(Ω_Ω)。
- **用到的值关系：** 与 `btbo-low` 同一种，即 `OCF.Align.Value._≼_`，作用在 `Ordᶜ zero` 上。W4 的读回 `read : Tr zero → Ordᶜ zero` 逐构造子对应；W4 第 0 层是纯布劳威尔树。

##### 1. 新文件、定理与档位
目录：`<实验目录>/math/B5D/`

| 文件 | 行数 |
|---|---|
| `WVOne.agda` | 226 |
| `WVTwo.agda` | 147 |
| `WVThree.agda` | 248 |
| `WVFour.agda` | 103 |

- 合计 724 行。
- 编译：删掉自己四个模块的 `.agdai` 后，从仓库根以 6G 堆冷编入口 `WVFour`，退出码 0，四个模块都重新检查过，用时约 33 秒。沙盒拿不到内存峰值。
- 编译脚本 `run.sh`，日志 `cold.log`，都在同一目录。

**WVOne：第 1 项与 ψ₀(Ω₁)**【编译定理，无前提】
- `btbo₁ : tr₀ (S.ψⁿ 1) ≼ read (twᶜ 1)`：BTBO 基本列第 1 项 ω。经 `BTBOValMain.ω≈` 得到。
- `tw1-ω : LV.ψ⁰ (LV.Ω LV.zero) ≼ read (twᶜ 1)`
- `tw1-ψΩ₁ : LV.ψ⁰ (LV.Ω (LV.suc LV.zero)) ≼ read (twᶜ 1)`
- `srcΩ₁ : tr₀ (S.ψ₀ (S.Ω (B.suc B.zero))) ≼ read (twᶜ 1)`：经 `ψ₀≈` 得到。
- 通用的一步 `L1g.low`：
  - 内容：以任意底 β、任意底族，在第 1 层把 Ω 树折到第 0 层。链底取底族在 `inc tt self` 上的分量；路径是 `inu` 或 `inc tt` 两种形状。
  - 前提：参照一侧只要给出满足 b·ω^y 型上界的链 H 与各项 Q。
  - 结论：`lim Q ≼ read` 折叠值。
- 辅助：`Mv`（参照一侧第 0 层的 b·ω^y，及其单调与膨胀），`P-read`（W4 第 0 层的折叠不低于 β·ω^x）。
- 经过的行：
  - 第 0 层的 suc/lim 行（`next⁺`）。
  - `tw 1` 的 Ω 行：kp 给 nothing，走链，链步是 ink 行。
  - sΩ、sL、sS 的 up 行（inu），sS 的 inc 行，limc⁺ 的累加。
  - 不经过 ex、E、It、upC、自身行。

**WVTwo：经 ex 行的第一个项**【编译定理，无前提】
- `Ψ₂-Ω₁ω : LV.ψ⁰ (LV.lim Tᴸ) ≼ read Ψ₂`
  - `Ψ₂ = proj₁ (ψ₀ lvl2 ok₂ (proj₁ (Ωt lvl2)))`，即 W4 的 ψ₀(Ω₂) 闭项。
  - `Tᴸ n` 是左结合的 Ω₁·(n+1)。把界读作 ψ₀(Ω₁·ω) 是判断。
- 形状测试（refl）：链点 1 是 `ex Ω₁ Ω₁ _ (suc zero) tt`，由第 1 层自身行给出。
- `EX.Ω₁ω` 对任意 `o`、`B` 成立，只要求链底不小于 1。
- 关键不变式 `EX.inv`：E 的 suc 行迭代 "折 Ω₁" 时，底 `itV` 与状态 `itS` 在链目标上的分量同步增长。
  - 底不低于 ψ⁰(Tᴸ n)。
  - 状态在链目标上的分量不低于 ψ_0(Tᴸ n)。
- 经过的行：第 2 层 Ω 行，inc 行加第 1 层自身行，inu 行，第 1 层 suc 行，ex 行（E，`opB`），E 的 suc 行与 zero 行，第 1 层 Ω 行（以状态为链底）。

**WVThree：E 的 Ω 行与 up 行（第一阶，孩子语境）**【编译定理，无前提】
- 第 0 层的影子算术 `Ξ y v c`：以（底，链底）同步迭代 "折 Ω₁" ω^y 次。已证三条：
  - 对底与链底单调：`Ξ-mono`。
  - 对指数按 ≼ 单调：`Ξ-monoʸ`。
  - 膨胀：`Ξ-infl`。
- Level 一侧 `Aᴸ`：`ψ⁰ (A T y) ≼ Ξ y (ψ⁰ T) (ψ_0 T)`，ψ_0 一侧同理。
- W4 一侧 `EW.Ew`：
  - 陈述：`Ξ (read y) (read v) (read 链底) ≼ read (E o T′ y F′ S′ zero (σ′ x) v)`。
  - 语境是 `cons (down stop tt) nil`。
  - 覆盖的部分：`chTD`、`chMT`、`enterO`、孩子语境里的 `itS`。
- `XS.low* : LV.ψ⁰ X* ≼ read (proj₁ (ψ lvl1 o B zero w₀ β xs))`
  - `xs = ex Ω₁ Ω₁ _ Ω₁ tt`，`X* = limᵢ (y ↦ A Ω₁ (y+1))`。
  - 对任意 `o`、`B`、β 成立，只要求底与链底都不小于 1。
- 经过的行：ex 行；E 的 Ω 行（kpT 给 nothing，链目标是 `inc tt self`，链底是状态）；E 的 up 行；孩子语境里 E 的 suc 行与 zero 行。

**WVFour：落到塔第 1 项**【编译定理，无前提；含一条 refl 形状测试】
- `tw1-X* : LV.ψ⁰ X* ≼ read (twᶜ 1)`
- `b*-shape : proj₁ bs ≡ XS.xs …`（refl）：在 `twᶜ 1` 的 G(z₁)（层号 ω）的第 1 个累加项（层号 2，累加底 β₁，底族 B*）里，链底 b* 字面上就是 `ex Ω₁ Ω₁ Ω₁`。它由 sL 层号的 inc 行在 m<n 一支（`cW (way …)`，`emb`）加第 1 层自身行给出。
- 链点 1 是 `ex b* b* (suc 0)`。它的折叠经 E（`Einf`）不低于以 β₁ 为底折 b* 的值，后者由 `XS.low*` 给出下界。

**哪些行没有经过：**
- It、Kb、Itᴺ、Kₑ、upC 都没有经过。
- sΩ 的 inc 回退行只以 x = zero 的形式出现（第 1 子句直接返回底），没有真正走过。

##### 2. 下一个必经缺口、位置与剩余距离
- **位置：**
  - `twᶜ 1` 是各 G(z_n) 的累加。在 n = 1（层号 ω）上，第 0 个累加项已完整（ψ₀(Ω₁)）。
  - 第 1 个累加项（层号 2）只用了链点 1 的底。
- **下一格：**
  - 链点 1 的完整值：E (suc 0) (opB b*) 迭代的是 "折 b*"，而折 b* 本身就是 E 的 Ω 行。所以需要把 `Ew` 推广到任意算子：给定一个影子 g，得到折叠的影子 Coll(g)。
  - 链点 2 = `ex b* b* (suc z′₁)`：E 的 ex 行进入 `It zero`（`Kb`，`limC`，算子的迭代）。这是第二阶，到这里为止都没有做。
- **剩余距离（各段都是判断）：**
  1. ψ₀(Ω₁²)（已到，读法）到 ψ₀(Ω₂)：要第 1 层上 It n 对一切 n 的值定理，并在 Level 一侧有对应的树构造（相当于在 Level 树上实现 "T + B·ω^X"）。
  2. ψ₀(Ω₂) 到 BTBO 第 2 项 BO = ψ₀(Ω_ω)：要一切有限层号。目标层非零时，kp 会把低于目标的槽位保留下来（W4 的保留行），参照一侧要用 Level ψ 的 injᵃ 情形。
  3. BO 到 BTBO = ψ₀(Ω_Ω)：要对层号一致的 LOWER，即对一切第 0 层树 x，有 `ψ⁰(Ω (toLevel (read x))) ≼ read (G x)`，对 G 与 K 两种路径都要成立；然后接上链。
- **链的组装（判断，未编译）：**
  - 参照一侧可以照搬 `YiLSBtbo` 的链：`V1`、`V2′`、`PW₁₂₃`、`Ψ-emb`。
  - 旧证明里 W4 侧专用的 V3，可以换成参照侧的 `BTBOFullV3.V3`，再接 LOWER 与 `Eb-wk`。
  - 这样还需要两件事：`toLevel (read x)` 的 `SV`；以及 "≺ 接 ≼ 仍是 ≺" 的引理。两者是否现成，没有查实。
- **为什么旧证明搬不过来（编译事实加判断）：**
  - 旧的 LOWER（`YiLSFold`，853 行，加上 `YiLSRel`，324 行）是为没有 ex 的折叠写的。
  - 在 W4 上，目标是非零的本层时，自身行给出 ex。从第 2 层起，链点就是 ex 项（WVTwo 的形状测试）。在 `twᶜ 1` 里，由于累加底，第二个累加项的链底已经是 ex 项（`b*-shape`）。
  - 所以 W4 的 LOWER 必须包含 E、It 对一切阶的值定理。
- **止损：** 照简报止损，停在 It 之前。下一步是对一切阶一致的影子理论，加上 Level 一侧的镜像。它的规模与前四个文件不同，我估计超出剩余的约 470 行预算。
- 路线状态写 "暂停"，不是否定：没有任何编译的否定定理。
- **盲区：** 只有下界，不涉及上界与 FGH。
  - Tᴸ 与 X* 是我自己写的 Level 树。ψ⁰ 对值不是同余（`Value.ψ⁰-not-cong`），所以 ψ₀(Ω₁·ω)、ψ₀(Ω₁²) 这两个标签是读法。
  - 只有 ψ⁰(Ω 0) 与 ψ⁰(Ω 1) 经 `ω≈` / `ψ₀≈` 编译地连到 src 的 ψ₀(Ω_a)。

##### 3. 没读、只凭转述的东西
- **没读：**
  - `probes/Survey/LEMAudit-2026-11-18.md`（包括 §3）、`RedefS2.md`、`DefD1.md`、`S1Sharp`（本路没有导入）、`W4Check` 的大部分。
  - `EBOHandbook` 只读了目录与 §3.3、§3.4、§3.7、§5.3、§5.4；没读 §4 正文。本路没有遇到堆墙。
- **只读了签名或片段：**
  - `YiLSFold`（只看了小节标题与 `lower` 的陈述）。
  - `BTBOFullV1`、`BTBOFullV3`、`BTBOFullEb`（只看了签名、`Eb` 的定义与 `V3` 的陈述）。
  - 第 2 节里 "V3 可由参照侧 V3 加 LOWER 代替" 这一条，依据就是这些签名，所以是纸面判断。
- **读了全文：** `B4W4.md`、`YiSHAccept`、`YiMTValue`、`YiUpValTw1`、`YiLSTw1`、`YiLSBtbo`（前半与链）、`BTBOFull`、`YiBtValBT`，以及 W4 的 Block、Ops、Path、Fold、Val、View 与 `W4Contrast`。

## 简报正文（子智能体读的文件，本机路径换成占位）

## B5D：给新折叠 W4 重证 BTBO 下界（Opus 5.5）

目录 <实验目录>/math/B5D/，模块前缀 `WV`。

### 背景

- 路线：作者定 "改定义 + 第 4 层经典数学"。构造性新折叠 W4（实验目录，`W4Fold`）已有塔的闭项 `twᶜ n` 与终点 `EBOᶜ : Tr zero`（Λ 上），但还没有任何值下界，旧定义上的 BTBO 下界不能当作 W4 的证据。外部审计 `probes/Survey/LEMAudit-2026-11-18.md` §3 方案 D 就是本路：给 W4 一个可报告的值基线。
- 旧定义上的 BTBO 下界可以参考：
  - `probes/OCF/Lean/YiSHAccept.lagda.md`：`btbo-low` 由 `BTBOFull.BTBO≈` 与 `YiMTValue.btbo-EBOᶻ` 复合而成；
  - `probes/OCF/Lean/YiMTValue.lagda.md`：`btbo-twᶻ`，塔每一项不低于 BTBO；
  - `probes/OCF/Lean/YiUpValTw1.lagda.md`：`bho-tw1`；
  - BTBO 的值与零层读回见 `src/OCF/BTBO.lagda.md`、`probes/OCF/Align/BTBOValBase`（`tr₀`）。
  先读这些的陈述与证明结构，选对 W4 最短的一条。
- W4 的结构：
  - 第 0 层禁挂起乘幂 `ex`，所以 `Tr zero` 是纯布劳威尔树；
  - 层号读回用带序结果代数上的迭代子；
  - 值在 `W4Val`；内部 View 在 `W4View`。
  - 设计与行律见 `probes/Survey/Reports-2026-11-16/B4W4.md`、`DefD1.md`、`RedefS2.md`。

### 任务

1. 先选旧证明里一个非零的闭近似项（例如塔第 1 项或 BTBO 基本列的第 1、2 项），在 W4 的具体 `ψ₀` 上重证它的下界，并列出它经过 W4 的哪些行（`ex`、`E`、`It`、`upC`、自身行、回退行）。
2. 再推广到 BTBO 全量：目标 `BTBO 的零层树 ≼ EBOᶜ`（或 `≼ twᶜ n` 的上确界），值关系用旧证明同一种，以便与 `btbo-low` 对照。
3. 不改 W4 的定义。若发现非改不可，停下，写明理由与最小改动（AGENTS "第 4 层不反过来改前 3 层"）。

交付：BTBO 下界（编译）或停在第几项、卡在哪一行。

### 公共约束（两路相同）

- 先读仓库 `<仓库>` 的 `AGENTS.md`（必须遵守）、`probes/Survey/EBOHandbook.md` §4（堆墙）与 §5。只信编译证据。
- 新折叠 W4 只在实验目录里：`<实验目录>/cl/W4/`（W4Block、W4Ops、W4Path、W4Fold、W4Val、W4View、W4Check、W4Contrast，纯 `.agda`）。W4Check 导入 S1Sharp，在 `<实验目录>/math/S1/`。只读，不改。
- 编译：仓库根目录，`agda +RTS -M6G -RTS --library-file=<库文件> -i src -i probes -i <实验目录>/cl/W4 -i <实验目录>/math/S1 -i <你的目录> <文件>`。每次只跑一个 agda；6G，单个大文件可以 8G。退出码不经管道：0 通过，42 类型错误（先看日志首行，`LibraryError` 是库文件问题），251 堆耗尽，124 超时。日志落你自己目录里的文件，只看首个错误附近。
- 选项行：`{-# OPTIONS --safe --without-K --lossy-unification --cubical-compatible --guardedness --hidden-argument-puns #-}`。无 postulate、洞、编译指示，不开 K。排中律与函数外延只能作模块参数，结论标 "条件"。
- 只在你自己的目录里写，新模块名用你的前缀。不改仓库与 W4、S1 的任何文件；不 `rm` 别人的文件，不删别人的 `.agdai`，不 `pkill`，不写 `/tmp`，不装包，不提交。
- 止损：新代码约 1200 行以内；第一种写法不通可换一种再试；两种都不通就停，交回卡住的精确陈述与机制。
- 回报（你的最终消息就是回报原文，会逐字留档）：先说对纲领与目标意味着什么；再列新文件、关键定理的签名与档位（编译定理 / 条件定理 / 有限测试 / 纸面 / 判断）；最后说下一个必经缺口、位置与剩余距离，以及没读、只凭转述的东西。强度写 ψ₀(Ω_x)，x 用 Ω 的算术。不用 "决定性" 一类的说法，不用比喻。
