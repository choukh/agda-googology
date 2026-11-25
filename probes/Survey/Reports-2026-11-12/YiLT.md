# Lift₁：读回层号的 Ω 树折到第 0 层 (YiLT)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-fable-5-2 |
| effort (转录里请求的字段) | medium |
| 起止 (转录的时间戳，UTC) | 2026-11-14 10:18 至 10:39 |
| 工具调用 / agda 编译 (粗数) | 45 / 14 |
| token (usage 字段，按消息去重) | 输出 101144；新写入缓存的输入 259941；读缓存的输入 6900591；其余输入 80 |
| 写过的仓库文件 | `YiLTLift.lagda.md` |
| 文件前缀 | `YiLT` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-14: 第四十三批 YiLT 返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 无前提: ℕ 极限层号上沿一致路径折到第 0 层的保持 (LimU.FoldU.LFu, 孩子为有限读回层号); Lift₁ 在 c = ω 及一切 ℕ 极限形状的 c、η = ω 处成立 (lift-ω, lift-lim, Qlim); 沿第 0 层树的序上行 (up◃); 精确有限对 (lift-fin); η ≤ ω 的二分 (Qinf≤); 条件: Lift₁ 归约到后继一步 StepS (lift-red), 塔第 1 项对着 ψ₀(Ω_Ω) 条件于 StepS (k1-redᶻ); 第一个缺口: StepS 在 c = suc ωᶜ, η = ω+1 处 (要读回层号上的关系族与两条保持); 都对新主线折叠与任意表陈述; 四件 8G 冷编退出码 0 |

## 简报原文

你是这个 Agda 研究仓库（<仓库>）的执行方。全程用中文。主审会从头冷编复核你交的每个文件，只认编译过的定理。

###### 作者的决定与原则（2026-11-14，选项原文或原话）
- 主线 "经指定孩子" 那一行："改取最小比较表，原主线的值保留作参照 (Recommended)"。主线候选折叠是 `YiTBRow.ψ` 配表 `YiMTTab.rbᶻ`，闭项 `twᶻ n`、`EBOᶻ`（`probes/OCF/Lean/YiMTTab`）。
- 本批本路（选项原文）："(1) Lift₁ (Recommended)"，说明是 "目标第 0 层、孩子是可数树的 Lift，先做 ℕ 极限的孩子；对 YiKP 的孩子接口陈述；与那一行的取舍无关"。
- 作者问过阶段次序与返工；主审的回答（`probes/LOG.md` 2026-11-14 那一条）：`Lift₁` 在阶段 2 里面；它与那一行无关，因为第 0 层的树没有 Ω 结点（`YiRWBlock` 第 81 行 `Pos zero = ⊥`），读回层号只有后继与 ℕ 极限形状（第 137–142 行），这些层号上那一行只能经底被调用（`YiNRHit.noHit`），而 `Lift₁` 把底当作满足 `OKB` 的任意前提。
- 原则："不能以'追求同步'为名反过来指导树的定义形状"。本路只在验收一侧。
- 作者批评过："兜兜转转原地踏步"。直奔目标。

###### 已有的东西（主审复核过；先读，不重证）
- **陈述与归约**：`YiKPRel`（接口 `Kid`、`Top.M¹`、`Top.Fold.LF¹`、`chain`、`leaf¹`、`LeafC`）、`YiKPInst`（`Sem.Kidˢ`、`Sem.Lift₁`、`Sem.k1ˢ`、`Sem.lift-fin`、`k1-tw`）。
  - `Lift₁ = ∀ {η c} → M⁰ η c → Kdˢ c (E.Ωt η) (proj₁ (Ωt (h₁ c)))`：第 0 层的树 c 对着 η 时，读回层号 `h₁ c` 的 Ω 树以任一 `OKB` 的底、沿一致路径或经下标层的路径折到第 0 层，对着 ψ₀(Ω_η)。
  - 已证：精确有限对 (natT n, nat n)（`lift-fin`）。
  - YiKP 回报（`probes/Survey/Reports-2026-11-12/YiKP.md`）说最近的缺口是 c 为 ℕ 极限的树：要 ℕ 极限层号上沿一致路径 `inu` 的保持；`YiHCLim.Lim.Fold.LFω` 只有 `inc n v`。另一个缺口：带松弛的有限对（`M⁰ η (nat n)`，η 小于 n），要 "由 `M⁰ η (nat n)` 得 η ≤ᵀ natT n" 一类引理。
- **关系**：遗传封闭的族 `YiHCRel.Mᴴ`（构造子 `mc`）、`YiHCFam`、`YiHCFold`、`YiHCLim`、`YiHCOmega`、`YiHCPlus`；回报 `Reports-2026-11-12/YiHC.md`。
- **折叠**：YiKP 用的是兄弟孩子折叠 `YiRBSib.ψ`。主线现在是 `YiTBRow.ψ` 配 `rbᶻ`。读回层号上两者行为相同（没有 Ω 形状）。
  - 请把陈述对新主线的折叠写；若能对任意表 `r : Rb ℓ` 一并陈述，就一并陈述（`YiMTRel` 的 `NoΩ` 前提可参考）。
- **记号一侧**：`YiCFCofin`（`cofin`、`CofinNF`）、`YiCFMono`（`mono≤ⁿ`、`mono<ⁿ`）。

###### 要做的（按序；推进的是 "Lift 的第一个一般实例"）
0. **最小实例检查**，在临时目录：
   - 在 c = `ωᶜ`（第 0 层的 ω 树）、η = ω 上写出 `Lift₁` 的那一个实例：`h₁ ωᶜ` 是 ℕ 极限形状的读回层号，它的 Ω 树沿一致路径折到第 0 层，对着 ψ₀(Ω_ω)。
   - 确认需要的 "ℕ 极限层号上沿一致路径的保持" 的陈述类型正确、前提可满足。
   - 不成立就停下回报。
1. **ℕ 极限层号上沿一致路径的保持**：照 `YiHCLim.Lim.Fold.LFω` 补 `inu` 路径的版本。
2. **`Lift₁` 对 ℕ 极限的孩子**：先 c = `ωᶜ`，再对一切读回层号是 "孩子为有限读回层号的 ℕ 极限" 的 c；然后看一般的 c（ω·2、ω² 一类）缺什么。带松弛的有限对能顺手补就补。
3. **检验**：若 `Lift₁` 对足够的 c 成立，用 `YiKPInst.k1ˢ` 的同类论证给塔第 1 项（新主线 `twᶻ 1`）一条值的下界，说明与已有的 `k1ᶻ`、`k1-tw` 的关系。
4. 交第一个挡住的引理，精确到 c 的形状。

**纪律**（作者同意的，必须照做）：
- 动手证一般形式之前，先用临时文件检查前提可满足。
- 已有引理先检索再写，不重证；搬来的证明在文首写明来源。
- 若某一步要改树、折叠或合法性的定义，停下回报。
- 停止条件触发时，先停下回报；不要像上一路那样改题继续。若你认为改题有价值，在回报里写成建议。

###### 规则
- **只新建文件**，放 `probes/OCF/Lean/`，前缀 `YiLT`（模块名 `OCF.Lean.YiLT…`）。不改任何已有文件，不碰 `src/`、`archive/`，不碰另一路的前缀 `YiVT`。验收文件，文首标明。
- 中文 literate Agda（`.lagda.md`），每个模块文首不超过 5 行。一次性的试验放临时目录，用纯 `.agda`，选项行加 `--cubical-compatible --guardedness --hidden-argument-puns`；在临时目录编译要加 `-l standard-library`。
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。不许 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY_CHECK`、`trustMe`、K、`--irrelevant-projections`、`--cubical`。函数外延只能作显式前提。
- 仓库文件里不写本机路径。
- **编译**，在仓库根目录：
  `agda +RTS -M8G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <临时目录>/<文件>.log 2>&1; echo "exit $?"`
  - 同时只跑一个 agda，堆上限 8G。另一路也在编译，不用 `--ignore-interfaces`，只删自己模块的 `.agdai`。不用 `--interaction`。大的 `refl` 前加 `timeout 600`。
  - 冷编只删自己模块的接口，写字面路径；`rm` 的目标不要写成 shell 变量，执行前核对路径。
  - 退出码：0 通过；42 类型错误（先看日志首行是不是 `LibraryError`）；251 堆耗尽；124 超时；154 是 Agda 内部错误，改写隐式参数后重试。
  - 堆墙：不要在具体推导上直接比较两个 `Rt`；具体参照树放 `opaque`；见 `probes/Survey/EBOHandbook.md` 第 4 节。
  - 沙箱里 `/usr/bin/time` 不可用，内存用 `+RTS -s` 看。
- 临时目录：`<实验目录>/agents/lt`（先 mkdir）。只在它和你前缀的新文件里写。不在这些之外 `rm`，不 `pkill`，不装包，不提交。
- 查签名用检索，不整篇读大文件。
- **停下的条件**：同一处两次重新设计仍过不了检查器；8G 仍耗尽；第 0 步触发的停止条件。没有编译的否定时只写 "未走通"。
- **过程要求**：第一个文件（第 0 步的临时文件也算）30 分钟内写出并编译；每次回复都要有工具调用。
- **结束前自查**：每个仓库文件删自己的接口后冷编，退出码 0，日志里只有自己模块的 `Checking` 行；检索禁用构造为 0。

###### 回报格式（只在回报里交一次）
1. 判决：第 0 步的结论；`inu` 版保持、`Lift₁` 各到哪一步；检验那一处的值；对纲领与目标的意义；列问题（表：问题、位置、档）。
2. 文件表：代码行、冷编退出码、内存。
3. 定理表：名字、逐字的陈述、一句白话、文件、档。
4. 第一个障碍，精确到引理与 c 的形状。
5. 偏离与事故；没有读、只凭转述引用的东西。

不用 "只差"、"自然" 一类形容；判断与定理分开写。

## 回报原文

### 回报: Lift₁ (YiLT)

四个新文件都在 `probes/OCF/Lean/`,删自己的接口后冷编退出码 0。没有改任何已有文件,没有改树、折叠、合法性的定义。

#### 1. 判决

**第 0 步: 成立。** 在临时文件里,对旧折叠 `YiRBSib.ψ` 写出了 c = `ωᶜ`、η = ω 的那一个 `Lift₁` 实例并证完,连同 `inu` 版保持。陈述类型正确;前提(`OKB` 的底、对着 ψ₀(0) 的起点、逐点的路径等式)都由实例填上。随后把所需引理搬到新主线折叠 `YiTBRow.ψ` 上,以下结果都对任意表 `r : YiTBRow.Rb` 陈述。

**`inu` 版保持: 做完(目标第 0 层)。** `YiLTLim.LimU.FoldU.LFu` 对一切 `Mω a x` 的推导成立,层号是"孩子为有限读回层号的 ℕ 极限"。朝第 j ≥ 1 层的一致路径没有做。

**`Lift₁` 到哪一步:**
- **c = `ωᶜ`、η = ω**: 无前提,两条独立证法(`Dir.lift-ω` 经 `LFu` 与 `leafω`;`Inst.lift-lim` 不经它们)。
- **一切 ℕ 极限形状的 c(`lim f a`,f 任意)、η = ω**: 无前提(`lift-lim`)。ω·2、ω² 作为树都在内,但对着的只是 Ω_ω,不是 Ω_{ω·2}。
- **η ≤ ω 时的二分**: 第 0 层的树 c 要么是字面的 `nat n`,要么层 `h₁ c` 的 Ω 树的折叠对着 ψ₀(Ω_η)(`Qinf≤`)。
- **精确有限对 (natT n, nat n)**: 在新折叠上重证(`lift-fin`)。
- **一般的 (η, c)**: 条件定理 `lift-red : StepS → Lift₁`。对 `M⁰ η c` 的推导归纳,`mz`、`mL`、`mw`、`mc` 四行无前提,只有 `m1`(c 是后继)一行归到前提 `StepS`。`StepS` 未证,没有编译的否定。
- **带松弛的有限对**: 没有做,见第 4 节。

**检验那一处的值:**
- 塔第 1 项 Ω 树的第 c 支(`blk c`)朝第 0 层的标准折叠:c 在每个 `nat k` 之上时对着 ψ₀(Ω_ω)(`val-ω≥`),c = `nat n` 时对着 ψ₀(Ω_n)(`val-fin`)。编译定理,无前提。
- `twᶻ 1` 本身没有新的无条件下界。回灌链的链点是折叠的输出,不是这些 c,要它们就要全部的 `Lift₁`。
- 条件的两条:`k1ᶻᴹ : Lift₁ → M⁰ (EBOψ 2) (twᶻ 1)` 与 `k1-redᶻ : StepS → M⁰ (EBOψ 2) (twᶻ 1)`。
- 与已有的关系:
  - `YiMTValue.k1ᶻ` 无前提,结论是 `Rt h ≼ readRW (twᶻ 1)`(h : HC (EBOψ 2)),经 BTBO 的标签与同值搬运得到。
  - `YiKPInst.k1-tw` 是旧折叠配 `rb-tw 1` 上的同一条件陈述;`k1ᶻᴹ` 是它在新主线上的对应,`k1-redᶻ` 把前提从 `Lift₁` 减到 `StepS`。
  - 这几条条件定理的结论停在 `M⁰`,没有过出口 `exitᴴ`。在序数值上它们不超过 `k1ᶻ` 已有的结论。

**对纲领与目标的意义:**
- 只在验收一侧,树侧新增定义为零,翻译账不变。
- `up◃` 是一条不按阶段定制的陈述:第 0 层的树 x ◃ c 时,层 `h₁ x` 的 Ω 树朝第 0 层的折叠对着的项,层 `h₁ c` 的也对着;对任意证据、任意表、任意 `OKB` 的底。它只对 Ω 树、目标第 0 层、一致路径陈述,不是一般的跨层单调接口。
- (判断)`Lift₁` 的量化域是"一切满足 `M⁰ η c` 的 c"。归约之后剩下的 `StepS` 仍对一切 x 量化;`M⁰` 是下界式的关系(`YiCLCrit.no-least`),从它读不出子层号的精确记号下标。这一处可能是量化域的问题,没有编译定理支持。

**问题表:**

| 问题 | 位置 | 档 |
|---|---|---|
| `StepS`(后继一步)未证 | `YiLTLift.StepS` | 未走通,无否定 |
| 带松弛的有限对 | 缺 `M⁰ η (nat n) → η ≤ᵀ natT n` | 未做 |
| `inu` 版保持只到目标第 0 层 | `YiLTLim.LimU.FoldU.LFu` | 范围 |
| 值的陈述没有过出口 | `k1ᶻᴹ`、`k1-redᶻ`、`val-ω≥` | 范围 |
| "读回层号上两个折叠行为相同"没有写成定理 | 做法是把证明在新折叠上重编 | 说明 |
| 搬来的证明约 500 行与 `YiHCFold`、`YiHCLim`、`YiKPRel` 重复 | `YiLTFold`、`YiLTLim`、`YiLTKid` | 账 |

#### 2. 文件表

| 文件 | 代码行 | 冷编退出码 | 内存 |
|---|---|---|---|
| `probes/OCF/Lean/YiLTFold.lagda.md` | 229 | 0 | 2454 MiB |
| `probes/OCF/Lean/YiLTLim.lagda.md` | 189 | 0 | 2400 MiB |
| `probes/OCF/Lean/YiLTKid.lagda.md` | 169 | 0 | 2432 MiB |
| `probes/OCF/Lean/YiLTLift.lagda.md` | 201 | 0 | 2514 MiB |

- 冷编日志里各只有自己模块的一行 `Checking`,警告与错误为 0。
- 禁用构造与本机路径检索为 0。
- 文首各 4 行,均标明验收文件。
- 日志在 `<实验目录>/agents/lt/`(`<文件>.cold.log`);第 0 步的临时文件是同目录的 `LT0.agda`,退出码 0。

#### 3. 定理表

全部是编译定理。折叠都是 `YiTBRow.ψ`,表任意。

**`YiLTFold`(搬运,外加两条新写)**

| 名字 | 陈述 | 白话 |
|---|---|---|
| `Qu`、`Self.PF`、`LF`、`chain`、`sΩ-LF`、`LFA`、`LFAB` | 同 `YiHCFold`、`YiHCBridge` 的同名定理 | 有限读回层号上封闭族的保持,换到新折叠 |
| `LFP` | `∀ {N} (p : Pt N 0) (o : Ok (fn N)) (r : Rb (fn N)) (B : Base (fn N)) (t₀ : E.T) → GBB (fn N) refl B t₀ → (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t₀) (proj₁ β) → ∀ {a x} → M N a x → M⁰ (ψᴺ 0 (t₀ ++ a)) (proj₁ (ψ (fn N) o r B zero (pt p) β x))` | 有限层沿 `inc` 链或 `inu` 链折到第 0 层 |
| `LFPB` | 同上,层号带等式 `e : ℓ ≡ fn N`,路径前提 `τ {j = 0} e v ≡ pt p` | `LFP` 对等式作 J |

**`YiLTLim`**

| 名字 | 陈述 | 白话 |
|---|---|---|
| `LimT.Fold.LFω` 一组 | 同 `YiHCLim.Lim.Fold` | 路径经孩子 n 的保持,换到新折叠 |
| `LimU.FoldU.LFu` | 模块参数 `(oc) (r : Rb Lω) (B : Base Lω) (t₀) (gb : GBω B t₀) (ws : ∀ n → zero ≤ G n) (P : ∀ n → Pt (d n) 0) (q : ∀ n → τ {j = 0} (eG n) (ws n) ≡ pt (P n))`;`LFu : (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t₀) (proj₁ β) → ∀ {a x} → Mω a x → M⁰ (ψᴺ 0 (t₀ ++ a)) (proj₁ (ψ Lω o r B zero (inu ws) β x))` | ℕ 极限层号上沿一致路径折到第 0 层的保持,对一切推导 |

**`YiLTKid`**

| 名字 | 陈述 | 白话 |
|---|---|---|
| `Kid`、`Top.M¹`、`Top.Fold.LF¹`、`chain`、`leaf¹` | 同 `YiKPRel` | `tw 1` 上的孩子接口与折到第 0 层的保持,换到新折叠 |
| `Sem.Lift₁` | `∀ {η c} → M⁰ η c → Kdˢ c (E.Ωt η) (proj₁ (Ωt (h₁ c)))` | 陈述,未证 |
| `Sem.k1ˢ` | `Lift₁ → M⁰ (EBOψ 2) (proj₁ (ψ₀ʳ ℓ¹ o¹ r (proj₁ (Ωt ℓ¹))))` | 条件:有 `Lift₁` 则塔第 1 项对着 ψ₀(Ω_Ω) |
| `k1ᶻᴹ` | `Sem.Lift₁ (rbᶻ ℓ¹) → M⁰ (EBOψ 2) (twᶻ 1)` | 同上,表取主线的 `rbᶻ` |

**`YiLTLift`**

| 名字 | 陈述 | 白话 |
|---|---|---|
| `Dir.lift-ω` | `Kdˢ ωᶜ (E.Ωt ωᵀ) (proj₁ (Ωt (h₁ ωᶜ)))` | 第 0 步的实例,经 `LFu` 与 `leafω` |
| `SΩ`(定义) | `SΩ t ℓ o r = (v : zero ≤ ℓ) → ZP ℓ v → (B : Base ℓ) → OKB B → (β : Tr⁺ zero) → M⁰ (Ωᴺ 0) (proj₁ β) → M⁰ t (proj₁ (ψ ℓ o r B zero v β (proj₁ (Ωt ℓ))))` | 层 ℓ 的 Ω 树沿一致路径折到第 0 层后对着 t |
| `Q`(定义) | `Q t ℓ = (o : Ok ℓ) (r : Rb ℓ) → SΩ t ℓ o r` | 上一条对一切证据与表 |
| `upS` | `∀ {t} {h : ⊤ → L} → Q t (h tt) → Q t (nd sS h)` | 沿后继形状上行 |
| `upL` | `∀ {t} {g : ℕ → L} (n : ℕ) → Q t (g n) → Q t (nd sL g)` | 沿 ℕ 极限形状从孩子 n 上行 |
| `up◃` | `∀ {t} {x c : Tr zero} → zero ⊢ x ◃ c → Q t (h₁ x) → Q t (h₁ c)` | 沿第 0 层树的序上行 |
| `Qfin` | `∀ n → Q (ψᴺ 0 (Ωᴺ n)) (fn n)` | 有限层对着 ψ₀(Ω_n) |
| `Qz` | `∀ c → Q (ψᴺ 0 (Ωᴺ 0)) (h₁ c)` | 任意层对着 ψ₀(Ω₀) |
| `StepS`(定义) | `∀ {η x} → cof η ≡ c1 → M⁰ (pred η) x → Q (ψᴺ 0 (E.Ωt (pred η))) (h₁ x) → Q (ψᴺ 0 (E.Ωt η)) (h₁ (suc x))` | 后继一步,未证 |
| `liftQ` | `StepS → ∀ {η c} → M⁰ η c → Q (ψᴺ 0 (E.Ωt η)) (h₁ c)` | 归约 |
| `Red.lift-red` | `StepS → Lift₁` | 条件定理 |
| `Red.k1-red` / `k1-redᶻ` | `StepS → M⁰ (E.EBOψ 2) (proj₁ (ψ₀ʳ ℓ¹ o¹ r (proj₁ (Ωt ℓ¹))))` / `StepS → M⁰ (E.EBOψ 2) (twᶻ 1)` | 条件定理 |
| `step-fin` | `∀ n → Q (ψᴺ 0 (E.Ωt (natT (suc n)))) (h₁ (suc (nat n)))` | `StepS` 的结论在精确有限对上成立 |
| `Qω` | `∀ c → (∀ k → zero ⊢ nat k ◃ c) → Q (ψᴺ 0 (E.Ωt ωᵀ)) (h₁ c)` | c 在每个自然数之上时对着 ψ₀(Ω_ω) |
| `nat⊴f` | `(f : ℕ → Tr zero) (a : ∀ n → zero ⊢ f n ◃ f (suc n)) → ∀ k → nat k ⊴ f k` | 第 0 层 ℕ 极限的第 k 项不低于 k |
| `Qlim` | `∀ f a → Q (ψᴺ 0 (E.Ωt ωᵀ)) (h₁ (lim f a))` | 一切 ℕ 极限形状的 c |
| `Qinf` | `∀ c → (Σ ℕ λ n → c ≡ nat n) ⊎ Q (ψᴺ 0 (E.Ωt ωᵀ)) (h₁ c)` | 二分 |
| `Qinf≤` | `∀ {η} → η ≤ᵀ ωᵀ → ∀ c → (Σ ℕ λ n → c ≡ nat n) ⊎ Q (ψᴺ 0 (E.Ωt η)) (h₁ c)` | η ≤ ω 的二分 |
| `Inst.lift-fin` | `∀ n → Kdˢ (nat n) (E.Ωt (natT n)) (proj₁ (Ωt (h₁ (nat n))))` | 精确有限对 |
| `Inst.lift-ω≥` | `∀ c → (∀ k → zero ⊢ nat k ◃ c) → Kdˢ c (E.Ωt ωᵀ) (proj₁ (Ωt (h₁ c)))` | `Qω` 的接口形式 |
| `Inst.lift-lim` | `∀ f a → Kdˢ (lim f a) (E.Ωt ωᵀ) (proj₁ (Ωt (h₁ (lim f a))))` | `Qlim` 的接口形式 |
| `Inst.lift-mono` | `∀ {t x c} → zero ⊢ x ◃ c → Q (ψᴺ 0 t) (h₁ x) → Kdˢ c t (proj₁ (Ωt (h₁ c)))` | `up◃` 的接口形式 |
| `Inst.val-ω≥` | `∀ c → (∀ k → zero ⊢ nat k ◃ c) → M⁰ (ψᴺ 0 (E.Ωt ωᵀ)) (proj₁ (ψ₀ʳ ℓ¹ o¹ r (blk c)))` | 第 c 支对着 ψ₀(Ω_ω) |
| `Inst.val-fin` | `∀ n → M⁰ (ψᴺ 0 (Ωᴺ n)) (proj₁ (ψ₀ʳ ℓ¹ o¹ r (blk (nat n))))` | 第 `nat n` 支对着 ψ₀(Ω_n) |

记号一侧的小引理:`cofΩω`、`fsnΩω`(η 余尾 ω 时 Ω_η 的余尾与基本列)、`Ωt≤`(Ω 对下标单调)。

前提可满足:`Qinf≤` 的前提取 `inj₂ refl`;`Qω` 的前提由 `ωᶜ`(`◃l k`)与一切 `lim f a`(`nat⊴f`)满足;`StepS` 是全称陈述,只知道它的结论在 `step-fin` 上成立。

#### 4. 第一个障碍

**引理 `StepS`,c 的形状是 `suc x`,x 不是字面的自然数。** 最小的一处是 x = `ωᶜ`,η = ω+1:要 `Q (ψᴺ 0 (E.Ωt η)) (h₁ (suc ωᶜ))`,其中 `cof η ≡ c1`、`pred η = ωᵀ`。

- **机制。** 层 `nd sS (λ _ → h₁ x)` 的 Ω 树是结点,朝第 0 层取回灌链 z_{k+1} = next(层 `h₁ x` 上的自身折叠 z_k)。要让链点对着 γ-链 ψ_{η′}(…),需要层 `h₁ x` 上的语法关系族,以及它上面"折到自身"与"折到第 0 层"两条保持。
- **`Q` 给不出。** `Q` 只说 Ω 树朝第 0 层的折叠,不能打开链点。
- **已有的。** x = `nat n` 有(`YiHCFam.M`,`sΩ-LF`)。x = `ωᶜ` 在旧折叠上有 `YiHCPlus`(路径是 `inc` 链、目标有限层)与 `YiHCOmega.Tω.Self.PFω`;它们没有搬到新折叠,也没有一致路径朝第 0 层的版本。对一般的 x 没有这样的族。
- **ω·2、ω² 一类。** 作为 ℕ 极限已由 `Qlim` 对着 Ω_ω。要对着它们自己的 η,由 `liftQ` 的 `mL`、`mw` 两行归到 ω+n 各处的后继一步,即同一个 `StepS`。

**带松弛的有限对**缺的引理是 `M⁰ η (nat n) → η ≤ᵀ natT n`。有了它,用 `Qc` 一步即得。对推导归纳时卡在 `mL` 一行:要从"`cof η ≡ cω` 且每个 `fsn η k` 都不超过 natT n"推出矛盾,这需要 η 的标准形(`YiCFCofin.cofin` 带 `NF` 前提),而 `M⁰` 不带。没有检索到现成的引理,没有尝试证,没有否定。

#### 5. 偏离与事故;只凭转述引用的东西

**偏离:**
- 第 0 步先在旧折叠上做(现成引理都在那里),再搬到新主线。
- 搬运用脚本按行截取 `YiHCFold`、`YiHCLim`、`YiKPRel` 的证明段并改导入,证明文本没有改,来源写在各文首。与折叠无关的部分(`Lim` 的关系、`GB`、`kcase`、桥、`leafω`、路径 `zq`/`pz-eq`/`pk-eq`)直接引用原文件。
- 第 2 步多做了一条不经 `LFu` 的路(`Q`、`up◃`、`liftQ`)。它回答"一般的 c 缺什么",把 `Lift₁` 归到 `StepS`,属于第 2、4 步的范围,没有改题。

**没有触发停止条件。** 编译错误都是作用域、重名、隐式参数未解一类,每处一次改好。

**建议(不是结论):**
- 下一步若继续,先在最小的一处 (ω+1, `suc ωᶜ`) 上做 `StepS`:把 `YiHCPlus` 与 `PFω` 搬到新折叠并补一致路径朝第 0 层。
- 同时派一路查 `Low¹ = M⁰` 的量化域是否太宽。

**没有读、只凭简报转述引用的:**
- `Reports-2026-11-12/YiKP.md`、`YiHC.md`,`probes/LOG.md` 那一条,`YiNRHit.noHit`,`EBOHandbook.md`。
- `YiHCPlus`、`YiHCOmega`、`YiMTValue`、`YiKSRead`、`YiCFCofin`、`YiCFMono` 只读了文首与签名;`YiMTRel` 只读了文首。
- `k1ᶻ` 与 BTBO 的关系只读了 `k1`、`k1ᶻ` 的一行证明与 `row₂-btbo`、`btbo-tw1ᴿ` 的签名。
