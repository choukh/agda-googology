# 旧折叠的值下界补到一切有限 n (YiLvAll)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-11 05:21 至 05:50 |
| 工具调用 / agda 编译 (粗数) | 53 / 12 |
| token (usage 字段，按消息去重) | 输出 182426；新写入缓存的输入 564278；读缓存的输入 11054256；其余输入 90 |
| 写过的仓库文件 | `YiLvAll.lagda.md`, `YiLvAllAdd.lagda.md`, `YiLvAllFold.lagda.md`, `YiLvAllRel.lagda.md`, `YiLvAllTree.lagda.md` |
| 文件前缀 | `YiLvAll` (在 `probes/OCF/Align/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 旧折叠的值下界补到一切有限 n 与 ω, 返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 一切有限 n 与 ω 的下界是无条件的定理；证明对层号一致；五件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库> = <仓库>) 的一路执行方, 任务是 "把乙线有限层号闭项的值下界从 n ≤ 3 补到一切有限 n 与 ω". 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

### 0 先读什么

1. `AGENTS.md` 全篇. 特别是: "用记号验收强度" 与 "中间站给界, 终点对 EBO 验收"; Agda 一节 (选项, 文字预算, 退出码, 堆; Funext 只准作前提); "结论的写法".
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 (编译与内存, 堆墙的对策) 与 §5.4.
3. **上一轮同一任务的回报原文**: `probes/Survey/Reports-2026-11-11/YiLvVal.md` (全读; 尤其 §4 办法与 §5 第一个障碍). 同目录 `README.md` 的 §2 里 "有限层号闭项的值下界" 一段.
4. 代码 (都在 `probes/OCF/Align/`, 模块名 `OCF.Align.<名>`; 都已定稿, 可以导入, 不许编辑):
   - **你接着做的文件**: `YiLvValBase` (`⟨_⟩ = L.natᴵ`, `Ψ`, `γ`, `reference-row`, 记录 `Interface M` (`Rel`, `start`, `step`, `absorb`, `lower`), `FromInterface.theorem`, `interface₀`, `lower₀`, `lower₁`, `read-plus`, `read-copies`, `suc-lower`, `one≼fold`), `YiLvVal2` (`_⊴_`, `interface₁`, `lower₂`), `YiLvVal3Base`, `YiLvVal3` (`_⊴₂_`, `ADD`, `TR`, `B`, `C`, `D` 三族, `Chain1`, `interface₂`, `lower₃`; 编译它要 6G), `YiLvValFin` (`AllLevels.lower-fin`, `AllLevels.lower-ω`: 前提是 `∀ M → Interface M`; `reference-ω-row`).
   - 被验收的对象: `YiLvFoldFin` (`foldᶠ`, `fold-Ωω`, `fin`, `wayᵇ`, `eqᶠ`, `eqᶠ-fin`, `complete-fin`, `sound-fin`, `keep-fin`, `lev-slotᶠ`, `slotᶠ`), `YiLvFold` (模块 `Fold`: `ψ`, `ψn`, 各行), `YiLvFoldAdd` (`plus`, `Alg`, `shS`), `YiLvFoldBase` (`Way`, `nodeAt`, `Chain`).
   - 可能用得上的: `YiRawNegLift` (`toRaw`, `fromRaw`, `from-to`, `to-from`, `gd-to`, `gd-from`: `Low K r` 与 `Raw (lev K r)` 之间逐子句恒等的往返); `YiLvIf` (`lev`, `Low-lev`).
   - 参照一侧: `OCF.Align.Level` (`Ordᶜ`, `ψ`, `ψ⁰`, `Ω`, `natᴵ`, `ωᴵ`, `<ᴵ-dec`, `≅ᴵ`), `OCF.Align.Value` (`≼`).
   查签名用检索, 大文件不要整篇读.

### 1 这一步是什么

乙线对层号参数化的折叠 (写在 `LF` 上) 的有限层号闭项 `foldᶠ n`, 读法 ψ₀(Ω_n). 上一轮证了 n = 0, 1, 2, 3 的值下界 (参照 ≼ 读回的闭项), 并把一切有限 n 归约到 "每层一个接口": `∀ M → Interface M` 推出 `∀ n → L.ψ⁰ (L.Ω ⟨ n ⟩) ≼ read (foldᶠ n)` 与 `L.ψ⁰ (L.Ω L.ωᴵ) ≼ read fold-Ωω`. 接口只对 M = 0, 1, 2 实填. 上一轮的执行方按工作量的判断停下, 没有碰到停下的条件, 并用探针指出了一般的 M 卡在哪 (回报 §5):

- (a) 树一侧的派发在变量层号上不化简: `wayᵇ (fin (suc N)) (fin N)` 不是字面的 `keep (inj₁ tt) refl`; 顶槽位可用 `eqᶠ-fin` 改写; 低槽位要把结点层号当变量用 J 消去.
- (b) 变量槽位的下界类型: `Low (fin N) r` 不能当作 `Raw (lev (fin N) r)`; 要对槽位递归定义关系, 或用逐子句恒等的往返.
- (c) 缺对 M 一致的关系族 `Rel : (M : ℕ) → ∀ {k} → L.Ordᶜ k → Raw (fin M) → Set` 与 `∀ M → Interface M`; 以及 `natᴵ` 层上 `<ᴵ-dec` 的派发引理 (`natᴵ j ≅ᴵ natᴵ m → j ≡ m`, `natᴵ m` 之下字面证明的分类).

本任务: 做出 `∀ M → Interface M`, 从而 `lower-fin`, `lower-ω` 成为无条件的定理 (读法 ψ₀(Ω_n) 对一切 n, 与 ψ₀(Ω_ω), 变成下界定理). 只要下界.

### 2 目标, 分步; 每步先交再往下

1. **M = 3 (即 n = 4) 的探针.** 不必交成文件; 目的是在写一般版本前, 看清关系与引理族随 M 怎样长, 哪些部分对 M 是一致的. 若直接写一般版本更省事, 跳过.
2. **对 M 一致的关系族.** 一个定义给出一切 M 的 `Rel`; 对槽位递归或用往返解决 (b).
3. **派发引理.** 解决 (a) 与 (c) 的后半: 树一侧 `wayᵇ` 在有限层号上的保留与折叠的一般陈述 (已有 `complete-fin`, `sound-fin`, `keep-fin` 可用); 参照一侧 `<ᴵ-dec` 在 `natᴵ` 上的分类.
4. **`∀ M → Interface M`**, 然后 `lower-fin`, `lower-ω` 无条件.

部分进展也算: 交出对 M 一致的关系族加上其中若干条性质 (其余作为带确切类型的模块参数), 也是可以汇报的结果.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要 Funext 或 K 才能证; 堆到 6G 仍耗尽 (先按手册 §4.2 的对策; 文件拆小). 约化: 把缺的引理写成带确切类型的模块参数, 其余条件地证出来并编译; 说明前提在 M ≤ 2 上是定理 (由已有的 `interface₀/₁/₂` 给出, 或由你的一致版本在这些 M 上的实例给出).

不要改折叠, 不要改已有的验收文件. 发现掉值 (某个 n 上闭项的值低于读法), 写成编译过的定理交回.

### 3 规则

- **只新建文件**, 前缀 `YiLvAll` (注意不是 `YiLvVal`: 那些是已定稿的文件), 放 `probes/OCF/Align/`, 中文 literate Agda (`.lagda.md`). 都是验收文件, 文首标 "验收文件". 不改任何已有文件 (含 README, LOG, RESULTS, AGENTS), 不碰 `src/`, `archive/`. 同时在跑的另四路用前缀 `YiOmFold`, `YiOmNeg`, `YiPsum`, `YiRawVal`, 不要动它们的文件, 也不要依赖它们.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. Funext 只准作显式前提, 用到它的定理在文首标 "条件".
- **文字预算** (AGENTS Agda 一节): 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件. 一次性的试验放你的临时目录, 用纯 `.agda`.
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Align/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Align/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块 (尤其不要删 `YiLvVal*` 的接口).
- 你的临时目录: `<实验目录>/agents/lvall`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几步, 一段话说对纲领与目标意味着什么 (哪些读法变成了定理, 哪些仍是读法).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 条件定理写出前提的 Agda 类型.
4. 办法: (a)(b)(c) 各是怎么解决的或没解决.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
强度写 ψ₀(Ω_x), 标明是定理还是读法; 下界不写成同值; 不用 "只差", "自然" 一类形容.

## 回报原文

#### 1 判决

我做完了第 4 步，中间跳过了第 1 步（M = 3 的探针），直接写了对 M 一致的版本。`interfaceᴬ : ∀ M → Interface M` 已经编译通过，所以 `AllLevels.lower-fin` 和 `AllLevels.lower-ω` 现在不带前提。

对纲领与目标意味着什么：
- **变成定理的读法（只是下界）：**
  - 对一切 n，`foldᶠ n` 读回的值不低于参照的 ψ₀(Ω_n)。
  - `fold-Ωω` 读回的值不低于参照的 ψ₀(Ω_ω)。
- **仍是读法：** 同值与上界（"不高于 ψ₀(Ω_n)" 没有证），以及 FGH 的比较。
- **没有发现掉值。**
- **没有动定义：** 新文件全是验收文件，没有新定义，没有改折叠，被验收的就是 `YiLvFoldFin.foldᶠ` 和 `fold-Ωω`。
- **翻译账：** 关系 `Rel` 是验收用的工具。它按参照一侧 `<ᴵ-dec` 的派发来组织，这一点受记号启发；但它不进成品。
- **没有用到 Funext，也没有用到 K。**

#### 2 文件表

逐一删掉我自己 5 个模块的 `.agdai`（写的是字面路径），然后按依赖顺序冷编译。每个日志里只有本模块的 `Checking` 行。

| 文件（`probes/OCF/Align/`） | 代码行 / 总行 | 退出码 | 常驻内存峰值（`-M6G`） |
|---|---|---|---|
| `YiLvAllRel.lagda.md` | 199 / 267 | 0 | 1.38G，7s |
| `YiLvAllTree.lagda.md` | 84 / 120 | 0 | 1.24G，6s |
| `YiLvAllAdd.lagda.md` | 141 / 182 | 0 | 1.46G，8s |
| `YiLvAllFold.lagda.md` | 205 / 254 | 0 | 1.28G，8s |
| `YiLvAll.lagda.md`（入口） | 29 / 43 | 0 | 1.28G，7s |

- 检索 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`--irrelevant-projections`、`--cubical`、本机路径，命中都是 0。`Funext` 只在正文 "没有 Funext" 一句里出现。
- 5 个文件的选项行都是 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。
- 入口导入了 `YiLvValFin`，所以导入闭包里有 `YiLvVal3`。只加载它的接口时内存不高；如果连它一起重编，要 6G。

#### 3 定理表

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `lower-all` | `∀ n → L.ψ⁰ (L.Ω ⟨ n ⟩) ≼ read (foldᶠ n)` | 对一切 n，不低于 ψ₀(Ω_n) | YiLvAll | 编译定理 |
| `lower-Ωω` | `L.ψ⁰ (L.Ω L.ωᴵ) ≼ read fold-Ωω` | 不低于 ψ₀(Ω_ω) | YiLvAll | 编译定理 |
| `interfaceᴬ` | `∀ M → Interface M` | 上一轮条件定理的前提，对一切 M 成立 | YiLvAll | 编译构造 |
| `FOLD` | `∀ M m {k} {x : L.Ordᶜ k} {η : Raw (fin M)} → Rel M x η → ∀ {ℓ} (p : ⟨ m ⟩ <ᴵ ℓ) (σ : L.Simᴵ k ℓ) .(nb : Nested (fin M) η) .(d : Dom (up (fin M) η nb)) → Rel m (L.ψ p σ x) (ψ (fin m) (up (fin M) η nb) d)` | 对任意输入层 M 和目标层 m，折叠保持关系 | Fold | 编译定理 |
| `ABSORB` | `∀ M θ {k} {x : L.Ordᶜ k} {η} → Rel M x η → Rel M x (plus (fin M) θ η)` | 加上前缀后关系不变 | Add | 编译定理 |
| `ADDg` | `∀ Lv {A : Alg (fin Lv)} (P : RA A) {ℓ k} (σ : L.Simᴵ k ℓ) {x : L.Ordᶜ ℓ} {θ} → ρ P x θ → ∀ {y : L.Ordᶜ k} {a} → Rel Lv y a → ρ P (L.add x σ y) (add (fin Lv) A θ a)` | 加法保持关系，嵌入深度任意 | Add | 编译定理 |
| `SUCC` | `∀ m {A : L.Ordᶜ ⟨ m ⟩} {Y} → Rel m A Y → Rel m (L.lim (iter (A L.+_) L.zero)) (successor (fin m) Y)` | ω 倍保持关系 | Add | 编译定理 |
| `START` | `∀ M → Rel M (L.Ω ⟨ M ⟩) (cO (fin M))` | 链的起点 | Rel | 编译定理 |
| `TRC-all` | `∀ M → TRC (Rel M)` | 关系对 `tr⁻ e` 和 `tr e` 封闭（e 任意） | Rel | 编译定理 |
| `TREE-KEEP` | `ψ (fin m) (lc (fin (levN m s)) c w b t g) d ≡ nodeA m s (rawAlg (fin m)) c (ψ (fin m) t (Node.first …)) (λ a e → ψ (fin m) (g a e) (Node.branch …))`（m、s 是变量） | 结点层号小于目标层时保留，且落在槽位 s | Tree | 编译定理 |
| `TREE-FOLD` | `∀ m j → m ≤ j → … → ψ (fin m) (lc (fin j) c w b t g) d ≡ G.lim (λ n → out (fin m) (fin j) c w b t g d (iterate (next …) (startᴸ …) n))` | 结点层号不小于目标层时走链行 | Tree | 编译定理 |
| `below-nat`, `nat-inj`, `nat-eq`, `slotOf` | `natᴵ j ≅ᴵ a′ → a′ <ᴵ natᴵ m → j < m`；`natᴵ a ≅ᴵ natᴵ b → a ≡ b`；`j ≅ᴵ natᴵ a → j ≡ natᴵ a`；`j < m → Σ s (levN m s ≡ j)` | 把 `<ᴵ-dec` 的三种结果读成 ℕ 上的三歧 | Rel | 编译定理 |

#### 4 办法

上一轮回报 §5 指出的三处卡点，各自这样解决：
- **(a) 变量层号上 `wayᵇ` 不化简（已解决）。**
  - 我定义了 `KO`：把派发结果 `keep s e` 读成 `nodeAt`。它是一个函数，结点层号在里面是变量，所以可以对 e 用 J，不需要 `lev` 定义性相等。
  - `stepˢ` 的两种情况各成为一条对变量层号成立的方程：`KO-top` 用 `eqᶠ-fin`，`KO-below` 用新证的 `eqᶠ-ne`。
  - 对槽位归纳得到 `way-slot`，再合成 `TREE-KEEP`。保留结点用 `nodeA` 造，它沿 `shS` 递归，下界直接在 `Raw (fin j)` 里。
  - 折叠的情况由 `way-fold` 给出 `TREE-FOLD`。
- **(b) `Low (fin N) r` 不能当作 `Raw` 用（已解决）。**
  - 槽位关系 `RelL (suc N) = SL`：`inj₁` 交给 `Rel N`，`inj₂ r` 交给 `RelL N r`。它对槽位递归，与 `Low` 同步化简。
  - 第 N+1 层的数据类型 `Lv._⊴_` 以第 N 层的关系为参数，所以能过正性检查。
  - `WALKN`、`WALKF` 沿 `upN` 对槽位递归，走到 `inj₁` 时就是一个下界在 `Raw (fin j)` 里的结点。
  - 加法里嵌入的深度是变量，引理对带关系的值域 `RA A` 来写；`shRA` 下移一层时，投影是定义性的。
  - 没有用 `toRaw`、`fromRaw`。
- **(c) 缺对 M 一致的关系族和派发引理（已解决）。**
  - `Rel M` 一个定义给出一切 M（第 0 层是 `R0`）。
  - 参照一侧结点的层号只要求 `≅ᴵ` 于槽位的层号，因为穿透之后结点挂在 `via` 给出的代表元上。保留的分支要经过一次 `tr⁻ e`，由 `TRC-all` 吸收；它的结点情况经 `back (res⁻ q e)` 用到低一层的封闭性。
  - 目标层 0 也用 `ψ p σ` 来陈述，所以 `FOLD` 不需要 `x ≅ x`。只在接口的 `lower` 字段里，用 `ψ⁰≅ψ` 换成 `ψ⁰`。

#### 5 第一个障碍

没有障碍，也没有碰到停下的条件。编译中只遇到语法错误：telescope 里漏写 `∀`、`L.back` 要写成 `L.Restr.back`、`open Lv` 造成构造子名字歧义。每处改一次就过了。

#### 6 偏离与事故

- **跳过了第 1 步的 M = 3 探针**（简报允许）。没有写临时实验文件。
- **入口依赖上一轮的接口：** 入口直接用 `YiLvValBase.Interface` 和 `YiLvValFin.AllLevels`，没有改动它们；因此依赖链经过 `YiLvVal3`。
- **一处自己改掉的错：** 写 `YiLvAllRel` 时，我先写了一段错误的 `TR0` 和一句解释文字，编译前已经替换成正确写法，最终文件里没有残留。
- **没碰的：** 没改任何已有文件（包括 README、LOG、RESULTS、AGENTS），没碰 `src/`、`archive/`，也不依赖 `YiOmFold`、`YiOmNeg`、`YiPsum`、`YiRawVal` 的文件。只删过我自己模块的 5 个 `.agdai`，没有提交。
