# 有限层号闭项的值下界 (YiLvVal)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-10 23:59 至 00:43 |
| 工具调用 / agda 编译 (粗数) | 42 / 11 |
| token (usage 字段，按消息去重) | 输出 269627；新写入缓存的输入 1266127；读缓存的输入 9264487；其余输入 80 |
| 写过的仓库文件 | `YiLvVal2.lagda.md`, `YiLvVal3.lagda.md`, `YiLvValBase.lagda.md`, `YiLvValFin.lagda.md` |
| 文件前缀 | `YiLvVal` (在 `probes/OCF/Align/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 值下界一路返回并复核; 三路结清 (主审)” 一节 |
| 主审复核后的一句结论 | 上一轮的折叠的闭项：n ≤ 3 的下界是定理，一切有限 n 与 ω 是条件定理；没有发现掉值；五件冷编退出码全 0 (YiLvVal3 用 6G) |

## 简报原文

你是这个 Agda 研究仓库 (<仓库> = <仓库>) 的一路执行方, 任务是 "给乙线有限层号一站的闭项补值的下界定理". 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

### 0 先读什么

1. `AGENTS.md` 全篇. 特别是: 纲领四条; "用记号验收强度" 与 "中间站给界, 终点对 EBO 验收" (序数值验收; 中间站给下界即可); Agda 一节 (选项, 文字预算, 退出码, 堆; Funext 只准作前提); "结论的写法" (三档; 前提要可满足).
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 (编译与内存, 堆墙的对策) 与 §5.4.
3. 代码 (都在 `probes/OCF/Align/`, 模块名 `OCF.Align.<名>`; 都已定稿, 可以导入, 不许编辑):
   - **你要照着做的范例 `YiIrrFbValue`** (验收文件, 445 行): `Ω₂-lower : L.ψ⁰ (L.Ω 2) ≼ read (ψ₀ Ω₂ dom-Ω₂)`. 办法: 跨两族的逐点前序 `_⊴_` (`Level` 族第 0, 1 层的树对 `Raw 1` 的值), 它对加前缀, 加法, 目标层 1 的折叠封闭 (`Ψ₁⊴Φ`); 结点处的一步定理 `NodeLower.node-lower` (参照用原链, 被验收一侧用加法链, 同步归纳); `fold-lower` 把关系送到值前序. 先把这个文件读懂. 更早的范例 `YiIrrFoldValue` (`read`, `read-add`, `read-copies`, 目标层 0 的同值).
   - **被验收的对象**: `YiLvFoldFin` 的 `foldᶠ n = ψ zero (Ω̂ (fin n)) (dom-Ωᶠ n)` (读法 ψ₀(Ω_n)) 与 `fold-Ωω = G.lim foldᶠ` (读法 ψ₀(Ω_ω)); 折叠的定义在 `YiLvFold` (模块 `Fold`, `open Fold wayᵇ` 在 `YiLvFoldFin` 里), 加法在 `YiLvFoldAdd` (`plus`, `copies`, `successor`, 值域接口 `Alg`), 结点与链在 `YiLvFoldBase` (`nodeAt`, `Chain`). 有限层号上派发完全且不多保留是定理 (`complete-fin`, `sound-fin`, `keep-fin`). 注意它与 `YiIrrFb` 的写法有两处不同: 加法是对层号一般的 `plus`, 不是 `_+ʳ_`, `_+¹_`; 第 0 层的 ω 倍从一份起 (`copies m y 0 = y`).
   - 块: `RR5IrrCore`, `RR5IrrCheck` (`up`, `Ω̂`, `tw`), `YiIrrIf`.
   - 参照一侧: `OCF.Align.Level` (`Ordᶜ`, `ψ⁰`, `Ω`, `limᵢ`), `OCF.Align.Value` (值前序 `≼`), `OCF.Align.RR4MonoFragment`; `Level` 族上折叠的单调引理在 `K4MonoFold`, `K4MonoValue` (`ψ-⊑`, `ψ⁰-monoᵖ`), 可能在参照一侧用得上.
   查签名用检索, 大文件不要整篇读.

### 1 这一步是什么, 为什么要做

乙线上一轮做成了一套对层号参数化的折叠, 有限层号一站的闭项对一切 n 合法. 但上一轮同时得到一条编译事实: **输出合法对任意派发都成立, 所以闭项合法不携带强度信息**. 有限层号一站的强度目前只有 "派发完全且不多保留" 的定理与读法, 没有对参照树的值定理. 作者 2026-11-11 定: 给它补值的下界定理. 做成后, "ψ₀(Ω̂ (sucⁿ 0)) 不低于参照的 ψ₀(Ω_n)" 才是定理而不是读法.

只要下界 (参照 ≼ 读回的闭项), 不要上界, 不要同值.

### 2 目标, 分步; 每步先交再往下

1. **n = 1.** `L.ψ⁰ (L.Ω 1) ≼ read (foldᶠ 1)`. 这是把 `YiIrrFoldValue` / `YiIrrFbValue` 的第 0 层部分搬到 `YiLvFold` 的定义上 (加法与 ω 倍的写法不同), 最便宜, 先做.
2. **n = 2.** `L.ψ⁰ (L.Ω 2) ≼ read (foldᶠ 2)`. 对照 `Ω₂-lower`; 这一步检验范例的办法在新定义上是否原样可用.
3. **一切有限 n.** `∀ n → L.ψ⁰ (L.Ω ⟨n⟩) ≼ read (foldᶠ n)`, 其中 `⟨n⟩` 是 `Level` 族里第 n 层的下标 (怎么写按 `Level` 的定义来). 需要把逐点前序推广到 "`Level` 族第 0 到 n 层的树对 `Raw (fin n)` 的值", 对一切层号的加法与一切有限目标层的折叠封闭. 这是本任务的主体.
4. **ω.** 由第 3 步得 `fold-Ωω` 不低于每个 ψ₀(Ω_n) 的参照 (`fold-Ωω ≡ G.lim foldᶠ` 是 `refl`); 若 `Level` 族里有 ψ₀(Ω_ω) 的参照树并且它是各 ψ₀(Ω_n) 参照的极限, 再给 `参照 ≼ read fold-Ωω`.

部分进展也算: 做到第 2 步就已经是可以汇报的结果.

**停下的条件.** 遇到下面任一种就停, 交已有的文件与约化, 不硬攻:
- 第 3 步的推广需要范例里没有的新机制, 并且同一处两次重新设计仍过不了检查器;
- 需要 Funext 或 K 才能证 (Funext 作显式前提的条件定理可以交, 但要另给不带它的最强结果);
- 堆到 6G 仍耗尽 (先按手册 §4.2 的对策: 陈述逐字写, 大参照树放 `opaque`, 隐式参数显式写出).
约化的意思: 把缺的引理写成带确切 Agda 类型的陈述 (模块参数), 其余在这个前提下条件地证出来并编译; 说明前提在 n = 1, 2 上是定理.

不要为了让值定理好证而改折叠: 被验收的对象就是 `YiLvFoldFin.foldᶠ`. 发现它的值低于读法 (例如某一步其实掉值), 那是重要结果: 写成编译过的定理交回, 不要自己修.

### 3 规则

- **只新建文件**, 前缀 `YiLvVal` (如 `YiLvValBase`, `YiLvVal1`, `YiLvValFin`), 放 `probes/OCF/Align/`, 中文 literate Agda (`.lagda.md`). 这些都是验收文件, 文首标 "验收文件"; 允许导入带记号闭包的 `Value` 与旧验收文件. 不改任何已有文件 (含 README, LOG, RESULTS, AGENTS), 不碰 `src/`, `archive/`. 同时在跑的另两路用前缀 `YiRawFold`, `YiRawNeg`, 不要动它们的文件, 也不要依赖它们.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. Funext 只准作显式前提, 用到它的定理在文首标 "条件".
- **文字预算** (AGENTS Agda 一节): 每个模块文首不超过 5 行 (判决与档位, 做了什么, 不否定什么, 入口指向); 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件; 编译表不进文件. 一次性的试验放你的临时目录, 用纯 `.agda`.
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Align/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Align/<精确模块名>.agdai`, 写精确名字, 不用通配). 第一次编译会连带检查 `Level`, `Value` 等依赖的接口是否已有; 不要重编别人的模块.
- 你的临时目录: `<实验目录>/agents/lvval`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几步, 一段话说对纲领与目标意味着什么 (哪些读法变成了定理, 哪些仍是读法).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 条件定理写出前提的 Agda 类型.
4. 办法: 逐点前序怎么推广的; 哪些引理是从范例原样搬的, 哪些是新的.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
强度写 ψ₀(Ω_x), 标明是定理还是读法; 下界不写成同值; 不用 "只差", "自然" 一类形容.

## 回报原文

我做完了第 1、2 步，另做了 n = 3 (属于第 3 步)。一般的 ∀ n 与 ω 只是条件定理：前提 "对一切 M 有 `Interface M`" 只对 M ≤ 2 证了，一般的没证。我在 n = 3 之后按判断停下，没有正式碰到停下条件 (见 5)。

#### 1 判决

n = 0, 1, 2, 3 时，"`ψ₀ (Ω̂ (sucⁿ 0))` (即 `foldᶠ n`) 不低于参照的 ψ₀(Ω_n)" 现在是编译定理 (下界，不是同值)。n ≥ 4 仍是读法，只有条件定理 `AllLevels.lower-fin`。

`fold-Ωω` 的编译定理是不低于 ψ₀(Ω₃) (`Ω₃≼fold-Ωω`)；"不低于 ψ₀(Ω_ω)" 是条件定理 (`AllLevels.lower-ω`)。

对纲领：
- 新文件都是验收文件，没有新定义。
- 没有改折叠：被验收的就是 `YiLvFoldFin.foldᶠ` 本身。
- n = 3 时目标层 1 上要折叠层号 1 的结点，范例 (`YiIrrFbValue`) 没有这一处。范例的办法在这里没有重新设计就过了。
- 没有发现 `foldᶠ` 哪一步比读法掉值。

#### 2 文件表

每个文件只删自己的 `.agdai` 后冷编译，日志里只有本模块的 `Checking` 行。

| 文件 | 代码行 / 总行 | 退出码 | 常驻内存峰值 (`-M6G`) |
|---|---|---|---|
| `probes/OCF/Align/YiLvValBase.lagda.md` | 127 / 187 | 0 | 1.18G, 6s |
| `probes/OCF/Align/YiLvVal2.lagda.md` | 292 / 371 | 0 | 1.60G, 8s |
| `probes/OCF/Align/YiLvVal3Base.lagda.md` | 333 / 401 | 0 | 3.56G (GC 驻留 1.5G), 14s |
| `probes/OCF/Align/YiLvVal3.lagda.md` | 246 / 293 | 0 | 6.59G (GC 驻留 4.13G), 29s |
| `probes/OCF/Align/YiLvValFin.lagda.md` | 25 / 40 | 0 | 1.22G, 6s |

检索 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`--irrelevant-projections`、`--cubical` 都是 0 处；Funext 唯一的命中是正文 "没有 Funext"。各文件的选项行都是 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。

#### 3 定理表

下文 `⟨ n ⟩ = L.natᴵ n` (`Level` 族第 n 层的下标)，`Ψ M = L.ψ {i = ⟨ M ⟩} {k = ⟨ M ⟩} {ℓ = L.suc ⟨ M ⟩} L.zero (λ q → L.suc q)` (参照一侧目标层 M 的折叠)。

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `lower₀` | `L.ψ⁰ (L.Ω ⟨ 0 ⟩) ≼ read (foldᶠ 0)` | 不低于 ψ₀(Ω₀) | Base | 编译定理 |
| `lower₁` | `L.ψ⁰ (L.Ω ⟨ 1 ⟩) ≼ read (foldᶠ 1)` | 不低于 ψ₀(Ω₁) | Base | 编译定理 |
| `lower₂` | `L.ψ⁰ (L.Ω ⟨ 2 ⟩) ≼ read (foldᶠ 2)` | 不低于 ψ₀(Ω₂) | Val2 | 编译定理 |
| `lower₃` | `L.ψ⁰ (L.Ω ⟨ 3 ⟩) ≼ read (foldᶠ 3)` | 不低于 ψ₀(Ω₃) | Val3 | 编译定理 |
| `Ω₃≼fold-Ωω` | `L.ψ⁰ (L.Ω ⟨ 3 ⟩) ≼ read fold-Ωω` | `fold-Ωω` 不低于 ψ₀(Ω₃) | Fin | 编译定理 |
| `reference-ω-row` | `L.ψ⁰ (L.Ω L.ωᴵ) ≡ L.lim (λ n → L.ψ⁰ (L.Ω ⟨ n ⟩))` | ω 的参照是各有限参照的极限 (`refl`) | Fin | 编译定理 |
| `reference-row` | `∀ M → L.ψ⁰ (L.Ω ⟨ suc M ⟩) ≡ L.lim (λ i → L.ψ⁰ (γ M i))` | 参照的链 (`refl`) | Base | 编译定理 |
| `FromInterface.theorem` | `L.ψ⁰ (L.Ω ⟨ suc M ⟩) ≼ read (foldᶠ (suc M))`，模块参数 `(M : ℕ) (I : Interface M)` | 第 M 层有接口，则 M+1 有下界 | Base | 条件定理 |
| `AllLevels.lower-fin` | `∀ n → L.ψ⁰ (L.Ω ⟨ n ⟩) ≼ read (foldᶠ n)`，模块参数 `(I : ∀ M → Interface M)` | 一切有限 n | Fin | 条件定理 |
| `AllLevels.lower-ω` | `L.ψ⁰ (L.Ω L.ωᴵ) ≼ read fold-Ωω`，同一前提 | 不低于 ψ₀(Ω_ω) | Fin | 条件定理 |
| `interface₀/₁/₂` | `Interface 0`, `Interface 1`, `Interface 2` | 前提在 M = 0, 1, 2 上成立 | Base / Val2 / Val3 | 编译构造 |

前提是下面这个记录 ("接口"：链点之间的一个关系，带四条性质)：
```agda
record Interface (M : ℕ) : Set₁ where
  field
    Rel : L.Ordᶜ ⟨ M ⟩ → Raw (fin M) → Set
    start : Rel (L.Ω ⟨ M ⟩) (cO (fin M))
    step : ∀ {x η} → Rel x η → .(nb : Nested (fin M) η) →
      .(d : Dom (up (fin M) η nb)) → Rel (Ψ M x) (ψ (fin M) (up (fin M) η nb) d)
    absorb : ∀ θ {x η} → Rel x η → Rel x (plus (fin M) θ η)
    lower : ∀ {x η} → Rel x η → x ≅ x → .(nb : Nested (fin M) η) →
      .(d : Dom (up (fin M) η nb)) → L.ψ⁰ x ≼ read (ψ B.zero (up (fin M) η nb) d)
```
前提可满足：`interface₀/₁/₂` 是实例。"对一切 M" 没有证。

#### 4 办法

- **分解 (新)。** `FromInterface` 把范例 §5 的两条链同步推广到任意 M。`foldᶠ (M+1)` 的链每步是 "目标层 M 的折叠，再加前缀"，观察是目标层 0 的折叠。所以一切有限 n 归约到 `Interface M`。
- **第 0 层 (新，Base)。** `read-plus`、`read-copies`、`suc-lower` 是对 `plus` 与 `copies` (第 0 项一份) 写的。`one≼fold` 对一切树成立：链行的第 0 项是下界那一支。
- **n = 2 (Val2)，从 `YiIrrFbValue` 搬。** 多数引理与范例同形：`⊴-embed`、`em-shift`、`add-em`、`⊴-add₀/₁`、`⊴-+ˡ`、`Ω⊴Φ`、`suc-step`、`Ψ₀⊴Φ₀`、`Ψ₁⊴Φ`、`NodeLower`、`fold-lower`。两处不同：
  - 证据全是无关参数 (`ψ` 的定义域参数本来就无关)。
  - 关系 `_⊴_` (跨两族的逐点前序) 里，"压在第一支之下" (`⊴t`) 换成 "压在下界那一支之下" (`⊴b`)。范例的写法要用 `ψ-position`，它的定义域参数是相关的。
  - 分支前提只要无关的守卫，所以链不需要 `ChainLegal` 的相关守卫。
- **n = 3 新加的部分。**
  - `_⊴₂_`，第 2 层的关系：槽位 `inj₁ tt` 放层号 1 的结点，槽位 `inj₂ (inj₁ tt)` 放层号 0 的结点。参照一侧结点的字面证明 `q` 取一般的，因为加法会把 `q` 换成 `σ q`。
  - `ADD₀/₁/₂`：对一般 `σ` 的加法。`out-into` 只是命题相等，所以要一次 `subst`。
  - `TR₀/TR₁`：对 `tr⁻ (s≅ z≅)` 封闭；需要它是因为目标层 2 穿透层号 1 的结点。
  - `B₀/₁/₂` (目标层 2)、`C₀/₁/₂` (目标层 1)、`D` (目标层 0) 都取一般的 `p`, `σ`。参照一侧的派发用 `with <ᴵ-dec (σ q) p` 分情况；层号不合的情况由 `<ᴵ`, `≅ᴵ` 的空模式排除。
  - 新机制是 `C₂` 与 `D` 的 `nd1`/`nt₂` 两个情况：`Chain1` 在第 1 层上跑两条链。每步是 `C₂` 自己 (`p = q`, `σ = id`)，前缀由 Val2 的 `⊴-+ˡ` 吸收。
  - `C₁` 是范例 `Ψ₁⊴Φ` 推广到任意 `p`, `σ`。
- **成本增长 (判断，测到 n = 3)。** `Interface M` 对每个目标层 m ≤ M 要一族引理，再乘上每个嵌入深度。M = 2 时是 3 个目标层 × 最多 3 个深度。

#### 5 第一个障碍 (一般的 M)

我没有正式碰到停下条件 (同一处两次重新设计仍过不了检查器)。做完 n = 3 后我判断工作量太大，没有写对 M 一致的版本。两个临时探针 (纯 `.agda`，放在我的临时目录，不进仓库) 确认了检查器卡在哪里：

- **(a) 树一侧的派发在变量层号上不化简。** `wayᵇ (fin 2) (fin 1) ≡ keep (inj₁ tt) refl` 是 `refl`；但 `∀ N → wayᵇ (fin (suc N)) (fin N) ≡ keep (inj₁ tt) refl` 报错：
  `stepˢ (eqᶠ (fin N) (fin N)) (wayᵇ (fin N) (fin N)) != keep (inj₁ tt) refl of type Way (fin (suc N)) (fin N)`
  顶槽位可以用 `eqᶠ-fin` 改写来修。低槽位要 `ψn` 化简，需要字面的 `keep s refl`，也就是 `lev (fin m) s` 与结点层号定义性相等；`lev-slotᶠ` 只是命题相等，所以只能把结点层号作为变量用 J 消去。
- **(b) 变量槽位的下界类型。** 检查器不接受把 `Low (fin N) r` 当作 `Raw (lev (fin N) r)`：
  `Low (fin N) r !=< G.R (Pre (lev (fin N) r)) (Low (lev (fin N) r)) ...`
  所以变量槽位上的结点构造子不能直接沿用第 j 层的关系，要么对槽位递归定义关系，要么沿 `Low-lev` 搬运。
- **(c) 缺的引理 (未做)。** 一是对 M 一致的关系族 `Rel : (M : ℕ) → ∀ {k} → L.Ordᶜ k → Raw (fin M) → Set`，连同 `∀ M → Interface M`。二是 `natᴵ` 层上 `<ᴵ-dec` 的派发引理：`natᴵ j ≅ᴵ natᴵ m → j ≡ m`，以及 `natᴵ m` 之下字面证明的分类。
- **(d) 嵌入深度 (判断，未测)。** `shS A` 的投影对变量 `A` 也定义性化简，所以对 `Alg` 一般地陈述、带一个关系记录的加法引理，应能处理变量深度 `shSᵈ`。

#### 6 偏离与事故

- **多拆了一个文件。** `YiLvVal3` 原来是一个文件：`-M4G` 时堆耗尽 (退出 251)，`-M6G` 时 GC 驻留 5.4G，所以拆成 `YiLvVal3Base` 和 `YiLvVal3`。现在 `YiLvVal3` 单独是驻留 4.13G、常驻内存 6.59G。复核请用 `-M6G` 冷编译，不要更低。
- **简报没要求的：** n = 0 (`lower₀`) 和 n = 3。
- **没动的：** 没改任何已有文件，没碰 `src/`、`archive/`。不依赖 `YiRawFold`、`YiRawNeg` 的文件，没有提交。
- **编译警告：** Val3 第一次编译报了 5 个不可达的 `with` 子句，删掉后重编通过。
