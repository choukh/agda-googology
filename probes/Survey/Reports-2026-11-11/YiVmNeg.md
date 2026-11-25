# 值单调，否定路 (YiVmNeg)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | high |
| 起止 (转录的时间戳，UTC) | 2026-11-11 08:59 至 09:29 |
| 工具调用 / agda 编译 (粗数) | 45 / 13 |
| token (usage 字段，按消息去重) | 输出 177894；新写入缓存的输入 409310；读缓存的输入 6851285；其余输入 70 |
| 写过的仓库文件 | `YiVmNegBase.lagda.md`, `YiVmNegBound.lagda.md`, `YiVmNegChain.lagda.md`, `YiVmNegIrr.lagda.md`, `YiVmNegSeg.lagda.md` |
| 文件前缀 | `YiVmNeg` (在 `probes/OCF/Align/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 值单调的否定路返回并复核; 证与否定两路的合读 (主审)” 一节 |
| 主审复核后的一句结论 | 那条值单调本身没有否定；保初始段的嵌入推出 LPO；不读推导的写法推出 Markov 原则；探针严格；链上的陈述足以推出 BTBO 下界；五件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 任务是 **对参照框架 (Level 族) 上的一条值单调性 `VMᴸ` 及其证法写否定**: 判定它 (或它的某种证法) 是否推出 LPO, WLPO 一类的全知原则, 或在什么量化域上有反例. 另有一路 (前缀 `YiVmCon`) 同时在证同一个陈述; 你们共用的陈述在已定稿的 `OCF.Align.YiMonoVM` 里, 谁也不改它. 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇. 特别是 "承认壁垒定理" 与 "交替路线" 两段 (已知的全知型后果: `dec→WLPO`, `Trich₂→WLPO` 等), "量化域先取带证据的读回域" (反例对象不在规范构造的读回域内的否定, 读作 "谓词太宽", 不读作数学障碍; 退化结点: 常值极限等), "律带公共上界, 构造与否定配对", Agda 一节, "结论的写法" (否定要有编译定理, 且定理否定的确实是这条路线; 前提要可满足; 归到已知的墙要逐条核机制).
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 与 §5.4.
3. **上一路的回报原文, 全读**: `probes/Survey/Reports-2026-11-11/YiMono.md` (§3 的陈述, §4 (甲) 说的左极限一致性与 "保初始段" 的嫌疑).
4. 代码 (在 `probes/OCF/Align/`, 模块名 `OCF.Align.<名>`; 都已定稿, 可以导入, 不许编辑):
   - **陈述所在 (共用接口)**: `YiMonoVM`. 逐字:
     ```agda
     VMᴸ : Set
     VMᴸ = ∀ (x : L.Ordᶜ L.zero) (hx : L.HS x) (y : L.Ordᶜ L.zero) (hy : L.HS y) → x ≼ y →
       L.ψ⁰ (L.Ω (L.toLevel x hx)) ≼ L.ψ⁰ (L.Ω (L.toLevel y hy))
     Crux : Set   -- 与 VMᴸ 同形, 结论两边的层号各套一个 L.suc
     EmbV : Set
     EmbV = ∀ x hx y hy → x ≼ y → PEmb (L.toLevel x hx) (L.toLevel y hy)
     crux→vm : Crux → VMᴸ ;  embV→vm : EmbV → VMᴸ
     ```
   - 前驱嵌入: `BTBOFullEmb` (记录 `PEmb a b`: 字段 `map`, `bnd`, `mono`, `coh`; `Ψ-emb`), `YiMonoEmb` (`PEmb-suc`, `PEmb-limˡ`, `PEmb-limʳ`, `ω-not`, `ω-inst`), `YiMonoBreak` (结构可比的证法的否定是怎么写的, 可作体例).
   - 参照框架: `OCF.Align.Level` (`Ordᶜ`, `Ordᴵ`, `ψ⁰`, `Ω`, `HS` (`hz`, `hs`, `hl`: 极限处相邻两项只要 `⊑⁰`, 不要求严格), `toLevel`, `_⊑ᴵ_`, `_≅ᴵ_`, `_<ᴵ_`, `<ᴵ-dec`), `OCF.Align.Value` (值的前序 `≼` 是归纳定义的, 推导带数据: `z≼`, `s≼s`, `≼l n d` (选了下标 n), `l≼`).
   - 全知原则与体例: `LPO`, `WLPO` 的定义在 `BrwViewNeg`, `DomFoldNeg` 等文件里各有一份 (检索 `^LPO : Set`), 用哪一份都行, 写明; 探针与归约的写法看 `BrwViewNeg` (`strict→LPO`), `YiOmNegBranch` (`top-branch→lpo`), `YiGenNegWall` (`chain→weak-eq`), `probes/OCF/Barrier.lagda.md`.
   - 已知的反面证据: `RR4MonoFragment` (`mono-fragment-not-cong`: 一般的第 1 层树上 ψ⁰ 不是值单调的), `K4MonoNeg`.
   查签名用检索, 大文件不要整篇读.

#### 1 问题是什么

`VMᴸ` 说: 两个带证书的可数序数 x, y, 值上 x ≼ y 时, ψ₀(Ω_x) ≼ ψ₀(Ω_y). 它是乙线的值与 BTBO 持平还缺的一环 (与树无关的那种写法). 上一路的判断 (都未编译): 它在经典意义下成立; 构造性地由 `x ≼ y` 的推导造前驱嵌入时, 左极限处要各段嵌入互相一致; 要求嵌入 "保初始段" 来得到一致时, 后继情形要定位前驱, 疑似推出 LPO 一类的原则.

注意两件事. (1) `≼` 的推导带数据 (`≼l n d` 记着下标), 所以 `VMᴸ` 的前提不是一个纯命题; 这对 "由它抽出判定" 既可能有利也可能不利, 要具体看. (2) `HS` 允许极限处相邻两项相等 (常值或最终常值的极限); 用这类退化对象的反例按规则只说明量化域太宽.

#### 2 目标, 分项; 每做成一项先交. 每一条写明否定的是什么, 不否定什么

N1. **`VMᴸ` 本身.** 它是否推出某条全知原则 (`VMᴸ → WLPO` 一类), 或有没有编译的反例 (具体的 x, hx, y, hy, 推导 `x ≼ y`, 与结论的否定). 结论的否定要证 `≼` 的不成立, 先找仓库里现成的 `¬ (_ ≼ _)` 的工具. 若做不出, 说明第一个障碍; 若你反而发现 `VMᴸ` 能证, 把证明思路写进回报 (不要去写另一路的文件).
N2. **证法的否定.** 把上一路的嫌疑做成定理或撤掉:
   - "保初始段的 `EmbV`" (把 "保初始段" 写成明确的记录; 例如嵌入的像向下封闭, 或嵌入与取前驱交换) 是否推出 LPO / WLPO. 探针取与一个布尔序列有关的 x, y (例如 y = suc (lim g), g 由 α 决定), 推导 `x ≼ y` 对一切 α 一致地给出.
   - 一般的 `EmbV` (不要求保初始段) 是否推出什么: 嵌入是函数, 像里含着 "x 的前驱落在 y 的哪个前驱上" 的选择.
   - "嵌入只依赖 (x, y), 不依赖推导" 这种更强的要求是否推出什么.
N3. **量化域.** 对 N1, N2 里每条成立的否定, 检查探针是不是退化对象 (最终常值的极限, 相邻两项相等). 若是, 把探针换成严格递增的再证一次; 换了之后还成立与不成立都要写成编译事实. 再检查: BTBO 的对角链 `D.γ n` (`OCF.Align.Diagonal`) 与旧树链点的读回 (`YiMonoVM.HS-read`) 在不在你的否定的定义域里; 给出一个把它们包含在内, 且你的否定不适用的子域的陈述 (供构造路用).
N4. **正面的边界.** 哪些情形明确不碰任何原则 (例如 x, y 都是有限的, 或层号结构可比, 或两边的层号有可判定的三歧 `<ᴵ-dec`): 写成定理.
N5. **挑战.** 对你自己的每条否定, 找一个绕过它的陈述的弱化 (例如把结论弱化成双重否定, 把嵌入换成关系), 说明弱化后是否仍够推出 `VMᴸ`.

**前提的可满足性.** 每条 "X → LPO" 的 X 要么给一个实例 (可以在一个显式的神谕前提下), 要么说明它为何可满足; 前提矛盾的定理什么也没说. 归到已知的墙 (壁垒定理, `dec→WLPO` 等) 之前逐条核机制, 形状相似不算.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K (可交显式前提的条件定理, 另给不带它的最强结果); 堆到 6G 仍耗尽. 没有编译的否定定理时, 只能写 "没有找到否定", 不能写成成立或不成立.

#### 3 规则

- **只新建文件**, 前缀 `YiVmNeg`, 放 `probes/OCF/Align/`, 中文 literate Agda (`.lagda.md`). 都是验收文件, 文首标 "验收文件"; 允许导入带记号闭包的 `Value`, `Level` 与旧验收文件. 不改任何已有文件 (含 `YiMonoVM`, README, LOG, RESULTS, AGENTS), 不碰 `src/`, `archive/`. 同时在跑的另两路用前缀 `YiVmCon` (同目录), `YiLeanVal` (在 `probes/OCF/Lean/`), 不要动也不要依赖它们的文件.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提, 用到它的定理在文首标 "条件".
- **文字预算**: 每个模块文首不超过 5 行 (判决与档位, 做了什么, 不否定什么, 入口指向); 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Align/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Align/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块.
- 你的临时目录: `<实验目录>/agents/vmneg`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 一段话说对纲领与目标意味着什么 (`VMᴸ` 本身有没有否定; 哪种证法被否定; 否定的量化域含不含 BTBO 的对角链).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 每条否定写明: 否定的是哪种写法, 不否定什么, 探针是不是退化对象, 前提的实例.
4. 正面的结果 (对构造路有利的): 不碰任何原则的子域.
5. 没写成的条目与第一个障碍.
6. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 回报原文

#### YiVmNeg 回报：`VMᴸ` 及其证法的否定

##### 1 判决

- **`VMᴸ` 本身没有否定。** 我没有找到推出全知原则的定理，也没有编译的反例。这里只能写 "没有找到否定"，不写成立或不成立。
- **两种证法被否定了，都是编译定理。**
  - **(甲) 保初始段的嵌入推出 LPO** (`embVᴰ→LPO`)。所谓保初始段：嵌入的像向下封闭。
    - 只限严格的树 (`SHS`) 时仍推出 LPO；向下封闭只要双重否定，或只要求在顶的像之下封闭，也都推出 LPO。
    - 在探针族上，这种嵌入的存在与 LPO 等价 (`seg↔LPO`)。
  - **(乙) 不读推导的写法推出 Markov 原则。** 把 `VMᴸ` 的前提从带数据的推导换成 `¬¬ (x ≼ y)`，得 `VM¬¬ → MP`；换成无关参数 `.(x ≼ y)`，得 `VMⁱ → MPⁱ`。
    - 探针族上的命题与 MP 等价。
- **探针都是严格的，不是退化对象。** 每个极限的相邻项严格上升，有编译事实 `probe-strict`。所以这两条否定不能读作 "谓词太宽"。
- **对构造路的意思。** 构造路要用普通的前驱嵌入 (`PEmb`，不要求初始段)，并且必须读 `x ≼ y` 推导里的数据。
  - 两组探针族上都有一致的普通嵌入与 `VMᴸ` 的实例：`probe-emb`/`probe-vm`，`emb-rel`/`vm-rel`。所以否定不碰原写法。
- **否定的量化域含不含 BTBO 的对角链。** 否定针对的是对一切 HS 树的全称陈述，用的探针是布尔序列族。
  - 只在链上要的子域陈述 `VMᶜʰ` (`D.γ n` 对 `read (coordᵐ (pointsᵐ n))`) 不被否定。`VMᶜʰ` 已经足以推出 BTBO 下界 (`ch→btbo`，条件定理)。
  - 链点不在 "公共上界" 那个正面子域里 (`no-bound-pt`)。
- **对纲领的意思。** 这与 "律带公共上界" 一致：两个层号有字面公共上界时，值序退化成结构序，保初始段也无害 (`bound-⊑`)。全知原则只出现在两种写法里：要求嵌入精确到值 (初始段)，或丢掉推导里的数据。

##### 2 文件表

都在 `probes/OCF/Align/`，都是验收文件。冷编译时删了全部五个自己的 `.agdai`，按依赖顺序逐个编译，每份日志只有本模块一行 `Checking`。

| 文件 | 代码行 / 总行 | 冷编译退出码 | 常驻峰值 |
|---|---|---|---|
| `YiVmNegBase.lagda.md` | 185 / 264 | 0 | 1.08G |
| `YiVmNegSeg.lagda.md` | 106 / 178 | 0 | 1.28G |
| `YiVmNegIrr.lagda.md` | 82 / 145 | 0 | 1.33G |
| `YiVmNegBound.lagda.md` | 64 / 95 | 0 | 1.42G |
| `YiVmNegChain.lagda.md` | 57 / 84 | 0 | 1.36G |

- 选项行都是 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。
- 检索 `postulate`、洞、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`--irrelevant-projections`、`--cubical`、`Funext`、本机路径，都是 0 处。
- 用到了无关参数 (`.( … )`) 与 `⊥-irr : .⊥ → ⊥` 的空模式，这是作者 11-10 允许的写法。
- 日志在 `<实验目录>/agents/vmneg/cold-*.log`。

##### 3 定理表

`LPO` 用的是 `OCF.Barrier` 那一份：`(α : ℕ → Bool) → (Σ[ k ∈ ℕ ] α k ≡ true) ⊎ (∀ k → α k ≡ false)`。`MP`、`MPⁱ` 定义在 `YiVmNegIrr`。

**两组探针** (定义在 `YiVmNegBase`)：

- **`Y α`**：等于 `lim (λ n → hb (seen α n) n)`。第 n 项在 α 到 n 都假时是 n，否则是 ω+n。所以 α 全假时值 ω，否则值 ω·2。
- **(甲) 用的一对**：`xP = suc ωᶜ` (即 ω+1)，`yP α = suc (Y α)`。
- **(乙) 用的一对**：`xI = suc ωᶜ`，y 取 `Y α`。

**YiVmNegSeg：保初始段的嵌入**

| 名字 | 陈述 (逐字) | 白话 | 档 |
|---|---|---|---|
| `embVᴰ→LPO` | `EmbVᴰ → LPO`，其中 `EmbVᴰ = ∀ x hx y hy → x ≼ y → PEmbᴰ (toLevel x hx) (toLevel y hy)` | 保初始段的嵌入推出 LPO | 编译定理 |
| `embVᴰˢ→LPO` | `EmbVᴰˢ¬¬ → LPO` (只限 `SHS` 的树，向下封闭取双重否定) | 弱化之后仍推出 LPO | 编译定理 |
| `seg→LPO` | `SegP → LPO`，`SegP = ∀ α → PEmbᴰ¬¬ (toLevel xP hxP) (toLevel (yP α) (hyP α))` | 只用到这一个探针族 | 编译定理 |
| `LPO→seg` | `LPO → ∀ α → PEmbᴰ (toLevel xP hxP) (toLevel (yP α) (hyP α))` | 前提在 LPO 神谕下可满足 | 编译定理 |
| `seg↔LPO` | `(SegP → LPO) × (LPO → SegP)` | 探针族上与 LPO 等价 | 编译定理 |
| `probe-strict` | `SHS xP × (∀ α → SHS (yP α))` | 探针不退化 | 编译定理 |
| `probe≼` | `∀ α → xP ≼ yP α` | 值序对一切 α 一致成立 | 编译定理 |
| `probe-emb`, `probe-vm` | `∀ α → PEmb (toLevel xP hxP) (toLevel (yP α) (hyP α))`；`∀ α → ψ⁰ (Ω (toLevel xP hxP)) ≼ ψ⁰ (Ω (toLevel (yP α) (hyP α)))` | 同一探针族上普通嵌入与 `VMᴸ` 一致成立 | 编译定理 |
| `probe-down→F` | `∀ α → Down¬¬ (probe-emb α) → ∀ k → α k ≡ false` | 这个一致的嵌入保初始段，恰当 α 全假 | 编译定理 |
| `PEmbᴰ-⊑`, `embVᴰ-⊑` | `a ⊑ᴵ b → PEmbᴰ a b`；`∀ x hx y hy → x ⊑⁰ y → PEmbᴰ (toLevel x hx) (toLevel y hy)` | 结构可比时恒等映射保初始段 (可满足性) | 编译定理 |
| `¬¬seg` | `∀ α → ¬ ¬ PEmbᴰ (toLevel xP hxP) (toLevel (yP α) (hyP α))` | 结论弱化成 ¬¬ 后否定失效 | 编译定理 |
| `segTop→LPO` | `(∀ α → Σ (PEmb (toLevel xP hxP) (toLevel (yP α) (hyP α))) DownTop) → LPO` | 只在顶的像之下要求向下封闭也够 | 编译定理 |

- **否定的是什么**：要求嵌入保初始段的那种证法 (`EmbVᴰ` 与它的弱化)。
- **不否定**：`VMᴸ`、普通的 `EmbV`、`VMᶜʰ`。
- **机制，逐条核过**：
  - 定理里没有折叠，也没有 ψ。失败的字段是 `down`。
  - 顶 ω 的像必须恰是 `B α` 里值为 |ω| 的那个前驱。也就是要判定 `B α` 的值是否等于 ω。
  - 它与 `Value.dec≈→LPO` 同类 (判定值相等)，但陈述不同。它不是壁垒定理的实例：没有下标类型。
- **可满足性**：在经典模型里成立 (判断：取按秩的嵌入)；编译的实例是 `embVᴰ-⊑`、`bound-seg`、`LPO→seg`。

**YiVmNegIrr：不读推导的写法**

| 名字 | 陈述 (逐字) | 白话 | 档 |
|---|---|---|---|
| `vm¬¬→MP` | `VM¬¬ → MP`，其中 `VM¬¬ = ∀ x hx y hy → ¬ ¬ (x ≼ y) → ψ⁰ (Ω (toLevel x hx)) ≼ ψ⁰ (Ω (toLevel y hy))`，`MP = ∀ α → ¬ ¬ (Σ ℕ λ k → α k ≡ true) → Σ ℕ λ k → α k ≡ true` | 前提只是 ¬¬ 时推出 MP | 编译定理 |
| `vmⁱ→MPⁱ` | `VMⁱ → MPⁱ` (前提是 `.(x ≼ y)`；`MPⁱ = ∀ α → .(Σ ℕ λ k → α k ≡ true) → Σ ℕ λ k → α k ≡ true`) | 前提是无关参数时推出 MPⁱ | 编译定理 |
| `embV¬¬→MP`, `embVⁱ→MPⁱ` | `EmbV¬¬ → MP`；`EmbVⁱ → MPⁱ` | 嵌入版更强，同样推出 | 编译定理 |
| `MP→MPⁱ` | `MP → MPⁱ` | MPⁱ 不强于 MP | 编译定理 |
| `strictΩ` | `suc (ψ⁰ (Ω A)) ≼ ψ⁰ (Ω (suc A))` (A 是 ω 的层号) | ψ₀(Ω_ω)+1 ≼ ψ₀(Ω_{ω+1})，全靠归约 | 编译定理 |
| `key` | `∀ α → ψ⁰ (Ω (toLevel xI hxI)) ≼ ψ⁰ (Ω (B α)) → Σ ℕ λ k → α k ≡ true` | 这条 ψ⁰ 不等式本身就给出见证 | 编译定理 |
| `MP→fam`, `fam→MP` | `MP → Fam¬¬`；`Fam¬¬ → MP`，`Fam¬¬ = ∀ α → ¬ ¬ (xI ≼ Y α) → PEmb (toLevel xI hxI) (B α)` | 探针族上与 MP 等价 (可满足性) | 编译定理 |
| `emb-rel`, `vm-rel` | `∀ α → xI ≼ Y α → PEmb (toLevel xI hxI) (B α)`；`∀ α → xI ≼ Y α → ψ⁰ (Ω (toLevel xI hxI)) ≼ ψ⁰ (Ω (B α))` | 前提是带数据的推导时，探针上直接成立 | 编译定理 |

- **否定的是什么**："嵌入或不等式只依赖 (x, y)、不依赖推导" 这一要求。
- **不否定**：`VMᴸ` 本身 (它的前提是带数据的推导)。
- **探针严格**：`Y α` 满足 `SY α : SHS (Y α)`。
- **判断，元理论，未编译**：MP、MPⁱ、LPO 在 `--safe` 的 Agda 里都不可证。

**YiVmNegBound：正面的子域**

| 名字 | 陈述 (逐字) | 白话 | 档 |
|---|---|---|---|
| `bound-⊑` | `∀ x hx y hy {z} → toLevel x hx ≺ᴵ z → toLevel y hy ≺ᴵ z → x ≼ y → toLevel x hx ⊑ᴵ toLevel y hy` | 有字面公共上界时，值序推出结构序 | 编译定理 |
| `bound-vm`, `bound-seg` | 同样的前提，结论分别是 `ψ⁰ (Ω (toLevel x hx)) ≼ ψ⁰ (Ω (toLevel y hy))` 与 `PEmbᴰ (toLevel x hx) (toLevel y hy)` | 那里 `VMᴸ` 与保初始段的嵌入都成立 | 编译定理 |
| `no-back` | `∀ x hx y hy → toLevel y hy ≺ᴵ toLevel x hx → ¬ (x ≼ y)` | 层号的字面前驱在值上严格更小 | 编译定理 |
| `emb-fin`, `vm-fin` | `∀ n (hx : HS (natᶜ n)) y (hy : HS y) → natᶜ n ≼ y → PEmb (toLevel (natᶜ n) hx) (toLevel y hy)`；`vm-fin` 是对应的 ψ⁰ 版本 | x 有限时，由推导直接造出嵌入 | 编译定理 |

**YiVmNegChain：供构造路用的子域**

| 名字 | 陈述 (逐字) | 白话 | 档 |
|---|---|---|---|
| `VMᶜʰ` | `∀ n → D.γ n ≼ read (pt n) → L.ψ⁰ (L.Ω (L.toLevel (D.γ n) (D.cert n))) ≼ L.ψ⁰ (L.Ω (L.toLevel (read (pt n)) (HS-read (pt n) (lawfulᵐ (pointsᵐ n)))))`，`pt n = coordᵐ (pointsᵐ n)` | 只在链上要的 `VMᴸ` | 定义 |
| `vm→ch` | `VMᴸ → VMᶜʰ` | | 编译定理 |
| `ch→btbo` | `VMᶜʰ → D.BTBOᴵ ≼ read T₃ᵐ` | 链上的单调性就够推出 BTBO 下界 | 条件定理 (前提 `VMᶜʰ`，未证；`VMᴸ` 推出它) |
| `no-bound`, `no-bound-pt` | `∀ n (a : R) (l : Lgl B.zero a) → NZ (read0 a) → D.γ (suc n) ≼ read a → ∀ {z} → L.toLevel (D.γ (suc n)) (D.cert (suc n)) ≺ᴵ z → L.toLevel (read a) (HS-read a l) ≺ᴵ z → ⊥`；`no-bound-pt` 是 a 取链点时的特例 | n ≥ 1 时，链上的值序若成立，两边层号没有字面公共上界 | 编译定理 |

##### 4 正面的结果 (对构造路有利)

- **公共上界子域** (`bound-⊑`)：两边层号有字面公共上界时，`VMᴸ` 成立，保初始段的嵌入也成立。但链点 (n ≥ 1) 不在这个子域里 (`no-bound-pt`)。
- **有限的 x** (`emb-fin`, `vm-fin`)。
- **结构可比的对** (`embVᴰ-⊑`)。
- **两组否定的探针族上**，普通嵌入与 `VMᴸ` 都一致成立 (`probe-emb`/`probe-vm`，`emb-rel`/`vm-rel`)。
- **构造路的目标可以缩到 `VMᶜʰ`** (`ch→btbo`)：只要 ℕ 下标的链上那些对，前提是带数据的推导。两条否定的机制 (要求精确到值的初始段，丢掉推导数据) 在这里都不出现。这一句是判断。

##### 5 没写成的条目与第一个障碍

- **N1：`VMᴸ` 本身。** 没有找到否定，也没有证明。
  - 判断：要推出全知原则，需要一个探针族，使得结论 ψ⁰ 不等式的每个推导都被迫做判定。但带数据的前提推导总能给出一致的普通嵌入：我试的两组都编译成立，其余几种只在纸面上试过。
  - 第一个障碍 (判断)：左极限处，各段嵌入 (由 `f n ≼ y` 各自造出) 不一致。
    - 若想逐段拼接，前一段的像要给后面留出空间 (有界)。
    - 由推导直接造出的嵌入可以是共尾的。纸面例子：x = y = ω·2，推导 `natᶜ n ≼ ω+n` 用 `s≼s` 走 n 步，把自然数 i 映到 ω+i，于是 ω 无处可放。
    - 这个例子没有编译。仓库里也没有 "由推导造嵌入" 的函数可以作为否定的对象。
  - 证明思路，供构造路参考 (判断)：用普通嵌入，在每个极限处借助下一项的推导 (严格树里 f n ≺ f (n+1)) 把前一段的像压在一个前驱之下，再逐段延拓。我没有试。
- **N2 第二项：一般的 `EmbV`。** 只在两组探针上得到正面实例，没有找到否定。
- **N5 的其余挑战。** "嵌入换成关系" 与原写法等价 (判断：保序的全关系模 `≅ᴵ` 是函数)，没有编译。"结论弱化成 ¬¬" 能逃过否定 (`¬¬seg`)，但它只给 ψ⁰ 不等式的双重否定，推不出 `VMᴸ` (判断)。

##### 6 偏离与事故

- 没有改任何已有文件，没碰 `src/`、`archive/`，不依赖 `YiVmCon*` 与 `YiLean*`，没有提交。
- 多写了两个文件，都是带定理的 literate 文件，不是只有导入的报告：
  - `YiVmNegBase`：两条否定共用的探针与引理。
  - `YiVmNegChain`：回答 N3 的子域陈述。
- 依赖：`YiVmNegBound` 从 `YiVmNegSeg` 导入 `PEmbᴰ`。`YiVmNegChain` 导入定稿的 `YiMonoVM`、`YiMonoBreak`、`YiBtValBT` 等。
- 编译中途的错误都是我自己的，各改一次就过：
  - `{zero}` 被当成双关，改成 `{u = zero}`。
  - `below` 与 `Level.below` 重名。
  - `with` 抽象之后布尔参数要写字面的 `false`。
  - `with` 不能作用在模块参数上。
- 只删过自己五个模块的 `.agdai`，用的是字面路径。没有一次性的试验文件。
