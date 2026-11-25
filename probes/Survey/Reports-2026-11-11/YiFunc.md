# 参照一侧的函子性 FUNC (YiFunc)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-11 14:37 至 15:23 |
| 工具调用 / agda 编译 (粗数) | 49 / 8 |
| token (usage 字段，按消息去重) | 输出 281326；新写入缓存的输入 624452；读缓存的输入 11687446；其余输入 82 |
| 写过的仓库文件 | `YiFuncBase.lagda.md`, `YiFuncChain.lagda.md`, `YiFuncCrux.lagda.md`, `YiFuncLim.lagda.md` |
| 文件前缀 | `YiFunc` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 第十二批两路返回并复核; BTBO 是下界, 无前提 (主审)” 一节 |
| 主审复核后的一句结论 | 第 1 步的实例是定理；一般的 FUNC 归约到 CRUX 与 NEXT（条件），未走通；对 BTBO 下界已不需要；四件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 任务是 **参照框架 (Level 族) 上 ψ⁰∘Ω 对前驱嵌入的函子性 `FUNC`**: 层号之间的前驱嵌入推出 ψ₀(Ω_·) 输出的层号之间的前驱嵌入. 它是 "BTBO 是主线闭项的下界" 只用下界的证法里缺的三条之一, 只谈参照框架, 与被验收的树无关. 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇. 特别是 Agda 一节 (选项, 文字预算, 退出码, 堆; 函数外延只准作前提), "结论的写法".
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 与 §5.4.
3. **回报原文**: `probes/Survey/Reports-2026-11-11/YiPE.md` (全读; `FUNC` 是怎么归约出来的, §5 第一个障碍), `YiEmb2.md` (照 `BTBOFullLe` 的 `LeE` 改写得到定义域版折叠单调的办法), `YiLow.md` (哪些写法推出 LPO: 由值序造嵌入, 对一切严格树也一样).
4. 代码 (都已定稿, 可以导入, 不许编辑):
   - **陈述所在**: `probes/OCF/Lean/YiPEStep.lagda.md`. 逐字:
     ```agda
     L⁺ : Ordᴵ → Ordᴵ
     L⁺ a = L.toLevel (L.ψ⁰ (L.Ω a)) (Un.Uniform a)
     FUNC : Set
     FUNC = ∀ {a b} → PEmb a b → PEmb (L⁺ a) (L⁺ b)
     func-⊑ : ∀ {a b} → a ⊑ᴵ b → PEmb (L⁺ a) (L⁺ b)      -- 结构可比时的结论, 已有
     btbo-FS⁺ : FUNC → KEYsuc → SpineT → D.BTBOᴵ ≼ NA.read NT.T⁺   -- 在 YiPEKey
     ```
     第一个要的实例: `PEmb (L⁺ (D.L 1)) (L⁺ (κ 1))`, 由 `YiPEBase.emb₁ⁿ` 的嵌入得到 (`D.L (suc n)` 定义性地是 `L⁺ (D.L n)`).
   - 前驱嵌入: `probes/OCF/Align/BTBOFullEmb.lagda.md` (`PEmb`: 字段 `map`, `bnd`, `mono`, `coh`; 模块 `PE` 由一个嵌入造出关系 `E` 与 `lt′`, `eq′`, 以及 `Ψ-emb` 的证法), `probes/OCF/Align/BTBOFullLe.lagda.md` (模块 `LeE`: 对一般的嵌入关系 E 的关系 `Le` 与 `Le-ψ`: 折叠保持 `Le`; `Laws`), `probes/OCF/Align/YiMonoEmb.lagda.md` (`PEmb-⊑`, `PEmb-∘`, `PEmb-limʳ`, `PEmb-suc`, `PEmb-limˡ`), `probes/OCF/Lean/YiPEStair.lagda.md` (阶梯粘接 `Stair.stair`: 目标逐块累加时各块嵌入不必一致), `YiPEStep.lagda.md` (`PEmb-shift`, `PEmb-≅ʳ`, `PEmb-≅ˡ`), `probes/OCF/Lean/YiEmb2Le.lagda.md` (`Two.WithLaws`: LeE 的改写).
   - 参照: `OCF.Align.Level` (`Ordᶜ`, `Ordᴵ`, `ψ`, `ψ⁰`, `Ω`, `limᵢ`, `toLevel`, `toLevel-⊑`, `toLevel-≺`, `HS`, `_≺ᴵ_`, `_≅ᴵ_`, `<ᴵ-dec`, `Ψ⁰-mono`), `OCF.Align.Uniform` (`Uniform a : HS (ψ⁰ (Ω a))`), `OCF.Align.Value`.
   查签名用检索, 大文件不要整篇读.

#### 1 要交的, 分步; 每做成一步先交

1. **最小的实例.** a, b 有限; a = ω 对一个非结构可比的 b (例如 `YiMonoEmb` 的 ω⁺ = lim (n+1)); 再 `PEmb (L⁺ (D.L 1)) (L⁺ (κ 1))`. 每个实例写明嵌入是怎么造的.
2. **一般的 `FUNC`**, 或它在一个明确的子类上的版本 (例如嵌入由结构给出的那一类: 由 `PEmb-⊑`, `PEmb-suc`, `PEmb-limʳ`, `PEmb-shift`, `PEmb-∘`, 阶梯粘接生成的嵌入; 写成一个归纳族 `Gen a b`, 证 `Gen a b → PEmb (L⁺ a) (L⁺ b)`), 并说明链上要的实例 (`D.L n` 对 `κ m`, 由 `YiPEStep` 的一步 `FUNC ∘ KEY ∘ shift-κ` 产生) 落在这个子类里.
3. **接线.** 若做成, 写出 `FUNC`(或子类版) 加 `YiPEKey` 的另两个前提 `KEYsuc`, `SpineT` 推出 `D.BTBOᴵ ≼ NA.read NT.T⁺` 的那一条 (若子类版需要改 `btbo-FS⁺` 的写法, 在你的文件里写新的一条).

**办法提示 (判断, 先挑战再用).**
- ψ⁰ (Ω a) 的前驱由 a 的前驱上的塌缩链生成; 嵌入 P : a → b 应当诱导塌缩链之间的对应. `BTBOFull` 的 `PE` 模块已经由一个嵌入造出关系 E, 用来证值上的 `Ψ-emb`; 看能否把那个证明从 "值序" 加强到 "前驱嵌入" (结论里的 `≼` 换成造出 `PEmb` 的数据).
- 已知的边界: 由值序造嵌入 (对一切树, 或一切严格树) 推出 LPO (`YiLowNeg.embVˢ→LPO`, `embV→LPO`). `FUNC` 的前提是嵌入, 结论是嵌入, 不经值序, 不在这个否定的范围里. 若你在某一步发现要由值序造嵌入, 那一步就会撞上它, 写清楚.
- 极限情形 (`PEmb-limˡ` 要各项嵌入一致): 若目标逐块累加可以用阶梯粘接; ψ⁰ (Ω b) 的极限不是累加的, 一致性要来自构造的自然性 (同一个嵌入 P 诱导各项).

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K (可交显式前提的条件定理); 堆到 6G 仍耗尽 (先按手册 §4.2). 若发现 `FUNC` 推出某条全知原则, 写成编译的定理交回. 做不成的部分写成带确切类型的模块参数. 没有编译的否定定理时只能写 "未走通".

#### 2 过程要求

- 读完上面的文件后尽快动手: 第一个文件 (哪怕只是 a, b 有限的情形) 在 20 分钟内写出并编译.
- 每写完一个文件就编译; 每次回复都要有工具调用, 不要在一次回复里只思考.

#### 3 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiFunc` (模块名 `OCF.Lean.YiFunc…`). 都是验收文件, 文首标 "验收文件"; 允许导入带记号闭包的 `OCF.Align.Value`, `OCF.Align.Level` 与旧验收文件. 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提, 用到它的定理在文首标 "条件".
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块.
- 你的临时目录: `<实验目录>/agents/func`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几步; 一段话说对纲领与目标意味着什么 (`FUNC` 或子类版是定理了没有; 链上要的实例在不在里面).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 条件定理写出前提的 Agda 类型与它的可满足性.
4. 办法: 嵌入怎么由塌缩链诱导; 极限情形的一致性从哪里来.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型; 它是不是在要求判定什么.
6. 偏离与事故.
不用 "只差", "自然" 一类形容; 判断与定理分开写.

## 回报原文

#### YiFunc 一路回报：ψ⁰∘Ω 对前驱嵌入的函子性 `FUNC`

##### 1 判决

- **第 1 步做成了。**
- **第 2 步只做成归约**，没有一般的 `FUNC`，也没有无条件的子类版。
  - 我限制的是**源层号**：极限逐项严格。嵌入本身不限制。
  - 在这一类源上，`FUNC` 加上一条边界性质 (`FB`) 归约到后继情形 `CRUX`；`CRUX` 又归约到折叠链的单块 `NEXT` 加上链严格 `ChainStr`。
  - 极限情形不需要各块嵌入一致，这是编译定理 (边界粘接)。
- **第 3 步只有条件版。** 两条接线：
  - `btbo-CS⁺ : CRUX → StrD → KEYsuc → SpineT → D.BTBOᴵ ≼ NA.read NT.T⁺`
  - `btbo-NX⁺ : NEXTall → (∀ n → HSt (D.L n)) → KEYsuc → SpineT → …`

**对纲领与目标的意思：**
- `FUNC` 还不是定理。`D.BTBOᴵ ≼ T⁺` 仍是条件定理，前提从 `FUNC` 换成了 `CRUX + StrD` 或 `NEXTall + HSt`。
- 链上要的实例：
  - n = 0 时，`StrD` 与 `HSt` 是定理 (`str₀`, `hst₀`)。
  - n ≥ 1 时，`D.L n` 里出现后继子层号，要 `CRUX`/`NEXT` 以及 c ≥ 1 的 `ChainStr`。这些都没证。
- 全部只谈参照框架，不引用记号，没有新的强度定理。ψ₀(Ω_Ω) 仍是读法。

##### 2 文件表

都在 `probes/OCF/Lean/`。冷编译的做法：只按字面路径删自己的 `.agdai`，按依赖序编，堆上限 6G。每份日志只有本模块一行 `Checking`。

| 文件 | 代码行 / 总行 | 冷编退出码 | 常驻峰值 |
|---|---|---|---|
| `YiFuncBase.lagda.md` | 76 / 118 | 0 | 1.47G |
| `YiFuncLim.lagda.md` | 154 / 238 | 0 | 1.57G |
| `YiFuncChain.lagda.md` | 78 / 121 | 0 | 2.61G |
| `YiFuncCrux.lagda.md` | 118 / 179 | 0 | 1.64G |

- 依赖序：Base → Lim → Chain，Lim → Crux。
- 选项行都是 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。
- 检索 `postulate`、`{!`、` ? `、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`irrelevant-projections`、`--cubical`、`Funext`、本机路径：都是 0 处。

##### 3 定理表

`L⁺ a = L.toLevel (L.ψ⁰ (L.Ω a)) (Un.Uniform a)`，取自 `YiPEStep`。

**YiFuncBase (第 1 步，都是编译定理)**

| 名字 | 逐字陈述 | 白话 |
|---|---|---|
| `PEmb-res` | `∀ {a b c} (P : PEmb a b) (r : c ≺ᴵ a) → PEmb c (map P r)` | 把嵌入限制到一个前驱之下 |
| `cnt` | `∀ n m → PEmb (L.natᴵ n) (L.natᴵ m) → n ≤ m` | 有限层号之间的嵌入数出 n ≤ m |
| `func-nat` | `∀ n m → PEmb (L.natᴵ n) (L.natᴵ m) → PEmb (L⁺ (L.natᴵ n)) (L⁺ (L.natᴵ m))` | a, b 有限时的 `FUNC` |
| `func-ω` / `func-ω′` | `PEmb (L⁺ L.ωᴵ) (L⁺ ω⁺ᴵ)` / 反向 | ω 与 ω⁺ 互为 `⊑ᴵ`，经 `func-⊑` |
| `func₂` | `∀ {a b} → XEmb a b → XEmb b a → PEmb (L⁺ a) (L⁺ b)` | 两个方向都有保值嵌入时成立 (`VMˣ₂` 经 `embˣ`) |
| `func-sω` | `PEmb (L⁺ (L.suc L.ωᴵ)) (L⁺ (L.suc ω⁺ᴵ))` | 非结构可比的实例 (`ω-not`)；`Xω` 的嵌入定义性地就是 `PEmb-suc (PEmb-⊑ ω⊑ω⁺)` |
| `func-L1` | `PEmb (L⁺ (D.L 1)) (L⁺ (κ 1))` | 链上第一个实例，见下 |

`func-L1` 的来源：它由 `YiEmb2.p1-one` 经 `embˣ` 得到，用的是 `D.γ 1` 与链点 1 两个方向的值相等。它**不是**把 `FUNC` 用在 `emb₁ⁿ` 上。

**YiFuncLim (极限情形)**

- `FB`：一个记录。
  - `R : PEmb (L⁺ a) (L⁺ b)`
  - `bd : ∀ {x} (r : x ≺ᴵ a) (r′ : L⁺ x ≺ᴵ L⁺ a) → L⁺ (map P r) ⊑ᴵ map R r′`
  - 白话：嵌入，外加 "前驱 L⁺ x 的像不低于 L⁺ (P x)"。
- `CRUX`：定义 `∀ {c c′} (Q : PEmb c c′) → FB (PEmb-suc Q)`。它是前提。
- `Str`：源的极限沿极限分支逐项严格 (`f n ≺ᴵ f (suc n)`)，遇到后继就停。

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `L⁺<` | `∀ {a b} → a ≺ᴵ b → L⁺ a ≺ᴵ L⁺ b` | L⁺ 严格单调 | 编译 |
| `L⁺-refl` | `∀ {x y z} → x ≺ᴵ z → y ≺ᴵ z → L⁺ x ≺ᴵ L⁺ y → x ≺ᴵ y` | 有公共上界时反射 | 编译 |
| `BG.emb` | 参数 `Q : PEmb a T`, `R : PEmb a′ T′`, `w : a ≺ᴵ a′`, `TT : T ⊑ᴵ T′`, `bw : T ⊑ᴵ map R w`；结论 `PEmb a′ T′`；`BG.ext` 说它在 a 的前驱上延拓 Q | 边界粘接：目标不必累加 | 编译 (参数都是输入) |
| `fb-suc₁` | `∀ {c b} (P : PEmb (L.suc c) b) → FB (PEmb-suc (PEmb-res P (via (L.≅ᴵ-refl c) L.zero))) → FB P` | 后继源归到 `PEmb-suc` | 编译 |
| `func-red` | `CRUX → ∀ {a} → Str a → ∀ {b} (P : PEmb a b) → FB P` | 归约 | 条件 |
| `func-str` | `CRUX → ∀ {a b} → Str a → PEmb a b → PEmb (L⁺ a) (L⁺ b)` | 同上，只取嵌入 | 条件 |

**YiFuncChain**

| 名字 | 逐字陈述 | 白话 | 档 |
|---|---|---|---|
| `crux₂` | `∀ {c c′} (X : XEmb c c′) (Y : XEmb c′ c) → FB (PEmb-suc (P X))` | `CRUX` 在两向的 Q 上成立 | 编译 |
| `crux-sω` | `FB (PEmb-suc (PEmb-⊑ ω⊑ω⁺))` | 上一条的实例 | 编译 |
| `str₀` | `Str (D.L 0)` | n = 0 的 `StrD` | 编译 |
| `btbo-CS` / `btbo-CS⁺` | `CRUX → StrD → KEYsuc → SpineT → D.BTBOᴵ ≼ read T₃` / `… ≼ NA.read NT.T⁺` | 接线 | 条件 |

`StrD = ∀ n → Str (D.L n)`。

**YiFuncCrux**

- `Λ c m = L⁺ (L.suc c) [ m ]ᴵ`：折叠链的第 m 项。
- `ChainStr c = ∀ m → Λ c m ≺ᴵ Λ c (suc m)`
- `NEXT {c} c′ cs m = Σ (PEmb (Λ c (suc m)) (Λ c′ (suc m))) λ R → Λ c′ m ⊑ᴵ map R (cs m)`
- `NEXTall = ∀ {c c′} → PEmb c c′ → (cs : ChainStr c) → ∀ m → NEXT c′ cs m`
- `HSt`：沿极限与后继都严格；后继 `suc c` 要 `HSt c` 与 `ChainStr c`。

| 名字 | 逐字陈述 | 档 |
|---|---|---|
| `crux-red` | `∀ {c c′} (Q : PEmb c c′) → FB Q → (cs : ChainStr c) → (∀ m → NEXT c′ cs m) → FB (PEmb-suc Q)` | 条件 |
| `func-red₂` | `NEXTall → ∀ {a} → HSt a → ∀ {b} (P : PEmb a b) → FB P` | 条件 |
| `btbo-NX⁺` | `NEXTall → (∀ n → HSt (D.L n)) → KEYsuc → SpineT → D.BTBOᴵ ≼ NA.read NT.T⁺` | 条件 |
| `chainStr₀` | `ChainStr L.zero` | 编译 |
| `hst₀` | `HSt (D.L 0)` | 编译 |

**前提的可满足性：**
- `CRUX`：
  - 两向的 Q 上是定理 (`crux₂`)。
  - 经典地成立 (判断)。理由：每棵树的字面前驱覆盖它下面的一切值，加上 ψ-项的翻译。
  - 构造地未证。
- `NEXTall`：同上，经典地成立 (判断)，构造地未证。
- `StrD`：
  - n = 0 是定理。
  - n = 1 是判断：只涉及第 0 层的 ψ⁰ 树与和，用 `ψ⁰-≺`、`toLevel-+`、`⊕-≺` 应可证。
  - n ≥ 2 要 c ≥ 1 的链严格，未证。
- `HSt (D.L n)`：n = 0 是定理；n ≥ 1 要 `ChainStr 1` 等，未证。
- `KEYsuc`、`SpineT`：与 YiPE 相同。

##### 4 办法

**极限情形 (`LimCase`)：**
- 第 n 块是 `FB (P 限制到 f n)`，目标是 `L⁺ (P (f n))`。
- 源的相邻两项严格，所以对 `L⁺ (f (n+1))` 的前驱，可以用有界三歧判定 "在不在 `L⁺ (f n)` 之下"。在之下的用旧块，否则用新块。
- 跨块的单调：旧块的像 ≺ `L⁺ (P (f n))` ⊑ 新块里 `L⁺ (f n)` 的像 (新块的边界性质) ⊑ 新块里更高前驱的像。
- 各块的一致性来自 "后一块延拓前一块" (`BG.ext`)，再照 `Stair` 的 `far`/`cohQ` 喂给 `PEmb-limˡ`。
- 不要求累加的目标 (Stair 要)，也不要求各块嵌入互相一致。代价有两个：
  - 源的极限要严格；
  - 嵌入要带边界性质，这本身成为归纳不变量。
- 输出的边界性质由 `L⁺-refl` 找到 x 首次出现的块。

**后继情形 (`crux-red`)：**
- `L⁺ (suc c)` 是折叠链 `Λ c m` 的极限，套用同一个粘接 (`GL`)。
- 第 0 块是 `FB Q` (经 `Λ0 : Λ c 0 ≅ᴵ L⁺ c` 搬运)；第 m+1 块是 `NEXT`。
- 边界在 x ≅ c 处由 `floor0` 给出，在 x ≺ c 处由 `low0` 加 `FB Q` 的 `bd` 给出。

**`chainStr₀`：** 第 0 层链的下一项 ≅ ψ⁰ (前一项) (`L.ψ⁰≅ψ`)，再用 `YiPEKey.ψ⁰-≺` 归纳。

**`crux₂`：** `R` 取 `embˣ` 给的保值嵌入。像与 `L⁺ (Q x)` 两向值相等：限制后的两个保值嵌入经 `VMˣ₂` 得到；两者又同在 `L⁺ (suc c′)` 之下，所以由 `≈→≅` 得 `≅ᴵ`。这里只在值相等时用 `≈→≅`，不由值序造嵌入，不在 `YiLowNeg` 的范围里。

##### 5 第一个障碍

没有检查器报错。缺的是 `NEXT` 与 c ≥ 1 的 `ChainStr`。

**`NEXT` 的类型** (见 §3)：给定 `PEmb c c′`，造 `Λ c (m+1)` 到 `Λ c′ (m+1)` 的嵌入，并把前一项 `Λ c m` 送到不低于 `Λ c′ m` 处。

**为什么难 (判断)：**
- `Λ c (m+1) = toLevel (ψ⁰ (ψ_c γ_m))`。穿透之后，它本身又是低层链 `lim_k ψ⁰ (g (δ_k))` 的极限。
- 要再粘接，就要一条边界性质：第 k+1 块把 `ψ⁰ (g (δ_k))` 送到不低于对应目标项处。
- 这取决于 `ψ⁰ (g (δ_k))` 在 `ψ⁰ (g (δ_{k+1}))` 里的位置。对 BTBOFullLe 的 `Lii` 情形里任意的分支 g，没有统一的控制。
- 换句话说，缺的是 BTBOFullLe `Le-ψ⁰` 的前驱嵌入版，带一个一般的边界不变量："推导 `Le x y` 给出的嵌入，把子项 `ψ⁰ u` 送到不低于对应 `ψ⁰ u′` 处"。

**`ChainStr c` (c ≥ 1)：** 要高层的 `ψ⁰ A ≺ ψ⁰ (A + B)`。这与 YiPE 回报里 `SpineT` 在 m = 1 处缺的是同一类引理 (判断)。

**两条别的路为什么不通 (判断，未编译)：**
- **由值得到一致性** (`XEmb-limˡ`)：要保值，而 `FUNC` 把 Ω_c 抬到 Ω_{Pc}，不保值。
- **目标的加法封闭 (改用 Stair)：** 结构上不成立。例：`suc (lim (1+n))` 不 ≅ ω² 的任何字面前驱。

**是不是在要求判定什么：**
- `Str`、`ChainStr` 是对具体参照层号的严格性命题，不是对一切树的判定。
- 若改为对一切层号判定 "相邻两项严格或相等"，按 YiPE 的判断推出 LPO。这一条我没有写成定理。
- `NEXT` 里没有看到要判定的东西。
- 没有编译的否定定理，所以 `FUNC` 与 `CRUX` 只能写 "未走通"。

**边界性质比 `FUNC` 强 (判断)：**
- `tri→FUNC` 给的保值嵌入，在 P 抬高值时不满足 `bd`。
- `func-⊑` 用在 `PEmb-suc (PEmb-⊑ k)` 上 (c 映到 c′，两者不 ≅) 时也不满足。
- 所以 `CRUX` 不能由一般的 `FUNC` 推出。我没有证这个方向。

##### 6 偏离与事故

**偏离简报：** 简报建议在嵌入上取一个生成族 `Gen a b`。我改为限制源层号 (`Str`/`HSt`)，嵌入任意。理由：链上每步含抽象的 `key n`，嵌入族的子类必须包含 KEY 的实例，而源一侧的限制直接落在 `D.L n` 上。

**简报没要求、多加的：** `YiFuncCrux` 的再归约，以及 `chainStr₀`、`hst₀`。

**编译错误 (都是我自己的)：**
- `YiFuncBase` 的辅助函数 `up` 类型写错 (`UnequalTerms`)，改用 `split` 后通过。
- `YiFuncLim` 初稿里留了占位写法，在首次编译前改掉；改后一次通过。
- `YiFuncCrux` 导入模块要写 `module BG; module Ext` (`NotInScope`)，改后通过。
- `YiFuncLim` 编过之后，我把 `fb-suc` 拆成 `fb-suc₁` 加 `fb-suc`，并重编了 `YiFuncChain`。

**其余：**
- 用 python/sed 改过自己的文件。
- 只按字面路径删过自己四个模块的 `.agdai`，没有用 `--ignore-interfaces`，没有写临时 `.agda`。
- 日志在 `<实验目录>/agents/func/` (`cold-*.log`)。
- 没改已有文件，没碰 `src/`、`archive/`，没有提交。

主审冷编请按依赖序：
1. <仓库>/probes/OCF/Lean/YiFuncBase.lagda.md
2. <仓库>/probes/OCF/Lean/YiFuncLim.lagda.md
3. <仓库>/probes/OCF/Lean/YiFuncChain.lagda.md
4. <仓库>/probes/OCF/Lean/YiFuncCrux.lagda.md
