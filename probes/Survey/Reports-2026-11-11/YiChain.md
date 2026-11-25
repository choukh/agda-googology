# 主线上证 ChainP (YiChain)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-11 10:39 至 11:18 |
| 工具调用 / agda 编译 (粗数) | 53 / 8 |
| token (usage 字段，按消息去重) | 输出 231090；新写入缓存的输入 922431；读缓存的输入 10805674；其余输入 82 |
| 写过的仓库文件 | `YiChainBack.lagda.md`, `YiChainBase.lagda.md`, `YiChainCond.lagda.md`, `YiChainFlat.lagda.md`, `YiChainOne.lagda.md` |
| 文件前缀 | `YiChain` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 主线上证 ChainP 的一路返回并复核 (主审)” 一节 |
| 主审复核后的一句结论 | 第 1 项无条件成立（两个方向）；参照对角链的第 2 项不高于主线闭项；一般的项归约到两条加强，缺主线折叠的上界与两个方向的嵌入；五件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 任务是 **在主线上证 `ChainP`**: 主线闭项的链点与参照 (不累加的 BTBO 对角线) 的项逐项落在值单调成立的定义域里. 做成它, "主线闭项的值不低于 BTBO 的参照" 就是无条件的定理, 作者短期目标里的 "值定理与 BTBO 持平" 就落实了. 另有一路 (前缀 `YiChainNeg`) 同时对同一个陈述找编译的否定; 你们共用的陈述在已定稿的文件里, 谁也不改它. 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇. 特别是 "量化域先取带证据的读回域", "第 4 层不反过来改前 3 层" (验收只新增关系与定理, 不改树, 折叠, 合法性的定义), Agda 一节 (选项, 文字预算, 退出码, 堆; 函数外延只准作前提), "结论的写法".
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 (编译与内存, 堆墙的对策) 与 §5.4.
3. **回报原文, 按顺序读**: `probes/Survey/Reports-2026-11-11/YiLeanVal.md` (主线上的值证明; §5 是第一个障碍: `ChainP` 在 n = 1 卡在哪, 缺的引理的类型与两种够用的引理), `YiVmCon.md` (定义域 `≼ˣ`, `≼ᵖ` 是怎么来的, 为什么这样设), `YiZero.md` §6 (同一个障碍在另一个候选上的分析: 链点是 "上一点 + y", 要吸收; 左边是 1 的实例可能可以构造地证), `YiDiag.md` (另一个候选在第 1 步怎么得到结构互模拟 `read-pt1`).
4. 代码 (都已定稿, 可以导入, 不许编辑; 模块名 `OCF.Lean.<名>` 或 `OCF.Align.<名>`):
   - **共用陈述 (主线上的)**: `probes/OCF/Lean/YiLeanValFin.lagda.md`. 逐字:
     ```agda
     ChainP : Set
     ChainP = ∀ n → Σ ℕ λ m → D.γ n ≼ᵖ read (co (pts m))
     btbo-p : ChainP → D.BTBOᴵ ≼ read T₃
     chainP₀ : D.γ 0 ≼ᵖ read (co (pts 0))
     ```
     同文件还有 `κ`, `T₃-own`, `top-one : read G.top ≡ L.suc L.zero`, `chain-cum : ∀ n → read (co (pts (suc n))) L.≅ (read (co (pts n)) L.+ read (obs (pts n)))`, `lower-read`, `HS-read`.
   - 主线的块与闭项: `probes/OCF/Lean/YiLeanCore.lagda.md`, `YiLeanFold.lagda.md`, `YiLeanLegal.lagda.md`, `YiLeanTw3.lagda.md` (`F`, `pts`, `obs`, `co`, `T₃`), 验收 `YiLeanAccFin.lagda.md` (`read`, `fold₀`, `chain₁`), `YiLeanValRel`, `YiLeanValAdd`, `YiLeanValFold` (`lower-any`, `FOLD`).
   - 定义域与值单调: `probes/OCF/Align/YiVmConExact.lagda.md` (`_≼ˣ_` 的构造子 `zˣ`, `sˣ : a ≼ˣ b → b ≼ a → L.suc a ≼ˣ L.suc b`, `wˣ`, `≼lˣ`, `lˣ`; `_≼ᵖ_` 的 `zᵖ`, `sᵖ`, `wᵖ`, `≼lᵖ`, `lᵖ`; `reflˣ`, `≅→≼ˣ`, `⊑→≼ˣ`, `ˣ→ᵖ`, `ˣ→≼`, `ᵖ→≼`; `VMᵖ`; `Tri` 与 `tri→LPO` 说明一般的二分推出 LPO), `YiVmConChain.lagda.md` (旧块上的同一陈述, `diag-in : ∀ n → D.γ n ≼ˣ D.γ (suc n)`).
   - 可用的保持定理 (只谈参照框架的树, 可以导入): `probes/OCF/Lean/YiZeroAccP.lagda.md` 的 `ψ⁰ˣ : a ≼ˣ b → L.ψ⁰ a ≼ˣ L.ψ⁰ b` 与 `+ˣ : p ≼ˣ p′ → p′ ≼ p → q ≼ˣ q′ → (p L.+ q) ≼ˣ (p′ L.+ q′)` (同底加法). 那个文件其余部分是另一个候选的, 只导入这两条.
   - 参照: `probes/OCF/Align/Diagonal.lagda.md` (模块 `Diagonal` 取 `OCF.Align.Uniform.Uniform`, 写法照 `YiLeanValFin`: `D.γ`, `D.cert`, `D.L`, `D.G`, `D.BTBOᴵ`, `D.diag-step`), `OCF.Align.Level` (`ψ⁰`, `Ω`, `+`, `_≅_`), `OCF.Align.Value` (`≼`, `≼-trans`, `+-mono` 等).
   查签名用检索, 大文件不要整篇读.

#### 1 目标, 分步; 每做成一步先交

1. **n = 1 的闭实例.** `Σ ℕ λ m → D.γ 1 ≼ᵖ read (co (pts m))`. 先算清两边的形状 (可以在临时目录用纯 `.agda` 规范化看, 那是有限测试), 再写推导. 两边都是具体的闭项, 所以每一个 `sˣ` 要的 "顶的值相等" 都是两个具体的树之间的值比较, 原则上可以逐个证出来; 困难在于有多少个, 以及能否一致地写. 先做成一个, 哪怕长.
2. **一般的 n.** 找一个对 n 归纳的不变量 (比 `D.γ n ≼ᵖ read (co (pts m))` 更强, 例如带 "读回的链点与参照的项在哪些子树上保值地对齐" 的信息), 第 0 步成立, 被一步保持. 允许错开下标 (m 可以不等于 n).
3. **无条件的 BTBO 下界.** 由 `btbo-p` 得 `D.BTBOᴵ ≼ read T₃`, 写成一条不带前提的定理.

**可以试的办法 (都是判断, 先挑战再用).**
- 回报里给过的两种够用的引理: 只对链上实际出现的对的局部二分 (这些对是闭的, 不需要一般的 `Tri`); 对折叠产出的那类树, "值的 ≼ 推出 ≼ˣ" 的完备性 (要找出那类树的结构谓词, 例如 "每个后继的前驱都已吸收", "相邻两项是加法前缀").
- 吸收: 链点形如 X + y, 当 y 不低于 X·ω 时 X + y 与 y 值相等; 链点里的后继形如 suc (X + b′). 左边 X = 1 的情形 (外层第 1 点 = 1 + F top) 可能可以构造地证; X 无穷的情形可能要参照树上的 "左减法" 结构.
- 已有的保持定理 `ψ⁰ˣ`, `+ˣ`, `⊑→≼ˣ`, `≅→≼ˣ` 让你在参照一侧搬运; `diag-in` 说参照对角链自身相邻两项在 `≼ˣ` 里.
- 若 `≼ᵖ` 对这些对太严, 可以换一个定义域 D′, 但必须同时交 D′ 上的值单调 (照 `VMᵖ` 的证法) 并说明它为什么不碰 `Tri → LPO` 的那种二分.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K (可交显式前提的条件定理, 另给不带它的最强结果); 堆到 6G 仍耗尽 (先按手册 §4.2: 陈述逐字写, 大的参照树放 `opaque`, 隐式参数显式写出, 文件拆小). 做不成的部分写成带确切类型的模块参数, 其余条件地证出来, 并说明前提在哪些实例上是定理. 没有编译的否定定理时只能写 "未走通".

不要为了好证而改主线的定义: 被验收的就是 `YiLeanTw3.T₃` 与它的链点.

#### 2 过程要求

- 读完上面的文件后尽快动手: 第一个文件 (哪怕只是 n = 1 两边的形状与第一条引理) 在 20 分钟内写出并编译.
- 每写完一个文件就编译; 每次回复都要有工具调用, 不要在一次回复里只思考. 想不清的地方先写最简单的版本编译, 再改.

#### 3 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiChain` (模块名 `OCF.Lean.YiChain…`; 不要用 `YiChainNeg` 开头, 那是另一路的前缀). 都是验收文件, 文首标 "验收文件"; 允许导入带记号闭包的 `OCF.Align.Value`, `OCF.Align.Level` 与旧验收文件. 中文 literate Agda (`.lagda.md`). 不改任何已有文件 (含 README, LOG, RESULTS, AGENTS), 不碰 `src/`, `archive/`. 同时在跑的另几路用前缀 `YiChainNeg`, `YiNextVal`, `YiFree` (都在 `probes/OCF/Lean/`), 不要动也不要依赖它们的文件.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提, 用到它的定理在文首标 "条件".
- **文字预算**: 每个模块文首不超过 5 行 (判决与档位, 做了什么, 不否定什么, 入口指向); 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块.
- 你的临时目录: `<实验目录>/agents/chain`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几步; 一段话说对纲领与目标意味着什么 (`D.BTBOᴵ ≼ read T₃` 是无条件定理了没有; `ChainP` 做到哪个 n).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 条件定理写出前提的 Agda 类型与它的可满足性.
4. 办法: n = 1 两边的形状; 每个 `sˣ` 的值相等是怎么得到的; 一般 n 的不变量.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型; 它是不是在要求判定什么.
6. 偏离与事故.
强度写 ψ₀(Ω_x), 标明是定理还是读法; 下界不写成同值; 不用 "只差", "自然" 一类形容.

## 中途消息（主审发给这一路）

转录时间戳 2026-11-11 11:08 (UTC)：

主审通知 (不改你的任务, 多给已定稿可导入的工具与一条归约): 同一陈述的否定路 (`YiChainNeg`) 已返回并经主审冷编复核, 它的两个文件现在定稿, 你可以导入: `OCF.Lean.YiChainNegLEM`, `OCF.Lean.YiChainNegAdd` (撤销简报里 "不要依赖 YiChainNeg" 这一条).

它的结论: 否定写不出来, 因为 `lem→chainP : LEM → ChainP` (经典逻辑下 `ChainP` 成立); 难处只在构造性的局部判定. 对你直接有用的 (都已编译):
- `TriOn x y = ∀ a b → Sub x (L.suc a) → Sub y (L.suc b) → a ≼ b → b ≼ a ⊎ L.suc a ≼ b` (只对两边实际出现的前驱对要二分); `triOn→cplˣ : TriOn x y → x ≼ y → x ≼ˣ y`;
- `triOn→chainP : (∀ n → TriOn (D.γ n) (read (co (pts n)))) → ChainP` (沿链归纳, 第 n 步的 `≼ᵖ` 经 `VMᵖ` 给出第 n+1 步的值, 不要 `VMᴸ`);
- `val₁ : D.γ 1 ≼ read (co (pts 1))` (无条件); `n1-from : TriOn (D.γ 1) (read (co (pts 1))) → D.γ 1 ≼ᵖ read (co (pts 1))`.
所以 **n = 1 只缺 `TriOn (D.γ 1) (read (co (pts 1)))` 这一个闭的陈述**, 一般的 n 缺 `∀ n → TriOn (D.γ n) (read (co (pts n)))`. 建议把它作为首要目标 (或给出直接的 `≼ᵖ` 推导, 两者等价地够用).

它也说明了哪些一般的捷径走不通 (编译的否定, 都推出 LPO; 只否定 "对一切树" 的引理, 不否定链上的实例): 对一切树的 "左加 1 保持 `≼ˣ`" (`add1→LPO`; 但在 `Strict` 的右树上成立: `add1-strict`, 可用); 对一切严格树的 "左加 ω 保持 `≼ˣ`" (`addω→LPO`); 对一切严格树 `≼ˣ` 的完备 (`cplˣS→LPO`). 所以要用链点自身的结构, 不能只靠 "严格".

它的纸面分析 (没有编译) 指出 n = 1 里判定落在哪里: `F top` 的内层链 c₀ = top, c₁ = top + Ψ⁰ top (值 ω), c₂ = c₁ + Ψ⁰ c₁; c₂ 的第 0 支 c₁ + ω² 的分支是 c₁ + ω·(i+1), 值 ω·(i+2), 这里吸收不成立; 所以推导在这一处要把分支下标平移一位, 在吸收成立处不平移. 判断: 这些子树都由有限路径确定, 值在 ε₀ 之下, 可以给前驱配上 Cantor 范式一类的编码并证明读回逐项一致, 从而判定; 若这样做, 它只能放在验收文件里 (你的文件本来就是验收文件), 并在回报里写明借了记号. 用不用由你判断.

## 回报原文

#### 1 判决

我做到了第 1 步。第 2、3 步只有条件定理，一般的 n 没有证出。

- **对纲领与目标的意思。** `D.BTBOᴵ ≼ read T₃` 还不是无条件定理，只有条件定理 `btbo-cond : P1 → P2 → D.BTBOᴵ ≼ read T₃`。
- **`ChainP` 做到哪里：**
  - n = 0：已有定理 `chainP₀`。
  - n = 1：无条件的编译定理 `chainP₁`，取 m = 1。
  - n ≥ 2：未走通。我没有编译的否定，也不写成路线已否定。
- **n = 1 是两个方向的 `≼ˣ`** (`γ₁≈`)，没有用 `TriOn`。办法是一条新的吸收引理：需要的二分由结构前驱推导的构造子 (`≺z` / `≺s` / `≺l`) 给出，不是值上的判定。所以没有借 Cantor 范式一类的记号编码，否定路回报里建议的那种编码我没有用。
- **新的无条件下界 `T₃-γ₂ : D.γ 2 ≼ read T₃`** (编译定理，是下界，不是同值)。
  - `D.γ 2` 是参照对角链的第 2 项，读法 ψ₀(Ω_{ε₀})。
  - 上一路的定理下界是 ψ₀(Ω_ω) (`T₃-Ωω`)。ψ₀(Ω_{ε₀}) 高于它只是读法，`D.γ 2` 与 ψ⁰(Ω ωᴵ) 的比较没有编译。
  - 主线 `T₃` 的 ψ₀(Ω_Ω) 仍是读法。

#### 2 文件表

都在 `probes/OCF/Lean/`，都是验收文件。冷编译前只删了本模块的 `.agdai`，每份日志只有本模块一行 `Checking`，堆上限 6G。

| 文件 | 总行 / 代码行 | 冷编译退出码 | 常驻峰值 |
|---|---|---|---|
| `YiChainBase.lagda.md` | 105 / 73 | 0 | 1.30G |
| `YiChainOne.lagda.md` | 145 / 95 | 0 | 1.49G |
| `YiChainCond.lagda.md` | 82 / 39 | 0 | 1.35G |
| `YiChainBack.lagda.md` | 119 / 82 | 0 | 1.38G |
| `YiChainFlat.lagda.md` | 45 / 30 | 0 | 1.30G |

- **检索：** `postulate`、洞、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`irrelevant-projections`、`cubical`、`Funext`、本机路径都是 0 处。
- **选项行：** 全是 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。
- **导入：** 从 `YiZeroAccP` 只导入了 `ψ⁰ˣ` 与 `+ˣ`。没有导入 `YiNextVal*`、`YiFree*`。按中途通知可以用 `YiChainNeg*`，但最后没有用到。

#### 3 定理表

`L` = `OCF.Align.Level`，`T₀ = L.Ordᶜ L.zero`。

| 名字 | 逐字的陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `transˣ` | `∀ {a b c : T₀} → a ≼ˣ b → b ≼ˣ c → a ≼ˣ c` | 定义域 `≼ˣ` 传递 | Base | 编译 |
| `Abs.ABS` | 模块参数 `hx : L.ψ⁰ c ≼ˣ X`、`hv : X ≼ L.ψ⁰ c`；`∀ (b : T₀) → L.HS b → c L.≺ b → L.ψ⁰ b ≼ˣ (X L.+ L.ψ⁰ b)` | `X` 与 ψ⁰ c 值相等且 c 是 b 的结构前驱时，ψ⁰ b 吸收左加数 X | Base | 编译 |
| `Abs.VABS` | 同样的模块参数；`… → (X L.+ L.ψ⁰ b) ≼ L.ψ⁰ b` | 吸收的值的一侧 | Base | 编译 |
| `step` | `∀ {X c Y : T₀} → L.HS X → c L.≺ X → L.ψ⁰ c ≼ˣ X → X ≼ L.ψ⁰ c → L.ψ⁰ X ≼ˣ Y → Y ≼ L.ψ⁰ X → (L.ψ⁰ X ≼ˣ (X L.+ Y)) × ((X L.+ Y) ≼ L.ψ⁰ X)` | 累加链的一步 | Base | 编译 |
| `Phi.PHI` | `∀ (b : R) → (L.ψ⁰ (read b) ≼ˣ read (Ψ zero v0 x b)) × (read (Ψ zero v0 x b) ≼ L.ψ⁰ (read b))` | 主线第 0 层的折叠对参照 ψ⁰ (ω 倍错开一位) | One | 编译 |
| `J` | `∀ n → (L.ψ⁰ (read (cc n)) ≼ˣ read (cc (suc n))) × (read (cc (suc n)) ≼ L.ψ⁰ (read (cc n)))` | `F top` 的内层累加链 (`cc = chain zero gk`) 每一步 | One | 编译 |
| `Gc` | `∀ k → D.G k ≼ˣ read (cc k)` | 参照 γ₁ 内部的链落在主线内层链之下 | One | 编译 |
| `chainP₁` | `Σ ℕ λ m → D.γ 1 ≼ᵖ read (co (pts m))` | `ChainP` 在 n = 1，无前提 | One | 编译 |
| `back₁` | `read (co (pts 1)) ≼ˣ D.γ 1` | 反向 | Back | 编译 |
| `γ₁≈` | `(D.γ 1 ≼ˣ read (co (pts 1))) × (read (co (pts 1)) ≼ˣ D.γ 1)` | 第 1 步两个方向都在定义域里 | Back | 编译 |
| `AbsR.ABSR`, `PHIR`, `JR`, `GcR` | 与正向对称 (例如 `ABSR : ∀ b → L.HS b → c L.≺ b → (X L.+ L.ψ⁰ b) ≼ˣ L.ψ⁰ b`) | 反向的吸收、折叠与内层链 | Back | 编译 |
| `chain-cond` | `P1 → P2 → ChainP` | 一般的 n，归约到两条 `≼ˣ` 加强 | Cond | 条件 |
| `btbo-cond` | `P1 → P2 → D.BTBOᴵ ≼ read T₃` | 第 3 步 | Cond | 条件 |
| `p1₀`, `p2₀` | `D.γ 0 ≼ˣ read (co (pts 0)) → L.ψ⁰ (L.Ω (D.L 0)) ≼ˣ L.ψ⁰ (L.Ω (κ 0))`；`L.ψ⁰ (L.Ω (κ 0)) ≼ˣ read (co (pts 1))` | 两个前提在 n = 0 的实例 | Cond | 编译 |
| `tri→P1`, `tri→P2` | `Tri → P1`；`Tri → P2` | 前提在经典模型里成立 | Cond | 编译 |
| `T₃-γ₂` | `D.γ 2 ≼ read T₃` | 参照第 2 项是下界 | Cond | 编译 |
| `ψ⁰-flat` | `∀ {k} (s : L.Ordᶜ k) → L.ψ⁰ s L.≅ L.ψ⁰ (flat s)` | 任意层的 ψ⁰ 结构互模拟于某棵第 0 层树的 ψ⁰ | Flat | 编译 |
| `ABSΩ` | `∀ {X c : T₀} → L.ψ⁰ c ≼ˣ X → X ≼ L.ψ⁰ c → ∀ {k} (s : L.Ordᶜ k) → L.HS (flat s) → c L.≺ flat s → L.ψ⁰ s ≼ˣ (X L.+ L.ψ⁰ s)` | 吸收推广到一切层的参照主项；`HS (flat s)` 与见证是假设 | Flat | 编译 |

两个前提的类型 (在 `YiChainCond` 里)：

```agda
P1 = ∀ n → D.γ n ≼ˣ read (co (pts n)) → L.ψ⁰ (L.Ω (D.L n)) ≼ˣ L.ψ⁰ (L.Ω (κ n))
P2 = ∀ n → L.ψ⁰ (L.Ω (κ n)) ≼ˣ read (co (pts (suc n)))
```

- **白话：**
  - `P1` 只谈参照框架：链点对上 `VMᵖ` 的结论 (值序) 加强到 `≼ˣ`。
  - `P2` 只谈主线：`T₃-own` 的项再加链的一步 (`plus≽`)，加强到 `≼ˣ`。
- **可满足性：**
  - 两者的值的版本都已是定理，所以 `Tri` 推出它们 (`tri→P1`, `tri→P2`)，在经典模型里成立。`Tri` 本身推出 LPO。
  - n = 0 的实例是无条件定理。
  - n ≥ 1 未证。

#### 4 办法

**n = 1 两边的形状 (编译出来的定义性展开)：**
- 参照：`D.γ 1 = lim (λ k → ψ⁰ (D.G k))`。
  - `D.G 0 = 1`，`D.G (k+1) = ψ zero suc (D.G k)` (≅ ψ⁰ (D.G k))。
  - 链不累加。
- 主线：`read (co (pts 1)) = lim (λ k → read (top + Ψ⁰ cₖ))`。
  - c₀ = top，cₖ₊₁ = cₖ + Ψ⁰ cₖ，是第 0 层的累加链。
  - 主线 ω 倍从 y 起，参照从 0 起。

**每个 `sˣ` 的值相等从哪里来：**
- 不逐个比较闭项，统一走三个工具：
  - `+ˣ` (同底加法)：要左加数值相等，这由不变量里随身带的值的反向不等式给出。
  - `PHI`：ω 倍错开一位。
  - 吸收引理 `ABS`。
- **`ABS` 是关键：**
  - 要证 `ψ⁰ b ≼ˣ X + ψ⁰ b`，见证是 `c L.≺ b` (结构前驱) 加上 X 与 ψ⁰ c 值相等。
  - 对见证的推导分情况：
    - `≺z` (c ≅ b′)：左加数与主项值相等，各项错开一位。
    - `≺s`：左加数被吸收，递归，再按结合律对齐。
    - `≺l m`：第 n 项搬到 `g (n ⊔ m)`，靠 `HS` 的步进。
  - 判定全由推导的构造子给出。
- **见证怎么取：**
  - 内层链的见证取上一个链点 (`read cₙ ≺ read cₙ₊₁`，由 `lead`)，第 0 步取 0。
  - 外层左加数 1 的见证取 0 (`z≺`)。
- **反向：** 用同一套见证，`ABSR`、`PHIR`、`JR`。

**一般 n 的不变量：** `inv n : D.γ n ≼ˣ read (co (pts n))`，取 m = n。
- 第 0 步是 `reflˣ`。
- 每一步是 `transˣ (P1 n (inv n)) (P2 n)`，中间点取 `ψ⁰ (Ω (κ n))`。

#### 5 第一个障碍

没有检查器报错。卡住的是缺的引理本身，最早缺的是 `P2 1` 与 `P1 1`。

- **`P2 1`：** 要 `L.ψ⁰ (L.Ω (κ 1)) ≼ˣ read (co (pts 2))`。
  - 其中第一块是 `lower-read` 的 `≼ˣ` 版，层号是极限 `κ 1`：`F (co (pts 1))` 是各支 `top` 折叠的部分和，各支层号是 ⌜top + Ψ⁰ cₖ⌝ (ε₀ 以下的后继 / 极限树)，那里有 ≥ 1 层上的累加链。
  - `≼ˣ` 在第 0 层每个 ω 倍处要值相等，也就是要主线折叠值的**上界** (判断)：

    ```agda
    UB : ∀ a (l : Lgl zero a) → read (F a l) ≼ L.ψ⁰ (L.Ω (L.toLevel (read a) (HS-read a l)))
    ```

    现有的关系族 `RelF` 只给下界，要补一个 "主线 ⊴ 参照" 的反向关系族。
  - n = 1 的第 0 层部分已经构造地做出来了 (`back₁`)。
- **`P1 1`：** 要 `≼ˣ` 版的 `Ψ-emb`。内部 ω 倍的值相等要反向的值单调 (判断)，所以合适的形式大概要两个方向的嵌入：

  ```agda
  ∀ {a b} → XEmb a b → XEmb b a → L.ψ⁰ (L.Ω a) ≼ˣ L.ψ⁰ (L.Ω b)
  ```

  办法是照 `BTBOFullLe` 改写。`γ₁≈` 说明第 1 步确实有两个方向。
- **第 ≥ 1 层上的吸收：** `ABSΩ` 把它归到两条结构事实：`L.HS (flat s)` 与 `flat` 树上一个结构前驱见证。两条都没有证；判断是要 `Uniform` 一类的结构单调理论。
- **是不是在要求判定：** 我判断不是。n = 1 的判定全由结构推导给出，一般情形的缺口是上界与结构单调。否定路编译的 `add1→LPO` 等只否定 "对一切树" 的引理，不碰链上的实例。规模估计 (判断)：两侧对称的关系族加第 ≥ 1 层的结构理论，上千行。

#### 6 偏离与事故

- **新加的结果：** 简报没要求的 `γ₁≈` (反向) 与 `ABSΩ` / `ψ⁰-flat`，是为了把障碍说准；另加了推论 `T₃-γ₂`。
- **编译：** 全程只有一次自己的错误。`YiChainBack` 从 `YiChainOne` 导入 `lead` 失败 (它没被重新导出)，改成 `Phi.lead` 后通过。其余文件都是一次通过。
- **我改动的范围：**
  - 没有改任何已有文件，没碰 `src/`、`archive/`，没有提交。
  - 只删过自己 5 个模块的 `.agdai`，写的是字面路径。
  - 没有在临时目录写 `.agda` 试验。
- **日志：** `<实验目录>/agents/chain/cold-*.log`。

主审冷编请按依赖序：
- `<仓库>/probes/OCF/Lean/YiChainBase.lagda.md`
- `<仓库>/probes/OCF/Lean/YiChainOne.lagda.md`
- `<仓库>/probes/OCF/Lean/YiChainCond.lagda.md`
- `<仓库>/probes/OCF/Lean/YiChainBack.lagda.md`
- `<仓库>/probes/OCF/Lean/YiChainFlat.lagda.md`
