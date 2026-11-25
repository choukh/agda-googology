# 主线折叠的值的上界 (YiUB)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-11 11:26 至 11:57 |
| 工具调用 / agda 编译 (粗数) | 80 / 9 |
| token (usage 字段，按消息去重) | 输出 176247；新写入缓存的输入 454493；读缓存的输入 14692627；其余输入 108 |
| 写过的仓库文件 | `YiUBNeg.lagda.md`, `YiUBOne.lagda.md`, `YiUBP2.lagda.md`, `YiUBRed.lagda.md` |
| 文件前缀 | `YiUB` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 上界一路返回并复核; 第九批的合读 (主审)” 一节 |
| 主审复核后的一句结论 | 第 1 层两个方向对上；对一切合法树的上界被否定（常值极限）；严格的树上两向的折叠界；与 BTBO 持平归到链点读回处处满足的条件，缺第 2 层以上的一步；四件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 任务是 **主线折叠的值的上界**: 证主线的折叠不高于参照 (Level 框架) 在同一层号上的 ψ₀(Ω_·), 并用它把 "与 BTBO 持平" 缺的两条加强之一 (`P2`) 往前推. 这会是乙线的第一个上界. 另有两路同时在做另外两条引理 (前缀 `YiEmb2`, `YiFlat`), 互不依赖. 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇. 特别是 "第 4 层不反过来改前 3 层" (验收只新增关系与定理, 不改树, 折叠, 合法性的定义), Agda 一节 (选项, 文字预算, 退出码, 堆; 函数外延只准作前提), "结论的写法".
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 与 §5.4.
3. **回报原文, 全读**: `probes/Survey/Reports-2026-11-11/YiChain.md` (§4 是 n = 1 怎么做成的, §5 是第一个障碍: `P2 1` 要的上界), `YiLeanVal.md` (主线上只带下界的值证明是怎么写的: 关系族 `RelF`, `FOLD`, `lower-any`).
4. 代码 (都已定稿, 可以导入, 不许编辑; 都在 `probes/OCF/Lean/` 或 `probes/OCF/Align/`):
   - 主线: `YiLeanCore`, `YiLeanFold` (`Ψ`, `chain`, `succ`, `psum`, `Lv`, `cmp`), `YiLeanLegal`, `YiLeanTw3` (`F η l = Ψ zero (lv η l) (λ _ → fold) G.top`, `pts`, `co`, `obs`, `T₃`), 验收 `YiLeanAccFin` (`read`, `fold₀`, `read-plus`), `YiLeanValRel`, `YiLeanValAdd`, `YiLeanValFold` (下界的关系族与 `FOLD`; 你要写的是它的反向), `YiLeanValFin` (`HS-read`, `lower-read`, `κ`, `ChainP`).
   - `n = 1` 已做成的: `YiChainBase` (`transˣ`, 模块 `Abs` 的 `ABS`, `VABS`, `step`), `YiChainOne` (`Phi.PHI`: 第 0 层的折叠对参照 ψ⁰ 两个方向, ω 倍错开一位; `J`, `Gc`, `chainP₁`), `YiChainBack` (反向的 `AbsR`, `PHIR`, `JR`, `GcR`, `back₁`, `γ₁≈`), `YiChainCond` (`P1`, `P2`, `chain-cond`, `btbo-cond`, `p2₀`), `YiChainFlat` (`flat`, `ψ⁰-flat`, `ABSΩ`: 第 1 层以上的吸收, 带两条假设).
   - 定义域: `probes/OCF/Align/YiVmConExact.lagda.md` (`_≼ˣ_`, `_≼ᵖ_`, `≅→≼ˣ`, `⊑→≼ˣ`, `reflˣ`, `ˣ→ᵖ`, `ˣ→≼`, `VMᵖ`), `probes/OCF/Lean/YiZeroAccP.lagda.md` (`ψ⁰ˣ`, `+ˣ`; 只导入这两条).
   - 参照: `OCF.Align.Level` (`ψ⁰`, `Ω`, `toLevel`, `HS`), `OCF.Align.Value`, `OCF.Align.YiBtValBT` 的 `module D`.
   查签名用检索, 大文件不要整篇读.

#### 1 要交的, 分步; 每做成一步先交

1. **值的上界 `UB`.** 陈述 (可以按需要调整, 说明理由):
   ```agda
   UB : ∀ a (l : Lgl zero a) → read (F a l) ≼ L.ψ⁰ (L.Ω (L.toLevel (read a) (HS-read a l)))
   ```
   先 a 是有限的 (第 1, 2 层), 再一般的合法 a. 一般情形的办法: 照 `YiLeanValRel`/`YiLeanValFold` 写一个反向的关系族 (主线的树 ⊴ 参照的树, 底关系是 `read a ≼ y`), 证折叠在一切输入层与目标层上保持它. 注意主线与参照的不同 (都是事实, 见回报): 主线的 ω 倍从第 1 项起而参照从零起; 主线极限层号的顶取部分和而参照逐项; 主线的链累加而参照不累加. 上界要证这些都不使值超过参照; 要用的吸收在第 0 层已有 (`Abs.VABS`, `PHIR`), 第 1 层以上可能要 `ABSΩ` 那种形状的假设: 把要的东西写成带确切类型的模块参数, 其余条件地证出来.
2. **两个方向的 `≼ˣ` 版.** 在 `UB` 与 `lower-read` 的基础上, 证 `L.ψ⁰ (L.Ω (κ n)) ≼ˣ read (obs (pts n))` 与反向 `read (obs (pts n)) ≼ˣ L.ψ⁰ (L.Ω (κ n))` (先 n = 1). 执行方的判断是 `≼ˣ` 在每个 ω 倍处要值相等, 所以两个方向的值界都要用上.
3. **`P2` 的 n = 1, 再一般的 n.** `P2 n : L.ψ⁰ (L.Ω (κ n)) ≼ˣ read (co (pts (suc n)))` (链点是 `co (pts n) + obs (pts n)`; 左加数要吸收). 若同时能给反向 `read (co (pts (suc n))) ≼ˣ L.ψ⁰ (L.Ω (κ n))`, 一并交: 另一路在做 `P1`, 它可能要两个方向的不变量.
4. **若 `P2` 只差第 1 层以上的吸收**, 把它写成以 `ABSΩ` 的两条假设 (`L.HS (flat s)` 与 `c L.≺ flat s`, 对链上出现的 s 与 c) 为模块参数的条件定理, 写明 s, c 是什么; 另一路 (`YiFlat`) 在证这两条.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K (可交显式前提的条件定理); 堆到 6G 仍耗尽 (先按手册 §4.2: 陈述逐字写, 大的参照树放 `opaque`, 隐式参数显式写出, 文件拆小). 做不成的部分写成带确切类型的模块参数, 说明前提在哪些实例上是定理. 没有编译的否定定理时只能写 "未走通". 若发现主线的值其实高于参照 (上界不成立), 那是重要结果: 写成编译的定理交回, 不要绕开.

#### 2 过程要求

- 读完上面的文件后尽快动手: 第一个文件 (哪怕只是有限 a 的上界) 在 20 分钟内写出并编译.
- 每写完一个文件就编译; 每次回复都要有工具调用, 不要在一次回复里只思考.

#### 3 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiUB` (模块名 `OCF.Lean.YiUB…`). 都是验收文件, 文首标 "验收文件"; 允许导入带记号闭包的 `OCF.Align.Value`, `OCF.Align.Level` 与旧验收文件. 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`. 同时在跑的另两路用前缀 `YiEmb2`, `YiFlat` (都在 `probes/OCF/Lean/`), 不要动也不要依赖它们的文件.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提, 用到它的定理在文首标 "条件".
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块.
- 你的临时目录: `<实验目录>/agents/ub`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几步; 一段话说对纲领与目标意味着什么 (`UB` 是无条件的定理了没有; `P2` 做到哪个 n).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 条件定理写出前提的 Agda 类型与它的可满足性.
4. 办法: 反向关系族怎么写的; 三处不同 (ω 倍, 部分和, 累加) 各自怎么不使值超过参照.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
强度写 ψ₀(Ω_x), 标明是定理还是读法; 上界与下界分开写, 不写成同值除非两个方向都编译了; 不用 "只差", "自然" 一类形容.

## 中途消息（主审发给这一路）

转录时间戳 2026-11-11 11:41 (UTC)：

主审通知 (你的任务收窄, 目标更清楚): 两向嵌入那一路 (`YiEmb2`) 已返回并经主审冷编复核, 文件定稿, 你可以导入 `OCF.Lean.YiEmb2` 与 `OCF.Lean.YiEmb2Le` (撤销简报里 "不要依赖 YiEmb2" 这一条).

它的结果: 参照框架一侧 (`P1`) 已全部解决, 无条件: `VMˣ : ∀ x hx y hy → x ≼ˣ y → y ≼ˣ x → L.ψ⁰ (L.Ω (toLevel x hx)) ≼ˣ L.ψ⁰ (L.Ω (toLevel y hy))`, `p1₂ : P1₂` (对一切 n). 并且它把 "与 BTBO 持平" 归约成**只剩主线一侧的一条两向陈述**:
```agda
P2₂ = ∀ n → (L.ψ⁰ (L.Ω (κ n)) ≼ˣ read (co (pts (suc n)))) × (read (co (pts (suc n))) ≼ˣ L.ψ⁰ (L.Ω (κ n)))
btbo-cond₂ : P2₂ → D.BTBOᴵ ≼ read T₃        -- 条件定理, 已编译
p2₂-0 : P2₂ 的 n = 0 实例                    -- 定理
γ₂-cond : P2₂ 的 n = 1 实例 → D.γ 2 与 read (co (pts 2)) 两个方向都在 ≼ˣ 里
```
所以请把你的第 3 步的目标定为 `P2₂` (两个方向都要, 不是可选的): 先 n = 1 (`L.ψ⁰ (L.Ω (κ 1))` 对 `read (co (pts 2))` 两个方向), 再一般的 n. 你的 `UB` 与两向的 `≼ˣ` 版正是它要的两半. 第 1 层以上的吸收仍可以 `ABSΩ` 的两条假设为模块参数 (另一路 `YiFlat` 在证, 已同样被告知要两个方向). 交的时候写一条 `P2₂ → …` 或 `… → P2₂` 的定理, 使得接上 `btbo-cond₂` 就是 BTBO 下界.

转录时间戳 2026-11-11 11:52 (UTC)：

主审通知 (你的目标再收窄一次): 结构事实那一路 (`YiFlat`) 已返回并经主审冷编复核, 四个文件定稿, 你可以导入 `OCF.Lean.YiFlatObs`, `YiFlatWit`, `YiFlatAbs`, `YiFlatChain` (撤销简报里 "不要依赖 YiFlat" 这一条).

它的结果: 第 1 层以上的吸收两个方向都是无条件的定理, 对任意 `a ≺ᴵ b` 与任意第 0 层的 X:
```agda
absΩ  : ∀ {a b} → a L.≺ᴵ b → ∀ {X : T₀} → L.ψ⁰ (L.Ω a) ≼ˣ X → X ≼ L.ψ⁰ (L.Ω a) → L.ψ⁰ (L.Ω b) ≼ˣ (X L.+ L.ψ⁰ (L.Ω b))
absΩR : ∀ {a b} → a L.≺ᴵ b → ∀ {X : T₀} → X ≼ˣ L.ψ⁰ (L.Ω a) → L.ψ⁰ (L.Ω a) ≼ X → (X L.+ L.ψ⁰ (L.Ω b)) ≼ˣ L.ψ⁰ (L.Ω b)
κ≺ : ∀ n → κ n L.≺ᴵ κ (suc n)        -- 无条件
```
并且它把 `P2₂` 归约到主线折叠值的两向界 (都在 `YiFlatChain`):
```agda
FoldB m = (L.ψ⁰ (L.Ω (κ m)) ≼ˣ read (obs (pts m))) × (read (obs (pts m)) ≼ˣ L.ψ⁰ (L.Ω (κ m)))
p2-from-fold : (∀ n → FoldB (suc n)) → ∀ n → P2at n      -- P2at 与 YiEmb2.P2₂ 的第 n 项逐字相同
```
所以 "与 BTBO 持平" 现在**只差 `∀ n → FoldB (suc n)`**: 主线折叠的输出 `obs (pts m)` 与它自己层号上的参照 ψ⁰ (Ω (κ m)) 两个方向都落在 `≼ˣ` 里 (m ≥ 1). 这正是你的第 1, 2 步 (上界 `UB` 与两向的 `≼ˣ` 版). 请把交付对准它: 最终写一条 `∀ n → FoldB (suc n)` (或先 m = 1), 接上 `p2-from-fold`, `YiEmb2.btbo-cond₂` 就是无条件的 BTBO 下界; 能接就在你的文件里接上 (写成一条无前提的 `D.BTBOᴵ ≼ read T₃`). 需要第 1 层以上的吸收时直接用 `absΩ`, `absΩR`, 不再需要模块参数.

## 回报原文

#### 1 判决

我做成了第 1 层的上界 (两个方向都无条件)，并编译了一条否定：简报给的 `UB` 对一切合法的 `a` 不成立。第 2、3 步只到条件定理，无条件的 BTBO 下界没有接上。

**对纲领与目标：**
- **`UB` 只在第 1 层是无条件定理。** `ub₁ˣ`/`lb₁ˣ`：读回的 `F (fin 1)` 与参照 ψ₀(Ω₁) 两个方向都在 `≼ˣ` 里。
- **简报原文的 `UB` 是假的，已编译否定 (`no-UB`)。**
  - 反例 `aₒ = lim (λ _ → top)` 是合法树：`Cp` 允许相邻两项相等。
  - 主线在极限层号上对各支取部分和，编译的下界是 `suc X ≼ read (F aₒ lₒ)`；参照逐项取，编译的上界是 `ref ≼ X`，X = ψ₀(Ω₁)。
  - 按 AGENTS 应读作 "量化域太宽"。它不否定链点上的上界：链点的极限严格增长。
- **一般的 `a`：** 两向定理 `FOLD2` 带前提 `Str`。
  - `Str` 在极限处只要相邻两支的读回是结构前驱 `≺`。这是树侧的条件，不引用参照；部分和用 `absΩ`/`absΩR` 吸收。
  - `Str` 在后继处是这一层的两向陈述 `SucP`。`SucP` 又归约到两条链的逐项两向 `ChainPt`。
- **`P2₂` 与 BTBO 下界：**
  - 条件定理 `btbo-str : StrChain → D.BTBOᴵ ≼ read T₃`。
  - n = 1 的 `p2₂-1` 只要 `Str (co (pts 1))`。
  - `∀ n → FoldB (suc n)` 没有做成。剩下的是第 1 层以上的链的一步 (第 5 节)。

**强度：** 第 1 层是 ψ₀(Ω₁) 两个方向的定理。其余高于 ψ₀(Ω_ω) 的都还是条件定理或读法。

#### 2 文件表

都在 `probes/OCF/Lean/`，都是验收文件。冷编译前只删了本模块的 `.agdai`，每份日志只有一行本模块的 `Checking`，堆上限 6G。

| 文件 | 总行 / 代码行 | 冷编退出码 | 常驻峰值 |
|---|---|---|---|
| `YiUBOne.lagda.md` | 43 / 26 | 0 | 1.46G |
| `YiUBRed.lagda.md` | 123 / 73 | 0 | 1.46G |
| `YiUBNeg.lagda.md` | 60 / 38 | 0 | 1.39G |
| `YiUBP2.lagda.md` | 54 / 32 | 0 | 1.46G |

- **冷编顺序：** One → Red → Neg → P2。
- **检索为 0 处：** `postulate`、洞、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`irrelevant-projections`、`--cubical`、`Funext`、本机路径。
- **选项行：** 全是 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。

#### 3 定理表

`L` = `OCF.Align.Level`；`Two A B = (A ≼ˣ B) × (B ≼ˣ A)`。

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `ub₁ˣ` | `read (F (fin 1) tt) ≼ˣ Ω₁ᵀ`，其中 `Ω₁ᵀ = L.ψ⁰ (L.Ω (L.toLevel (read (fin 1)) (HS-read (fin 1) tt)))` | 第 1 层上界，定义域版 | One | 编译 |
| `lb₁ˣ` | `Ω₁ᵀ ≼ˣ read (F (fin 1) tt)` | 第 1 层下界，定义域版 | One | 编译 |
| `ub₁` | `read (F (fin 1) tt) ≼ Ω₁ᵀ` | 值的上界 | One | 编译 |
| `no-UB` | `¬ (∀ a (l : Lgl zero a) → read (F a l) ≼ L.ψ⁰ (L.Ω (L.toLevel (read a) (HS-read a l))))` | 对一切合法树的上界不成立 | Neg | 编译 (否定) |
| `low`, `ref≼X`, `no-ub` | `L.suc X ≼ read (F aₒ lₒ)`；`L.ψ⁰ (L.Ω (L.toLevel (read aₒ) (HS-read aₒ lₒ))) ≼ X`；反例上的否定 | 反例的两半 | Neg | 编译 |
| `no-str` | `¬ Str aₒ lₒ` | 前提 `Str` 排除这个反例 | Neg | 编译 |
| `absorb2` | `∀ {X Y : T₀} {a b} → a L.≺ᴵ b → Two (L.ψ⁰ (L.Ω a)) X → Two (L.ψ⁰ (L.Ω b)) Y → Two (L.ψ⁰ (L.Ω b)) (X L.+ Y)` | 两向吸收 (用 `absΩ`/`absΩR`) | Red | 编译 |
| `FOLD2` | `∀ a (l : Lgl zero a) → Str a l → Two (L.ψ⁰ (L.Ω (L′ a l))) (read (F a l))` | 一般层号的两向折叠，带前提 | Red | 编译 (带前提) |
| `UB-str` | `∀ a (l : Lgl zero a) → Str a l → read (F a l) ≼ L.ψ⁰ (L.Ω (L.toLevel (read a) (HS-read a l)))` | 改过量化域的 `UB` | Red | 编译 (带前提) |
| `sucP₀` | `SucP G.zero tt` | 第 1 层的 `SucP` | Red | 编译 |
| `chainPt₀` | `∀ b (l : Lgl zero b) → Str b l → ChainPt b l 0` | 链的第 0 项 | Red | 编译 (带前提) |
| `sucP-chain` | `∀ b (l : Lgl zero b) → (∀ n → ChainPt b l n) → SucP b l` | 后继层号归约到链的逐项 | Red | 条件 |
| `foldB₀` | `FoldB 0` | `T₃` 第 0 项两向 | P2 | 编译 |
| `foldB` | `∀ m → Str (co (pts m)) (lw (pts m)) → FoldB m` | 链点上的两向折叠 | P2 | 条件 |
| `p2₂-str` | `StrChain → P2₂` | `P2₂` 的归约 | P2 | 条件 |
| `btbo-str` | `StrChain → D.BTBOᴵ ≼ read T₃` | BTBO 下界 | P2 | 条件 |
| `p2₂-1` | `Str (co (pts 1)) (lw (pts 1)) → (L.ψ⁰ (L.Ω (κ 1)) ≼ˣ read (co (pts 2))) × (read (co (pts 2)) ≼ˣ L.ψ⁰ (L.Ω (κ 1)))` | `P2₂` 的 n = 1 | P2 | 条件 |
| `γ₂-str` | 同一前提 `→ (D.γ 2 ≼ˣ read (co (pts 2))) × (read (co (pts 2)) ≼ˣ D.γ 2)` | 参照第 2 项与第 2 个链点两向 | P2 | 条件 |

**前提的确切类型 (都在 Red)：**
```agda
L′ a l = L.toLevel (read a) (HS-read a l)
SucP b l = Two (L.ψ⁰ (L.Ω (L′ (G.suc b) l))) (read (F (G.suc b) l))
Str G.zero l = ⊤ ; Str G.top l = ⊤ ; Str (G.suc b) l = SucP b l
Str (G.lim f) (st , lf) = (∀ n → Str (f n) (lf n)) × (∀ n → read (f n) L.≺ read (f (suc n)))
ChainPt b l n = Two (L.ψ⁰ (refγ (L′ b l) n))
  (read (Ψ zero (lv b l) (λ _ → fold) (chain ⌜ b ⌝ (Ψ ⌜ b ⌝ (lv b l) (self ⌜ b ⌝)) n)))
StrChain = ∀ n → Str (co (pts (suc n))) (lw (pts (suc n)))   -- 在 P2
```
其中 `refγ c = iterᴸ (λ x → L.ψ L.zero (λ r → r) (L.up L.zero x)) (L.Ω c)`。

**可满足性：**
- `Str` 在 `zero`、`top`、`fin 1` 上成立。
- 在常值极限上编译地不成立 (`no-str`)。
- `StrChain` 未证。我判断 (纸面展开) `Str (co (pts 1))` 含每个有限层号 ≥ 2 上的 `SucP`：`top + Ψ⁰ top` 的各项是 `suc^{n+1} top`。`Str (co (pts 1))` 还含后继的极限层号上的 `SucP`。
- 我没有发现反例。

#### 4 办法

**我没有写反向关系族 (偏离简报建议的办法)。** 改做三步：
1. 第 1 层直接用已有的 `PHIR`/`GcR` (上界) 与 `PHI`/`Gc` (下界)。`F (fin 1)` 与 `F top` 定义性相同，逐项对齐，不错开下标。
2. 对 `a` 递归的归约 `FOLD2`。
3. 链上的归约接 `p2-from-fold` 与 `btbo-cond₂`。

**三处不同各自怎么处理：**
- **ω 倍：** 主线从 y 起，参照从 0 起，错开一位 (第 0、1 层的 `succR`/`PHIR`)。只要错位，不使值超过参照。
- **部分和：** 不加条件时值会超过参照 (`no-UB`，编译)。加 `Str` 的严格条件后，第 n-1 个部分和被第 n 支吸收：`absorb2` 加上 `L.toLevel-≺` 把读回的 `≺` 变成层号的 `≺ᴵ`。
- **累加：**
  - 第 0 层由已有的 `Abs`/`AbsR` 处理 (第 1 层的链在第 0 层上)。
  - 第 1 层以上被隔离成 `ChainPt b l (suc n)`，未证。

#### 5 第一个障碍

没有检查器报错。卡住的是缺的引理本身。

**最早的实例是 `ChainPt G.top tt 1`** (第 2 层 `SucP G.top tt` 的第 1 项)：
- 一边是 `L.ψ⁰ (L.ψ L.zero (λ r → r) (L.up L.zero (L.Ω (L.suc L.zero))))`。
- 另一边是 `read (Ψ zero (vs v0) (λ _ → fold) (plus L1 G.top (Φ G.top)))`，其中 `Φ = Ψ L1 (vs v0) (self L1)`。
- 两边的读法都是 ψ₀(Ω₁²)，这是读法，不是定理。

**缺的引理，大致类型：**
```agda
∀ b (l : Lgl zero b) → (树侧严格) → SucP b l
```
它要一个第 1 层以上主线对参照的跨族关系，并且这个关系在 `θ + Φ θ` 一步下保持。以下都是判断 (纸面分析，未编译)：
- **结点规则不能照 `RelF` 的 `ndr` 逐支镜像。** `c₁ = top + Φ top` 的第 0 支是 `top + top` (Ω·2)，参照 `ψ₁(Ω₁)` 的第 0 支是 Ω₁，逐支不成立。两边的折叠都不读第 0 支 (链从 `top` 或 Ω₀ = 1 起)，所以结点的定义域要限制在起点以上，并且要共尾的比较。
- **第 0 层内部的链要吸收的值不是 ψ⁰(Ω a) 的形状** (如 ψ⁰(X + G y))，`absΩ` 不覆盖，要 `ABSΩ` 那类 `HS (flat s)` 与见证。
- **不是在要求判定：** 需要的二分都可以由结构给出。
- **规模估计：** 上千行。

#### 6 偏离与事故

- **没写反向关系族：** 理由见第 4、5 节。
- **改了 `UB` 的陈述：** 对一切合法树的版本是编译的否定，正面的版本放在 `Str` 上。
- **导入：** 按两次中途通知导入了 `YiEmb2` (`P2₂`, `p2₂-0`, `btbo-cond₂`, `γ₂-cond`) 与 `YiFlatAbs`/`YiFlatChain` (`absΩ`, `absΩR`, `FoldB`, `step₂`, `p2-from-fold`)。
  - 中间一版用 `YiChainFlat` 的 `flat` 假设作前提，收到 `YiFlat` 的通知后换成无条件的 `absΩ`，前提随之变成树侧的 `read (f n) ≺ read (f (suc n))`。最终版本不导入 `YiChainFlat`。
- **改动范围：**
  - 只新建了上面四个文件，没有改任何已有文件，没碰 `src/`、`archive/`，没有提交。
  - git status 里已修改的 `AGENTS.md` 等是开工前就有的。
  - 只删过自己四个模块的 `.agdai`，写的是字面路径，删过两次。
  - 没有写临时的 `.agda` 试验。
- **日志：** `<实验目录>/agents/ub/cold-*.log`。

文件 (按依赖序冷编)：
- `<仓库>/probes/OCF/Lean/YiUBOne.lagda.md`
- `<仓库>/probes/OCF/Lean/YiUBRed.lagda.md`
- `<仓库>/probes/OCF/Lean/YiUBNeg.lagda.md`
- `<仓库>/probes/OCF/Lean/YiUBP2.lagda.md`
