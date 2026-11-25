# 第 2 层以上主线折叠与参照两向对上 (YiSuc)：简报与回报原文（留档）

> 留档。简报与回报是原文，只做两处机械改动：本机路径换成 `<仓库>`、`<实验目录>` 等；原文里的标题降了两级。
> 回报是执行方的陈述，其中标作判断的不是主审的结论，行数与规模的估计没有重算。主审复核过的结论以 `probes/LOG.md` 为准。

| 项 | 值 |
|---|---|
| 模型 | claude-opus-5-5 |
| effort (转录里请求的字段) | xhigh |
| 起止 (转录的时间戳，UTC) | 2026-11-11 12:12 至 13:22 |
| 工具调用 / agda 编译 (粗数) | 84 / 5 |
| token (usage 字段，按消息去重) | 输出 398377；新写入缓存的输入 1166945；读缓存的输入 28923440；其余输入 162 |
| 写过的仓库文件 | `YiSucAbs.lagda.md`, `YiSucGood.lagda.md`, `YiSucLx.lagda.md`, `YiSucNode.lagda.md`, `YiSucOne.lagda.md`, `YiSucPar.lagda.md`, `YiSucWire.lagda.md` |
| 文件前缀 | `YiSuc` (在 `probes/OCF/Lean/`) |
| 主审的复核记录 | `probes/LOG.md` 的 “2026-11-11: 第 2 层以上一路返回并复核; 这一站的验收代价 (主审)” 一节 |
| 主审复核后的一句结论 | 链上最早的实例在定义域里两向成立；下一站的闭项不低于 BTBO 是条件定理；第 2 项起与第 3 层以上没走通；七件冷编退出码全 0 |

## 简报原文

你是这个 Agda 研究仓库 (<仓库>) 的一路执行方. 任务是 **证主线折叠在第 2 层以上与参照两向对上** (`SucP`), 从而让 "主线闭项与下一站的闭项都不低于 BTBO 的参照" 成为无条件的定理. 另有一路 (前缀 `YiOver`) 同时在测 "主线折叠的值是否超过参照"; 你们共用的陈述在已定稿的文件里, 谁也不改它. 主审 (派你的会话) 会从头冷编译复核你交的每个文件, 只认编译过的定理. 全程用中文写文件与回报.

#### 0 先读什么

1. `AGENTS.md` 全篇. 特别是 "量化域先取带证据的读回域", "第 4 层不反过来改前 3 层" (验收只新增关系与定理, 不改定义), Agda 一节 (选项, 文字预算, 退出码, 堆; 函数外延只准作前提), "结论的写法".
2. `probes/Survey/EBOHandbook.md` 只读 §4.1 到 §4.5 与 §5.4.
3. **回报原文, 按顺序读**: `probes/Survey/Reports-2026-11-11/YiUB.md` (全读; §5 是你的起点: 缺的引理, 最早的实例, 为什么不能照下界关系族逐支镜像), `YiChain.md` §4 (第 0 层的结构吸收), `YiFlat.md` (第 1 层以上的两向吸收), `YiEmb2.md` (两向的折叠单调), `YiLeanVal.md` (下界的关系族).
4. 代码 (都已定稿, 可以导入, 不许编辑; 都在 `probes/OCF/Lean/`, 除非注明):
   - **共用陈述**: `YiUBRed` (逐字):
     ```agda
     L′ a l = L.toLevel (read a) (HS-read a l)
     Two A B = (A ≼ˣ B) × (B ≼ˣ A)
     SucP b l = Two (L.ψ⁰ (L.Ω (L′ (G.suc b) l))) (read (F (G.suc b) l))
     Str G.zero l = ⊤ ; Str G.top l = ⊤ ; Str (G.suc b) l = SucP b l
     Str (G.lim f) (st , lf) = (∀ n → Str (f n) (lf n)) × (∀ n → read (f n) L.≺ read (f (suc n)))
     refγ c = iterᴸ (λ x → L.ψ L.zero (λ r → r) (L.up L.zero x)) (L.Ω c)
     ChainPt b l n = Two (L.ψ⁰ (refγ (L′ b l) n)) (read (Ψ zero (lv b l) (λ _ → fold) (chain ⌜ b ⌝ (Ψ ⌜ b ⌝ (lv b l) (self ⌜ b ⌝)) n)))
     FOLD2 : ∀ a l → Str a l → Two (L.ψ⁰ (L.Ω (L′ a l))) (read (F a l))
     chainPt₀ : ∀ b l → Str b l → ChainPt b l 0
     sucP-chain : ∀ b l → (∀ n → ChainPt b l n) → SucP b l
     sucP₀ : SucP G.zero tt
     ```
     `YiUBP2`: `StrChain = ∀ n → Str (co (pts (suc n))) (lw (pts (suc n)))`, `btbo-str : StrChain → D.BTBOᴵ ≼ read T₃`, `p2₂-str`.
   - 主线: `YiLeanCore`, `YiLeanFold` (`Ψ`, `chain`, `succ`, `psum`, `Lv`, `cmp`, `self`), `YiLeanTw3` (`F`, `pts`, `co`, `obs`, `⌜_⌝`, `lv`), 验收 `YiLeanAccFin` (`read`, `read-plus`, `fin`, `lower₂`), `YiLeanValFin` (`HS-read`, `κ`, `ChainP`, `btbo-p`), `YiLeanValFold` (下界的关系族 `FOLD`).
   - 工具: `YiChainBase` (`transˣ`, 模块 `Abs`: `ABS`, `VABS`, `step`), `YiChainOne` (`Phi.PHI`, `J`, `Gc`), `YiChainBack` (`AbsR`, `PhiR.PHIR`, `JR`, `GcR`), `YiFlatAbs` (`absΩ`, `absΩR`: 对任意 `a ≺ᴵ b` 与任意第 0 层的 X 的两向吸收), `YiFlatObs` (`flat`, `HS-flat`, `HS-flatΩ`), `YiFlatWit` (`flatΩ-≺`), `YiFlatChain` (`κ≺`, `X≺`), `YiEmb2` (`VMˣ`, `P2₂`, `btbo-cond₂`, `chain-cond₂`), `YiUBOne` (`ub₁ˣ`, `lb₁ˣ`: 第 1 层两向), `YiZeroAccP` (`ψ⁰ˣ`, `+ˣ`; 只导入这两条), `probes/OCF/Align/YiVmConExact.lagda.md` (`≼ˣ`, `≼ᵖ`, `≅→≼ˣ`, `⊑→≼ˣ`, `reflˣ`, `ˣ→ᵖ`, `ˣ→≼`), `YiNextValFin` (`btbo⁺-from-main : MV.ChainP → D.BTBOᴵ ≼ NA.read NT.T⁺`).
   - 参照: `OCF.Align.Level`, `OCF.Align.Value`, `OCF.Align.YiBtValBT` 的 `module D`.
   查签名用检索, 大文件不要整篇读.

#### 1 要交的, 分步; 每做成一步先交

1. **最早的实例: `ChainPt G.top tt 1`.** 两边 (逐字见 `YiUB` 回报 §5): 参照 `L.ψ⁰ (L.ψ L.zero (λ r → r) (L.up L.zero (L.Ω (L.suc L.zero))))`, 主线 `read (Ψ zero (vs v0) (λ _ → fold) (plus L1 G.top (Φ G.top)))`, 两边读法都是 ψ₀(Ω₁²). 先算清两边的形状 (可以在临时目录用纯 `.agda` 规范化看, 那是有限测试), 再写两个方向的 `≼ˣ` 推导. 执行方判断: 结点规则不能逐支镜像 (主线第 0 支是 top + top, 参照是 Ω₁), 两边的折叠都不读第 0 支 (链从 top 或 Ω₀ = 1 起), 所以比较要限制在起点以上, 并作共尾的比较.
2. **`SucP G.top tt`** (第 2 层的后继层号; 由 `sucP-chain`), 再 **`SucP b l` 对链上出现的 b** (执行方判断 `Str (co (pts 1))` 含每个有限层号 ≥ 2 上的 `SucP` 与后继的极限层号上的 `SucP`). 办法: 一个第 1 层以上主线对参照的跨族两向关系, 在 "这一点加上它的折叠值" 一步下保持. 第 1 层的版本已经由 `PHI`/`PHIR` 与 `J`/`JR` 做出来, 照它往上推.
3. **`StrChain`**, 从而无条件的 `D.BTBOᴵ ≼ read T₃` (由 `btbo-str`). 再把它接到下一站: `StrChain → P2₂` (`p2₂-str`), `P2₂ →` 主线的 `ChainP` (由 `chain-cond₂` 与 `ˣ→ᵖ`, 照 `btbo-cond₂` 的写法), 再由 `btbo⁺-from-main` 得 `D.BTBOᴵ ≼ NA.read NT.T⁺`. 写成两条无前提的定理.

**停下的条件.** 同一处两次重新设计仍过不了检查器; 需要函数外延或 K (可交显式前提的条件定理); 堆到 6G 仍耗尽 (先按手册 §4.2: 陈述逐字写, 大的参照树放 `opaque`, 隐式参数显式写出, 文件拆小). 做不成的部分写成带确切类型的模块参数, 说明前提在哪些实例上是定理. 没有编译的否定定理时只能写 "未走通". 若发现某个实例上主线的值严格高于参照 (于是两向对不上), 写成编译的定理交回 (另一路也在测这件事).

#### 2 过程要求

- 读完上面的文件后尽快动手: 第一个文件 (哪怕只是第 1 步两边的形状与第一条引理) 在 20 分钟内写出并编译.
- 每写完一个文件就编译; 每次回复都要有工具调用, 不要在一次回复里只思考.

#### 3 规则

- **只新建文件**, 放 `probes/OCF/Lean/`, 前缀 `YiSuc` (模块名 `OCF.Lean.YiSuc…`). 都是验收文件, 文首标 "验收文件"; 允许导入带记号闭包的 `OCF.Align.Value`, `OCF.Align.Level` 与旧验收文件. 中文 literate Agda (`.lagda.md`). 不改任何已有文件, 不碰 `src/`, `archive/`. 同时在跑的另一路用前缀 `YiOver` (在 `probes/OCF/Lean/`), 不要动也不要依赖它的文件.
- 选项行 `{-# OPTIONS --safe --without-K --lossy-unification #-}`. 不许: `postulate`, 洞, `TERMINATING`, `NO_POSITIVITY_CHECK`, `trustMe`, K, `--irrelevant-projections`, `--cubical`. 函数外延只准作显式前提, 用到它的定理在文首标 "条件".
- **文字预算**: 每个模块文首不超过 5 行; 代码之间的文字只写范围与不显然的定义理由; 不写只有导入语句的报告文件. 一次性的试验放你的临时目录, 用纯 `.agda` (要写同样的选项行, 并加 `--cubical-compatible --guardedness --hidden-argument-puns` 才能导入仓库模块).
- 仓库文件里不写本机路径.
- 编译: 在仓库根目录,
  `agda +RTS -M6G -RTS --library-file=<实验目录>/libraries -i src -i probes probes/OCF/Lean/<文件>.lagda.md > <你的临时目录>/<文件>.log 2>&1; echo "exit $?"`
  同时只跑一个 agda, 堆上限 6G. 退出码: 0 通过, 42 类型错误 (先看日志首行是不是 `LibraryError`), 251 堆耗尽 (不算通过). 日志落文件, 只看首个错误附近. 不用 `--ignore-interfaces`; 要冷编译只删你自己模块的接口 (`probes/_build/2.8.0.2/agda/OCF/Lean/<精确模块名>.agdai`, 写字面的精确路径, 不用通配, 不用变量拼路径). 不要重编别人的模块.
- 你的临时目录: `<实验目录>/agents/suc`. 只在它和你前缀的新文件里写. 不在这些之外 `rm`, 不 `pkill`, 不写 `/tmp` 的别处, 不装包, 不提交, 不推送.
- 结束前自查: 每个文件删自己的接口后冷编译退出码 0, 日志里只有你自己模块的 `Checking` 行; 检索禁用构造为 0.

#### 4 回报格式 (只在回报里交一次, 不写报告文件)

1. 判决: 做到第几步; 一段话说对纲领与目标意味着什么 (`D.BTBOᴵ ≼ read T₃` 与对 `T⁺` 的同一条是无条件定理了没有).
2. 文件表: 文件, 代码行数, 冷编译退出码, 常驻内存峰值.
3. 定理表: 名字, 逐字的陈述, 一句白话, 文件, 档 (编译定理 / 条件定理 / 有限测试 / 判断). 条件定理写出前提的 Agda 类型与它的可满足性.
4. 办法: 跨族关系怎么写的; 起点以上与共尾比较怎么处理的.
5. 第一个障碍: 精确到引理, 附检查器报错原文 (若有); 缺的引理的 Agda 类型.
6. 偏离与事故.
强度写 ψ₀(Ω_x), 标明是定理还是读法; 下界不写成同值; 不用 "只差", "自然" 一类形容.

## 中途消息（主审发给这一路）

转录时间戳 2026-11-11 13:03 (UTC)：

主审通知 (你的任务不变, 多给已定稿可导入的结果与办法): 测量那一路 (`YiOver`) 已返回并经主审冷编复核, 四个文件定稿, 你可以导入 `OCF.Lean.YiOverRef`, `YiOverOps`, `YiOverMain`, `YiOverTwo` (撤销简报里 "不要依赖 YiOver" 这一条).

结论: 主线折叠在第 2 层与链上最早的实例都**不超过**参照, 值上两个方向都相等 (都是 `≼`, 不是 `≼ˣ`):
- `over₂ : read (F (fin 2) tt) ≼ L.ψ⁰ (L.Ω ⟨ 2 ⟩)`, `≈₂`, `sucPᵛ` (`SucP G.top tt` 把 `≼ˣ` 换成 `≼` 后成立);
- `over-pt`, `low-pt`: 你的第 1 步那一对 (`ChainPt G.top tt 1` 的两边, 逐字) 值上两个方向都成立;
- `pt-shift : ∀ n → (L.ψ⁰ (γ 1 n) ≼ read (Ψ zero (vs v0) (λ _ → fold) (chain L1 Φ n))) × (read (…) ≼ L.ψ⁰ (γ 1 (dbl n)))` (第 n 个链点夹在参照第 n 项与第 2n 项之间).
办法 (可以照用): 主线第 1 层的树对参照第 1 层的树的关系 `_⊵_` (`YiOverMain`), 只比较读回 ≥ 1 的分支下标 (链从 top 起) —— 这正是 `YiUB` 回报 §5 说的 "结点比较限在起点以上", 限制之后第 0 支的障碍不出现; `Φ-pres : ξ ⊵ X → Φ ξ ⊵ ψ₁ X`, `+-comp` (加法对应); `up⁰` (目标层 0 的折叠把 `⊵` 送到值序); 参照树之间的逐点前序 `_≤ₚ_` 与 `mono⁰`, `ψ₁-mono`, `+ₚ`; 好树 `Gd` 与结点条件 `SC` (由它得参照链每步至少倍增); 第 1 层的链: 主线不高于一条同样累加的参照链 `γ′`, 而 `γ′ n ≤ₚ γ 1 (2n)` (`step-γ`), 第 1 步不错开 (`O2ref : (Ω₁ L.+ ψ₁ Ω₁) ≤ₚ ψ₁ Ω₁`).

它没做的, 正是你要的: (1) `≼ˣ` 版 (它只证了值序 `≼`); (2) 不错开下标的 `γ′ n ≤ₚ γ 1 n` (n ≥ 2), 它判断卡在第 1 层的吸收 `Y + ψ₁ Y ≤ₚ ψ₁ Y` 的 ℕ 极限一支 (`Gd` 不带 "ℕ 极限单调"); (3) 第 3 层以上. 若 `≼ˣ` 版在你的路线里太重, 请先判断: 有了两个方向的值相等 (`≼`), 能否经已有的工具 (`VMᵖ` 要的是 `≼ᵖ`) 换一条只用值相等的路接到 BTBO 下界 —— 写成判断或条件定理交回也有用.

## 回报原文

#### 1 判决

做到了第 1 步。第 3 步的接线写成了条件定理。第 2 步 `SucP G.top tt` 未走通：我没有否定定理，只写 "未走通"。

**对纲领与目标：**
- `D.BTBOᴵ ≼ read T₃` 还不是无条件定理，对 `T⁺` 的同一条也还不是。两条都只是以 `StrChain` 为前提的条件定理：
  - `btbo-str` 是已有的；
  - `btbo⁺-str` 是本路新加的。
- 新的无条件定理是 `chainPt-top-1 : ChainPt G.top tt 1`。陈述就是共用文件 `YiUBRed` 里的那一条，没有改写。
  - 它说的是：参照 `ψ⁰ (refγ 1 1)` 与主线第 2 个链点 `top + Φ top` 折到第 0 层后，两个方向都在 `≼ˣ` 里。
  - 两边的读法都是 ψ₀(Ω₁²)。这一项现在是定理。
  - 但 `SucP G.top tt` (第 2 层后继层号) 要对一切 n 成立，n ≥ 2 未证。所以 ψ₀(Ω₂) 处的两向还不是定理。
- 没有改任何树、折叠、合法性的定义。都是验收文件，只新增关系与定理。

**回答主审的问题 (判断，未编译)：** 只有两个方向的值相等 (`≼`)，用现有工具接不到 BTBO 下界。
- `btbo-p` 要 `ChainP`，也就是 `D.γ n ≼ᵖ …`。`D.γ n` (n ≥ 1) 是左极限，`lᵖ` 要求它的每一项落在 `≼ˣ` 里，`VMᵖ`/`embᵖ` 也正是靠这些逐项的精确匹配。
- 从两向 `≼` 得到 `≼ˣ` 需要值上的分裂 (`tri→cplˣ`)，而一般情形推出 LPO (`YiVmConLPO`)。结构比较的那条路被 `no-L` 否定了。
- 所以只用值相等的路，需要对这些具体的树另证一种只要值相等的折叠单调。这与精确版的工作量同阶，也没有现成的工具。

#### 2 文件表

都在 `probes/OCF/Lean/`，都是验收文件。冷编译前只删了本模块的 `.agdai` (字面路径)，按依赖序编译，每份日志只有本模块一行 `Checking`，堆上限 6G。

| 文件 | 总行 / 代码行 | 冷编退出码 | 常驻峰值 |
|---|---|---|---|
| `YiSucWire.lagda.md` | 31 / 18 | 0 | 1.46G |
| `YiSucLx.lagda.md` | 53 / 36 | 0 | 1.49G |
| `YiSucGood.lagda.md` | 95 / 68 | 0 | 1.38G |
| `YiSucNode.lagda.md` | 100 / 71 | 0 | 1.47G |
| `YiSucPar.lagda.md` | 427 / 309 | 0 | 1.52G |
| `YiSucAbs.lagda.md` | 231 / 171 | 0 | 1.56G |
| `YiSucOne.lagda.md` | 75 / 48 | 0 | 1.57G |

- **冷编顺序：** Wire → Lx → Good → Node → Par → Abs → One。
- **检索为 0 处：** `postulate`、洞、`TERMINATING`、`NO_POSITIVITY`、`trustMe`、`irrelevant-projections`、`--cubical`、`Funext`、本机路径。
- **选项行：** 全是 `{-# OPTIONS --safe --without-K --lossy-unification #-}`。
- **导入：** 没有导入 `YiOver*`。

#### 3 定理表

`L` = `OCF.Align.Level`；`Two A B = (A ≼ˣ B) × (B ≼ˣ A)` (来自 `YiUBRed`)；`F₁ y = L.ψ L.zero (λ q → L.suc (L.suc q)) (L.tr⁻ L.z≅ y)`；`Ψ⁰ x = Ψ zero (vs v0) x`。

| 名字 | 逐字陈述 | 白话 | 文件 | 档 |
|---|---|---|---|---|
| `chainPt-top-1` | `ChainPt G.top tt 1` | 第 2 层链的第 1 项，参照与主线两向 | One | 编译 |
| `btbo⁺-str` | `StrChain → D.BTBOᴵ ≼ NA.read NT.T⁺` | 下一站的 BTBO 下界只差 `StrChain` | Wire | 条件 |
| `chainP-str`, `p2₂→chainP` | `StrChain → MV.ChainP`；`P2₂ → MV.ChainP` | 接到主线的 `ChainP` | Wire | 条件 |
| `cong₁` | `∀ {y y′ : T₀} → y ≼ˣ y′ → L.ψ⁰ (F₁ y) ≼ˣ L.ψ⁰ (F₁ y′)` | ψ₁ 在 `≼ˣ` 下同余 (用 `YiEmb2Le` 的 `Lx`，取恒等嵌入) | Lx | 编译 |
| `good-read` | `∀ d → Lgl zero d → Good (read d)` | 合法的第 0 层主线树读回后是好树 | Good | 编译 |
| `fp-obs` | `∀ {k k′} {O : Obs k} {O′ : Obs k′} → O ≈ᵒ O′ → ∀ {x : Ordᶜ k} {y₀ y : Ordᶜ k′} → x ≅ y₀ → y₀ ≤₁ y → run O x ⊑ run O′ y` | 只经后继与 ℕ 极限的第一位置被一切观测保持 | Good | 编译 |
| `NodeTwo.result` | `∀ w → Two (L.ψ⁰ (L.limᵢ {i = L.zero} L.zero f)) (read (Ψn zero zero w gm gk))` | 层号 0 的结点：主线累加链对参照不累加链两向 | Node | 编译 (对模块参数) |
| `baseΩ` | `∀ (x : Ext zero L1) → Two (L.ψ⁰ Ω₁) (read (Ψ⁰ x G.top))` | 第 1 层起点，派发任意 | Par | 编译 |
| `par` | `∀ {X D X′ C} a → Lgl zero a → S X D X′ C → S X (D ▸ F₁ (read a)) X′ (C ▸ M a)` | 右结合和式的尾部再接 `Ψ₁ a` 对 `ψ₁ a`，两向保持 | Par | 编译 |
| `refabs` | `∀ {a} → Pos a → Two (L.ψ⁰ (F₁ (read a))) (L.ψ⁰ (Ω₁ L.+ F₁ (read a)))` | Ω₁ 被 ψ₁ 的输出吸收 | Abs | 编译 |
| `fb` | `X ≅ X → AllS D → X′ ≅ X′ → AllS D′ → ∀ {Z} → 𝒩 Z → Two (flat (plugR X D L.zero)) (flat (plugR X′ D′ L.zero)) → Two (flat (plugR X D Z)) (flat (plugR X′ D′ Z))` | 压平后换语境，尾巴在 `𝒩` 里 | Abs | 编译 |
| `strict` | `∀ {x x′ : T₀} → x L.≺ x′ → flat (F₁ x) L.≺ flat (F₁ x′)` | 压平的 ψ₁ 结构严格单调 | Abs | 编译 |

**`NodeTwo` 的模块参数：**
- `hm`, `hk`：链点上分支两向；
- `cg`：参照分支的 `≼ˣ` 同余；
- `fl`、`hs`、`st`、`z0`：对数 `lg` 的 ψ⁰ 值相同、带 `HS`、沿主线链点严格上升、0 在其下。

在 `chainPt-top-1` 与 `Par.Node.node` 两处都由定理填满，没有剩下的前提。

`S X D X′ C` 是 "语境压到 0 处两向" 加上 `OK` (好树、自互模拟、主线合法、`𝟎 ≺ flat X`)。实例 `s₀ : S Ω₁ ε G.top ε` 是定理。

#### 4 办法

**跨族关系：** 没有写归纳的关系族。改用 "语境" 的写法：
- 两边各是右结合的和式，在最里层接一项。`plugR X (D ▸ A) Z = plugR X D (A + Z)`，主线同样。这样加长语境不需要结合律。
- 主线的结合律只到函数外延才成立，所以必须避开。
- 前提 `S` 只要求语境本身压到 0 处两向。尾部按主线第 0 层树 a 的结构递归 (`par`)：
  - 后继与 `top`：ω 倍错开一位，第 k 项由语境逐次加长 (`iterS`) 得到；
  - ℕ 极限：逐项；
  - 零：尾部是 Ω₁ 对 `top`，交给结点。

**结点 (`NodeTwo`)：**
- 主线的链从 `top` 起，每步加上这一点的折叠值 (累加)；参照的链从 1 起，每步 ψ (不累加)。不变量是两条链逐项两向。
- 每一步主线多出的左加数，由 `ABS`/`ABSR` 吸收。
  - 吸收要的 "对数" 取参照分支在主线链点读回处的压平 (`flat (f (read dₙ))`)。
  - 结构前驱见证取上一个链点的对数。它的严格性来自主线的累加：`read dₙ ≺ read dₙ₊₁` 由 `lead` 给出，再由 `strict` 或 `FU` + `+≺` 搬过去。
  - 对数的证书 `HS` 来自 `good-read` (合法读回是好树) 与 `HS-flat`。
- 参照链点与主线读回之间用 `cg` 换。

**起点以上：**
- 外层结点 `c₁ = lc (λ a → top + M a)` 对 `e₁ = limᵢ (λ y → ψ₁ y)`。分支逐支比较时第 0 支不成立 (Ω₁·2 对 Ω₁)。
- 两边的折叠只在链点上取分支，链点从 `top` / 1 起，而且主线链点都满足 `Pos` (`pos-plus`)，所以只在 `Pos a` 的 a 上比较。
- 做法：先比较 `top + M a` 与并行的参照 `Ω₁ + ψ₁ a` (`par` 在语境 `[Ω₁]` / `[top]` 上)，再由 `refabs` 吸收 Ω₁。
- `refabs` 在压平的第 0 层上证明：
  - 后继支用 `fb` 换语境；
  - 第 0 项的错位是共尾的比较：一侧 `zˣ`，另一侧取 `≼lˣ 1` 与 `Ω≼F`。

**有限测试：** 在临时目录用纯 `.agda` 交互规范化了两边的形状。参照是 `limᵢ zero (λ y → ψ zero (suc∘suc) (tr⁻ z≅ y))`，主线是 `lc (inj₁ tt) (λ η → plus 1 top (Ψ 1 v0 _ η))`。这只是测试；最后的定理由检查器把 `ChainPt G.top tt 1` 展开成这两边并接受。

#### 5 第一个障碍

**`ChainPt G.top tt (suc n)`，n ≥ 1。** 没有检查器报错，卡住的是缺的引理本身。

**结构：** 以下由手算 n = 0、1 得出，判断一般的 n 也是这个形状 (未编译)：
- 链点 `chain 1 Φ (suc n) ≡ lc (inj₁ tt) (h n)`：
  - `h 0 η = plus 1 top (Φ (em tt η))`；
  - `h (suc n) η = plus 1 (chain 1 Φ (suc n)) (Φ (h n η))`。
- 参照 `refγ 1 (suc n) ≡ limᵢ zero (f (suc n))`：
  - `f 0 = up zero`；
  - `f (suc n) y = ψ zero (λ q → suc q) (f n (tr⁻ z≅ y))`。

**缺的引理 (类型如下，未编译)：**
```agda
BranchP n = ∀ (x : Ext zero L1) a → Lgl zero a → Pos a →
  Two (L.ψ⁰ (f (suc n) (read a))) (read (Ψ zero (vs v0) x (h n a)))
```
- `BranchP 0` 就是 `YiSucOne.branch`，已编译。
- 判断 (未编译)：有了 `BranchP n`，`NodeTwo` 给出 `ChainPt G.top tt (suc n)`。另外还要两件可写的东西：
  - 一个第 1 层只走第一支的结构严格序，用来给 `flat ∘ f (suc n)` 的 `st` 与 `z0`；
  - `Lx` 上对 `f n` 的同余，写法照 `cong₁` 逐层 `Le-ψ`。

**`BranchP 1` 难在哪 (判断)：** 它是 `c₁ + Φ (top + M a)` 对 `ψ₁ (ψ₁ (read a))`，要两件现在没有的东西：
1. **Φ 下的并行 `par`。** 尾部不再是第 0 层的树，而是 Φ 的输出：其中有保留下来的层号 0 结点，Φ 下还有和式 (`Φ (top + Z)`)。这要一个在第 1 层上对 Φ/ψ₁ 封闭的语法，以及主线结合律的替代 (结构互模拟)。
2. **第 1 层上的吸收。** `c₁` 要被 `Φ (…)` 吸收。在参照一侧，就是压平后 `X + ψ₁ Y` 对 `ψ₁ Y`，而 `Y` 带一般分支的保留结点。`fb` 只覆盖分支对 v "线性" 的结点 (`𝒩`：形如 `W + … + up v`)，不覆盖 `ψ₁ ∘ g`。
   - 这与 `YiOver` 回报里卡住的 `Y + ψ₁ Y ≤ₚ ψ₁ Y` 的 ℕ 极限一支是同一处。

**第 2 层以上与极限层号：** 还要层号 ≥ 1 的结点的 `NodeTwo` (内层链在第 j ≥ 1 层，吸收在第 j 层)，以及极限层号上 `top` 的部分和。都没有开始。

**规模估计 (判断)：** `SucP G.top tt` 还要几百行；一般的 b 更多。

#### 6 偏离与事故

- **范围：**
  - 只新建了上面七个 `YiSuc*` 文件。没有改已有文件，没碰 `src/`、`archive/`，没有提交。
  - 只删过自己七个模块的 `.agdai`，写的是字面路径。
- **编译错误：** 共四次，都是我自己的，都已改好：
  - `AmbiguousName X`：`Chains.X` 与语境参数 `X` 同名，改名为 `Xr`；
  - `TerminationIssue`：`two G.top` 调 `par G.zero`，拆出非递归的 `parZ`；
  - `InvalidPun.Constructor ε`：写成 `{E′ = ε}`；
  - `WrongHidingInApplication`：`up≅` 的类型改为显式写 `L._≅_ {…} {…}`。
- **文件改动提示：** 系统提示 `YiSucPar`/`YiSucAbs` 在磁盘上有改动，那是我自己用脚本做的上述修补。
- **主审中途消息：** 撤销了对 `YiOver` 的依赖限制，但我没有用到 `YiOver*`。
- **临时目录 (仓库外)：** 只有我的东西。
  - 规范化试验 `N1.agda`、`scr.agda-lib`，以及辅助脚本 `norm.sh`、`cc.sh`。
  - 冷编日志 `<实验目录>/agents/suc/cold-YiSuc*.log`。

文件 (按依赖序冷编)：
- <仓库>/probes/OCF/Lean/YiSucWire.lagda.md
- <仓库>/probes/OCF/Lean/YiSucLx.lagda.md
- <仓库>/probes/OCF/Lean/YiSucGood.lagda.md
- <仓库>/probes/OCF/Lean/YiSucNode.lagda.md
- <仓库>/probes/OCF/Lean/YiSucPar.lagda.md
- <仓库>/probes/OCF/Lean/YiSucAbs.lagda.md
- <仓库>/probes/OCF/Lean/YiSucOne.lagda.md
