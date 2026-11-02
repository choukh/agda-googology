# 良序证明代码调查: BMS/Y 系、ε₀ API 与树侧闭包的对照

> **证据记录, 手册见 [CodeGuide](../CodeGuide.md).** 查结论看手册; 本文是阅读当时的记录, 已知更正记在手册 §3、§6, 原文未改.

> 静态阅读 (2026-11-02). 没有构建、运行或类型检查这些仓库的任何代码. sorry/axiom 计数除非注明都是文本 grep. "README 称" 表示未核实. "读了" 指读了所列 file:line 的代码; "推断" 指我由代码形状得出的判断.

## 1. 各证明逐个看

### 1.1 EgoFakeFantasy/BMS-Well-Ordering-Lean (`3a4a945`, 2026-10-28, Apache-2.0)

路径前缀: `Y/` = `YesMetaZFC/BMS/`, `C/` = `ConstructibleBridge/BMSConstructibleBridge/`.

**主命题 (两个, 读了).**

- ZFC 版: `bm4_strictWellOrder_l : StrictWellOrder GeneratedArray GeneratedStrictDescent` (`C/FinalAssembly.lean:63`), `bm4_no_infinite_descent_l` (`:56`). 载体是种子生成的 BM4 数组, 不是任意数组.
- Z₂ 版: `derives_m (H : Nat) : Derives theory_m [] (closed_m H)` (`C/SecondOrderHereditaryBMSWellOrder.lean:29`). 每个**外部**高度 H 一份对象推导, 目标是"当前高度 ≤ H 的生成数组无无限一步下降链". 不含线性可比性, 也不是 Z₂ 内部对 H 的全称 (`docs/FIXED_HEIGHT_Z2.md` 开头明说, 我核对了 `closed_m` 是对同一矩阵做数码替换 `C/SecondOrderConcreteFormula.lean:45`).

**顶层策略 (读了).** Hunter 的路线: 给数组的列贴**稳定序数标签**, 每次非平凡展开严格压低标签上界. 这是全局论证里最该记住的一点: **BMS 的定义没有序数语义, 证明有.** 只是语义不是 ψ, 而是可构造层级上的稳定关系.

- 抽象框架 `StabilityFrame Label` (`Y/Stability.lean:16`): 良基的 `lt`, 按层索引的 `stableLt : ℕ → Label → Label → Prop`.
- 不变量 `StableRepresentation frame array` (`Y/Stability.lean:142`): `label : 列 → Label`, 严格递增, 且**第 row 行的祖先边 ⟹ 标签在第 row 层稳定** (`preservesAncestor`). 上界 `BoundedBy` (`:154`).
- 核心接口 `RepresentationDescentSystem` (`Y/WellFoundedness.lean:41`): `seed_bounded` + `expand_bounded`: 对**任意**有界表示, 非平凡展开给出严格更小上界下的新表示. 良基性 `accessible_of_bounded` (`:77`) 只是沿 `lt` 良基归纳. `expand_bounded` 的证明在 `Y/ExpansionReflectionInput.lean:1262,1369`.
- 展开的表示用**反射迭代**构造: `ExpansionReflectionState` 固定不变式 (G 块标签不变, 当前末复制块用原 B₀ 标签), `successorFamily` 单轮重标记, 证明义务分四区 G×G、G×Bᵢ、Bᵢ×Bᵢ、Bᵢ×Bⱼ (`Y/STAGE4.md` 的完成清单; 我读了清单, 只抽查了部分证明).
- 可比性: 同一数组的展开对索引单调 (`Y/STAGE4.md`), `generated_comparable` (`Y/WellFoundedness.lean:189`) 从共同种子导出. `docs/FIXED_HEIGHT_Z2.md` 记录了一个循环风险: 全局可比性要先用良基性, 所以不能拿它证良基性.

**Z₂ 路线的高度索引 (读了).** `FiniteHeightRepresentation.chain_l` (`C/FiniteHeightRepresentation.lean:28`): 在第 H+1 层有限稳定边界 σ 之下, 对链长归纳, 单点反射逐次延长一条两两 H-稳定的链. `representation_l` (`:54`) 由此给**一切**高度 ≤ H 的合法数组一个表示, **不用生成性, 不用种子覆盖, 不用全局良基** (文件头语; `acc_l :72`, `wf_l :80`). 关键事实 (文档语, 我认为成立): 祖先所在行严格低于当前高度, 所以链的 H 层稳定性足以保住所有祖先边. 也就是说, **一个粗到"所有列两两稳定"的表示就够了**, 精细的祖先结构在固定高度下被一个均匀对象吞掉. 之后 81 个 `*Hereditary*` 文件把这个对象内部化到 Z₂ 的遗传可数集模型 (`C/SecondOrderHereditaryCandidateSource.lean:exists_l`): 每个模型每个候选 X 只给 `Nonempty` 的源, 再经 Type 0 完备性回到推导.

**"标准形"不变量.** 数组本身没有标准形谓词: `GeneratedArray` 就是"种子可达" (`generated_iff_seed_path`, `Y/Generation.lean`). 语义不变量全在 `StableRepresentation`. ZFC 版用生成性, 固定高度版连生成性都不用.

**假设.** ZFC 版: 无数据参数, 用可构造层级数据 `constructibleStabilityFormulaData_l` (`C/FinalAssembly.lean:52-56`), 用 Mathlib 序数. README 称公理足迹只有 `propext, Classical.choice, Quot.sound`, 有 `AxiomAudit.lean` 守卫, **我没有运行**. `sorry` 文本 grep: 全仓 4 处, 全在说明性注释里 ("无 sorry") (`C/SecondOrderProgram{Recurrence:27,Totality:29,Recursion:20,Constructors:22}.lean`); `axiom` 行首声明 0 处.

**规模.** `.lean` 共 3230 个 551730 物理行 (含上游 YesMetaZFC 与历史研究). 组合核心很小: `Stability` 162 行, `WellFoundedness` 238 行, `ExpansionReflectionInput` 至少 1400 行. README 称 ZFC 版 BMS 部分 44989 行/165 文件, Z₂ 含历史研究 314553 行/2419 文件.

### 1.2 Phyrion1343/1Y-Well-Ordering-Lean (`03d794f`, 2026-09-21, Apache-2.0)

路径前缀: `RI/` = `formalization/OneY/RootIndexed/`, `Tr/` = `formalization/Concrete/OneYTruth/`.

**主命题 (读了 `Tr/ActualWellOrdering.lean:15-31`).** 四个无参数定理: `expansion_wellFounded : WellFounded (ExpansionStep expand)` (全部首项为 1 的序列上的一步展开良基, **不限生成集**); `generated_strictWellOrder`; `descendants_strictWellOrder s`; `expansion_chain_reaches_empty`. 全部合法式的字典序不良基 (README 称已形式化反例 `(1,2) > (1,1,2) > …`). 0-Y 一侧: 合法 0-Y 式与可逆 BMS 矩阵序同构 (README 称, 未读证明).

**顶层策略: 严格两层分离 (读了 `RI/Representation.lean`, `RI/README.md`).** 这是全部调查对象里形状最干净的一个.

- 组合层 `actual_expansion_wellFounded` (`RI/ExpansionWellFounded.lean:133`) 对**任意**标签类型 α 多态, 输入只有 `lt, D, R` 和 6 个假设: `hWF`、`hTrans`、`hStrict`、`hWeak`、`FiniteReflection`、`initial`. 其中 `R : ℕ → α → α → α → Prop` 是**根索引的**: `R k root parent child`. 组合层 `Representation.lean` 只依赖 `Std`.
- 语义层 `Tr/` 实例化: α = 序数, D = `Adequate`, R = $L$ 上按 $(k,\eta)$ 字典序分层的混合真值塔的 Σ₁ 保持 (`Tr/RootSemantics.lean:22,28`).

**不变量.** `Atom = (layer, root, parent, child)`, `Diagram = (size, atoms, valid)`, `Representation lt D R G f` = 域内、严格递增、每个原子成立 (`RI/Representation.lean:54`, 附近 `:20-53`). `Bounded lt n f bound`. 这里没有"标准形"; 标准形是**有限图的可表示性**.

**单步下降.** `FiniteReflection` (`RI/Representation.lean:301`): 图 G 有表示 f, 且切点到环境 β 有 `R K θ (f cut) β`, 那么整张图连同一批合法"顶端需求"可以被一次反射到 `f cut` 之下, 切点左侧不动. 合法性 `Admissible`: 需求的层低于 K, 或同层而根更小. `exists_bounded_representation_splice` (`:318` 起) 把它变成**一个块**的展开; `spliceLabel` 右侧重用旧标签.

**如何不写逐阶段论证 (这是对我们最有价值的一点).** `blockScheme_bounded_representations` (`RI/Representation.lean:401`) 对块数做归纳; `BlockScheme` (`:372`) 只含图、列号映射和纯组合的逐边分类, **没有表示、稳定关系、反射或下降字段** (`RI/README.md` 第 6 条). README 明确指出模板关系不要求是当前图的实际边: 最右块沿用原标签, 所以保留原模板的较强"储备", 再次反射时只保存当前图的实际有限关系, 然后新末块**重新获得原储备**. 对照 §3.

**假设.** Lean 经典逻辑 + Mathlib 序数 + 可构造宇宙库. sorry 文本 grep 0 处, `axiom` 0 处 (排除 `vendor/`, 444 个 `.lean` 51992 行). 审计输出见 `formalization/Concrete/OneYTruth-audit-output.txt`, README 称只有三公理; 未运行. README 明说审计不等于对象理论 ZFC 内可形式化, 也不判定最弱系统. `research/1y-object-theory-strength-check.md` 指出 `Adequate` 不蕴含 ZFC 模型 (缺幂集), 反例是 $H_{\omega_1}$. ZFC 论证只是纸面; 一阶 ZFC 演算的对象推导未生成.

### 1.3 koteitan/1y-wo-por (`d555ade`, 2026-09-26, Apache-2.0, 含 NOTICE)

组合层照搬 Phyrion, **只换语义层**. 这本身就是对 §1.2 两层接口的一次外部验证: 同一组合层换一个完全不同的模型仍然通过 (README 称绿; 我只读了代码, 未构建).

**主命题.** 同样四个定理, `Por/WellOrdering.lean`. 180 个 `.lean` 29261 行, sorry 文本 0, `axiom` 0.

**语义 (读了 `Por/Relation.lean`, `Por/Closure.lean`, `Por/Chain.lean`, `Por/Reflection.lean`).** 不用 $L$、不用可容许序数, `D` 恒真. `R k η a b ⟺ η ≤ a ∧ a < b ∧ Elem k η a b` (`Por/Relation.lean:99`): 高度 a 的结构是高度 b 的结构在段 $(k,\eta)$ 语言下的 Σ₁ 初等子结构. 语言含内部关系 $\mathrm{Rel}_j$ (所有层) 和上端谓词 $\mathrm{Top}_j$ ($j<k$)、$\mathrm{Top}_{k,\xi}$ ($\xi<\eta$), 后者**读当前高度**. 定义是对键 $(b,k,\eta)$ 的字典序良基递归 (`RF`, `:50`; `ilt_wf :37`).

- 这就是一个**按上下文分层**的关系: "能看见什么"由 $(k,\eta)$ 决定, 而不是由被比较的两点决定. 对照 §3 的 `𝓖`.
- `R_weaken` (`:113`): 根索引向下单调. 这是组合层唯一要的弱化.
- `finiteReflection` (`Por/Reflection.lean:88`) 约 40 行: 把 (图 + 需求) 写成一个 Σ₁ 公式 (`reflMat :66`), 用初等性下移. 一步到位, 没有对图的结构归纳.
- `initial_all` (`Por/Chain.lean:97`): 闭包点链 `cC : ℕ → Ord` (`:65`), 任意两点在**所有层、小点以下所有根**上都有 R (`chain_R :81`), 所以这条链表示**任意**有限图. 用 `Good`、`lam_good` (`Por/Closure.lean:29,127`), 以及 ω₁ 的正则性与选择 (`Por/Omega1.lean`).

整个语义层只有 `Por/` 下 10 个文件 <900 行. README 明说得不到序数上界或记号系统.

**假设.** 选择公理与 $\omega_1$ 正则. **ω₁ 是初始表示的来源**: 这是强度全部集中的地方, 而不在组合层. 关于"组合层依赖无许可的 YesMetaZFC, 需重写" `notes/01-design.md` 有记录 (§0); 仓库内 `notes/02-port.md` 记录移植, 未细读.

### 1.4 zball-bz/btbms-formalization (`4f31c78`, 2026-10-28, **仓库无 LICENSE 文件, 无许可 = 不能复用代码**)

路径前缀: `P/` = `lean/BTBMS/Plan/`, 论文 `paper/paper.txt` (test_alpha0 著).

**主命题.** `MainTheorem := (∀ n, ∃ κ, IsWeaklyMahlo n κ) → IsWellOrder Std Std.lt`; 证明 `mainTheorem` (`lean/BTBMS/Main.lean`). `Std` = 种子经 `expand` 生成的森林. `sorry` 文本 grep 9 处, **全在蓝图说明注释** (`Spine:54,57`, `U1:13,15,18`, `U2:8,33`, `U4:18`, `U5:9`); `axiom` 0. README 称 4027 个声明、三公理, 未运行. 14 个文件 73050 行, 其中 `U2` (闭包 + 共尾) 37080 行, `U3` 17833, `U5` 6980, `U1` 6588, `U4` 1818 (反射层级, 见下).

**这是调查中与我们最接近的工作.** 记号的良序被分解成五件事 (`FinalHyps`, `P/Spine.lean:2099`), 并由一个 **60 行不到的抽象定理** `abstract_wellOrder` (`:2117`) 组装:

| 字段 | 内容 | 语义? |
|---|---|---|
| `order` | `<` 严格全序 | 否 |
| `closure : IsStd E → InL E` (`P/U2.lean:22763`) | 生成集落在语法类 L 中 | **否, 纯有限组合** |
| `cofinal : IsStd B → InL E → B < E → ∃ n E', expand E n = some E' ∧ B ≤ E'` (`P/U2.lean:37068`) | 语法序下的共尾 | **否** |
| `seed` | 每个种子有 Conf | 是 |
| `descent` | 展开把 Conf 的最大值严格压低 | 是 |

证明读了 (`:2120-2165`): 对 θ 良基归纳, `C < A` 经 `cofinal` 得 `C ≤ A[n]`, 经 `descent` 得更小 θ. **语法侧和语义侧通过 `cofinal` 咬合.** 注意这里"标准形"和"良序"是分开的问题.

**没有序数语义的标准形 (读了论文 §2–§3 与 `P/Spine.lean:682`).** `InL E := CondV ∧ CondI ∧ CondH ∧ CondA ∧ CondS`, 全部是语法谓词:

- `CondH`: 每列条目非增 (`:664`);
- `CondA`: 第 i 个父是第 i−1 个的 $g_{B_c(i-1)}$-祖先 (祖先路径相对于"查询字");
- `CondS`: 每个 owner return 处 $h_c(J) < h_a(H)$, 比较相对键 (`:674`).

闭包定理 `inL_expand : InL E → expand E n = some E' → InL E'` (`P/U2.lean:22733`) 证明 **L 是展开封闭的不变类**, 比 `Std` 大, 而且**不用任何良基性**: 论文开头明说 "No well-foundedness of the syntax is used in any induction below", 区分三种归纳: 有限语法/列号/生成见证上的; 目标高度的有限大小上的; 单步内部对一对真实序数最小化反例的. 配套工具值得记: (a) **`L` 的文法条件不含序数**; (b) `Barrier lemma` 从 S 推出"任何 cut 对活动包含条目的读取都严格低于 $B_a(u)$", 这是对列号和条目序号的归纳; (c) **Capping lemma**: 在 V、S 下, 条件 A 等价于其"独立封顶"版本, 证明中间态可以暂时破坏 H, 所以中间步骤不需保持完整的 L; (d) profile `π(H) = (d,m)` 与条件 P 只用于有限修补, 闭包结束时一并证明保持.

**阶段化归纳 (读了 `paper.txt:1171-1216`, `P/Spine.lean:2011-2079`).** 公式 (18): `S<n ⟹ W<n ⟹ D<n ⟹ Sn`, n 是**目标高度的有限大小** (内部角色数). `SStrict P n` 对一切有效源包量化 (`:2011`): "All frames, charts, assignments and low budgets are quantified. Only the original target expression is required to be standard." 这是把逐阶段依赖变成**对环境全称**的做法. 对照 §3 的 `Good s 𝓖`.

**语义层是接口 (读了 `P/Spine.lean:1319`).** `Hier.Interface`: `Elem a b`、`Edge c b a` 及其传递性、限制、扩张, 加 `capture` (参数在 a 下, 见证从 b 拉到 a) 和 `transport`. 论文的 J-层级 (§5) 被决定 D-4 **整个替换掉** (`tracker/ledger.json` D-4; 该记录写的估算是 2.5k–5k 行对 18k–37k 行; 最终 `U4` 1818 行, `Descent.finalHyps Hier.jInterface`). 所以形式化**并没有验证论文 §5 本身**, 只验证了主定理. 这也再次说明: **接口足够窄时语义模型可替换**.

**假设.** ZFC + 对每个 n 有弱 n-Mahlo 基数. 这是元层假设, 严格超出 Z₂; 用基数论的是 `seed` (Mahlo 给初始 configuration, L6.7). `closure` 与 `cofinal` 完全不用它. **强度全部在 `seed`/`descent` 里, 不在 `closure`/`cofinal` 里.** 这对 §5 是决定性的观察.

### 1.5 koteitan/pss-proof (`d1be91f`, 2026-09-06, **根目录无 LICENSE, 无许可 = 不能复用代码**)

**131 与 5 的矛盾: 已解决.** 两个数都对, 说的不是一回事.

- `isabelle/8/audit.thy:41-42` 的 ML 列表 `all_sorries` 有 **131** 项 (`tr ',' | wc -l` 数的), 按定理名前缀: `P_5_` 13, `P_6_` 55, `P_7_` 27, `P_8_` 33, `pss_paper.` 3. 也就是原文全部被转录为 `sorry` 的陈述的**历史清单**.
- 这些陈述在"章节迁移"中搬进了 `5/ 6/ 7/ 8/` 下的单命题文件 (`pss_paper.thy:10-17` 自述: "this file holds no article statement of its own", 只留三条 [Buc1] 引用). README 第 30 行 "pss_paper.thy の 131 個の sorry" 与 README 文件表第 61 行"すべて sorry" 是**迁移前的过时说法**. `memo.md:111` 记录了 r71 时的原话.
- `pss_paper.thy` 的 grep 5 = **3 条真 `sorry`** (`:233 buc1_2_2_OT_B_wf`, `:239 buc1_3_2a_fseq_lt`, `:250 buc1_3_2_OT_B_closed`) + 2 处注释提及 (`:14,:222`).
- 全 `isabelle/` 中独占一行的 `sorry` 命令共 **8 处**: 上述 3 条, 加上 `8/P_8_1_condI_III_c1_around:80`, `8/P_8_6_Trans_fseq_condVI:47`, `8/P_8_6_trailing_principal_annihilable:30`, `8/P_8_7_OT_tail_annihilable:27`, `8/P_8_7_Pred_oper0:24`. 其中 `P_8_1_condI_III` 被 `Support_8_C.thy:17201` 附近标为**原文为假**. 其他 grep 命中 (`Support_8_B` 56, `Support_8_C` 25 等) 我抽查 `Support_8_C` 全是注释/文本. 我的正则不抓同行内的 `by sorry`, 这是文本 grep 的局限.
- **审计强度要打折:** 审计是**按名字**而不是按证明项. `Support_8_C.thy:12651-12652` 自己写明 oracle 审计分不清真 sorry 与包产物, 所以"0 sorry 依赖"只能读作 by-name 审计; `quick_and_dirty` 也关不掉. Lean 版独立一层, 见下. 我未运行任何一边.

**主命题 (读了).** `theorem y5_PSS_wf: "wf y3_PSSrel"` (`Support_8_C.thy:13087`), 由 `y4_PSS_wf_of_KK[OF ox12_KK_free]` 得. Lean 版: `lean/8/`, `p_8_7_termination`, 独占命令的 `sorry` 0 处 (`sorry` 全词 368 处, 我的抽样都在文本里, 没有逐一看), `axiom` 行首匹配 1 处是注释 (`8/8.3-condII-LDJB-a0trmax.lean:55`). 续作 `bijectivity/`: `Trans` 是 $CT_{PS}\to\{t\in OT_{B\omega}: t<_B D_0D_\omega0\}$ 的序同构; README 称全部 23 项无 sorry, **满射依赖 [Buc2] Thm 1.4(a) 的一条引用** (单项情形).

**顶层策略.** 翻译 `Trans : pairseq → BT` 到 Buchholz 项, 然后**沿 Buchholz 项的迭代归纳集 W 做无序数归纳**. 引擎 `y3_PSS_acc_of_cofimg` (`Support_8_C.thy:10543`) 的假设只有 `DESC` (`Trans(N[n]) < Trans N`)、`TOT` (`Trans N ∈ OT_B`)、`COF : y3_cofimg` (`:10501`, 翻译像在基本列下共尾). 证明: $Y=\{a\mid a\in OT_B \Rightarrow \forall N.\ \mathrm{Trans}\,N\le a\Rightarrow N\in\mathrm{acc}\}$ 对算子 $A_v$ 封闭 (`:10552` 起). 这是 Buchholz 1987 的**分层 (distinguished set) 法**.

### 1.6 Buchholz 式 $W_u$ (pss-proof 内部, 但值得单独一节)

路径 `lean/OTB-well-founded-syntactic/` (2571 行含文档, `.lean` 2032 行), `lean/Buchholz-1987/`. Isabelle 对应 `isabelle/8/Support_8_C.thy:7593-7668`.

定义 (读了 `Support_8_C.thy:7593`, `OTB-well-founded-syntactic-main.md` 式 (8)): 
$$c\in A_u(X)\iff c=0\ \lor\ (\mathrm{dom}\,c\in\{\{0\},\mathbb N\}\land\forall n.\ c[\bar n]\in X)\ \lor\ (\exists m<u.\ \mathrm{dom}\,c=T_m\land\forall z\in W_m.\ c[z]\in X),$$
$W_u=\mathrm{lfp}\,A_u$. 这里 $W_m$ 是外层的 **守卫**. Isabelle 用 `primrec bwl_Wf : nat → nat → BT set` 把层级实现成对 u 的递归 (`:7643-7649`).

三步 (读了 `.md`, 证明文件只看了定理名):

1. `OTB-DFREE-IN-W`: $z\in T_m$ 且不含 $D_\omega$ ⟹ $z\in W_m$. 分解到主项 $D_{k_i}b_i$ 上, 用 Buchholz 1987 的 Lemma 2.8 ($D_kb\in W_k$) 和 $W$ 对加法封闭 (2.4b).
2. `OTB-BC`: **Bachmann 共终** (`OTB-well-founded-syntactic-cofinality.lean`, 1791 行): $a,b\in OT_B$, $b<a$ ⟹ $b\le a[n]$ 或 $b\le a[z]$, $z\in T_m\cap OT_B$. 这一步才是重活, **不用序数值, 纯项上的归纳**.
3. `OT_B_wellFounded` (`OTB-well-founded-syntactic-main.lean:235`): 令 $Y=\{c\mid \forall b\le c.\ \mathrm{Acc}_R\,b\}$, 用共终证 $A_u(Y)\subseteq Y$, 应用 $W$ 的归纳原理. 最后这一步只有 200 余行.

**这条路不用任何序数语义, 是所有调查对象里唯一的, 也是唯一一条直接可以搬到 `--safe` Agda 的路.** 见 §3、§5.

Buchholz 1987 的闭包骨架 (读了 `lean/Buchholz-1987/Buchholz-1987-2.4-2.8.md` 全部陈述与 `-2.3-W.lean:62,115,121,141,157,163`), **这是对我们闭包定理最直接的先例**:

- 2.4: $A_v(X)\subseteq X, a\in X\Rightarrow A_v(X^{(a)})\subseteq X^{(a)}$, 其中 $X^{(a)}=\{y\mid a+y\in X\}$. 加法只改左端, 基本列穿过加法. 推论: $W_v$ 对加法封闭. (**注意是对任意 A-封闭的 $X$ 证的**, 不只 $W_v$.)
- 2.5: 塔分支 $x_0=D_u0$, $x_{i+1}=D_u(b[x_i])$ 的项都在适当的 $W$ 里.
- 2.6, **核心**: $W^*=\{x\mid\forall u.\ D_ux\in W_u\}$, 则 $A_\omega(W^*)\subseteq W^*$. 关键情形 $\mathrm{dom}\,b=T_u$, $v\le u$: $(D_vb)[n]=D_v(b[x_n])$, 对辅助列归纳得 $x_n\in W_u$, 于是 $b[x_n]\in W^*$, 从而 $D_v(b[x_n])\in W_v$.
- 2.7: $A_\omega(X)\subseteq X$ ⟹ 每个不含 $D_\omega$ 的项 $\in X$. **对项长度归纳, 不要求标准形.** 主项 $D_vb$: 归纳假设给 $b\in W^*$, 2.6 给结果.
- 2.8: 特别地 $D_ua\in W_u$.

三点要记住: (a) **闭包不用标准形**: 2.7 对一切 $D_\omega$-free 项成立, 标准形只在共终 (`OTB-BC`) 处才出现; (b) 没有按 $u$ 的逐阶段证明, 2.6 的量词 $\forall u$ 放在类的定义里; (c) 2.6 的外层是 $W^*$ 对 $A_\omega$ 封闭, 一条引理覆盖全部 $u$.

### 1.7 googology-lean `Y/WellOrder`, `OmegaY/WellOrder` (`6da2de5`, 2026-11-02; 仓库 MIT, 这些目录 Apache-2.0, `NOTICE` 有逐项记录)

都是移植, 无新数学 (`Y/WellOrder/README.md`, `OmegaY/WellOrder/README.md`). `Y/WellOrder`: 40096 行; 取自 1y-wo-por 与 1y-expand-equiv. 主定理 `ySys_wf` (`Notation/Y/WellFounded.lean:122`). `OmegaY/WellOrder`: 493 文件 132846 行; 取自 koteitan/wy-wo-por. 主定理 `wellFounded_step : WellFounded Descent.Step` (`OmegaY/Official/Recon/FinalStageF.lean:81`), **每个 `List ℕ` 都是状态** (README 称), `omegaYAll_wf` (`OmegaY/WellFounded.lean:66`).

ω-Y 的新东西: 语义层的 `R θ a b` 用**通用键** `Key` (`Por/Relation.lean`: 对 `(top, key)` 字典序递归; `KeySyntax Label Key`), 于是 §1.3 的 $(k,\eta)$ 被抽象掉了. 组合层规模 (约 130k 行) 比语义层 (3 个文件) 大两个量级. `OmegaY/WellOrder/OmegaY/Reflection.lean:25` 的 `axiom` 命中是注释中的 "axiom is assumed". 这两个子树行首 `axiom` 没有其他命中. 整个 `Googology/` 有 160 处行首 `axiom`, **在 `Trans/` 的 PoR 下** (见 §4).

### 1.8 hzyhhzy/column-ordinal-notations-hzy (`2da3765`, 2026-10-22; **根目录无 LICENSE**, 只有 `lean/licenses/1Y-Apache-2.0.txt` 针对上游 1Y)

七个记号 (Y, RPD, LRD, Ω-LRD3, ARD, IPD, ARD2) 的 Lean 良序证明, 337 个 `.lean` 46614 行, sorry 文本 0, `axiom` 0. 由 GPT 设计 (README 称). 其他记号 (CDMN, DQDN…) 的结论是纸面或未决, 这里不评.

**主定理 (读了).** `standard_with_top_strictWellOrder` (`lean/RPD/src/FiniteDemandRPDFinal.lean:44`), `valid_accessible : Columns.Valid g → Acc RPD.Step g` (`:22`). `RPD/src/` 只有 4 个私有文件, 291 行 + 共用后端. `Ω-LRD3`: `standard_accessible` (`lean/Omega-LRD3/src/OmegaLRD3Final.lean:102`).

**策略: 有限需求后端.** `lean/shared/src/FiniteDemand*.lean` 共 1180 行: 语义不再用 $L$ 真值塔, 只要"有限标签 + 递归阶段 (上端点, 行, 根)", 定义 `Stage`/`Earlier`/`Demands`/`Guard`/`Rule` (`FiniteDemandCore.lean:30-84`), 对行序良基参数化 (`rowLt`, `earlier_wellFounded :33`). 文件头称只有到当前端点的边需要守卫 ("Only edges to the current endpoint use the admissibility guard").

**强度下调 (纸面, 未形式化).** `proofs/paper/well-ordering.zh-CN.md`: 四个系统的标准域在 $S=KP_\omega+\exists\nu$ (不可数) 内良序, **无幂集、完全分离、选择**. README 称思路来自 test_alpha0 的短证明. Lean 文件是普通经典 Lean, 不是 KP 推导.

**Ω-LRD3 的深度归纳 (§8.3, 读了 `:460-498`, 这一节对"下标回灌"最直接).** 行标是同记号的有限图, 也就是 **折叠输出再当下标**, 和我们"交替"同形. 处理方式:

1. 语法上 (§8.1, 不依赖良序性): 嵌套深度 $d(G)$, 每条直接边的行 $K$ 有 $d(K)<d(G)$; FS 只递归调用这些 $K$; $d(G[n])\le d(G)$. 严格全序和 $G[n]<G$ 都对深度归纳, "不沿 FS 链比较".
2. 归纳命题**不是"无无穷链", 而是"存在秩见证 $\mu_G:D(G)\to\kappa$"**, 严格降秩且保序. 带数据的归纳假设才能传给下一层.
3. **行域一次固定**: $X_G=\{0\}\cup\bigcup_iD(K_i)$. 从 $G$ 出发的全部外层展开, 所有行都留在这个 $X_G$ 里, "复制过程中不重新选择较大的行域". Lean 中是 `Pool a` 与 `RowInvariant.AllRows` (`OmegaLRD3Final.lean:49,79`). 然后用 $\rho_G:X_G\hookrightarrow\sigma_G$ 把行码压进一个序数, 外层就变成行域为序数的已证系统.

## 2. 总表: 问题 1 的答案

| 证明 | 主命题 | 顶层策略 | 标准形/不变量 | 假设 (基础) |
|---|---|---|---|---|
| BM4 ZFC | `bm4_strictWellOrder_l` | 列贴稳定序数标签, 展开压低上界 | `StableRepresentation`; 载体 = 生成集 | ZFC 级经典 Lean; 可构造层级 |
| BM4 Z₂ | `derives_m H`, 外部 H | 同上, 高度 ≤H 时一条 H-稳定链表示一切数组, 内部化到遗传可数模型 | `representation_l`, 不用生成性 | Z₂ 对象推导, **逐 H** |
| 1-Y Phyrion | `expansion_wellFounded` 等 4 条 | 组合层 + 语义层; 根索引 R; 一次有限反射 | `Representation`, `BlockScheme` | 经典 Lean; $L$ 真值塔; 纸面 ZFC |
| 1-Y koteitan | 同 | 换语义层为 PoR 式 Σ₁ 初等 | 同 | 选择; ω₁ 正则 |
| RPD/LRD/Ω-LRD3 等 | `standard_with_top_strictWellOrder` 等 | 有限需求后端; Ω-LRD3 加深度归纳 | 图本身; `Pool` | 经典 Lean; 纸面 $KP_\omega+\exists$ 不可数 |
| BTBMS | `MainTheorem` | 五项分解; `S<n ⟹ W<n ⟹ D<n ⟹ Sn` | **语法类 $L=V∧I∧H∧A∧S$** | ZFC + ∀n 弱 n-Mahlo |
| PSS | `y5_PSS_wf` | 翻译到 Buchholz 项; $W_u$ 归纳; Bachmann 共终 | `ST_PS` 经 `Trans` 进 `OT_B` | HOL/Lean; **无序数语义** |
| ω-Y (移植) | `wellFounded_step` | 同 1-Y, 键抽象 | 每个 `List ℕ` | 经典 Lean; ω₁ 级 |

**直接修正任务书的一个前提.** "BMS 风格系统没有序数语义, 良序性是内蕴证明的": 只有**定义**是内蕴的. 除 PSS 外, 我读到的全部良序证明都给每列贴**真实序数标签**, 并在一个经典良序类上下降 (`StabilityFrame.lt_wellFounded`, `Por.R`, `Conf : Forest → Ordinal → Prop`). 它们不用 ψ, 但用序数, 而且用的是任意大序数加反射, 比 ψ 更"语义". 真正的"无序数"归纳只有两处: BTBMS 的 `closure`/`cofinal`, 和 Buchholz $W_u$. 所以对我们的**证书定理**, 这两处才是正确的对照, 而不是 Y/BMS 的语义层.

另一个区别: 这些"无 ψ"系统依然有**有限句法**和可判定比较. 它们摆脱的是 ψ, 不是记号. 我们的树有 ℕ 分支和 $\Omega$ 分支, 没有有限句法. 所以"树自己领路"比"BMS 无 ψ"要求更高, 只有 $W_u$ (对基本列而非句法做归纳) 的形状能直接照搬.

## 3. 问题 2: 对我们的树侧不变量可复用什么

对照对象: `Good s 𝓖 x` (`probes/OCF/Align/UniformPendingGoodClass.lagda.md:174`, 构造子 `:133-166`), `Above` (`:86`), `Step` (`UniformPendingGoodTower.lagda.md:132`), `CQ` (`:113`), `Pk` (`:292`).

以下对应是我的推断, 不是任何仓库的说法.

### 3.1 能对上的

| 他们 | 我们 | 对得多紧 |
|---|---|---|
| $A_u(X)$ 第三支 $\forall z\in W_m.\ c[z]\in X$ | `bi` 的 "`G<` 下的输入 $z$ ⟹ `Good₊ s 𝓔 (f z)`" (`:138-146`) | **几乎同形.** 分支只在低层好的输入上要求好 |
| `bwl_Wf n u` 对层 primrec (`Buchholz-1987-2.3-W.lean:115`) | `Gd` 对 `i ◃ ℓ` 递归 + `module _ (ℓ) (G<)` (`:131,:168`) | 同形 |
| $W^*=\{x\mid\forall u.\ D_ux\in W_u\}$ (Lemma 2.6) | `Step` 的输入 `vQ : ∀ {i ℓ} ev p → Good true (VisT i) …` | 同形: 全称放在类的定义里 |
| 2.6 关键情形 $(D_vb)[n]=D_v(b[x_n])$, $x_n$ 辅助归纳 | `ch₀`/`chS` 给 `Br (lvl y_{m+1}) O`, `growQ`/`pickB` (`Tower:187-205`) | 同形: 链从头重新起步 |
| 2.4: $X^{(a)}=\{y\mid a+y\in X\}$ 仍 $A$-封闭 | `addo`, `W ⟨ 𝓔 ⟩`, `Above j C′ D` | 我们更一般 (任意外层吸收者); 但他们的证明对**任意** A-封闭 $X$ 做, 我们目前对具体 `Good` 做 |
| $X\mapsto$ 任意 A-封闭集 | `bi` 的 "对一切子类 𝓔" | 同样是 Set₁ 量词 |
| `blockScheme_bounded_representations` 的模板储备: "每次反射后被证明重新成立, 不是被假设为下一阶段的不变量" (`RI/Representation.lean:398-400`) | "阶段步不从上一阶段的对角取数据" (`Tower` 头注 3) | **同一个发现**, 他们也是这样避开逐阶段论证的 |
| `hWeak`, `R_weaken` | `Good-mono` (`GoodClass:200`) | 同 |
| `Admissible`: 需求层低于 K, 或同层且根更小 (`RI/Representation.lean:281`) | "凡被比较的下标有公共上界"; `FlΛ`, `Fl` | 松. 他们的是可判定的语法守卫 |
| BTBMS `SStrict`: "All frames, charts, assignments and low budgets are quantified" (`paper.txt:1178`) | `CQ` 对 `k′ φ′ cv′ ℓ′ ev′` 全称 | 同形 |
| Ω-LRD3 `Pool a r := r = nil ∨ ∃ old ∈ directRows a, Reach Step old r` (`Omega3RowPool.lean:43`), **对 FS 封闭** (`fs_mem`) | 全局 `G`、`Gs n` (`InaccStrike` 事实 5, 6) | **方向不同, 值得试**: 见 §7 |
| Ω-LRD3 深度 $d(G)$, 归纳假设带秩见证 | `A d`, `lvG`, 深度一致性 | 见 §7 |

### 3.2 如何避开逐阶段论证: 四种办法

1. **全称进类** (W*, `SStrict`, `CQ`). 我们已经在用.
2. **一个归纳, 一次抽象接口** (`BlockScheme`, `RepresentationDescentSystem`, `FinalHyps`). 阶段是接口的自然数字段, 不写在语义定义里. 我们的 `Step` 的输入已经很像, 但 `Step` 还不是脱离 `Good` 的纯组合数据.
3. **一个足够粗的均匀对象吞掉结构** (`chain_l`, `chain_R`): 高度固定时一条两两稳定的链可以表示一切图, 精细祖先结构被吞掉. 对我们的启示: `ys` 这种链**不一定**要逐点跟随项的结构. 但这靠序数的 ω₁ 正则性供应闭包点, 树侧没有 (否定见 §3.3).
4. **对项长度而不是对阶段归纳** (Buchholz 2.7): 表面的"阶段"其实是项的一层, 归纳假设给 $b\in W^*$, 阶段全被 2.6 吸收. **这是我们目前没做的**: `Tower` 对 $k$ 递归, 是阶段计数. 按前缀语法长度归纳可能才是深度一致的正确形式.

### 3.3 对不上的

- **经典逻辑.** BTBMS 单步内"对一对真实序数最小化反例", 线性序的双候选论证 (`paper.txt:1201-1210`), Por 的 `by_cases`, `Ordinal` 的全序: 全部依赖真实序数. 对 `Ordᴵ` 我们只有有界三歧, `Trich₂→WLPO`、`noBT` 封死全局三歧 (见 `probes/README.md:80`). **注意好消息**: Phyrion 组合层的 6 个假设**不要全序** (`RI/ExpansionWellFounded.lean:133`: 只要 `hWF`、`hTrans`、`hStrict`、`hWeak`、`FiniteReflection`、`initial`). 全序是后来由可比性导出的.
- **反射.** `FiniteReflection` 把有限图写成 Σ₁ 公式, 用初等性下移, 见证只给 `∃`. 树侧没有"结构高度", 也不能对一切公式做满足关系. 如果硬要类比, 只能是折叠, 但折叠是函数不是存在量词; 这个映射我认为**不成立**, 不要试.
- **`Set`-级概括.** `InL` 是可判定的有限句法条件, 所以闭包是有限归纳. 我们的 `Good` 含 `⊑ᵒ`、`≅ˢ`、`Goodᴺ` 量化, 是 Π 型语义条件. **`Good` 对应的不是 `InL`, 而是 `W*`**. 想照搬 `InL` 就等于重新引入记号.
- **Lean `lfp`.** `lfpS_w3` 是非直谓的最小不动点. Agda 要改写成内层 `data` + 对层递归. 对 $u<\omega$ 没问题. 下标超过 ω 时需要对 `Ordᴵ` 的结构递归, 那正是 `Gd` 已经做的事.
- **Z₂ 逐实例.** `derives_m H` 对 H 是外部的, Z₂ 内没有统一真值谓词. **我们不受此限**: `Gᴺk : ∀ k → …` 是内部全称, 靠 Set₁ 的大消去. Z₂ 版的 81 个 `Hereditary` 文件和完备性绕路对我们没有用.
- **规模警告.** 把语法类的闭包做完就很贵: BTBMS `U2` 共 37080 行, `inL_expand` 在第 22733 行, `cofinal` 在 37068 行 (按文件位置粗估闭包约 2.3 万行, 共终约 1.4 万行).

## 4. 问题 3: 与 ψ / Buchholz 的关系, 有多重

**只有 PSS (两行矩阵) 一级有定理. 到 BMS、Y、BTBMS 的序数值, 我读到的范围内都没有.** BM4 README: "不涉及 BM4 的精确序型". koteitan README: 得不到序数上界或记号系统. Phyrion 文档: 精确序型未定. hzy 的 DQDN 等比较是纸面, 且明确区分未决.

| 关系 | 位置 | 内容 | 行数 | 依赖 |
|---|---|---|---|---|
| PSS → Buchholz 项, 良基 | pss-proof `isabelle/` | `Trans`, 停机 | 5/ 673 + 6/ 17126 + 7/ 11045 + 8/ **126681** + PSS/ 52695 = **208220** 行 (其中 `Support_8_B` 98666) | 见 §1.5 |
| 同, Lean | pss-proof `lean/` | `p_8_7_termination` | 全部 142300; `8/` 88120, `6/` 32651, `7/` 13603 | 三公理 (README 称) |
| `Trans` 是序同构 | pss-proof `bijectivity/` | 到 $\{t\in OT_{B\omega}: t<D_0D_\omega0\}$ | 6542 | 满射引 [Buc2] Thm 1.4(a) 单项情形 |
| PSS rank = 1 + val | googology-lean `Trans/BMS/ExBuchholz/PSS` | `rank_pairL_eq` | 2637 + pss-proof 依赖 | 三公理 (README 称) |
| PSS ↔ Carlson $R_1^+$ | googology-lean `Trans/BMS/PoR/PSS` | `mainTheorem_mat`: $\iota\Phi(M)=$ `pairOrdL M` $=1+$`val(pairTerm M)` (`Main.lean:209`) | 25276 | **45 条行首 `axiom`** (Wilken/CW12 引用: `TR/Cited` 12, `Main/Cited` 16, `Cited2` 7, `Cited3` 10) |
| 单行 ↔ ε₀ | googology-lean | `read_expandL`, `rank_bms_eq_val` | 未分开数 | — |
| 三行 cofinality | googology-lean `TrioCof` | `trio_cofinality` 移植 | 约 16600 (文件头称) | 只有共终, 无值 |
| ψ₀(Ω_α) → 三行矩阵 | `omegaIndexMatrix` | **校准表, 不是定理** (`results.md:64` 自述) | — | — |
| $R_2^+$ core vs ω 个不可达的 ψ | `Trans/PoR/InaccPsi` | Wilken 断言, 条件于 FRAG, 部分纸面 | `R2/Cited.lean` 等 25 个文件含 axiom | README 自述 |
| 0-Y ≅ 可逆 BMS | Phyrion | 序同构 (README 称) | — | 不涉及 ψ |

**"重"的量化.** p進大好きbot 的说法成立: 只翻译 PSS (BO = ψ₀(Ω_ω), 两行) 这一级, Isabelle 就 20 万行, 其中第 8 章 (翻译与基本列的交换律) 12.7 万行, Lean 重写 14 万行, 过程中找出 30 条原文修正 (README 称) 和 9 条"原文转录为假"的登记 (`Support_8_C.thy:17201`). 对比: 良基性本身 `OTB-well-founded-syntactic` 2032 行 + `Buchholz-1987` 1361 行. **重的不是序数, 是交换律.**

**基本列比较不是逐项相等.** 这条对我们的 `Lab` 路线要紧:

- 原文陈述 `Trans(M[n]) = operB (Trans M) (numBT (if adm M j0 then n-2 else n-1))` (`8/P_8_6_Trans_fseq_condVI.thy:43-46`, 该文件是 `sorry` 转录, 不在证明链里, 证明链用修正后版本): **下标有偏移**, 且分情形.
- `p_8_7_Pred_oper0`: $\exists k.\ [0]^k(\mathrm{Trans}\,M)=\mathrm{Trans}(\mathrm{Pred}\,M)$ (`8/P_8_7_Pred_oper0.thy:20-24`, 同样是转录): **只到若干次 [0]**.
- googology-lean: `pairOrdTerm_step_ne_fs` (不交换), `pairToExb_steps_unbounded` (一步 PSS 可对应 p+1 步 ψ, `results.md:149,180`). PSS 的基本列和 ψ 的基本列不一致, 只有 **"可达性保持且反映"** (`pairToExbOT_transGen_iff`).

对比我们: `Lab` 要求**逐项一致**, 是比这些都强的目标, 这也是树侧能直接得到 FGH 递归方程的原因. 值相等路线已被 `value-equality-verdict` 判为不省代价. 但 PSS 的经验提示: 如果 `Lab` 只是在高阶段成为负担, **"可达性 + 共尾"足够推出良基和序同构** (`y3_cofimg` 就够, 见 §1.5). 这不改变 FGH 精确性需求, 但在"只证强度下界"时可以考虑.

## 5. 问题 4: 值得抄的 API 与基本列设计

| 模式 | 出处 | 抄什么 | 对我们 |
|---|---|---|---|
| **基本列返回分类, 规格单独写** | Mathlib `fundamentalSequence : ONote → Option ONote ⊕ (ℕ → ONote)` (`Notation.lean:925`), `FundamentalSequenceProp` (`:967`), `fundamentalSequence_has_prop` (`:989`) | 定义在**全部原始项**上; 规格里 NF 保持是**条件式** `o.NF → a.NF`, 不是函数的前提 | 与 `corr : ∀ t → Shape t` 无前提的做法一致. 可把 `cof`/`fsn` 的规格收成一个 `FSProp` |
| FGH 沿规格递归 | `fastGrowing` (`Notation.lean:1057`): `match fundamentalSequence o, has_prop o`, 停机来自规格 | 我们已有 `Acc`-FGH; 形状可更干净 | 低优先 |
| 通用记录 + 认证分类器 | SteveWmoc `OrdinalNotationSystem` (`Generic/OrdinalNotationSystem.lean:29`), `ClassificationResult`, `Satisfies`, `OrdinalClassifier` (`Generic/Classifier.lean:18`) | `limit` 支三件事: 极限, 逐步递增且 `< a`, 语义共尾 | 可作 `EBOI`/`Label` 的验收接口; 但它用 `eval` 进 `Ordinal`, 我们要换成树 |
| 免带分支等式 | `LimitSequenceData` (`Generic/LimitSequence.lean:24`, 文件头语) | 已知是极限后直接拿列, 不用拖 `classify a = limit f` | 我们多处 `with` 爆炸 (`agda-pitfalls`) 时有用 |
| 三层纪律 | SteveWmoc `docs/gamma0-design.md`: raw / canonical / semantic; "比较器不得用求值实现" | 已是我们的做法 | — |
| **信息性共尾** | hydra `canon_limit_strong : nf λ → T1limit λ → ∀ β, β t1< λ → {i : nat \| β t1< canon λ i}` (`Epsilon0/Canon.v:823`) | Σ 不是 ∃, 算出下标 | **对 `--safe` 直接适用**, 比 Mathlib 的 Prop 版好 |
| `<` 由基本列路径刻画 | hydra `acc_from`, `LT_acc_from` (`Epsilon0/Paths.v:884`), `acc_from_LT` (`:919`), `LT_path_toS` (`:831`) | 双向: $\beta<\alpha\iff$ 存在路径 | 我们的 `desc-lab`、`occ<` 的通用形式 |
| 全局总函数 | hydra `canon : T1 → nat → T1`, `canon zero i = zero` (`Epsilon0/Canon.v:27`) | 无三分类, 单函数 | 简单但丢信息; 不如 Mathlib |
| 两套 FS 约定 | hydra `canonS`; PSS 的偏移 | 记下下标约定, 否则对不上 | Guide 已有"下标错位速记" |
| **共尾是统一接口** | BTBMS `cofinal` (`P/U2.lean:37068`), PSS `y3_cofimg` (`isabelle/8/Support_8_C.thy:10501`), `OTB-BC`, trio `TrioCofinal` | **`B < A ⟹ ∃k. B ≤ A[k]`** 是全部良序证明的连接件 | 见下 |

Hydra 的 `Gamma0/` (`ed8e604`): `T2.v` 429 行, `Gamma0.v` 3794 行, 文本 grep `Admitted` 0 处; 良基性经 RPO (`:974`, Contejean), **文件里没有 `canon` 或 fundamental 字样**, 所以 Γ₀ 没有基本列. 文件内未见 "draft" 字样, Guide §5.4 的 "draft" 我没能在代码里印证. SteveWmoc 的 `Gamma0/` 比 Guide 记的新 (README 有 Γ₀ 一节), 30 个文件, `OrdinalAnalysis/` 全部 `.lean` 共 6483 行, sorry 0, `axiom` 0; 有 `LimitSequenceData`, 但我没读其 Veblen 基本列细节.

**树侧的结构性好处 (我的推断).** 记号侧要证的五件事 (`FinalHyps`) 在树上几乎都是定义: `x ≺ lim f` 就是 ∃n; 没有 seed; 没有 descent (树本身结构递归). **唯一不是定义的就是 `closure`.** 这说明"树领路"并没有省掉难点, 而是把难点全部压到闭包上, 这一点与 BTBMS 把一半代码放在 `U2` 一致.

## 6. 问题 5: 强度图景对我们意味着什么

下面的强度等式来自文献常识或仓库自述, **我没有在此核实证明**; `[仓库]` 标出来自所读仓库的自述.

| 系统 | 证明所在 | 备注 |
|---|---|---|
| PSS, BO = ψ₀(Ω_ω) | Buchholz $W_u$, 即 $ID_{<\omega}$ 形状, 与 $\Pi^1_1\text{-CA}_0$ 对应 | Buchholz 1987 的标题是 $(\Pi^1_1\text{-CA})+\mathrm{BI}$ 独立性 [仓库引]. **这是可直接搬进 Agda 的强度** |
| 1-Y, RPD, LRD, Ω-LRD3 | $KP_\omega+\exists$ 不可数 | 纸面 [仓库]; Z₃ 上界和最弱系统未定 |
| BM4 高度 ≤ H | Z₂, 逐 H | [仓库]; 统一命题未在 Z₂ 证 |
| BMS 极限 | $\le$ PTO(Z₂) | 纸面 [仓库, hzy DQDN], 未核 |
| BTBMS | ZFC + ∀n 弱 n-Mahlo | [仓库]; 纯粹上界, 不是下界 |
| 我们: EBO 级 | Agda `--safe --without-K`, `Good : Set₁` | 目标 ψ₀(Λ) 在文献常识中远低于 Setzer 的 MLTT + W + 一个宇宙 (KPi 级, 未核). **不存在强度壁垒**, 只有代价 |

**证明能用的:**

1. 内层 `data` + 对层/下标结构递归定义的迭代归纳类 (形同 `bwl_Wf`, 我们的 `Gd`). 不用 lfp.
2. Set₁ 上对类的量词: `∀ (X : Cl ℓ) → A-闭 X → …` (Buchholz 2.4, 2.7; `bi` 的 𝓔). 直谓于 Set₁.
3. 大消去带来的内部统一 `∀ k`, 这是 Z₂ 没有的 (§3.3).
4. Σ 形式的信息性共尾 (hydra).
5. `Acc` 与结构归纳: 对项长度、前缀语法长度、深度.

**不能用的:**

1. 排中律、全局三歧、对真实序数最小化反例. (`Trich₂→WLPO`、壁垒定理.)
2. 任何"存在闭包点"的超限论证: `lam_good` 的 ω₁ 正则与选择; club; Mahlo 基数. **所有 `seed`/`initial` 都在这里**, 构造性无替代, 只有链的显式构造 (我们的 `ys`/`γ`).
3. 对全部公式的满足关系, 反射, 紧致性/完备性 (Z₂ 版经 Type 0 完备性回传).
4. `Nonempty`/`∃` 见证后再取值: 我们的 `forceᴺ` 要读输出, 证据必须是数据.

**强度结论.** BTBMS 的切分显示: **强度全在 `seed`/`descent` (Mahlo + 反射), `closure`/`cofinal` 是有限组合.** 我们的问题则相反: `Good` 把 closure 和"下降"合在一起. 树结构已经解决下降, 所以 `Good` 闭包的**真正强度是 $W^*$ 型的迭代归纳**: 每升一层下标, 需要一层新的 `G<`. 下标回灌 (`toLevel (ys m)`) 意味着这是**对自身输出的自主迭代**, 对应的不是 $ID_{<\omega}$ 而是其自主版本. Agda 对 `Ordᴵ` 递归已能写出, 这正是 `Gd` 的类型. 所以 Buchholz 骨架的超限推广**在类型上可表达**; 没有人证明过它成立, 这是开放的.

## 7. 排序: 对记号无关闭包定理最有用的三个想法

### 第 1: Buchholz 的 $W^*$ 骨架, 参数化到任意 A-封闭类, 对前缀语法长度归纳

**出处.** `pss-proof/lean/Buchholz-1987/Buchholz-1987-2.4-2.8.md` Lemma 2.4–2.8 (`:117` 起有 2.8), `Buchholz-1987-2.3-W.lean:62,115,121,163`; `isabelle/8/Support_8_C.thy:7593-7649`. pss-proof 无 LICENSE: **只取数学, 不抄代码**; 数学本身是 Buchholz 1987.

**为什么排第一.** 无序数, 无标准形, 无经典原理 (陈述层面; Lean 体未逐行查), 目标形状 (分支带低层守卫, 全称进类, 链重新起步) 与 `Good`/`Step` 同形. 它给出我们缺的那一招: 现在 `Tower` 对阶段 $k$ 递归, `Good` 闭包对具体类做; Buchholz 对**任意 A-封闭的 X** 证, 再对**项长度**归纳, 阶段被吸收.

**怎么试 (两步, 第一步 200–1400 行).**

1. 玩具, 单独一个 `probes/OCF/Align/` 下的新文件: `--safe --without-K` 写出 Buchholz 项 (下标 ℕ)、`dom`、`_[_]`, 内层 `data A u X` + 对 `u` 递归定义 `W`, 证 2.4–2.7. **判据**: 能否不用 funext 与 LEM 完成. 这同时验证 `lfp → data` 改写和 `Set₁` 量词够用.
2. 移植形状: 把 `Step` 的 `vQ` 换成任意满足 "`A`-封闭" 字段的 `X : ∀ {i} → Cl i → Ordˢ i → Set₁`, 不改 `Good` 本身, 看 `Step.V` 的证明用了 `Good` 的哪些具体性. 再对 `TopDown` 的前缀语法 (`A d`) 而非 $k$ 归纳. **决定性检验**: `Tower` 明确未做的深度 ≥ 1 与 $\psi_0(\Omega_\Omega+\Omega_\eta+\Omega_\Omega)$ (`UniformPendingGoodTower.lagda.md:10,361`). `Tower:361` 记下深度 ≥ 1 的阻塞是 `Obs` 没有 `fo1`, 等 `≅ᴬ`; 这个想法**不会**自动解决它, 只是把问题变成 "A-封闭需要哪个 `fo1`".

**风险.** Buchholz 排除 $D_\omega$ (2.7 只对 $D_\omega$-free), 对应 ψ₀(Ω_ω) 以下, 而 `Tower` 已超过. 超限/自主版本没有先例; 第一步是玩具, 只能证明形状可搬, 证不出 EBO.

### 第 2: BTBMS 的 `S<n ⟹ W<n ⟹ D<n ⟹ Sn`, 全称量词只留"原始出现"必须标准

**出处.** `zball-bz/btbms-formalization/paper/paper.txt:1171-1216`; `lean/BTBMS/Plan/Spine.lean:2011` (`SStrict`), `:2017` (`WFit`), `:2032` (`DCore`), `:2099` (`FinalHyps`), `lean/BTBMS/Plan/U2.lean:22733` (`inL_expand`). 仓库无 LICENSE: **只取想法**. 论文作者 test_alpha0.

**为什么.** 我们 (Ω_Ω)² 的两个否定 (`OmegaSq` 的 `low-term`, `Relative` 的 `¬BranchΩ`) 的根因是: "链点在高目标算出后又在低目标再折叠", 于是**任意** ≅ˢ 相关的底都被读到. BTBMS 面对的是同一种形状 (低处预算, 高处证书): 它对"一切帧、一切低预算"全称, 但"**只要求原始目标表达式标准**", 中间项可以不标准. 归纳量 $n$ 是目标高度的有限大小, 不是阶段, 也不是序数.

**怎么试 (纸面先做, 不写 Agda).**

1. 在 `Relative` 的反例上做判定: `PL`, `PR` 是不是某个"原始出现"谓词排除的? 也就是把 `BranchΩ (Ω̂A 0) []` 的"对一切 ≅ˢ 相关的底"收窄成"对 `Pk`/闭包实际产生的底". 如果 `PL`/`PR` 确实不是原始的, **`¬BranchΩ` 就只否定了过强的陈述**, 新陈述可能成立. 这是便宜的决定性试验.
2. 若通过, 把 `Good` 的量词结构按 `S/W/D` 切开: 目标 $S_n$ ("尾巴"), 拟合 $W_{<n}$ (查询), 下降 $D_{<n}$ (普通后继). 用**前缀里 Ω̂ 帧的个数**作 $n$.

**风险.** 这是类比, 不是映射; BTBMS 的语法类 $L$ 可判定, 我们的不可判定. "原始出现"在树上如果只能用记号表述, 就失去记号无关性. 这是要先回答的问题.

### 第 3: 按项固定的 `Pool`, 替代全局生成类 `G`

**出处.** `hzyhhzy/column-ordinal-notations-hzy/lean/Omega-LRD3/src/OrdinalFormal/Omega3RowPool.lean:43` (`Pool`, 及 `fs_mem`), `lean/Omega-LRD3/src/OmegaLRD3Final.lean:49,79,102`, `lean/Omega-LRD3/src/OrdinalFormal/RowInvariant.lean:16`, `proofs/paper/well-ordering.zh-CN.md:405-418,460-498`. 根目录无 LICENSE: **只取想法**.

**为什么.** `InaccStrike` 事实 5, 6: 任何判决下 `G` 不能对 + 封闭 (`T₂-cert→⊥`, `no-sound-1+ω`), `Gen/Run` 互递归不严格正, 需要对 $n$ 分层的 `Gs`. Ω-LRD3 与我们同形 (行标是同记号的项, 即"折叠输出回灌下标"), 但它**从不寻找全局类**: 行域 `Pool a` 由 `a` 的直接行经 FS 可达组成, 只对 FS 封闭, **不对 + 封闭**, 整个外层展开都留在里面. 它把"降序和是树侧推出的"这条否定变成设计.

**怎么试.**

1. 在 `InaccStrikeOracle` 上定义 `Pool t`: 从 `t` 的直接下标出发沿 `dz (S _)` 的基本列可达. 这和 `Tower.close` 的分层一致, 所以正性应当没有问题.
2. **决定性检验**: `T₂-cert→⊥` 的前提要求 `G` 含 `ω+2`、`0`、穿透后的 `suc ω⁺T`. 验证 `Pool(ψ₀(Ω_Ω·2))` 是否包含 `ω⁺T` 这类树; 如果否, 否定不适用, `Commute` 的前提 `GV` 可以只在 `Pool` 上要求. 再用 `ver-dev` 的 `ψ₀(ψ_{Ω₂}(Ω_{Ω₁+1}))` 检验判决是否仍答错.
3. 附带: 归纳假设带数据. Ω-LRD3 的深度归纳命题是"存在秩见证 $\mu_G$", 不是"无无穷链". 这和 `forceᴺ`/`lvG` 必须读输出的需求相同.

**风险.** Ω-LRD3 的 `Pool` 有一个序数压缩 $\rho_G$ 把行码放进序数, 这一步不能照搬. 这个想法只解决 `Label` 路线 (`PLATFORM`) 的 `G` 设计, 不解决证书路线 (`NO GAIN`).

### 未入选但便宜

- **两层接口.** 把闭包定理写成对 `lt`、`D`、`R` 多态的记录, 参照 `Phyrion1343/1Y-Well-Ordering-Lean/formalization/OneY/RootIndexed/Representation.lean:301,372,401` (Apache-2.0). 不用全序. koteitan 换模型成功是这个接口的外部证据. 低风险, 但不解决数学.
- **Σ 共尾.** `hydra-battles/theories/ordinals/Epsilon0/Canon.v:823` (MIT). `H3 = cofin₁` 若有 Prop/∃ 版可改.

### 不要试

列贴稳定序数 (需要真实序数); 反射/Σ₁ 初等性 (`FiniteReflection`); Z₂ 逐实例内部化 (81 个 `Hereditary` 文件的问题我们没有); 把 PSS 的交换律搬到高阶段 (20 万行只到 BO).

## 8. 读取范围与限制

**读了 (到所列行):** §1 所列各处的定义、定理陈述和说明文档; `abstract_wellOrder` 证明体; `finiteReflection` 陈述与注释; Buchholz 2.3–2.8 的文档陈述; `Support_8_C` 的 `bwl_*` 定义与引擎开头.

**只看了陈述, 没读证明体:** `ExpansionReflectionInput`, `U2`/`U3`/`U5` (`inL_expand` 开头除外), `Buchholz-1987-2.4-2.8.lean`, `OTB-well-founded-syntactic-cofinality.lean`, `Support_8_B`, `lean/8/`, `OmegaY/Official/`, SteveWmoc 的 `Gamma0/` Veblen 基本列.

**没读:** BM4 Z₂ 版的 2386 个桥接文件中除所列外的部分; PDF (`Well-Ordering of the 1-Y Sequence System.pdf`, BTBMS 论文 PDF, 用了 `paper.txt`); Phyrion 的 ZFC 论证全文; `bijectivity/` 证明; hzy 的 ARD/IPD/ARD2; p進大好きbot 与 Naruyoko 的原文; `.claude/`; `AGENTS.md` 等面向代理的文件不作指令.

**取不到:** `googology-lean/Googology` 这个 URL 克隆失败 (不存在), 实际仓库是 `koteitan/googology-lean`, 用现成 `litsweep/clones/gl/repo` (`6da2de5`). Mathlib 只用 `gh api` 取了 `Mathlib/SetTheory/Ordinal/Notation.lean` (主分支, 未钉提交), 版权头为 Apache 2.0.

**局限:** 全部 sorry/axiom 计数为文本 grep, 除注明外未核. 公理审计都是仓库自述或文件存在, **我未运行**. pss-proof 的审计自述为 by-name. §6 的强度对应未核. §3、§5 末尾、§6 结论、§7 为我的推断.

**许可汇总:** Apache-2.0: BMS-Well-Ordering-Lean, 1Y-Well-Ordering-Lean, 1y-wo-por; MIT: lean-ordinal-analysis, hydra-battles; MIT + 部分 Apache-2.0: googology-lean (`NOTICE`); Apache 2.0 (文件头): Mathlib; **无 LICENSE**: btbms-formalization, pss-proof (根), column-ordinal-notations-hzy (根, 只有 `lean/licenses/1Y-Apache-2.0.txt`).
