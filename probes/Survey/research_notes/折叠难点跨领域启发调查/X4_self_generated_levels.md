# X4 层号由系统自己生成、运算对层一致的系统: 跨领域可移植装置调查

范围: 不找与我方问题一模一样的先例, 只收可移植的装置. 每个想法给五项: (1) 原领域的技术与出处; (2) 对应抽象形状的哪一面; (3) 在我方设定里的具体草图; (4) 最便宜的实验; (5) 可能碰到的已编译否定 (只标出, 不据此丢弃). 编号 #1–#15 按前景排名 (排名是判断, 理由见问题 6). 来源档位: [原文·读] 读了相关段落; [原文·摘读] 经抓取工具摘要读了正文; [检索摘要] 只见摘要或检索片段; [据记忆, 未核] 未经本轮核对. 与前一轮 (R1–R5) 重复的来源只在给出新角度时引用.

## 问题 1: 大数记号社区 (BMS, Y 序列, Taranovsky) 的展开规则怎样不经全局比较处理系统自生的层

### Takeaway
BMS 一类记号里, 一个元素在展开时 "升级" 还是 "保留", 取决于被折叠的根是否落在它的祖先链上, 不取决于数值比较; 第 m+1 行的父子关系被限制在第 m 行的祖先链里, 所以层由系统自己生成, 并且逐层嵌套. Taranovsky 把层号取消成 "度" (degree), 度就是同一系统里的序数; 唯一的构造子 C(a,b) 的定义里没有按层分情况, 目标层由底数 b 代替, 对角由输出 c 截断. 两者在有限句法上都把序化成字典序; 搬到无穷树上, 能留下的是 "按祖先或来源派发" 和 "以底数与输出代替目标层" 两条.

### Cited Findings
- **BMS 的父与祖先 (Definition 1.1) [原文·摘读].** 第 m 行的 m-parent 是 "在它之前、第 m 个元素更小的最后一列"; m > 0 时还要求这一列是它的 (m−1)-ancestor. 所以第 m 行的父子关系只在上一行的祖先链里找. 严格 m-ancestor 是 m-parent 及其 m-ancestor. — [arXiv:2307.04606, Well-Orderedness of the Bashicu Matrix System](https://arxiv.org/html/2307.04606v3) (作者署名检索摘要给出两种说法, 未核)
- **BMS 的展开与升级 (ascension) [原文·摘读].** 设末列 C 的最大 m₀ 使 C 有 m₀-parent, 写 A = G + B₀ + (C), B₀ 的首列是 C 的 m₀-parent. 对 B₀ 中每列 D 与每个 m < m₀: 若 B₀ 的首列是 D 本身或 D 的 m-ancestor, 则 D 的第 m 个元素 "ascends". Bᵢ 是 B₀ 的拷贝, 升级的元素加 i·(C 的第 m 元 − B₀ 首列的第 m 元); A[n] = G + B₀ + … + Bₙ. — [同上](https://arxiv.org/html/2307.04606v3)
- **BMS 的良序证明 [原文·摘读].** Lemma 2.1: A[n] 字典序小于 A; Lemma 2.3 全序; Corollary 2.4: 序与字典序一致; Lemma 2.5: 祖先关系在各拷贝之间保持 (对 k 归纳). 最后一步 (Lemma 2.6, Theorem 2.7) 用 L_α 的 Σₙ-初等子结构 (稳定性) 把数组映到序数; 文中说自足的证明仍是开放问题. — [同上](https://arxiv.org/html/2307.04606v3); 本仓库 `CodeGuide.md` §3 已记 BMS 类良序证明 "只有定义无序数".
- **Y 序列的父结点 [检索摘要].** 每个非 1 的项向左找第一个更小的数作 "父", 连线得 hydra 图; 第二层起由上一层参与确定父结点. — [Introduction to Googology (wxyhly)](https://wxyhly-en.github.io/archives/ggg-ord) (检索片段, 未逐字核对出处)
- **Taranovsky 的度与 C (§2.1) [原文·读].** "度" 是良序集上的任意二元关系; C(a,b) 定义为 b 之上、度 ≥ a 的最小元. 度的公理: 一切元有度 0; 极限 a: 有度 a 当且仅当有一切更小的度; 后继 a+1: 度 a 的元的极限点 (或带界的变体). 标准形下 C(a,b) < C(c,d) ⇔ C(a,b) ≤ d ∨ (b < C(c,d) ∧ a < c). — [Taranovsky, Ordinal Notation, arXiv:1610.04633](https://arxiv.org/abs/1610.04633)
- **Taranovsky 的对角度截断 (§2.1) [原文·读].** 一列递增的度 a₁, a₂, … 的对角 a_diag: c 有度 a_diag 意为 c 有度 a_c; 为保单调, "aᵢ may only be used when i<c", i ≥ c 时视同 a_diag. 他还写: c 增大越过 a 的某些子项时, 这些子项从反射配置的构件变成参数. — [同上](https://arxiv.org/abs/1610.04633)
- **Taranovsky 主系统 (§5.1) [原文·读].** 句法只有 0, Ωₙ 与二元 C; 比较是后缀式的字典序 ('C' < '0' < 'Ωₙ'); C(a,b) 标准当且仅当 a, b 标准, b 是 0, Ωₙ 或 C(c,d) 且 a ≤ c, 并且 a 从 <C(a,b) "n-built from below". 定义: a 0-built from below from <b 当且仅当 a < b; n+1 级要求 a 的标准表示只在 n 级子项的作用域内用到 a 之上的序数. 良基证明只对弱化版本给出, 强度是猜想. — [同上](https://arxiv.org/abs/1610.04633); [FOM 2012 帖](https://cs.nyu.edu/pipermail/fom/2012-March/016349.html)

### Inferences

**#1 祖先链决定升级 (按来源派发, 不按值派发).**
- (2) 对应的面: "保留/对角/走链按层与目标的关系分情况" 与 "两个裸层号不可比". BMS 的升级判据是 "被折叠的根是否在我的祖先链上", 是一条路径谓词; 第 m+1 行嵌在第 m 行的祖先树里, 正是 "层由系统生成" 的有限版本. 我方已编译的 `compare-link` (只有路径相连的位置对可比) 与它同形.
- (3) 草图: 树里出现的每个层号不存成裸树, 存成 "指向祖先结点的指针" 加上 "在该结点参数上的读法" (类似 de Bruijn level). 折叠到目标 t 时, 孩子的层号若经由被折叠结点的参数而来 (被折叠结点是它的祖先) 就走链或对角, 否则保留. "是不是祖先" 沿指针结构递归即可判定, 不碰层号的值. 当前的保留缺陷 (目标经指定孩子时, 低于目标的槽位仍走链) 在这一写法下变成: 槽位的指针不经过被折叠结点, 就自动保留.
- (4) 实验: 在 `<实验目录>` 写纯 `.agda` 玩具, 两层 (Ω₁, Ω₂) 的树, 结点层号写成祖先指针 (深度下标或路径类型); 写 ψ₀, ψ₁, 派发只看指针是否经过被折叠结点. 判据: 不用 `Dec` 与 `Funext` 通过检查; 两三棵小闭项与 YiLean 读回的值至少单向 ≼. 通过后再把层号本身换成带指针的树, 试第 3 站 ψ₀(Ω_{Ω_Ω}) 的第一层.
- (5) 可能的冲突: `locate→irr-search` (保留结点的位置必须是数据): 一致, 指针就是数据. `top-branch→lpo`: 若要求 Ω-分支的各支对一切带守卫坐标满足保留律则推出 LPO; 指针在各支里是否一致需要查. `moved-undirected` 与 `self-not-cohX` (各支用各自的槽位时互不为第一位置; 槽位必须规范): 指针方案要让各支的指针取规范位置. `chain→weak-eq`: 值相同而来源不同的两个层号会被分到不同的行, 值上是否互相 ≼ 要用验收定理说 (见 #3). 纲领第 4 条: 借的是装置, 不引用 BMS 的项; 按 "借助记号探路" 如实标出. BMS 自己的值分析用稳定性, 没有可直接借的值定理.

**#8 以底数代替目标层, 以输出对角 (Taranovsky 的 C(a,b)).**
- (2) 对应的面: "层号由同一构造产生" 与 "规则对层一致". 在 Taranovsky 的系统里没有单独的层号类型, Ω 类的序数只是度很高的元; C 的定义没有按层分情况, 层与目标的关系被 "底数 b" 与 "输出 c" 吸收.
- (3) 草图: 树侧定义 next(a, b) = "b 之上第一个度 ≥ a 的点", 对度树 a 递归: a = 0 给 b+1; a 为后继形给 next(a′, ·) 从 b 起的 ω 次迭代; a 为 ℕ-极限给 sup_n next(a[n], b); a 为 Ω-极限 (分支 g) 给对角不动点: c₀ = b+1, c_{k+1} = next(g(c_k), b), 结果 sup_k c_k. 也就是 Ω-分支总在当前的输出近似处取值, 对应 "aᵢ 只在 i < c 时用". 这样 "折叠到目标层" 换成 "底数之上取下一个闭包点": 小于输出的子项自然成为参数, 不再要显式的保留行.
- (4) 实验: 只用 Ω₁-分支的度树写 `next`, 与 BTBO 的 ψ₀ 在小闭项上比 (先证一个方向的 ≼); 再加 Ω₂-分支, 这时 g(c_k) 要把可数的 c_k 嵌进第 1 层 (要一个嵌入). 用 `YiNextAccTest` 式的有限测试看保留是否不经派发自己出现.
- (5) 可能的冲突: Taranovsky 的标准形 (built from below) 要拿子项与输出比较, 在树上不可判定, 属 `obs→dec` 一族; 去掉标准形限制, 他本人指出单调性会失效, 值定理可能不成立. Ω-分支在可数近似处取值要求嵌入, 留意 `Toy.loop` (不可数下标不能作可数层的构造子). 判断: 不加限制地 "一切 Ω 结点都按输出对角" 可能使强度掉到远低于 ψ₀(Ω_Ω) 的地方, 需先在小例子上测.

- 两个系统共有的一点: 标准形使序退化成句法的字典序 (BMS Corollary 2.4; Taranovsky §5.1 的后缀字典序). 搬到树上的读法 [判断]: 只在规范读回域上、沿有限主干比较时, 才可能有 "第一处不同" 式的比较; 这与 "字面公共上界" 的要求同向.

### Gaps
- 社区里称为 "hyper-recursion" 的记号与 "Ω-level" 记号没有找到可读的一手定义, 未收.
- Y 序列与 ω-Y 序列的一手定义 (日文 wiki, 作者原帖) 未读; 上面只有检索片段. pair/primitive sequence system 的停机分析见本仓库 `CodeGuide.md` 的 `pss` 一条, 本轮不重复.
- BMS 论文的作者署名 (检索摘要两种说法) 未核.

## 问题 2: 类型论里由系统自己生成的宇宙与层 (下层工具包, 外部 Mahlo, 层号代数, 很依赖的类型, 二层类型论) 怎样对层一致地定义函数

### Takeaway
类型论这一侧有三种可借的做法. 一是把 "下层的能力" 打包成记录, 由结点里存的 `l′ < l` 证明取出, 层号从不比较 (LogRelKit). 二是外部 Mahlo 宇宙: 每个子宇宙由系统内的算子生成, 按算子的码递归; 对 "全体层" 不给消去规则, 因为加了自然的消去规则就矛盾 (Palmgren 悖论), 这与我方的壁垒定理同形. 三是让层号成为带并 (⊔) 的符号表达式, 比较换成从约束推导 (Bezem–Coquand). 另有两种结构性的手段: 很依赖的函数类型与二层类型论或余归纳的层塔.

### Cited Findings
- **LogRelKit (Abel–Öhman–Vezzosi 的 Agda 形式化) [原文·读].** `module LogRel (l : TypeLevel) (rec : ∀ {l′} → l′ < l → LogRelKit)`; 宇宙情形的记录存 `l′`、`l< : l′ < l`, 再 `open LogRelKit (rec l<)` 取下层的判断; 最后 `kit l = LogRel.kit l (logRelRec l)`. 那里层号只有 ⁰, ¹. — [logrel-mltt, Definition/LogicalRelation.agda](https://github.com/mr-ohman/logrel-mltt/blob/master/Definition/LogicalRelation.agda); 论文 [Decidability of Conversion for Type Theory in Type Theory, POPL 2018](https://www.cse.chalmers.se/~abela/popl18.pdf)
- **Kovács 的一般层级 (新角度) [本仓库已读].** `CodeGuide.md` 记: 该库 "全程消费证据, 只上行 `Lift`", 没有把高层压到低层, `cmp` 是假设. 本条只补一个角度: 往下的方向 (折叠) 正是这类构造缺的那一半. — 本仓库 `probes/Survey/CodeGuide.md` §3 (`kv` 一行)
- **Palmgren 悖论与外部 Mahlo 宇宙 [原文·读, pp.1–6].** Dybjer–Setzer 写: Palmgren 发现给 Mahlo 宇宙加自然的消去规则导致矛盾. 他们区分 "external" Mahlo 宇宙 (类型 Set 本身, 对其每个族算子 f = (f₀, f₁) 有归纳-递归定义的子宇宙 `U f₀ f₁` 与解码 `T`) 和 "internal" 的 `M : Set`. Set 视为 "开放", 不自然加消去规则. 关键: 把子宇宙加进 Set, 只要求 f 在 `U f` 自身上的族上是全的; 类型检查只检查 `T f₀ f₁` 像里的参数, 避免循环. 文中附 Agda 代码 (构造子 c₀, c₁). — [Dybjer & Setzer, Predicativity of the Mahlo Universe in Type Theory (2025)](https://csetzer.github.io/articles/dybjerSetzerWeylVolume2025/dybjerSetzerWeylVolume2025Final.pdf)
- **超宇宙 [原文·读, p.2].** 超宇宙对 "把宇宙 (Uₙ, Tₙ) 映到下一个宇宙" 的算子封闭, 再迭代得 superⁿ 宇宙; Mahlo 宇宙包含一切由族算子生成的宇宙作子宇宙. — [同上](https://csetzer.github.io/articles/dybjerSetzerWeylVolume2025/dybjerSetzerWeylVolume2025Final.pdf); TYPES 2024 报告 [slides](https://types2024.itu.dk/slides/Peter%20Dybjer%20-%20Predicativity%20of%20the%20Mahlo%20Universe%20in%20Type%20Theory.pdf) [检索摘要]
- **层号约束的判定 [检索摘要].** Bezem–Coquand: 带一个膨胀自同态 (+) 的并半格, 其一致字问题与 loop-checking (是否有 t+ ≤ t) 都在 PTIME; 无 loop 时约束在 (ℕ, max, succ) 里有模型; 动机是类型检查里的宇宙层号约束. MetaCoq 有基于其构造性证明的实现. — [Bezem & Coquand, TCS 913 (2022)](https://research.chalmers.se/en/publication/530474); [MetaCoq PR #704](https://github.com/MetaCoq/metacoq/pull/704)
- **很依赖的函数类型 (§3) [原文·读].** Hickey 记作 {f | x:A → B_{f,x}}: 值域可以引用 f 本身; 要求值域的说明 "respect some well-founded order on the domain", 语义按 {a′ : A | a′ < a} 上的限制逐步定义, 排除 f(i) 依赖 f(i) 的循环. HoTT 里与 Reedy fibrant 图相关 (邮件列表帖, 检索摘要). — [Hickey, Formal Objects in Type Theory Using Very Dependent Types (FOOL 3, 1996)](https://www.cs.cornell.edu/jyh/papers/fool3/paper.pdf); [types-list 帖](https://www.mail-archive.com/types-list@lists.seas.upenn.edu/msg00421.html)
- **二层类型论 [检索摘要].** 对每个外部固定的 k 能构造编码 k 级半单纯类型的 S_k, 但没有内部函数一次覆盖所有层; 外层 (exo) 类型满足 UIP; Agda 有 `--two-level`. — [Annenkov, Capriotti, Kraus, Sattler, Two-Level Type Theory and Applications, MSCS 33 (2023), arXiv:1705.03307](https://arxiv.org/abs/1705.03307)
- **余归纳的 opetopic 层塔 [检索摘要].** 以定义性结合、单位的多项式单子宇宙扩展类型论, 得到 opetopic type (opetopic 胞腔的余归纳族); Agda 形式化用了公设与重写规则. — [Allioux, Finster, Sozeau, Types are Internal ∞-Groupoids, LICS 2021, arXiv:2105.00024](https://arxiv.org/abs/2105.00024); [HoTT 2023 slides](https://hott.github.io/HoTT-2023/slides/allioux.pdf)

### Inferences

**#2 由证据取出的下层工具包, 派发写成字典沿路径传下.**
- (2) 对应的面: "每层的定义要用到更低层的定义, 又不比较层号". LogRelKit 里比较从不发生: 宇宙结点自己存着 `l′` 与 `l< : l′ < l`, 下层的工具包凭这条证明取出.
- (3) 草图: 把折叠写成 `module Fold (t : Lv) (rec : ∀ {t′} → Below t′ t → FoldKit t′)` 的开放递归, 字段是 keep 行, diag 行, chain 行等. 结点不问 "我的层号与 t 什么关系", 只调用传到它手里的工具包: 根处的工具包由调用者给出 (调用者知道目标), 孩子的工具包由 "孩子的层号是在本结点的分支域里产生的" 这条证据算出, 是数据. 打结时对目标 t 的构造良基递归, 不对树. 现有的派发证书 `Carry` 已经接近工具包的形状; 这个写法提示把它从 "证书" 改成折叠模块的参数.
- (4) 实验: 在临时目录复制 YiLean 折叠, 改成上面的开放递归形状; 只看 "同层对角" 一行能否写成对 Ω-结点分支类型携带的证据调用 `rec`. 判据: 定义里不出现 `Dec`; 行数与原折叠对比.
- (5) 可能的冲突: 壁垒定理要 "有界三歧", 工具包只要 `<` 的证据, 不在其中; 但若要求对每个孩子都给出工具包 (派发完全), 会落到 `branch-complete→lpo`、`bare-incomplete`. `compare-irr→irr-search` 与 `keep→irr-search`: 工具包里的证据必须是相关数据, 不能标成无关参数 (LogRelKit 的 `l<` 也是相关的). Kovács 一路只有上行, 往下的这一半是新的, 没有现成的定理可借.

**#5 外部 Mahlo 式的层: 按生成算子的码递归, 合法性只查 "像", 不对全体层消去.**
- (2) 对应的面: "层是系统自己运算的输出" 与 "全局的层比较被禁止". 每个子宇宙 `U f` 由 Set 里的算子 f 生成; 对 "全体层" 不给消去, 因为 Palmgren 悖论. 这和我方壁垒定理 (下标类型不能同时是精确初始段、含 Ω-共尾元、有有界三歧) 是同一类事实: 能对一切层一致地消去的结构推出坏结论.
- (3) 草图: (a) 层号不当裸树, 当 "由哪个已有的折叠或算子生成的" 码, 如 `U f` 其中 f 是已经造出的折叠; 新层上的折叠对码 f 的构造递归, 不与别的层比较. (b) 合法性仿 "f 在 `U f` 自身上全": 新层只要求生成它的算子在这一层自己的像上有定义, 正好对应 "律先对读回域陈述". (c) 不写 "对全体层号消去" 的函数.
- (4) 实验: 30 行左右的归纳-递归玩具: `data U (f : Op) : Set` 与 `T : U f → Tree`, 其中 `Op` 是对复合封闭的折叠类算子; 检查 Ω, Ω_Ω, … 能否写成 `U (fold ∘ …)`; 再试在层号为 `U f` 的结点上只按 f 的码分情况写折叠.
- (5) 可能的冲突: 码是系统自己的句法, 证书是否算 "引用记号" 要由作者判断 (纲领第 4 条). `Toy.loop`: 若 `U f` 被用作可数层构造子的下标就违反. 归纳-递归在 Agda `--safe` 下可用 [判断, 未在本仓库选项下测]. 外部 Mahlo 的强度论证用的是集合论模型, 对我方没有现成的值定理.

**#7 层号的符号代数: 有字面的并, 比较只从记录的约束推出.**
- (2) 对应的面: "被比较的两个下标必须有字面的公共上界". 在 Agda 的 `Level` 与 Bezem–Coquand 的代数里, 任何两个层号都有字面的并 ℓ ⊔ t; 实践中从不比较层号, 只往并上提升.
- (3) 草图: 层号表达式以 "已产生的折叠输出" 为原子, 用 ⊔ 与 Ω-后继 (作膨胀自同态) 生成; 约束是构造时记下的证据 (例如 "这个输出是折叠含那个层号的树得到的" 给出 a < b). 派发只问 "从已记录的约束能否推出 ℓ < t / ℓ = t", 结果是 "可推出 / 推不出" 两种, 推不出时一律走同一条规则; 值的正确性只在读回域上证, 那里需要的事实都能推出.
- (4) 实验: 玩具 `data LExp` (原子取 `Fin n`, `_⊔_`, `Ωₑ_`), 约束是列表, 写一个可靠但不完全的推导检查器, 接到塔的第 3 项闭项的派发上. 判据: 闭项合法无前提; 链点上的派发在需要的地方都推得出 (仿 `chain-honest`).
- (5) 可能的冲突: 壁垒要求 "精确初始段": 表达式一个值有许多名字, 三歧只是部分的, 看来不在其中 [判断]; 但若要求原子的解释精确, `seg↔LPO` 与 `embVᴰ→LPO` 会出现. 纲领第 4 条: 表达式是系统自己的句法, 不是序数记号, 归属要作者定. 翻译账: 这是新增的脚手架.

**#9 输出回灌写成很依赖的函数 (或归纳-递归的链).**
- (2) 对应的面: "折叠输出回灌作下标". 后面的层号由前面的输出算出, 正是 {f | x:A → B_{f,x}} 的形状; 值域只能引用更小参数处的 f.
- (3) 草图: 结点内部的对角链写成 `data Ch : Set` 与 `top : Ch → Tree` 互相定义, 构造子 `step : (c : Ch) → Tree (lvl (top c)) → Ch`. 这样 "第 n+1 个链点的层号由第 n 个输出建成" 是定义性的, 任意两个链点都沿这条路径有字面公共上界 (链的极限).
- (4) 实验: 写上面的归纳-递归玩具, 看 `compare-link` 要求的 "路径相连" 能否定义性地满足, 而不需要额外的证据字段.
- (5) 可能的冲突: `no-compare-tw2` (公共上界含 Ω 结点时任意两个位置的比较不可满足): 只对链上的位置对有效, 不对任意位置对; `moved-undirected`. Hickey 的语义是 PER 语义, Agda 里只能用归纳-递归模拟 [判断].

**#11 二层类型论与余归纳的层塔: 层号的簿记放到严格的外层或余归纳塔里.**
- (2) 对应的面: "对自生的各层一致地定义". 半单纯类型在内部对一切层一致的定义是著名难题, 2LTT 把层号放到外层的严格自然数上就能写; opetopic 方案用余归纳的塔, 每一层由上一层经同一个运算得出.
- (3) 草图: (a) 外层: 层号用一个归纳类型的码 (如 "第几次折叠应用"), 其相等由构造严格给出并可判定, 派发只看外层码; 布劳威尔树的 View 把码映到树. (b) 余归纳: `record Tower : Set where field here : Sig; next : Tower`, 下一层的分支签名由这一层经单一运算得出 (Ω_{ℓ+1} 在第 ℓ 层的树上分支), 折叠对塔余归纳, 对树归纳; 本仓库的库选项已有 `--guardedness`.
- (4) 实验: 带 `--guardedness` 的余归纳塔玩具, 签名到 ω 层, 用 copattern 定义折叠; 看在 `--safe --without-K` 下能否一致地到 Ω_ω, 以及到 Ω_Ω 时哪里失败 (层号由树而不是 ℕ 索引).
- (5) 可能的冲突: 若外层码是含 Ω-共尾元、有三歧的精确初始段, 壁垒定理直接适用, 所以外层必须不精确或不全比较. Allioux 等用了公设与重写规则, 不能照搬到 `--safe`. 纲领第 4 条的归属同 #7. `Toy.loop`.

### Gaps
- Kovács CSL 2022 原文 ("Generalized universe hierarchies and first-class universe levels", arXiv:2103.00223 [据记忆, 未核]) 本轮没有重读; 只引用本仓库已有的读后记录.
- Palmgren 悖论的证明细节 (Dybjer–Setzer 附录里的 Agda 代码) 未读到; 只读了正文前 6 页.
- 2LTT 与 opetopic 两篇只有摘要级信息; 半单纯类型的余归纳写法出处未核.
- Bezem–Coquand 全文未读, 只有摘要与幻灯片的检索片段.

## 问题 3: 递归格式 (Mendler, PHOAS, sized types, 历史表) 能否让定义不看层号

### Takeaway
Mendler 式迭代与 PHOAS 都靠参数性: 递归调用或约束变量的类型是抽象的, 定义无法检查它们, 只能使用. 搬过来的读法是: 让 Ω-结点的分支参数类型抽象, 折叠以 "实例化哪个类型" 代替 "比较哪个层号". sized types 给出极限尺寸处的语义判据 (上半连续), 对应我方极限层号处 "部分和还是逐项极限" 的问题. 历史表 (comonad 递归格式) 给出沿结构查表而不比较的做法.

### Cited Findings
- **Mendler 式递归组合子的层级 [检索摘要].** Ahn–Sheard: Mendler 式 catamorphism 对含负出现的数据类型也停机; course-of-values (histomorphism) 对负类型有问题 (后来的文献说对任意负类型推出不停机); 新组合子 msfcata 对一切归纳类型停机. — [Ahn & Sheard, ICFP 2011](https://bibtex.github.io/ICFP-2011-AhnS.html); [Course-of-Value Induction in Cedille, arXiv:1811.11961](https://arxiv.org/abs/1811.11961)
- **Mendler 迭代的类型 [据记忆, 未核].** mit : (∀R. (R → A) → F R → A) → μF → A: 递归调用以抽象的 R → A 给出, 定义不能检查 R 的结构. 出处 Mendler (APAL 51, 1991); 范畴论读法 Uustalu–Vene "Mendler-style inductive types, categorically" (Nordic J. Computing 1999).
- **PHOAS [检索摘要].** Chlipala 用对抽象变量类型参数化的高阶抽象语法在 Coq 里形式化语义与变换 (CPS, closure conversion, System F 的 CPS). — [Chlipala, Parametric Higher-Order Abstract Syntax for Mechanized Semantics, ICFP 2008](https://adam.chlipala.net/papers/PhoasICFP08/)
- **上半连续的 sized types [原文·摘读].** Abel 把 sized type 解释为从序数到强正规项集合的函数; 递归函数的类型若对尺寸上半连续 (lim sup_{α→λ} A(α) ⊆ A(λ)) 就可接受 (§1, §4). 反例 A(ı) = (Nat^ω → Nat^ı) → Nat^ω 不上半连续, 导致不停机 (§1). 尺寸语法 ı | s a | ∞, 解释为直到闭包序数的真序数 (§2.3, §3.2); 数类 NC_n 需要逐级更高的闭包序数 (§3.4). — [Abel, Semi-continuous Sized Types and Termination, LMCS 4(2:3) 2008](https://lmcs.episciences.org/1236); [arXiv:0804.0876](https://arxiv.org/abs/0804.0876)
- **comonad 递归格式 [检索摘要].** Uustalu–Vene–Pardo 给出以函子与 comonad 参数化的通用递归格式, histomorphism 是取 cofree comonad 的特例; Hinze–Wu–Gibbons 证明 adjoint folds 涵盖它. — [Recursion Schemes from Comonads, Nordic J. Computing 8(3) 2001](https://www.academia.edu/7453886/Recursion_Schemes_from_Comonads); [Unifying structured recursion schemes, JFP](https://www.cambridge.org/core/journals/journal-of-functional-programming/article/unifying-structured-recursion-schemes/2CF2B29B85890E893F9761EA1C3B709E)
- **Agda 的 sized types 与 `--safe` [据记忆, 未核].** Agda 的内建 sized types 有已知的不一致 (∞ < ∞ 一类问题), 新版本里 `--sized-types` 不能与 `--safe` 同用.

### Inferences

**#4 极限层号处的上半连续律.**
- (2) 对应的面: 一个对层号定义的东西延伸到极限层号时怎样才对. Abel 的判据: 极限处的值必须包含前面各层的 lim sup, 递归穿过极限才可靠. 我方已编译: 保留模式下极限层号上的 top 只能取各支折叠的部分和 (`side-lim-illegal`); 部分和与逐项极限在 ω, ω·2 上互相 ≼, 在退化的常值层号上严格偏高 (`ω-psum≼lim`, `const-inflates`).
- (3) 草图: 把 "合法性 (或读回域) 对层号上半连续" 写成接口的一条律: 对极限层号 λ 与基本列 λ[n], 在无穷多个 λ[n] 上合法的东西在 λ 上合法. 若读回域满足这条律, 逐项极限无须部分和就合法. 另一层用法: 给每棵树带一个尺寸 (一棵布劳威尔树) 作字面上界, 比较换成沿 `≤` 证据的强制转换, 任意两棵树的尺寸有字面的并, 公共上界不用另找.
- (4) 实验: 对当前合法性谓词在塔的读回域上陈述这条律, 先证层号 ω 一处; 证不出就抽出反例. 预计反例是常值层号一类的退化结点 (与 `const-inflates` 同位置), 这样能精确定位部分和是被哪个对象逼出来的.
- (5) 可能的冲突: 内建 sized types 不能用, 只能用显式的尺寸下标模拟; 尺寸若作为有三歧的下标类型就触壁垒定理; 按 "量化域先取读回域" 的最佳实践, 这条律在全合法域上多半不成立, 只在读回域上有望成立 [判断].

**#6 分支参数类型抽象, 折叠以实例化代替比较 (Mendler / PHOAS).**
- (2) 对应的面: "折叠不该检查层号". 参数性保证对抽象类型多态的函数不能检查它的元素; 派发变成 "实例化哪个类型".
- (3) 草图: `Tree (V : Sort → Set)`, 其中 `Sort` 是 "到目前为止生成的层" 的上下文位置 (不是层号的值); 第 s 类的 Ω-结点是 `(V s → Tree V) → Tree V`. 折叠到目标类 s₀ 就是一次实例化: V s₀ 取可数树 (对角处喂入输出), 其他类保持抽象, 分支仍是抽象类型上的函数, 于是自动保留. "高于目标就走链" 需要知道上下文里哪些位置在 s₀ 之上; 位置是上下文的下标, 比较可判定. 这一条与 #1 是同一思路的两种实现: #1 用祖先指针, #6 用类型.
- (4) 实验: 两类的 PHOAS 风格玩具, 用实例化写 fold₀; 记下 "高于目标" 的那一行到底需要位置的什么信息, 判据是它不需要层号的值.
- (5) 可能的冲突: 纲领第 1 条: PHOAS 树不是布劳威尔树, 要给 View (实例化 V := 对应层的树); 中间层可以比布劳威尔树多, 不违规. Agda 没有内部参数性, 但实例化本身不需要它; 值的正确性仍要另证. `locate→irr-search`: 位置是数据, 一致. Ahn–Sheard: 只用 Mendler 式迭代 (弱归纳), 不用 course-of-values, 以免碰到负出现的问题 (我方 Ω-分支是正出现, 判断风险小).

**#13 沿层号路径的历史表 (cofree comonad).**
- (2) 对应的面: 同层对角要用到更早算出的结果. histomorphism 让每一步看到沿结构的全部历史结果, 不重算也不比较.
- (3) 草图: 对层号树 (不是对被折叠的树) 写 histomorphism: 层 ℓ 处的结果是沿 ℓ 的构造排成的、各层折叠的表 (cofree comonad); 在 ℓ 的历史里产生的孩子层号 ℓ′ 用 "在历史中的位置" 查表 (与 #1 相同的位置化). 成品里已有 "折叠与表", 这里的读法是把表取成层号基函子的 cofree comonad, 查表就是取位置.
- (4) 实验: 把 YiSHEntry 的表改写成 `Cofree F` (F 为层号的基函子), 看派发能否写成 "取出 ∘ 按路径查表".
- (5) 可能的冲突: `locate→irr-search` (位置要是数据, 一致); `Toy.loop`; 表的大小随层号增长, 编译期堆的问题按手册 §4 处理.

### Gaps
- Mendler 原文与 Uustalu–Vene 1999 未核链接与卷期; Ahn–Sheard 全文未读.
- Abel 论文后半 (§4 以后关于高阶类型的演算) 未读完.
- 没有找到 sized types 直接用于高数类 (Ω_n 分支) 上的递归的工作; Abel §3.4 只说明数类需要更高的闭包序数.

## 问题 4: 可计算性与描述集合论: 沿记号的超限迭代怎样不判定记号之间的序

### Takeaway
超算术层级 H(a) 只沿记号 a 自己的构造 (零, 后继, 极限) 递归定义, 从不比较两个不同的记号; "选哪个记号无关" 是事后的 Spector 唯一性定理 (同序数给 Turing 等价的集合), 而且归约可以对 (a, b) 一致地写出, 只在 |a| ≤ |b| 成立时有效, 不需要判定它. Montalbán 的 true stages 用一族按层号嵌套、一致可计算的近似关系代替对 ξ 跳的判定, 极限层取交, 不连续处 "归咎" 到前面某一层; 每个阶段只有有限多层有非空近似. Duparc 的 Wadge 度从构造运算直接读出.

### Cited Findings
- **Kleene O 与 Spector 唯一性 [检索摘要].** <_O 是 Π¹₁-完全的; 对 a ∈ O, {b : b <_O a} 线序且可计算枚举; Spector: |a|_O = |b|_O 推出 H(a) 与 H(b) Turing 等价, 所以 Σ⁰_α 可经任一 |a| = α 的 H(a) 定义. — [Wikipedia, Kleene's O](https://en.wikipedia.org/wiki/Kleene%27s_O); [Spector, Recursive well-orderings, JSL 1955](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/recursive-wellorderings/00E43739CDCB310B2C134F03599EE246)
- **Moschovakis 的一致形式 [检索摘要].** |a| ≤ |b| 时 H_a 递归于 H_b, 归约的指标由 a, b 递归地算出; 序数相等时两者一一归约, 递归同构. — [Moschovakis, PJM 18(2) 1966](https://msp.org/pjm/1966/18-2/pjm-v18-n2-p11-p.pdf)
- **有效超限递归 [据记忆, 未核].** H 的定义经递归定理写成一个全函数 e ↦ (H(e) 的指标), 每一步只调用记号自身构造给出的前驱或基本列; 对不在 O 里的 e 也有输出, 只是不保证意义 (Rogers 1967).
- **true stages 的公理 [原文·摘读].** Montalbán 对每个计算序数 ξ 给阶段 (ℕ) 上的关系 ≤_ξ: 一致可计算的预序 (B1–B2); 嵌套, γ ≤ ξ 且 s ≤_ξ t 推出 s ≤_γ t (B3); 极限 λ 处 ≤_λ 是此前各 ≤_ξ 的交 (B4); 近似沿 ≤_ξ 增长 (B5); true stages 共尾 (B6); 另一条组合性质 (♣). Lemma 7.4: 给定阶段只有有限多层有非空近似, 可计算地找出; Lemma 7.8: 极限处的不连续由 "归咎" 到前面某层 γ_{λ,v} 修正. 他说难点从元定理里分离出来, 移进近似的定义. — [Montalbán, Priority arguments via true stages, arXiv:1306.2623](https://arxiv.org/abs/1306.2623)
- **true stages 的局限 [检索摘要].** 后来的文章指出元定理按原写法只覆盖 η 为后继序数的情形, 极限要另做. — [Day, Greenberg, Harrison-Trainor, Turetsky, Iterated priority arguments in descriptive set theory, arXiv:2211.07958](https://arxiv.org/abs/2211.07958)
- **Wadge 度与 Veblen 层级 [检索摘要].** Duparc 构造简单的 Borel 运算, 分别对应序数加法, 乘可数序数, 指数, 由此把有限秩 Borel 集映到其 Wadge 度, 并给出规范形. — [Duparc, Wadge hierarchy and Veblen hierarchy Part I, JSL 66(1) 2001](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/wadge-hierarchy-and-veblen-hierarchy-part-i-borel-sets-of-finite-rank/1CEA2E6C2A8B52CD64BFCB52D4F68BC8)

### Inferences

**#3 一致公式在假设成立时正确, 唯一性事后作值定理.**
- (2) 对应的面: "不比较层号的一致定义" 与 "树侧 '该有的值' 没有定义". 超算术层级给出三件事: 定义只沿对象自己的构造; 不同表示的一致性是事后定理, 只到等价 (Turing 度), 不到相等; 跨表示的归约对 (a, b) 一致, 只在假设成立时有效.
- (3) 草图: (a) 写一个全函数 emb(ℓ, t) : Tree_ℓ → Tree_t, 对一切 ℓ, t 都有定义 (按 t 的构造把 ℓ 层的树抬进去), 只证 "ℓ ≤ t 成立时 emb 保 ≼"; 保留行无条件地用 emb. (b) "该有的值" 定义成等价类: 先证 Spector 式定理 "值相同的两个层号, 折叠输出互相 ≼", 而不在定义里要求. (c) 对不在同一路径上的层号对, 规定一个统一的安全输出 (例如一律走链), 只在读回域上证明它不掉值.
- (4) 实验: 层号是到 Ω 的布劳威尔树的玩具里写 emb, 证 "ℓ ≼ t → emb 单调" 这一条件定理; 再把塔的第 3 项闭项的保留行改成无条件用 emb. 判据: 闭项合法无前提, 值下界不变.
- (5) 可能的冲突: `bare-way→lpo` 否定的是 "只读两个裸层号而处处正确" 的派发; 这里不要求处处正确, 只在假设下正确, 不在其中; 但如果输出的合法性要求处处成立, `bare-incomplete` 适用. `embVᴰ→LPO` 与 `seg↔LPO`: emb 不能要求保初始段. `no-L` (结构不可比): 唯一性只能是值上的 ≼, 不能是结构. 这条与 "第 4 层不改前 3 层" 相容: 唯一性是新增的值定理.

**#10 有限阶段的近似派发 (true stages 的读法).**
- (2) 对应的面: "裸层号的比较不可判定". Montalbán 不判定 ξ 跳, 而用一族按阶段可判定的猜测, 在无穷多个 true stage 上正确, 对层号一致; 每个阶段只有有限多层在场.
- (3) 草图: 我方每个 ℕ-极限都提供阶段 n. 在对角链或 ℕ-极限的第 n 项里, 用第 n 个猜测 guess_n(ℓ, t) 代替 "ℓ 与 t 的关系"; guess_n 只用有限信息 (例如两棵层号树沿主干的深度 n 截断). 布劳威尔极限的值只看共尾行为: 若猜错只会让该项的值不升 (安全性), 并且沿共尾子列最终猜对, 极限的值就对. 极限层号仿 B4 取交, 不连续处仿 Lemma 7.8 归咎到第 n 支.
- (4) 实验: 层号只有可数层 (Ω_ω 以内) 的玩具: 定义截断与 guess_n, 用它写折叠; 先证合法 (相邻项按第一位置步进), 再对 ψ₀(Ω_ω) 的参照证一个方向的 ≼. 关键判据是 "猜错只降值" 能否证出.
- (5) 可能的冲突: `strict→LPO` (BrwViewNeg; 要求 ℕ-极限严格递增推出 LPO): 猜测可能使相邻项不单调, 合法性要求第一位置步进, 必须证安全性. `side-lim-illegal`. 层号里有 Ω-分支时, 有限截断要取可数多个分支的近似, 可能根本做不到 (`Toy.loop` 一类); 这是本条最大的风险 [判断]. 规则形状不来自 FGH 的推广, 翻译账上算新增脚手架.

**#15 由构造运算读出度.**
- (2) 对应的面: 对象的 "层" 由生成它的运算读出, 而任意两个对象的层不好比.
- (3) 草图: 把 "怎样造出来的" (运算历史) 作为数据保存, 层的关系在历史的规范形上定义; 与 #5 (按生成算子的码), #7 (符号代数) 同一方向.
- (4) 实验: 没有便宜的 Agda 实验; 先读 Duparc 原文, 看运算与序数运算对应的证明是否只用构造信息.
- (5) 可能的冲突: 规范形近于记号, 纲领第 4 条的风险最高; 翻译账.

### Gaps
- 有效超限递归的一手出处 (Rogers 1967 的相应节) 本轮未读, 上面的描述据记忆.
- Montalbán 全文的最后约 7000 字符未读; 极限情形的完整处理以 Day 等的后续文章为准, 未读.
- Borel 码 (作为良基树) 的求值与秩的构造性处理, 本轮没有检索.

## 问题 5: 证明论里的层相对比较与反射式记号

### Takeaway
Takeuti 的序数图不做全局比较, 而用一族按指标 i 相对的序 <_i, 每个只看 "i-截面"; Arai 与 Pohlers–Stegert 分析 Πₙ-反射时, 用 Mahlo 类 Mh_k(ξ) 或反射配置代替基数层. 两者对我方的启发偏弱: 截面或类成员关系本身仍要与层号比较, 只在层号已经位置化 (#1, #6) 时才可能可判定.

### Cited Findings
- **序数图的 i-截面与序族 [检索摘要].** Takeuti 1957 递归地定义 "β 是 α 的 i-截面" (0 < i ≤ n); 顶点指标 j < i 时问题化归到尾部. 后来的表述对每个指标 i (或 ∞) 定义序 <_i, 集合 F_i 随 i 增大而递减; Yasugi 1978 比较不同指标的序型. — [Wikipedia, Ordinal notation](https://en.wikipedia.org/wiki/Ordinal_notation); [On Quasi Ordinal Diagram Systems, arXiv:1902.02012](https://arxiv.org/abs/1902.02012); [Yasugi, Some properties of ordinal diagrams](https://core-prod.cambridgecore.org/core/services/aop-cambridge-core/content/view/732612CF9C010A9D85E0331A805ECCB2/S0027763000021838a.pdf/some-properties-of-ordinal-diagrams.pdf)
- **一阶反射的简化分析 [检索摘要].** Arai 以 ψ-函数的记号 OT 与算子控制的推导消切, 用 Mahlo 类 Mh_k(ξ) 处理反射, 结构与 Pohlers–Stegert 的反射配置相近; KPΠ_N 的证明论序数为 ψ_Ω(ε_{K_N+1}). — [Arai, A simplified ordinal analysis of first-order reflection, JSL 85 (2020), arXiv:1907.07611](https://arxiv.org/abs/1907.07611)
- **BMS 与 Taranovsky 的反射读法 [原文·摘读 / 原文·读].** BMS 的良序证明经稳定表示把数组映到序数 (Lemma 2.6); Taranovsky 把 a 在 <c 的序数上的表示看成以它们为参数的反射配置 (§2.1). — [arXiv:2307.04606](https://arxiv.org/html/2307.04606v3); [arXiv:1610.04633](https://arxiv.org/abs/1610.04633)

### Inferences

**#12 只要相对于目标层的比较 ≺_t, 它只看 t-截面.**
- (2) 对应的面: 用一族相对于层的局部比较代替一个全局比较.
- (3) 草图: 对目标 t 定义 ≺_t, 只检查沿主干、层号 ≥ t 的部分 (t-截面); 折叠到 t 只需 ≺_t 的信息; 保留还是走链取决于 "这个结点有没有 t-截面", 这是结构存在性的问题, 对上 "按存在性保留" 的先验检查.
- (4) 实验: 先在纸上为 YiLean 的树写 t-截面函数, 看当 t 是字面子树时 "有没有 t-截面" 是否化归为字面形状; 化归得了再写 Agda 玩具.
- (5) 可能的冲突: 判定 "有 t-截面" 要拿结点的指标与 t 比较, 属 `obs→dec` 一族; 指标是树时碰 `chain→weak-eq`. 只有与 #1 或 #6 的位置化合用才可能成立 [判断].

**#14 以类成员资格代替基数层.**
- (2) 对应的面: 层是系统定义的类 (Mh_k(ξ), ξ 由系统内部产生), 折叠取参数之上类中的最小元, 没有 Ω_ξ 之间的比较.
- (3) 草图: 树侧的 "类" 是对指标树递归定义的谓词 (与 #8 的度同形); 折叠输出带类成员的见证, 派发读见证.
- (4) 实验: 先纸面: 查 Mh_k(ξ) 的定义里是否只用到 "ξ 在参数闭包中" 这类条件, 若是, 在树上它对应字面子树出现.
- (5) 可能的冲突: 类成员谓词在树上多半不可判定, 见证必须是相关数据 (`keep→irr-search` 一类); 照抄 Arai 的 OT 会加深翻译, 记翻译账.

### Gaps
- Takeuti 原文 (J. Math. Soc. Japan 1957) 与 Pohlers–Stegert 的反射配置都没有读到原文.
- Klammersymbole 与 Schütte 的多元 Veblen 函数、Ackermann 式的层号不动点, 本轮没有检索, 未收.
- 稳定性 (Rathjen 的 stability 分析) 只经 BMS 论文间接出现, 没有单独读.

## 问题 6: 综合: 排名, 交汇的装置, 建议的第一批实验

### Takeaway
各领域在三处交汇. (i) 用 "来源/位置/证据" 代替 "值的比较": BMS 的祖先链, LogRelKit 的 `l′ < l`, PHOAS 的类, Bezem–Coquand 的约束, 外部 Mahlo 的算子码. (ii) 先一致地定义, 不同表示的一致性事后作等价定理 (Spector, Montalbán 把验证移出构造, Taranovsky 的 C 定义里没有分情况). (iii) "对全体层一致消去" 普遍是禁区 (Palmgren 悖论, 2LTT 内部没有覆盖一切层的函数, 我方壁垒定理). 前景最高的是 #1 与 #2 合用: 层号位置化, 派发作为沿路径构造的字典传下, 再配 #3 的事后值定理.

### Cited Findings
- 排名表 (前景是判断; 出处见问题 1–5 各条):

| 排名 | 装置 | 原领域与出处 | 主要对着的面 | 最便宜的实验 | 先要查的否定 |
|---|---|---|---|---|---|
| #1 | 祖先链决定升级 | BMS ([arXiv:2307.04606](https://arxiv.org/abs/2307.04606)) | 保留/走链的派发; 只比较路径相连的位置 | 两层玩具, 层号写成祖先指针 | `top-branch→lpo`, `moved-undirected`, `chain→weak-eq` |
| #2 | 由证据取出的下层工具包 | LogRelKit ([logrel-mltt](https://github.com/mr-ohman/logrel-mltt/blob/master/Definition/LogicalRelation.agda)) | 每层定义用下层而不比较 | YiLean 折叠改开放递归 | `branch-complete→lpo`, `compare-irr→irr-search` |
| #3 | 一致公式 + 事后唯一性 | Spector / Moschovakis ([PJM 1966](https://msp.org/pjm/1966/18-2/pjm-v18-n2-p11-p.pdf)) | 不比较的一致定义; "该有的值" | 无条件的 emb + 条件单调定理 | `bare-way→lpo`, `embVᴰ→LPO`, `no-L` |
| #4 | 极限层号处的上半连续 | Abel ([LMCS 2008](https://lmcs.episciences.org/1236)) | 极限层号的行 | 在读回域上陈述并试证该律 | `side-lim-illegal`, `const-inflates` |
| #5 | 按生成算子的码递归, 只查像 | Dybjer–Setzer ([2025](https://csetzer.github.io/articles/dybjerSetzerWeylVolume2025/dybjerSetzerWeylVolume2025Final.pdf)) | 层是系统运算的输出; 无全局消去 | 归纳-递归 `U f` 玩具 | 壁垒定理, `Toy.loop` |
| #6 | 抽象分支类型, 实例化代替比较 | Mendler / PHOAS ([Chlipala 2008](https://adam.chlipala.net/papers/PhoasICFP08/)) | 折叠不检查层号 | 两类 PHOAS 玩具 | 纲领第 1 条的 View, `locate→irr-search` |
| #7 | 层号符号代数 | Bezem–Coquand ([TCS 2022](https://research.chalmers.se/en/publication/530474)) | 字面公共上界 | `LExp` + 可靠的推导检查器 | 壁垒定理, `seg↔LPO` |
| #8 | 以底数代目标层, 以输出对角 | Taranovsky ([arXiv:1610.04633](https://arxiv.org/abs/1610.04633)) | 层号与对象同类; 规则无分情况 | Ω₁-分支度树上的 `next` | `obs→dec` 一族, `Toy.loop` |
| #9 | 回灌写成很依赖的函数 | Hickey ([FOOL 1996](https://www.cs.cornell.edu/jyh/papers/fool3/paper.pdf)) | 输出回灌作下标 | 归纳-递归的链 | `no-compare-tw2`, `moved-undirected` |
| #10 | 有限阶段的近似派发 | Montalbán ([arXiv:1306.2623](https://arxiv.org/abs/1306.2623)) | 不可判定的比较 | Ω_ω 以内的猜测玩具 | `strict→LPO`, `Toy.loop` |
| #11 | 二层类型论 / 余归纳层塔 | 2LTT ([arXiv:1705.03307](https://arxiv.org/abs/1705.03307)), opetopic ([arXiv:2105.00024](https://arxiv.org/abs/2105.00024)) | 对自生的层一致定义 | `--guardedness` 塔玩具 | 壁垒定理 (外层不能精确) |
| #12 | 层相对的序族 | Takeuti 序数图 ([arXiv:1902.02012](https://arxiv.org/abs/1902.02012)) | 局部比较代替全局比较 | 纸面 t-截面 | `obs→dec`, `chain→weak-eq` |
| #13 | 沿层号路径的历史表 | Uustalu–Vene–Pardo ([2001](https://www.academia.edu/7453886/Recursion_Schemes_from_Comonads)) | 对角要用早先的结果 | 表改写成 `Cofree F` | `locate→irr-search` |
| #14 | 类成员代替基数层 | Arai ([arXiv:1907.07611](https://arxiv.org/abs/1907.07611)) | 层是系统定义的类 | 纸面 | `keep→irr-search` |
| #15 | 由构造运算读出度 | Duparc ([JSL 2001](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/wadge-hierarchy-and-veblen-hierarchy-part-i-borel-sets-of-finite-rank/1CEA2E6C2A8B52CD64BFCB52D4F68BC8)) | 层从构造读出 | 无便宜实验 | 纲领第 4 条 |

### Inferences
- 排名理由 [判断]: #1, #2 直接对着当前的保留缺陷, 并与已编译的 `compare-link` (只有路径相连可比) 和 `locate→irr-search` (位置必须是数据) 同向, 不像是要绕过已证的墙; #3 不改定义, 只给 "该有的值" 一个可写的形式, 符合 "第 4 层不改前 3 层"; #4 便宜, 对着一个已定位的编译事实 (极限层号的部分和). #8, #10 想法新, 但风险集中在 Ω-分支的可数近似上. #12–#15 依赖先把层号位置化, 单独做意义不大.
- 合用的建议 [判断]: #1 + #2 + #3 可以拼成一条路线: 层号写成指向生成它的结点或折叠应用的位置 (#1, 或 #5 的算子码, 或 #6 的类); 派发作为字典沿路径构造 (#2); 不在同一路径上的位置对规定统一的安全输出, 值上的一致性事后证 (#3). 这三条都不要求对裸层号作判定, 所以不直接落在 `bare-way→lpo`、`branch-complete→lpo` 的前提里; 是否落在 `top-branch→lpo` (各支对一切带守卫坐标满足保留律) 里, 取决于位置在 Ω-分支各支之间是否一致, 这是第一个要查的点.
- 与纲领的关系: 这些装置都不要求公理; #5, #7, #11 引入系统自己的句法 (算子码, 层号表达式, 外层码), 是否算 "引用记号" 需作者裁决; #1, #8, #12 的灵感来自记号, 按 "借助记号探路" 如实标出, 不能算树自足.
- 翻译账的预估 [判断]: #1, #6 的新字段 (指针, 类) 不读自任何记号的基本列规则, 属于 "由树的要求逼出" 一侧的候选; #7, #10 是新增的脚手架; #8, #14 若照抄标准形或 OT 会加深翻译.
- 对 "形状不同" 的提醒: 上述类比多数只在有限句法或可数层上验证过 (BMS, Taranovsky, 2LTT 的 k, Montalbán 的计算序数); 搬到含 Ω-分支的树上后, 哪些不再成立没有定理, 只能由上面的最小实验回答.

### Gaps
- 本轮没有找到在含不可数分支的树上直接实现 #1, #2, #3 任一装置的已有工作; 这不说明没有, 只说明本轮的检索没有覆盖到.
- 排名是判断, 没有任何一条经编译验证; 每条的 (4) 是建议的实验, 不是结果.
- Kovács (CSL 2022)、Ahn–Sheard、2LTT、Bezem–Coquand、Duparc、Takeuti、Arai 只读到摘要或检索片段; 若要据其中某条开路线, 先读原文对应的节.
