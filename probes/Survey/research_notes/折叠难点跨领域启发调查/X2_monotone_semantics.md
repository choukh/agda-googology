# X2 给非规范表示一个单调的 "意图值": 跨领域可移植的想法 (终止性, 逻辑关系, NbE, 抽象解释, sized types, 模拟, 摊还分析, 证明挖掘)

范围: 本篇不找与我们完全同形的先例, 只收可移植的技术. 每条想法按五项写: (1) 原领域的技术与出处; (2) 对应我们困难的哪一面; (3) 在我们设定里的草图; (4) 最便宜的实验; (5) 与已编译否定结果可能的冲突 (只标出, 不据此排除). 核实档位: [抓取原文] 是本轮用 WebFetch 读到的正文或摘要页; [读首页] 是读了 PDF 的前几页; [检索摘要] 只见检索结果的摘要; [据记忆, 未核] 是我凭已有知识写的, 引用前须核. 草图与实验都是判断, 没有编译过. 文中 `Ref` 指参照树 (参照值), `fold c t` 指以 c 为目标的折叠, `lim f` 指 ℕ-极限, `Lim g` 指 Ω-极限 (g 以低层树为参数). 与已有调查 (R1–R5) 重合的部分只在带来新角度时提及.

## 0. 总览: 排序, 分组与组合

### Takeaway
最有希望的一组 (想法 1–3) 都处理同一件事: 把 "局部落后, 只在外层极限追上" 写成局部可查的义务. 办法是给落后量一个良基的秩或一笔显式的欠账, 或者用一个本身就落后的下估计函数. 第二组 (想法 4–8) 给意图值换形状: 让它依赖上下文, 检查陈述在极限处的半连续性, 只要求弱单调, 或者把语义影子与树粘合在一起并标成无关参数. 其余各条 (9–15) 是补充工具.

### Cited Findings
各条的出处见各节. 排序表 (排序是判断):

| 名次 | 想法 | 原领域 | 对应的面 | 最便宜实验 | 主要风险 |
|---|---|---|---|---|---|
| 1 | 滞后作为良基资源 (WEB 秩 / delayed simulation / transfinite step-indexing 解耦) | 模型检测, 程序逻辑 | 逐步对应被否定, 外层极限才追上 | 在逐步对应的反例上找字面可读的滞后秩 | 秩若要比较值, 撞 `dec→WLPO` 一族 |
| 2 | metering function (下界版的 ranking function), 两段式分解 | 程序下界分析 | "实际 ≥ 意图" 的逐规则证书 | 定义一个与折叠同样落后的下估计 m, 分开证 m ≼ fold 与 Ref ≼ m | Ω 分支的对角规则要求 fold 对下标单调 |
| 3 | 摊还势 / 欠账 (inductive potentials) | 摊还资源分析 | 局部欠账, 外层极限还清 | 逐规则验 Ref ≼ fold + D, 再验极限处的 "还账" 引理 | 加法不交换, 还账在 Ω 极限处要字面公共上界 |
| 4 | context-dependent interpretations + Kripke 世界 | 改写终止性, 逻辑关系 | 意图值依赖外层目标 | 写 V_c(t), 验逐规则与世界扩张单调 | 跨层单调接口已被否定 |
| 5 | 半连续性与可容许性检查表 (Abel) | sized types | 陈述在极限处不保持 | 把已失败引理的前提与结论按半连续性分类 | 基本无; Agda 自带 sized types 不 `--safe` |
| 6 | 弱单调代数, argument filtering, 自然和 | 改写终止性 | V 在每个参数上单调 | 列 "规则 × 参数" 单调表, 看落后是否来自左加法 | 自然和在 Ω 层要并族, 可能造出不合法的 ℕ-序列 |
| 7 | glueing / NbE, 语义分量标成无关参数, Kripke 函数空间 | 正规化证明 | 读回域的原则化, 退化树的 "reflect" | 给现有折叠配 Glued 记录, 看哪些规则需要额外前提 | 若计算依赖语义分量, 撞 `obs→dec` |
| 8 | 抽象解释: 只用 γ, 不动点转移, 局部完备, 下近似逻辑 | 静态分析 | 意图值作为抽象, 只在局部要求精确 | 写每个构造子的 γ 可靠性方块 | 最佳抽象 α 要判定 |
| 9 | 双正交闭包 / 饱和集 CR3 | 逻辑关系 | 退化树按行为进入好集合 | 单层玩具上验常值序列是否进入 Good | 观察者若比较分支, 撞判定一族 |
| 10 | Bezem 强优化 (strong majorizability) | 证明挖掘 | 高层结点作泛函, 分支函数不单调 | 证对角规则保持 ⊑* | 与 Aczel–Danner 重叠; 跨层单调否定 |
| 11 | up-to 技术作为保尺寸函数 | 余归纳证明法 | 候选关系逐步不闭, 闭包后成立 | 验被否定的逐步引理 "up to 传递 + 重排" 是否成立 | ≼ 是归纳的, 要用对偶版本 |
| 12 | chaotic / asynchronous iteration 的调度无关性 | 抽象解释的不动点求解 | 同样的更新换了顺序 | 在反例里查 "更新是否终究都做了" (公平性) | 中间状态上的单调性 |
| 13 | size-change → 全局 ranking function | 终止性 | 由局部约束合成 V 的形状 | 取折叠的调用矩阵推词典序 | 原技术是上界方向 |
| 14 | meaningless terms 的公理化 | 无穷改写 | 退化树一致地取平凡值 | 查已知退化反例是否满足闭包公理 | 只能做关系, 不能按退化与否分情况 |
| 15 | 值作下集, 可数抽象基 | 域论 | sup 是并, 单调是包含 | 选一个可枚举的参照基, 改写下界陈述 | 与 Fairtlough 路径重叠 |

### Inferences
- [判断] 1, 2, 3 是同一个问题的三种记账方式: 1 把落后量放进关系的下标 (秩下降), 2 让意图值自己就落后 (两段式), 3 把落后量写成显式欠账加在输出上. 可以先在同一个反例上并排试这三种, 只需一个单层玩具.
- [判断] 4 与 7 都落到 "按世界索引的语义", 区别在 4 索引的是意图值, 7 把语义整个当成 Kripke 函数空间. 两者都要先核 "跨层单调接口被否定" 那条否定的前提.
- [判断] 5 (半连续性) 是诊断工具, 开销最小, 适合在开任何新行之前先用一次: 它说明一条陈述能否从各项传到极限.
- [判断] 2 与 8 是同一个思路的两种写法: 在下近似 (under-approximation) 的方向上做抽象. 抽象解释给出组合律 (不动点转移, 局部完备), metering 给出逐步检查的形式.

### Gaps
- 排序没有任何编译实验支持; 名次只反映 "与 '局部落后, 外层追上' 这一形状对得多准" 和 "实验有多便宜".

## 想法 1: 滞后作为良基资源 (well-founded bisimulation 的秩, delayed simulation, transfinite step-indexing 的解耦)

### Takeaway
模型检测与程序逻辑里有一类成熟的办法, 专门允许一侧 "暂时跟不上". 要求是每次跟不上时某个良基的秩下降, 于是跟不上只能持续有限步. 这正对着我们 "逐步对应被否定, 只在外层极限追上" 的形状.

### Cited Findings
- **(1) Namjoshi 的 well-founded bisimulation.** 用到良基集的秩函数替代 stuttering bisimulation 里的无穷路径匹配, 于是证明只需匹配单步迁移 — [Namjoshi, A simple characterization of stuttering bisimulation, FSTTCS 1997](https://kedar-namjoshi.github.io/papers/Namjoshi-FSTTCS-1997.pdf), [Springer](https://link.springer.com/doi/10.1007/BFb0058037) [检索摘要; PDF 为扫描件未能抓取]. 后来的转述: 每个状态要么直接走进目标类, 要么在本类内走一步且秩严格下降, 所以不能在本类内无限 "原地踏步" — [Bisimulation Learning, arXiv:2405.15723, Thm 4.1 的改写](https://arxiv.org/html/2405.15723v1) [抓取原文].
- **(1) WEB.** Manolios, Namjoshi, Sumners 定义 well-founded equivalence bisimulation: 保持原子命题的等价关系, 加一个到良基序的秩函数, 用来把定理证明与模型检测接起来 — [CAV 1999, LNCS 1633](https://link.springer.com/content/pdf/10.1007/3-540-48683-6_32.pdf) [检索摘要]; 详细章节见 [Manolios 博士论文 2001](https://www.ccs.neu.edu/~pete/pub/phd-dissertation.pdf) [检索摘要].
- **(1) delayed simulation.** Etessami, Wilke, Schuller 在 Büchi 自动机上引入 delayed simulation: 商掉后保持语言, 而 fair simulation 不保持; 比 direct simulation 约简更多 — [ICALP 2001](https://link.springer.com/doi/10.1007/3-540-48224-5_57); 期刊版 SIAM J. Comput. 34(5):1159–1175 (2005), DOI 10.1137/S0097539703420675 [检索摘要]. 定义细节 (Spoiler 访问接受态后, Duplicator 只须在之后某一时刻访问接受态) [据记忆, 未核].
- **(1) transfinite step-indexing 的解耦.** Svendsen, Sieczkowski, Birkedal 指出: 在通常的 step-indexed 模型里, 逻辑步与具体归约步一一捆绑, 而逻辑步数无法事先限定时这种捆绑出问题. 他们用按词典序比较的超限下标 (第一分量数具体步, 第二分量数下一个具体步之前允许的逻辑步), 使每个具体步之后可以有任意有限多个逻辑步 — [Transfinite Step-Indexing: Decoupling Concrete and Logical Steps, ESOP 2016](https://hal.archives-ouvertes.fr/hal-01408649v1), DOI [10.1007/978-3-662-49498-1_28](https://unpaywall.org/10.1007%2F978-3-662-49498-1_28) [检索摘要; HAL 与 CORE 本轮被拦, 正文未读].
- **(1) Transfinite Iris.** 有限的 step-index 不能验证他们称为 existential property 的性质 (逻辑内外的存在量词能否交换), 换成序数下标后可以验证, 并用于证明终止与保终止的精化 — [Spies, Gäher, Gratzer, Tassarotti, Krebbers, Dreyer, Birkedal, PLDI 2021](https://iris-project.org/transfinite-iris/) [抓取原文]. 同类工作: [Spies, Krishnaswami, Dreyer, Transfinite step-indexing for termination, POPL 2021](https://www.cl.cam.ac.uk/~nk480/transfinite-step-indexing.pdf) [检索摘要].

### Inferences
- **(2) 对应的面.** 逐步对应 "每一步 Ref ≼ fold" 被否定, 而外层极限处成立. 这些文献给的模式是: 不改目标关系, 只给跟不上的一侧一个下降的秩, 单步义务因此仍然是局部的.
- **(3) 草图.** 在 ℕ-极限 `lim f` 上, 把要证的 `Ref (lim f) ≼ fold c (lim f)` 拆成单步义务:
  ```
  -- 滞后秩 d : L, L 良基 (先取 ℕ, 必要时取低层树)
  -- Behind f d n m: "Ref (f n) 将在折叠的第 m 项或其后被追上", 滞后秩为 d
  data Behind (f : ℕ → Tree) : L → ℕ → ℕ → Type where
    sync  : Ref (f n) ≼ fold c (f m)                         → Behind f d n m
    stall : Behind f d' n (suc m) → d' < d                     → Behind f d n m
  -- 主引理: Behind f d n m → Σ m' (Ref (f n) ≼ fold c (f m')), 对 d 作良基归纳
  ```
  `stall` 就是 WEB 的 "原地踏步, 秩下降": 折叠的第 m 项还没追上参照的第 n 项, 义务转给第 m+1 项, 同时滞后秩下降. 最后得 `∀ n → Σ m (Ref (f n) ≼ fold c (f m))`, 正是 ℕ-极限处 ≼ 所要的形状. 词典序 (外层位置, 滞后秩) 对应 Svendsen 等的 (具体步, 逻辑步): "逻辑步" 是参照一侧在一个外层位置内多走的链步或对角步. 要追上的地方若在 Ω-极限, 秩就取低层树, "下一个位置" 改为带字面公共上界证据的更大分支.
- [判断] Transfinite Iris 的 existential property 与我们的量词顺序问题同形: "对每个近似层次都有见证" 与 "有一个对所有层次都行的见证" 不能互推. 如果某条失败的引理要求一致的见证 m, 换成按层次各取一个 m, 再把层次放进超限下标, 可能就够了.
- **(4) 最便宜的实验.** 取逐步对应被否定的那个编译反例, 在它上面逐项算出第 n 项在第几项被追上 (m(n)), 看 m(n) − n 或更一般的 "还差几步" 能否从树的字面结构读出 (例如待走的链步数, 嵌套的对角层数). 能读出, 就在 <实验目录> 用纯 `.agda` 写单层 (只有 ℕ-极限) 的玩具, 证一条 `catch : ∀ n → Ref (f n) ≼ fold c (f (n + L (f n)))`, L 按结构递归.
- **(5) 可能的冲突.** (a) 秩若要靠比较 Ref 与 fold 的值来算, 就是判定 ≼, 撞 `dec→WLPO`, `Trich₂→WLPO` 一族; 秩必须字面可读. (b) `strict→LPO`: `stall` 允许不前进, 不要求严格递增, 方向上相容. (c) 秩取低层树时, "下一个位置" 若要求比较两个分支, 撞 `noBT` 与全分支比较的禁令; 要带字面公共上界. (d) V64 (链步引理被退化反例否定): 退化的常值序列也许滞后无界, 需要先查它是否在读回域内.

### Gaps
- Namjoshi 原文是扫描件, 定义的精确条款没有逐字核. Svendsen 等的正文没有读到, 词典序的具体顺序取自检索摘要.
- delayed simulation 的定义细节凭记忆.

## 想法 2: metering function, 即下界版的 ranking function, 与 "两段式" 分解

### Takeaway
程序分析里有与 ranking function 对偶的 metering function: 它低估循环次数, 条件是每步至多降 1, 守卫不成立时 ≤ 0. 下估计可以很粗 (½x 也行). 移到我们这里: 先造一个本身就和折叠同样局部落后的下估计 m, 证 m ≼ fold; 外层极限处 m 追上 Ref, 这是只涉及参照一侧的另一条引理.

### Cited Findings
- **(1) 定义.** 对带更新 μ 的简单循环, 表达式 b 是 metering function, 若 (i) 守卫不成立时 b ≤ 0; (ii) 守卫成立时 bμ ≥ b − 1. 定理: bσ ≥ 0 时循环至少可执行 ⌈bσ⌉ 次. 与 ranking function (守卫成立时 b > 0 且 bμ ≤ b − 1, 是高估) 对偶; 例: ½x 是 metering function 但不是 ranking function, x² 反之 — [Frohn, Naaf, Brockschmidt, Giesl, Inferring Lower Runtime Bounds for Integer Programs, TOPLAS (arXiv:1911.01077), Def. 3.1–3.2, Thm 3.3](https://ar5iv.labs.arxiv.org/html/1911.01077) [抓取原文].
- **(1) conditional metering function.** 守卫为 φ ∧ ψ 且 ψ 在一次迭代后恒成立时, ⟦ψ⟧·b (ψ 的特征函数乘 b) 是 metering function, 条件是 ¬φ ∧ ψ ⇒ b ≤ 0, φ ∧ ψ ⇒ bμ ≥ b − 1 — [同上, Thm 3.4](https://ar5iv.labs.arxiv.org/html/1911.01077) [抓取原文]. 首发于 IJCAR 2016 — [MSR 页](https://www.microsoft.com/en-us/research/?p=238181) [检索摘要].

### Inferences
- **(2) 对应的面.** 直接针对 "证实际结果 ≥ 意图值": 下估计只需逐规则验一个不等式, 并且可以粗.
- **(3) 草图.** 去掉减法, 改成前向形式, 让 m 满足折叠的方程的 "下解" 条件:
  ```
  (M0)   m zero ≼ fold c zero
  (Msuc) m (suc x) ≼ F (m x)        -- 若 fold c (suc x) 展开为 F (fold c x), F 对 ≼ 单调
  (Mlim) m (lim f) ≼ lim (m ∘ f)     -- m 按结构递归定义时自动成立
  (MΩ)   按低于 / 同层 / 高于目标三种情形各一条
  定理 A: m t ≼ fold c t             (对 t 归纳, 一切树)
  定理 B: Ref t ≼ m t                (只对读回域, 或只在外层极限)
  ```
  关键在 m 的选法: 让 m 与折叠同样落后, 例如在 ℕ-极限内部用 `Ref (f n)` 的 "晚一站" 版本, 使 A 逐规则成立. 落后带来的差额全部挪到 B. B 只涉及参照系统自身 (去掉序列的有限前段不改变上确界), 与折叠无关. conditional 版对应: ψ 是读回域的证据, m 只定义在 Σ (t : Tree) (证据 t) 上, 读回域之外不需要值, 不需要判定 "是否退化".
- [判断] 这是把 "意图值单调" 的要求从 Ref 转移到一个专门构造的 m 上: Ref 不必逐规则单调, m 才须如此.
- **(4) 最便宜的实验.** 对 BTBO 档 (已有无前提下界的那一档) 的折叠写 m, 分别证 A 与 B; 看 A 的四条义务里哪一条非要读回域证据不可. 只需一个文件, 不动定义.
- **(5) 可能的冲突.** (a) 同层对角规则 (输出回灌作下标) 里, (MΩ) 需要 fold 对下标单调; 对非规范下标若不成立, 与 `no-carry-Ω₂` 一类否定同区, 要限到读回域. (b) 定理 B 若需要 "Ref 的序列严格递增", 撞 `strict→LPO`; 应只用 "去掉有限前段" 这种字面操作.

### Gaps
- metering function 原文是整数程序, 没有超限版本; 超限化是本篇的判断.

## 想法 3: 摊还势与欠账 (potential method, inductive potentials)

### Takeaway
摊还分析允许某一步实际开销超过预算, 前提是差额记在数据结构携带的势里, 以后再还. 资源分析把势挂在数据类型的构造子上, 逐条规则验局部不等式. 移到我们这里: 允许 fold 在内部欠一笔字面写出的账 D, 在外层极限处证明 "账被后面的项还清".

### Cited Findings
- **(1) 带势的类型.** Hoffmann 与 Hofmann 把势方法从线性推广到多项式界, 推导产生线性约束 (RaML 一系); 非负的势为代价高的操作付账 — [Hoffmann, Hofmann, Amortized resource analysis with polynomial potential, ESOP 2010, 扩展版](https://www.cs.yale.edu/homes/hoffmann/papers/aapoly_extended.pdf) [检索摘要]; 博士论文 *Types with Potential* (2011) 说类型上标注多元资源多项式 — [论文](https://www.cs.yale.edu/homes/hoffmann/papers/hoffmann11diss.pdf) [检索摘要]. 线性界的前身是 Hofmann 与 Jost (POPL 2003) [检索摘要中提及, 原文未开].
- **(1) inductive potentials.** 用户可在数据结构声明上标注势在类型内部怎样分配, 允许非均匀分配 — [Knoth, Reynolds, Wang, Hoffmann, Polikarpova, Liquid Resource Types](https://cseweb.ucsd.edu/%7Enpolikarpova/publications/lrt.pdf) [检索摘要; 会议与年份未核, 记作 ICFP 2020 待核].
- **(1) 势方法本身.** Tarjan, Amortized computational complexity, SIAM J. Algebraic Discrete Methods 6(2) (1985) [据记忆, 未核].

### Inferences
- **(2) 对应的面.** "局部落后" 就是局部欠账, "外层追上" 就是还账. 势方法把它变成逐规则的局部义务加一条还账引理.
- **(3) 草图.**
  ```
  D : Tree → Tree                          -- 欠账, 按构造子结构递归给出 (inductive potential)
  (不变量)   Ref t ≼ fold c t + D t           -- 欠账放右边, 左加法会吞掉它 (1 + ω = ω), 右边不会
  (还账)     fold c (f n) + D (f n) ≼ fold c (f m)   对某个字面给出的 m
  (清账)     D (lim f) = zero
  ⇒ Ref (lim f) ≼ fold c (lim f)
  ```
  欠账只允许出现在内部, 到外层 ℕ-极限清零. 在 Ω-极限处, "后面的项" 换成带字面公共上界证据的更大分支. 势挂在构造子上: 例如链步结点欠一个后继, 对角结点欠一次迭代, 用 inductive potential 式的按构造子标注写 D.
- [判断] 与想法 2 的分工: 想法 2 把差额挪进参照一侧, 这里把差额显式写成树. D 可以直接读作 "这一站差多少", 也就是翻译账里 "树的基本列与记号的差" 的一种编译形式.
- **(4) 最便宜的实验.** 在逐步对应的反例上, 把每处缺的部分写成字面的 D, 分两步验: 先验逐规则不变量, 再验还账引理. 如果还账引理的 m 能写成 n 加一个常数, 这个常数就是想法 1 的滞后秩.
- **(5) 可能的冲突.** (a) 序数没有减法, D 不能定义成 "Ref 减 fold"; 必须字面构造, 否则就要比较值. (b) 加法不交换: D 若放左边 (D + fold), 在 fold 是加法主数时被吸收, 不变量退回到 Ref ≼ fold, 什么也没放宽; 要防这一点. (c) Ω-极限处还账需要比较分支, 必须带公共上界证据 (见 AGENTS "律带公共上界").

### Gaps
- 没有找到超限 (序数值) 的势方法文献; 本节的超限化是判断.

## 想法 4: context-dependent interpretations 与 Kripke 世界: 意图值依赖外层目标

### Takeaway
改写终止性里, Hofbauer 的 context-dependent interpretations 让项的解释带一个来自上下文的参数, 普通单调解释证不出或界太松的系统由此能证. 逻辑关系与 NbE 里, 语义按 "世界" 索引, 并要求沿世界扩张单调 (Kripke 单调). 移到我们这里: 意图值写成 V_c(t), c 是外层目标, 规则按目标变换上下文.

### Cited Findings
- **(1) 出处.** Hofbauer, Termination Proofs by Context-Dependent Interpretations, RTA 2001, LNCS 2051, pp.108–121 — [Springer](https://link.springer.com/doi/10.1007/3-540-45127-7_10) [检索摘要]. 它是在自然数解释之上扩展的语义终止方法 [检索摘要]. Moser 与 Schnabl 给出两个子类, 证明诱导的 derivational complexity 有紧的上界 (其一为二次), 并给机械化算法 — [RTA 2008](https://rd.springer.com/chapter/10.1007/978-3-540-70590-1_19) [检索摘要]. 定义的具体形状 (解释 [t]_Δ 带正实参数 Δ, f(t) 的解释用 [t] 在变换后的参数下的值) [据记忆, 未核].
- **(1) Kripke 逻辑关系.** Pitts 与 Stark 的逻辑关系按状态间关系索引, 并且同时关联求值上下文与表达式, 才得到含局部状态与递归时的基本性质 — [Operational Reasoning for Functions with Local State, 1998](https://homepages.inf.ed.ac.uk/stark/operfl.html) [检索摘要]. Dreyer, Neis, Birkedal 构造 step-indexed Kripke 逻辑关系 — [ICFP 论文](https://people.mpi-sws.org/%7Edreyer/papers/stslr/icfp.pdf) [检索摘要]. Kripke 逻辑关系的起源 (Plotkin 1980; Jung–Tiuryn 1993) [据记忆, 未核].

### Inferences
- **(2) 对应的面.** 带挂起上下文的结点 (保留, 链) 的值依赖外层目标, 所以 "树 → 值" 的单一函数 V 不存在或不单调. 把上下文提为参数, 单调性只要求在固定上下文下, 再加上上下文之间的 Kripke 单调.
- **(3) 草图.**
  ```
  V : (c : 目标) → Tree → Tree
  逐规则:  V c (该构造子的树) ≼ 用 V c' (各部分) 拼出的值,  c' 由规则给出
           (低于目标: c' = c;  同层对角: c' 取输出;  高于目标走链: c' 为链的下一站)
  Kripke:  e : c ⊑ₗ c'  (字面的世界扩张证据, 如 wk 或公共上界)  →  V c t ≼ V c' t
  主定理:  ∀ c → V c t ≼ fold c t
  ```
  世界序只用字面扩张证据, 不做比较.
- **(4) 最便宜的实验.** 找出值依赖外层目标的那类结点 (台账里的 framed keep 一类), 只给它写 V_c, 其余构造子沿用现有意图值, 看逐规则不等式与 Kripke 单调是否同时成立.
- **(5) 可能的冲突.** 强烈标注: 记忆中 "跨层单调接口被否定 (对 dl 矛盾, 对任意 D 推出 LPO), 根源是位置摊平". Kripke 单调是一种跨世界单调. 必须核: 被否定的接口量化的是任意 D, 还是字面扩张; 若世界扩张只取 `wk` 这类字面映射, 也许不在否定的前提内. 未核, 不作结论.

### Gaps
- Hofbauer 原文未读, 定义形状凭记忆; 引用前须核 [Springer 页](https://link.springer.com/doi/10.1007/3-540-45127-7_10) 或 Schnabl 2007 硕士论文.

## 想法 5: 半连续性与可容许性 (Abel 的 sized types): 先判断一条陈述能否传到极限

### Takeaway
Abel 证明: 按序数尺寸索引的类型 A(α) 在极限处上半连续时, 对它做递归是可靠的. 他还给出一套组合规则: 函数类型要求定义域下半连续, 值域上半连续; 单调的上半连续, 反单调的下半连续; ∀ 保持上半连续. 这是一张现成的检查表, 可以先拿来判断一条引理的陈述能不能从各项传到极限.

### Cited Findings
- **(1) 定义.** 对从序数到格的 f 与极限 λ: lim inf_{α→λ} f(α) := sup_{α₀<λ} inf_{α₀≤α<λ} f(α), lim sup 对偶; 上半连续: lim sup f ⊑ f(λ); 下半连续: f(λ) ⊑ lim inf f — [Abel, Semi-continuous Sized Types and Termination, LMCS 4(2:3) 2008](https://lmcs.episciences.org/1236), [arXiv:0804.0876](https://ar5iv.labs.arxiv.org/html/0804.0876) [抓取原文].
- **(1) 可容许性.** 对 μ 的情形, A(α) 可容许, 若形状合格, α = 0 时归纳部分为空, 且每个极限 λ 上 inf_{α<λ} A(α) ⊆ A(λ) [抓取原文, 同上].
- **(1) 组合规则.** Prop. 6: A 下半连续且 B 上半连续 ⇒ A→B 上半连续; 单调函数上半连续, 反单调函数下半连续; 归纳类型 μ^α F 下半连续, 余归纳类型上半连续; lim sup 穿过下确界, 所以 ∀ 保持上半连续 (Lemma 7) [抓取原文, 同上].
- **(1) 反例.** A(ı) = (Nat^ω → Nat^ı) → Nat^ω 通过 α = 0 检查但不上半连续, 用 succ, pred 与一个移位函数可写出不终止的循环 [抓取原文, 同上].

### Inferences
- **(2) 对应的面.** "每一项都不成立, 极限处成立" 与 "每一项都成立, 极限处不成立" 都是陈述在极限处的连续性问题. 先判定陈述形状属于哪一类, 再决定把它放在哪一层证.
- **(3) 草图.** 把 Abel 的定义翻成命题格 (ℕ-序列): lim inf_n P(n) 读作 "从某项起恒成立", lim sup_n P(n) 读作 "无穷多项成立" (这是对 Abel 一般定义的特化, 是推导, 不是引文). ℕ-极限结点上:
  - 结论形如 `Ref x ≼ fold c x` 时, 要它上半连续, 需要 Ref 在 `lim` 处等于各项之上确界, fold 在 `lim` 处不低于各项之上确界. 局部落后时 P(f n) 本身不成立, 所以应把陈述换成本身上半连续的 `∀ n → Σ m (Ref (f n) ≼ fold c (f m))`.
  - 前提 (如 "下标合法", "有公共上界") 要下半连续: 在极限处成立能推出从某项起成立. 否则就是 Abel 反例的形状: 尺寸变量出现在全尺寸对象的反变位置.
- [判断] Abel 的反例 (Nat^ω → Nat^ı) → Nat^ω 对应一类引理: 前提对低层的一切树量化 (全尺寸), 结论只说当前站, 而当前站变量出现在前提的反变位置. 退化反例 (`no-start-all`, `no-K2′`, V64) 是否都利用了这种形状, 值得逐条核.
- **(4) 最便宜的实验.** 纸面: 把近期失败的引理的前提与结论逐个标成 "单调 / 反单调 / 上半连续 / 下半连续", 看反例是否都出在 "前提不下半连续" 的位置. 不需要编译.
- **(5) 可能的冲突.** 与已有否定无直接冲突. 注意: Agda 自带的 sized types 与 `--safe` 不兼容 [据记忆, 未核], 所以只借检查表, 不借 `Size` 类型; 尺寸用树自身的下标表示.

### Gaps
- 抓取只覆盖到全文前一半, 和类型, 存在类型等的规则在第 6 节, 未读.

## 想法 6: 弱单调代数, argument filtering, 序数解释与自然和 (改写终止性)

### Takeaway
终止证明里的单调代数分弱 (≥) 与强 (>) 两种序. 很多方法只要求解释对 ≥ 单调, 并且可以丢掉某些参数位置. 序数解释的老问题是普通加法在左参数上只弱单调, 所以终止证明常改用自然和 (Hessenberg sum). 我们只要下界, 只需要弱定向, 可选的意图值因此多得多. 局部落后可能只是左加法不严格的表现.

### Cited Findings
- **(1) 弱单调代数.** 弱单调代数要求一个良基序, 各函数符号的解释只需对非严格序单调; 若还对 > 单调, 称 extended monotone. 弱单调允许多项式解释取 0 系数 — [Endrullis, Waldmann, Zantema, Matrix Interpretations for Proving Termination of Term Rewriting, JAR 40:195–220 (2008)](https://portal.mardi4nfdi.de/wiki/Publication:928655) [检索摘要].
- **(1) 只在可用位置要求严格.** μ-monotone algebra 只在可用参数位置 μ(f) 上要求严格单调 — [Hirokawa, Moser, Automated Complexity Analysis Based on the Dependency Pair Method, arXiv:1102.3129](https://ar5iv.arxiv.org/html/1102.3129) [抓取原文].
- **(1) 序数解释的自动化.** 新的序数解释实现自动证明了 Goodstein 序列的改写系统终止 — [Winkler, Zankl, Middeldorp, Beyond Peano Arithmetic, RTA 2013](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.RTA.2013.335); 期刊版 [JSC 2015](https://portal.mardi4nfdi.de/wiki/Publication:485843) [检索摘要]. 据检索摘要, 文中要求加法, 自然加法, 乘法, 指数在两个参数上都弱单调, 并用自然加法 (交换) [检索摘要].
- **(1) Hydra.** Dershowitz 与 Moser 把 Hercules 与 Hydra 之战写成改写系统与 while 程序, 并证终止 — [The Hydra Battle Revisited (2007)](https://www.cs.tau.ac.il/~nachum/papers/LNCS/Hydra.pdf) [读首页]. Cichon 1991 问: Hydra 系统的终止序是否必须以 Howard 序数为序型; Moser 2009 给了否定回答 — [RTALooP Problem 23](https://www.cs.tau.ac.il/~nachum/rtaloop/problems/23.html) [检索摘要].
- **(1) 高阶版.** Gandy 把项解释为严格单调泛函以证强正规化 — Gandy, Proofs of strong normalization, 收于 *To H.B. Curry* (1980) pp.457–477 [二手转述]; van de Pol 的博士论文有一章讲弱单调与严格泛函 — [Termination of Higher-order Rewrite Systems (1996)](https://www.cs.au.dk/~jaco/papers/thesis.pdf) [检索摘要]; [van de Pol, Schwichtenberg, Strict functionals for termination proofs, TLCA 1995, LNCS 902](https://dblp1.uni-trier.de/rec/conf/tlca/PolS95.html) [检索摘要]. 改用非严格单调泛函的变体见 [arXiv:2211.13140](https://arxiv.org/pdf/2211.13140) [检索摘要].

### Inferences
- **(2) 对应的面.** 意图值 V 要沿每条规则单调. 终止性文献把这件事拆成三个可以分别调的旋钮: 每个参数位置上是弱单调还是强单调; 哪些位置可以过滤掉; 用哪种算术 (普通 + 还是 ⊕).
- **(3) 草图.**
  - 下界只要弱定向: 每条规则 `V (左) ≼ V (右)`. 不需要严格.
  - argument filtering: V 可以不看某些字段 (脚手架, 框住的上下文). 这把 "新增脚手架是序数值需要的, 还是翻译带来的" 变成一个可检查的问题: 被过滤掉的字段就不是值所需要的.
  - 自然和: 若某条规则的落后来自 `α + β` 中 α 变动 (左参数), 在意图值一侧改用 `α ⊕ β`, 再另证 `α + β ≼ α ⊕ β`. 布劳威尔树上的自然和本轮没有找到现成定义 (下见 Gaps). 一个候选写法是两参数同时递归:
    ```
    lim f ⊕ lim g = lim (交错 (λ n → f n ⊕ lim g) (λ n → lim f ⊕ g n))
    ```
    每次调用都有一个参数结构下降, Agda 的调用矩阵检查大概能接受 [判断]. 注意 `lim (λ n → f n ⊕ g n)` 是错的: ω ⊕ ω 会算成 ω.
  - 高阶: Ω-结点的意图值写成弱单调泛函 (van de Pol 的 weakly monotonic functionals), 而不是一棵树.
- **(4) 最便宜的实验.** 纸面上列一张 "规则 × 参数位置" 的单调表, 标出现有意图值在哪个位置上不单调; 若不单调全都出在左加法, 自然和就是候选.
- **(5) 可能的冲突.** (a) 自然和在 Ω 层要把 Ω-族与 ℕ-族并起来, 交错出的 ℕ-序列不单调, 可能违反 ℕ-极限的合法性 (相邻项按合法性步进); 自然和若只用在意图值 (证明一侧) 而不进树, 这条约束可能不适用, 须核. (b) 用了自然和以后, 要另证 `+ ≼ ⊕`, 这在布劳威尔树上需要自己证. (c) 与 Aczel–Danner 的 hereditarily inflationary 泛函 (已有调查) 相邻; 新角度是 "规则定向 + 弱/强之分 + 过滤".

### Gaps
- 布劳威尔树上的自然和: 检索只找到 Cantor 范式上的经典定义 ([Some transfinite natural sums, arXiv:1509.04078](https://ar5iv.arxiv.org/html/1509.04078)) 与 KNFX 的算术一节 ([arXiv:2208.03844](https://arxiv.org/abs/2208.03844), 是否含自然和未核).
- Hydra 论文正文 (第 8 节的终止证明) 未读.

## 想法 7: glueing / NbE: 语义影子与树粘在一起, 语义分量标成无关参数, Ω 分支取 Kripke 函数空间

### Takeaway
NbE 把正规化写成 "解释到模型再读回 (quote)", glueing 把语法与语义配对. Coquand 与 Dybjer 指出这个方法能推广到布劳威尔序数这样的超限归纳类型. 移到我们这里: 每棵树带一个语义影子 (参照值的下界) 与证明, 影子标成无关参数, 折叠的计算看不到它. 读回域就是读回函数的像. 退化树按 NbE 处理 neutral 项的办法 "reflect", 带一个平凡的影子.

### Cited Findings
- **(1) NbE 与 glueing.** Coquand, Dybjer 不用归约关系, 直接研究正规化函数: 造一个合适的模型和一个 quote 函数, 正规化 = quote ∘ 解释; 用范畴论的 glueing 给组合子形式的 Gödel T 一个正规化算法; 方法可推广到积, 不交并以及布劳威尔序数等超限归纳类型 — [Intuitionistic model constructions and normalization proofs, MSCS 7 (1997) 75–94](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/intuitionistic-model-constructions-and-normalization-proofs/15AE4B790FF9E4B1998CE92054DBD3CF) [检索摘要].
- **(1) proof-relevant Tait 与 Artin glueing.** Coquand 2021 在项模型与预层模型之间做 Artin glueing, 被描述为 Tait 可计算性论证的证明相关版本 — [arXiv:2103.04287](https://ar5iv.labs.arxiv.org/html/2103.04287) [检索摘要].
- **(1) 综合 Tait 可计算性 (STC).** 把逻辑关系当作原语类型, 在 Artin glueing 构造的 topos 的内语言里构造逻辑关系 — [Sterling, Harper, Logical Relations as Types, arXiv:2010.08599](https://arxiv.org/pdf/2010.08599); [nLab](https://ncatlab.org/nlab/show/synthetic+Tait+computability) [检索摘要].
- **(1) 读回与 neutral.** NbE 的语义域含 neutral 值 (卡住的项), 由 reflect 嵌入, 再由 reify 读回 (Berger–Schwichtenberg 1991) [据记忆, 未核].

### Inferences
- **(2) 对应的面.** 给 "读回域" 一个原则化的定义 (读回函数的像), 并给 "退化树要不要有意图值" 一个现成答案: 有, 是平凡的那个. 判定不需要, 因为 reflect 对一切项都有定义.
- **(3) 草图.**
  ```
  record Glued : Type where
    tree : Tree
    ref  : Tree                 -- 语义影子: 参照值的下界
    .lb  : ref ≼ fold c tree     -- 无关参数 (AGENTS 允许)
  foldᴳ : Glued → Glued          -- tree 分量照常折叠, ref 分量用参照运算, lb 由逐规则引理给出
  reflect : Tree → Glued         -- 退化或未知的树: ref := 平凡下界 (如 zero 或字面下界)
  quote   : 读回域 → Glued       -- 规范构造: ref := Ref t
  ```
  STC 的纪律对应: 树一侧的计算不能依赖 ref 与 lb, 也就是 "开模态 / 闭模态" 的分离. Kripke 函数空间对应: Ω-结点的语义分量取 `∀ c' (字面扩张 c ⊑ₗ c') → ⟦低层⟧ c' → ⟦·⟧ c'`, 这样它沿 `wk` 稳定. NbE 用同样的结构让语义函数在弱化下稳定.
- **(4) 最便宜的实验.** 给现有折叠配一个 `Glued`, lb 用现有的逐规则引理填; 凡是填不进去、要额外前提的规则, 就是读回域必须收窄的地方. 这同时是一份 "哪些规则依赖读回域" 的清单.
- **(5) 可能的冲突.** (a) 若折叠的计算要查看 ref 才能决定分支, 就撞 `obs→dec` 一族 (`branch→wdec` 等); 无关参数在类型层面防止这一点. (b) Kripke 函数空间量化一切扩张, 本身不判定; 但若要求它对任意 D 稳定, 可能落入 "跨层单调接口被否定" 的前提, 须核.

### Gaps
- Coquand–Dybjer 正文 (付费) 未读, 推广到布劳威尔序数的具体做法未核.

## 想法 8: 抽象解释: 只用 γ, 不动点转移, 局部完备, 下近似逻辑

### Takeaway
把意图值看作从树到参照序数的抽象, 可靠性只需逐步的 "松弛交换方块". 有三点可用: 只用具体化 γ (无需判定, 是上集) 的框架; 局部完备, 即精确性只在给定输入上要求; 下近似逻辑 (Incorrectness Logic), 它关心 "这些结果确实达得到", 正是下界方向. Urban 与 Miné 已经有序数值的抽象域.

### Cited Findings
- **(1) 终止性的抽象解释框架.** 基于迹的终止收集语义有不动点定义, 抽象它得到 "最好的变元函数" (best variant function) 的不动点定义, 再抽象得到 Floyd/Turing 方法与新的静态分析; 还引入基于 inductive trace cover 的语义结构归纳 — [Cousot, Cousot, An Abstract Interpretation Framework for Termination, POPL 2012, pp.245–258](https://cs.nyu.edu/~pmc309/COUSOTpapers/POPL12.shtml) [抓取原文 (摘要页)].
- **(1) 序数值的 ranking function 抽象域.** 自然数值的 ranking function 在无界非确定性下不够; 他们把分段 ranking function 推广到以自然数值函数为系数的 ω-多项式, 用后向不变分析推断, 自称是第一个能推理序数的抽象域 — [Urban, Miné, ESOP 2014, LNCS 8410, pp.412–431](https://www-apr.lip6.fr/%7Emine/publi/article-urban-mine-esop14.pdf) [检索摘要]; 工具 [FuncTion](https://github.com/caterinaurban/function) [检索摘要].
- **(1) 局部完备.** 抽象解释的完备性只需对给定的输入集合成立; 逻辑 LCL_A 混合上近似与下近似, 可证三元组的后条件是最强后条件的下近似; A 取最粗抽象时退化为 O'Hearn 的 incorrectness logic — [Bruni, Giacobazzi, Gori, Ranzato, A Logic for Locally Complete Abstract Interpretations, LICS 2021](https://research.unipd.it/bitstream/11577/3400197/1/cameraready.pdf) [检索摘要].
- **(1) 下近似逻辑.** 三元组 [P] c [Q] 成立当且仅当 Q 中每个状态都能从 P 中某状态经 c 达到; 循环的处理以展开规则与 "backwards variant" 规则为主, 循环不变式作用较小 — [O'Hearn, Incorrectness Logic, POPL 2020](https://discovery.ucl.ac.uk/10095439/1/IL.pdf) [检索摘要; 循环规则的精确形状未读].
- **(1) 超限迭代.** Cousot 与 Cousot, Constructive versions of Tarski's fixed point theorems, Pacific J. Math. 82(1) (1979) — [msp.org](https://msp.org/pjm/1979/82-1/p04.xhtml) [仅见检索结果中的条目, 未打开].

### Inferences
- **(2) 对应的面.** 意图值不必是 "最佳抽象" (那要判定), 只需逐规则的松弛方块成立; 精确性 (Ref 等于值) 只在读回域上要求, 这正是局部完备.
- **(3) 草图.**
  - 只用 γ: `γ r := λ t → r ≼ fold c t` (树的上集, 不需判定). 逐构造子的可靠性: 各部分 ∈ γ(r_i) ⇒ 结点 ∈ γ(F♯(r_i)), F♯ 是参照运算. 这与 "意图值沿规则单调" 是同一个义务, 但写成集合包含以后, 可以直接用抽象解释的组合定理 (序列复合, 不动点转移).
  - 局部完备: 读回域 P 要对折叠的递归调用封闭, LCL 的规则正好管 "局部完备性沿程序结构传播". 读回域的封闭条件可照 LCL 的规则写.
  - 下近似的循环规则: 极限处的下界是 "存在某一站达到" (∃ n), 与 ≼ 在 ℕ-极限处的 ∀∃ 一致. IL 的 backwards variant 规则可当作 ℕ-极限下界的模板.
- **(4) 最便宜的实验.** 对最简单的单层折叠写出 γ 的逐构造子方块, 看哪些方块只在某个输入集合上成立, 把这个集合记下来, 与现有读回域比较.
- **(5) 可能的冲突.** Galois 连接里的 α (最佳抽象) 需要下确界或判定, 不能用; 只用 γ 的框架没有这个问题. 不动点转移若要求 α 保持上确界, Ω-极限处的上确界要按结构给出, 不经比较.

### Gaps
- Cousot 1992 的 "只用 γ 的框架" (Abstract interpretation frameworks, JLC 1992) 本轮未检索核实 [据记忆].
- IL 循环规则的原文没有读到.

## 想法 9: 双正交闭包与饱和集 (CR3): 退化树按行为进入 "好集合"

### Takeaway
Tait/Girard 的可约性候选用三条闭包条件定义 "好项", 其中 CR3 让 neutral 项凭它的一步归约结果进入, 不需要先判断它是什么. 双正交 (⊤⊤) 闭包把类型解释为 "对一切通过规范项检验的观察者都通过" 的项. 移到我们这里: 退化树按它在观察者面前的表现进入好集合.

### Cited Findings
- **(1) 双正交.** Melliès 与 Vouillon 从无类型的项与上下文出发, 把类型解释为在双正交下封闭的项集, 主结果是递归类型由收敛的区间类型序列逼近 — [Recursive Polymorphic Types and Parametricity in an Operational Framework, LICS 2005, pp.82–91](https://www.irif.fr/~vouillon/publi/recursivetypes.pdf) [检索摘要].
- **(1) 同时关联上下文.** Pitts–Stark 的逻辑关系同时关联求值上下文与表达式 — [1998](https://homepages.inf.ed.ac.uk/stark/operfl.html) [检索摘要]; 双正交与 step-indexing 的结合见 Dreyer, Neis, Birkedal 的 [ICFP 论文](https://people.mpi-sws.org/%7Edreyer/papers/stslr/icfp.pdf) 与 Benton–Hur ICFP 2009 [检索摘要中提及].
- **(1) CR1–CR3.** Girard, Lafont, Taylor, *Proofs and Types* (1989) 第 6 章 [据记忆, 未核].

### Inferences
- **(2) 对应的面.** "非规范树到处都是, 不能靠收窄定义域排除": 双正交与 CR3 的好集合不靠语法分类, 只靠行为.
- **(3) 草图.**
  ```
  观察者 E : 目标 c, 参照下界 r, 外层折叠上下文
  t ⊥ E  :=  r_E ≼ E[fold c t]
  Canon  := 读回域的生成元
  Good   := (Canon^⊥)^⊥          -- 通过一切 "规范树都通过的观察者" 的树
  CR3 式:  常值序列 lim (λ _ → s) ∈ Good ⇐ s ∈ Good;  Ω-结点各分支 ∈ Good ⇒ 结点 ∈ Good
  基本引理: 折叠的每条规则保持 Good (观察者对折叠的上下文封闭)
  ```
  好处是 Good 的成员资格不需要判定, 退化树只要表现与规范树一样就在里面.
- **(4) 最便宜的实验.** 单层玩具 (只有 ℕ-极限) 上按 CR 条件定义 Good, 看常值序列与已知退化反例 (`no-start-all`, `no-K2′` 里的反例对象) 是否进入 Good. 若进入, 就说明这些否定读作 "谓词太宽" 时可以换成 Good.
- **(5) 可能的冲突.** (a) 对一切观察者量化是大量化, 要升宇宙, Agda 中可行. (b) 观察者若比较两个分支, 撞 `full→dec`, `dec→WLPO`; 观察者只能是字面上下文. (c) 双正交闭包可能过大: 观察者太弱时会把值偏低的树也收进来, 观察者集合的选取决定成败.

### Gaps
- 没有找到在序数值关系上用双正交的文献; 本节的移植是判断.

## 想法 10: Bezem 的强优化 (strong majorizability): 高层结点作泛函, 不要求分支函数单调

### Takeaway
Howard 的优化关系与 Bezem 的强优化给一切有限型泛函 (包括不连续的) 配上单调的上界; Bezem 的版本让每个强优化子都优化自身, 单调性因此内建在关系里. Kohlenbach 的单调泛函解释用它在证明里只追踪界, 不追踪精确的见证. 移到我们这里: 对 Ω-结点用 Bezem 式的关系比较, 只在 "较小参数对较大参数" 上比较, 不要求被比较的分支函数单调.

### Cited Findings
- **(1)** Howard 引入 majorizability, Bezem 推广为 strong majorizability; 强优化泛函构成 Spector bar recursion 演算的模型, 尽管其中含不连续泛函; 每个强优化子都优化自身; Kohlenbach 研究的逐点变体有相同的可优化泛函 — [Kohlenbach 关于逐点优化的论文 (point.pdf)](https://www2.mathematik.tu-darmstadt.de/~kohlenbach/point.pdf) [检索摘要; 标题与出版信息未核]; [Ferreira 等的相关论文](https://webpages.ciencias.ulisboa.pt/~fjferreira/nonstandardness.pdf) 说: 语言的每个闭项都有优化子, 可在 E-PAω 中证 (Howard) [检索摘要].
- **(1)** 单调泛函解释与单调修正可实现性都依赖 Howard–Bezem 的优化关系 — [Proof interpretations and majorizability, Logic Colloquium 2007 (CUP)](https://www.cambridge.org/core/books/logic-colloquium-2007/proof-interpretations-and-majorizability/2FC03749E11297163C73D54BCF66862D) [检索摘要; 作者未核].

### Inferences
- **(2) 对应的面.** Ω-结点的分支函数 g (以低层树为参数) 在非规范输入上不单调; 要比较两个这样的结点, 又不能比较分支.
- **(3) 草图.**
  ```
  r ⊑* t  (t 遗传地支配 r), 按结构递归:
    Lim h ⊑* Lim g  :=  ∀ c c' → (c' ≼ c) → h c' ⊑* g c     -- Bezem 式: 在较小参数上比较
  强版本还要求 g 自支配:  c' ≼ c → g c' ⊑* g c
  ```
  前提 c' ≼ c 是作为证明交进来的, 不是判定出来的. Howard 的定理 "每个闭项都有优化子" 对应 "每个由折叠生成的树都有一个按结构构造的参照下界", 下界随构造给出, 不取单调包络 (包络 sup_{c' ≼ c} g c' 不是布劳威尔树能表示的上确界).
- **(4) 最便宜的实验.** 只看同层对角规则 (输出回灌作下标): 证它保持 ⊑*. Bezem 式的子句正是让 "下标变大, 输出不降" 进入关系的地方.
- **(5) 可能的冲突.** (a) 与已有调查中的 Aczel–Danner hereditarily inflationary 泛函相邻; 新角度是 Bezem 的 "自支配" 与 "模型容纳不连续对象". (b) 这是一种跨层单调, 须对照 "跨层单调接口被否定" 的前提. (c) 若 c' ≼ c 只能靠比较得到, 撞 `Trich₂→WLPO`; 必须由字面公共上界给出.

### Gaps
- Bezem 1985 (JSL 50) 原文未读; 本节的定义形状凭检索摘要与记忆.

## 想法 11: up-to 技术作为保尺寸函数

### Takeaway
余归纳证明里, 候选关系常常不是逐步封闭的 (不是模拟), 但在某个闭包算子下封闭 (up to 传递, up to 上下文); companion 理论说明这些闭包何时可靠. Danielsson 把许多 up-to 技术写成 sized types 下的保尺寸函数, 代码是 Agda. 移到我们这里: 被否定的逐步引理也许在 "up to ≼ 传递与序列重排" 下成立.

### Cited Findings
- **(1)** Pous 给任意单调函数配一个 companion, 重新叙述 Knaster–Tarski 与 up-to 增强理论, 覆盖参数化余归纳, 并可对增强本身做余归纳推理 — [Coinduction All the Way Up, LICS 2016, pp.307–316](https://lics.siglog.org/2016/Pous-CoinductionAlltheWa.html) [检索摘要]. 范畴化推广 — Bonchi, Petrişan, Pous, Rot, A general account of coinduction up-to, Acta Informatica 2017 [检索摘要].
- **(1)** Danielsson 把许多 up-to 技术表为保尺寸函数, 用 sized types 跟踪尺寸, 与 Pous 的 "companion 之下的函数" 密切对应; 代码为 Agda — [Up-to Techniques using Sized Types, POPL 2018 (PACMPL 2, Art. 43)](https://www.cse.chalmers.se/~nad/publications/danielsson-up-to-using-sized-types.html) [检索摘要].

### Inferences
- **(2) 对应的面.** 候选关系 R = {(Ref t, fold c t)} 逐步不封闭; 闭包后可能封闭.
- **(3) 草图.** ≼ 是归纳定义的 (良基模拟), 要用对偶: 把 ≼ 的证明按显式的布劳威尔树尺寸 i 分层, 写 `_≼[ i ]_`; 一个 up-to 函数是把尺寸 i 的关系映到尺寸 i 的关系的函数. 候选闭包: ≼-传递, 序列重排 (∀∃ 下的重新编号), 折叠上下文 (读回域上的相容性). 主引理改证 `Ref x ≼ cl(fold c x)`.
- **(4) 最便宜的实验.** 拿被否定的逐步引理, 检查它的 "up to 传递 + 重排" 版本在反例上是否成立 (反例若只是错位, 重排后应成立). 这是一条小引理.
- **(5) 可能的冲突.** Agda 的 `--sized-types` 不 `--safe` [据记忆, 未核], 只能用显式尺寸. "归纳关系的 up-to" 与余归纳版本的对偶是否完全对称, 本轮未核 [判断].

### Gaps
- Danielsson 的框架是否覆盖归纳关系, 未读正文.

## 想法 12: chaotic / asynchronous iteration 的调度无关性

### Takeaway
Cousot 证明: 从前不动点出发, 单调方程组的 chaotic 或异步迭代, 不论调度策略如何, 都收敛到同一个极限. 我们的折叠与参照树也许做的是 "同样的更新, 不同的顺序": 局部先后不同, 外层极限一样. 要的条件是公平性 (每个更新终究都做).

### Cited Findings
- **(1)** P. Cousot, Asynchronous iterative methods for solving a fixed point system of monotone equations in a complete lattice, IMAG 研究报告 RR-88 (1977) — [条目](https://cs.nyu.edu/~pmc309/COUSOTpapers/IMAG-RR88.shtml) [检索摘要]. 1978 博士论文自述证明了 chaotic, 异步, 带记忆的异步迭代的收敛 — [论文页](https://cs.nyu.edu/~pmc309/COUSOTpapers/CousotTheseEsSciences1978.html) [检索摘要]. NACSA'98 讲义: 从前不动点出发, 不论哪种 chaotic 或异步策略, 都收敛到同一个极限 — [讲义](https://cs.nyu.edu/~pmc309/publications.www/slides/Cousot-NACSA-98-slides-4-1.pdf) [检索摘要].

### Inferences
- **(2) 对应的面.** "局部落后, 外层追上" 若只是更新顺序的差别, 就是调度无关性的特例.
- **(3) 草图.** 把 Ref 在某个 ℕ-极限处的序列看成按规范调度对一个单调更新算子的迭代, 把 fold 的序列看成另一种调度. 引理模式: 若 (i) 更新算子对 ≼ 单调, (ii) 参照调度的第 n 次更新终究被 fold 调度执行 (给出字面的 σ(n)), 则 `lim Ref-序列 ≼ lim fold-序列`. 这与想法 1 的滞后秩可以合并: σ(n) − n 就是滞后.
- **(4) 最便宜的实验.** 在逐步对应的反例里, 把参照与折叠各自的 "后继步" 列出来, 看是否只是换了次序 (公平), 还是折叠真的少做了某些更新.
- **(5) 可能的冲突.** 中间状态可能是非规范的, 更新算子在其上未必单调 (`no-start-all` 一类); 要限到读回域. 格的并不可用, 只能用 ℕ-链的上确界.

### Gaps
- RR-88 原文未读, 定理的精确条件 (前不动点, 连续性) 未核.

## 想法 13: size-change 终止性 → 全局 ranking function: 从局部约束合成意图值的形状

### Takeaway
size-change 与单调性约束的理论能判定终止, 并从局部的大小关系构造显式的全局 ranking function (词典序). 移到我们这里, 不必去猜全局的 V: 记下每条规则在各字段之间的大小关系, 用这套理论合成 V 的词典形状.

### Cited Findings
- **(1)** Ben-Amram 把 size-change 理论从 size-change graph 推广到 monotonicity constraints, 给出精确的终止判定程序, 并能在单指数时间里从单调性约束构造显式的全局 ranking function — [Size-Change Termination, Monotonicity Constraints and Ranking Functions, LMCS 6(3:2) 2010](https://lmcs.episciences.org/1001) [检索摘要]. 整数域版 (非良基) 构造的 ranking function 在最坏情形大小与序数维数上最优 — [LMCS 7(3:4) 2011](https://lmcs.episciences.org/1002) [检索摘要]. 原始 SCT: Lee, Jones, Ben-Amram, POPL 2001 [据记忆, 未核].

### Inferences
- **(2) 对应的面.** 意图值的形状 (先比哪个字段, 后比哪个) 目前靠人猜; SCT 给出由局部约束推出全局词典序的算法.
- **(3) 草图.** 对折叠的每条规则, 记录输入的各字段 (树本身, 目标, 回灌的下标) 与递归调用的字段之间的 ≽/≻/= 关系; 求闭包; 读出 Ben-Amram 构造的词典序元组, 当作 V 的候选形状 (第一分量用哪个字段, 第二分量用哪个).
- **(4) 最便宜的实验.** 折叠能编译, 说明 Agda 的调用矩阵检查已经接受了它; 由团队用 Agda 的终止检查详细输出取出调用矩阵 (本调查不运行 Agda), 手算闭包, 与参照树的结构对比.
- **(5) 可能的冲突.** SCT 是上界 (终止) 方向, 我们要下界; 只借它推形状, 不借界. 无穷分支的 Ω-结点在调用矩阵里被当作结构下降, 不提供大小信息.

### Gaps
- 没有核 Agda 调用矩阵输出的具体格式.

## 想法 14: meaningless terms 的公理化: 退化树一致地取平凡值

### Takeaway
无穷改写与 λ 演算里, Kennaway, van Oostrom, de Vries 用五条公理刻画 "无意义项" 的集合. 满足公理的任何集合都可以一致地等同为 ⊥, 并推出 genericity 与模无意义项的合流. 正交系统中最小的这样的集合是 root-active 项. 移到我们这里: 用闭包公理, 而不是判定, 规定哪些退化树取平凡值; 公理保证这种取法与一切规则相容.

### Cited Findings
- **(1)** 对有限与超限改写及 λ 演算给出无意义性的公理化; 公理推出 genericity, 模无意义项相等的合流, 等同一切无意义项的一致性; 正交 TRS 中最小的这种集合是 root-active 项 — [Kennaway, van Oostrom, de Vries, Meaningless Terms in Rewriting, JFLP 1999](https://scholar.lib.vt.edu/ejournals/JFLP/jflp/articles/1999/A99-01/A99-01.html); [作者 PDF](https://www.cs.le.ac.uk/people/ferjan/fdv1/Distribution/meaningless.pdf) [检索摘要; 五条公理的原文未读]. 后续: Severi, de Vries 研究无穷组合子逻辑中的无意义集 [检索摘要].

### Inferences
- **(2) 对应的面.** 退化树到处都是, 不能排除; 若给它们统一的平凡值, 需要保证这与各条规则相容.
- **(3) 草图.** 定义谓词 `Degen` 为满足闭包公理的集合 (对折叠的子调用封闭, 对 ≼-等价封闭, 与规则左边的重叠封闭), 意图值写成关系 `Vrel t r`: 在 Degen 的子树处允许 r 取平凡下界. 公理保证, 任取一个满足公理的 Degen, 所得语义都一致. 再取由已知退化形状 (常值序列等) 生成的最小 Degen.
- **(4) 最便宜的实验.** 把 `no-start-all`, `no-carry-Ω₂`, `no-K2′`, V64 的反例对象收成一个集合, 逐条查它是否满足 "对子调用封闭" 等公理; 满足, 就说明这些否定可以用 "把它们当无意义项" 统一处理.
- **(5) 可能的冲突.** Degen 不可判定, V 不能按 "是否退化" 分情况定义, 只能是关系; 若某条规则的计算需要知道子树是否退化, 撞 `obs→dec`.

### Gaps
- 五条公理的原文未读.

## 想法 15: 值作下集, 可数抽象基 (域论的 ideal completion)

### Takeaway
域论用抽象基上的 rounded ideal (下集) 表示元素: 上确界是有向并, 单调就是包含. 移到我们这里, 意图值不必是一棵树, 可以是 "可枚举参照基上的下集"; 下界定理变成下集的包含, 局部落后不影响包含, 因为下集只问 "终究包含".

### Cited Findings
- **(1)** Abramsky, Jung, Domain Theory, *Handbook of Logic in Computer Science* vol. 3 (1994), §2.2 ideal completion [据记忆, 未核]. 构造性序数作下闭谓词方面, Taylor 的 plump 序数与 KNFX 已在旧调查中 (R3 Q5), 不重复.

### Inferences
- **(2) 对应的面.** "sup 是并, 单调是包含" 正是想要的; 区别在于基的选择.
- **(3) 草图.** 选一个可数的参照基 B (例如参照树的有限下降路径, 或有限前段), 令 `D t := λ (b : B) → b 落在 fold c t 之下` (Σ 型, 不判定); 下界定理写成 `∀ b → b ∈ D (Ref t) → b ∈ D (fold c t)`. 在 ℕ-极限处 D(lim f) 是并, 所以局部落后只影响 "哪一项先包含 b", 不影响包含本身.
- **(4) 最便宜的实验.** 纸面: 看现有 ≼ 的 ∀∃ 证明能否改写成对某个可数基的包含; 若能, 基的元素就是要找的 "字面见证".
- **(5) 可能的冲突.** 与 Fairtlough 的路径与 Ketonen–Solovay 的 step-down (已有调查, 经 Buchholz 的 ≪_k) 重叠; 新的只是域论的组合律 (有向并, 连续性). 基若需要对高层树枚举, 不可数, 只能分层取.

### Gaps
- 本节文献未在本轮检索核实.
