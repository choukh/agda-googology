# X1 不判定而计算: 跨领域可移植想法 (只需下界时怎样绕开不可判定的分情况)

> 档位说明. 本文所有 "移植草图", "最便宜的实验", "冲突" 都是判断 (纸面), 没有编译过的定理, 也没有有限测试. 来源标注: [读原文] 本轮实际读过正文或幻灯片; [检索摘要] 只见检索摘要或书目; [依记忆, 未核] 本轮未打开, 依训练知识, 需复核. 已由前一轮调查 (`布劳威尔树折叠难点文献调查/` R1–R5) 覆盖的条目 (Eremondi 的 SMB-树 max, KNFX 的 join 禁忌, Chapman–Uustalu–Veltri 的延迟单子商, Taylor 的 plump 序数) 只在有新角度时提到.

## 问题 0: 抽象形状的分解与总排序

### Takeaway
把我们的困难拆成七个形状 (S1–S7) 后, 找到 11 个可移植的想法. 前景最好的三个是: (A) proof mining 的单调函数解释, 它把 "不可判定的二选一" 换成 "对一切判定都成立的上界"; (B) 把 ℕ-极限当作 "无限时间的并行搜索", 半可判定的见证可以放进极限里, 不需要停机; (C) 试错学习与更新过程 (Avigad, Aschieri–Berardi, Ershov 层级), 用 "默认 + 改判" 代替判定. 共同的出发点是: 我们只要 "≥ 参照", 而不要 "= 参照", 所以输出不必是 P 的函数.

### Cited Findings
- 在单调函数解释下, LLPO 这种 "二选一" 原则没有 dialectica 解释 (否则可分离两个递归不可分的 r.e. 集), 却有单调解释: 选择子 n 的界取常数 1, 其余见证的界取 max(k, r). [读原文] — [Ferreira, *Proof interpretations and majorizability*, §4.2](https://webpages.ciencias.ulisboa.pt/~fjferreira/proof_interpretations.pdf)
- Konečný–Park–Thies 在 Coq 里公理化非确定性的 `select`: 已知两个 Kleenean 中 (经典地) 至少一个为真, 就在非确定性单子 M 中选出一个. 由它得到多值 "软比较" `mSplit`, 输出 `(x<y+ε)+(y<x+ε)`. [读原文] — [Konečný, Park, Thies, *Extracting efficient exact real number computation from proofs in constructive type theory*, arXiv:2202.00891](https://arxiv.org/abs/2202.00891)
- Escardó: 在 ℕ 上加一个无穷远点得到 ℕ∞, 它满足全知原理 (对一切 p : ℕ∞ → 2, "存在 x 使 p x = 0" 可判定), 不需要连续性公理; 推论之一是任意两个函数 ℕ∞ → ℕ 相等或不等. [读原文] — [Escardó, CCC 2015 幻灯片 *Infinite, exhaustibly searchable sets*](https://martinescardo.github.io/.talks/ccc-2015.pdf); [Escardó, JSL 78(3) 2013](https://projecteuclid.org/euclid.jsl/1389032274)

### Inferences
- **七个抽象形状** (下文各想法用这些编号):
  - S1 只要下界: 输出 ≥ 参照即可, 超出无妨. 能否 "以界代判定".
  - S2 偏分支: "保留" 只在 P 有见证时有定义 (类型上要 P 的证据, 否则造出不可数下标进可数层, 即 `Toy.loop` 一类). 这是 "两边都做再相加" 不能直接用的原因.
  - S3 E 型 P: 两个子对象 (孩子下标) 字面相等.
  - S4 S 型 P: 层号比较或 "存在可保留的槽位" (存在命题).
  - S5 输出回灌作下标 (同层对角): 选择的后果会被放大, 要求单调性.
  - S6 Ω-分支不可枚举: 对一切低层树的分支不能逐个检查.
  - S7 观察约束: 任何全函数, 只要头部观察与 P 等价, 就判定 P (`obs→dec` 一族, `sig→lpo`, `branch→wdec`, `viaE→dec`, `full→dec`), 加上壁垒定理 (有界三歧 ⇒ LPO).
- **排序总表** (判断, 依 "离我们的形状近, 实验便宜, 与已编译否定冲突少" 三项):

| 序 | 想法 | 主要对应形状 | 实验成本 | 与否定结果的主要张力 |
|---|---|---|---|---|
| A | 单调函数解释: 对一切判定神谕一致的上界 | S1, S2, S5 | 低 | 需要回灌方向的单调性 (跨层单调接口已被否定) |
| B | ℕ-极限即无限时间并行: 半可判定见证放进极限 | S1, S2, S4 | 低 | 只对 "∃n. 可判定" 型的 P; 相邻项合法性 |
| C | 试错学习, 更新过程, Ershov 层级 | S1, S3, S4 | 中 | 要有逐阶段可判定的猜测; 保留需近似可做 |
| D | 软比较 / 重叠分情况 / Kleenean select | S3, S4, S7 | 中 | 值上带固定松弛的软比较对序数是禁忌 (纸面论证见 D) |
| E | 可搜索的下标类型 (ℕ∞, 紧序数) | S3, S6 | 中 | 树本身不离散; Ω-分支的全体低层树不紧 |
| F | 偏元素的包络 (dominance, 沿嵌入延拓, Kan 延拓) | S2, S6 | 中 | 守卫域为空的退化结点; View 的分类 |
| G | 抽象解释: 三值测试 + 并 + widening | S1, S2 | 低 | "未知" 处若保留无定义仍卡住 |
| H | 动态求值 (D5): 分裂语境而不分裂值 | S2, S4 | 中 | 与现有证书路线重合 |
| I | 有限候选表 (Herbrand 析取, Lifschitz 可实现性) | S1 | 中 | 候选仍须是全定义的项 |
| J | 控制算子的回溯实现子 (call/cc, Krivine) | S2, S7 | 高 | `branch→wdec` 直接相关 |
| K | 几乎满关系与析取良基 | 终止性侧 | 中 | 只管停机, 不直接给值 |

### Gaps
- 排序是判断, 没有对照实验. 下一路应先挑战排序 (特别是 A 与 F 是否其实是同一件事的两面, 见 F 的推论).

## 想法 A: 单调函数解释与可优超性 (proof mining): 用 "对一切判定一致的上界" 代替判定

### Takeaway
proof mining 的核心经验正是我们的 S1: 不可判定的分情况本身不可实现, 但 "分情况结果的上界" 可以实现, 因为二选一的选择子有界 (≤ 1), 两个分支的界取 max. 移到树上: 写一个不读 P 的 "优超折叠", 证明它对一切 "部分见证神谕" 定义的折叠都 ≽.

### Cited Findings
- Howard 1973 的可优超性 (hereditary majorizability) 与 Bezem 1985 的强可优超泛函 (y 强优超 x 时 y 也优超自己, 即单调) 是单调函数解释与有界函数解释的基础. [读原文] — [Ferreira, *Proof interpretations and majorizability*](https://webpages.ciencias.ulisboa.pt/~fjferreira/proof_interpretations.pdf); 原文 Bezem, *Strongly majorizable functionals of finite type: a model for bar recursion containing discontinuous functionals*, JSL 50 (1985) 652–660; Howard, *Hereditarily majorizable functionals of finite type*, Springer LNM (1973) 454–461 (书目取自 Ferreira 文末, 原文未打开)
- 不连续的泛函 E (α 恒为 0 时取 1, 否则取 0) 是可优超的 (由常数 1); 而 "最小的 n 使 α(n) ≠ 0" 的泛函 Σ 不可优超 (界会被构造的 α 超过). [读原文] — [Ferreira §2 (强可优超泛函模型)](https://webpages.ciencias.ulisboa.pt/~fjferreira/proof_interpretations.pdf)
- LLPO 没有 dialectica 解释 (否则一个闭项把两个递归不可分的 r.e. 集分开), 但有单调函数解释: 选择子的界是 λw.1, 见证的界是 λw,k,r. max(k,r); 验证时要用一点选择. [读原文] — [Ferreira §4.2](https://webpages.ciencias.ulisboa.pt/~fjferreira/proof_interpretations.pdf)
- 单调函数解释的可靠性定理: 对收缩公理, 项的选择 "变成 canonical"; 但证明里仍要用无量词公式的可判定性与按情况定义的泛函. [读原文] — [Ferreira, Theorem 4.6 及其后说明](https://webpages.ciencias.ulisboa.pt/~fjferreira/proof_interpretations.pdf)
- 单调函数解释出自 Kohlenbach, *Analysing proofs in analysis* (Keele Logic Colloquium 1993, OUP 1996); 系统参考书是 Kohlenbach, *Applied Proof Theory: Proof Interpretations and their Use in Mathematics*, Springer 2008. [读原文中的书目] — [Ferreira 文末 [27], [35]](https://webpages.ciencias.ulisboa.pt/~fjferreira/proof_interpretations.pdf); [Springer 页面](https://link.springer.com/book/10.1007/978-3-540-77533-1) [链接依记忆, 未打开]
- 有界函数解释 (bounded functional interpretation) 把内涵的优超关系 ≤* 放进语言, 使许多经典原则 (Π⁰₁-LEM 的一种形式, 有界选择, WKL 的一种改写) 成为 "无害" 原则. [读原文] — [Ferreira §3.6, §5](https://webpages.ciencias.ulisboa.pt/~fjferreira/proof_interpretations.pdf); 原文 Ferreira, Oliva, *Bounded functional interpretation*, APAL 135 (2005) 73–112 [书目取自 Ferreira 文末]

### Inferences
- **(2) 对应形状.** S1 (只要界) 为主; S5 (回灌) 对应 Bezem 的 "强" 优超, 即优超者必须单调; S2 (偏分支) 是本想法不直接解决的部分.
- **(3) 移植草图.**
  - 把参照折叠写成以一个 **部分见证神谕** 为参数的折叠 `fold[w]`, 其中 `w : (x : 结点) → Maybe (P x)`: w 给出见证时走保留, 否则走链. 这不是公设, 是模块参数; `w = λ_ → nothing` 就是现行的 "默认走链"; 经典地 "P 成立就给见证" 的神谕给出意图中的参照值.
  - 目标定理改写成 **神谕一致的优超**: `∀ w → fold[w] x ≼ fold* x`, 其中 `fold*` 不读 P. 由于对一切 w 成立, 也对 "正确" 的神谕成立, 验收时由记号侧 (P 在记号上可判定) 提供那个神谕即可, 定义里不出现.
  - 分情况行的优超行: `keep* ⊕ chain*` (和, 或自然和), 对应 "选择子界为 1, 见证界取 max"; 树上 max 不可得, 用和代替 (和 ≥ 两者).
  - Σ 不可优超这条提醒: 若选择的 **内容** (哪个孩子, 见证本身) 会被回灌成下标 (S5), 就从 "有界二选一" (像 E) 变成 "无界搜索" (像 Σ), 优超可能不存在, 除非折叠对回灌的下标单调.
  - 本想法给出 **证法的形状**, 不给 `keep*`. `keep*` (保留的全定义优超者) 的候选见想法 F 与 B.
- **(4) 最便宜的实验.** 纯 `.agda` 临时文件: 只含 ℕ-极限的玩具树, 行为 "保留 = 恒等, 链 = 迭代基本列"; P 取任意 `d : ℕ → Bool` 作参数; 定义 `fold*` 用 `keep ⊕ chain`, 证 `∀ d → fold[d] ≼ fold*`. 通过后加一层 Ω-分支, 看单调性在哪一步被要求.
- **(5) 冲突.** (i) 跨层单调接口已被否定 (对 dl 矛盾, 对任意 D 推出 LPO), 强优超要求的单调性可能正落在那里; 需要逐条核对那条否定的量化域是否就是这里要的单调性, 不能凭形状判定. (ii) `keep*` 若要对 P 不成立的结点也全定义, 就碰到 S2 与 `Toy.loop`. (iii) 与 S7 无冲突: `fold*` 不读 P, 头部观察与 P 无关.

### Gaps
- 没有找到在序数值 (而非 ℕ 值) 上做单调函数解释的文献; Kohlenbach 书中关于序数递归 (bar recursion, 序数值泛函的优超) 的章节本轮未读.
- "收缩公理的 canonical 项即 max" 是我对 Ferreira 一句话的解读, 需在 Kohlenbach 书 (第 8–9 章附近, 依记忆) 核对.

## 想法 B: ℕ-极限即 "无限时间的并行": 把半可判定的见证搜索放进极限里

### Takeaway
在序列式语言里, 两个半判定的 "并行或" 不能顺序地写出; 但布劳威尔树的 ℕ-极限的值是上确界, 它天然容纳 "永远跑下去的搜索": 第 n 项只看 "到第 n 步为止找到见证没有" (可判定). 找到就把保留加进去. 这样不需要停机 (不需要 Markov 原则), 也不需要判定 P, 只要 P 是 "∃n. 可判定" 型的.

### Cited Findings
- Escardó–Knapp 用 dominance (可作偏元素定义域的命题之集) 在单值类型论里重建偏性, 不假设可数选择或 Markov 原则. [检索摘要] — [Escardó, Knapp, *Partial Elements and Recursion via Dominances in Univalent Type Theory*, CSL 2017, LIPIcs 82, 21:1–21:16](https://drops.dagstuhl.de/opus/volltexte/2017/7682/)
- Plotkin 证明 PCF 中不能定义 parallel-or, 加入它后语言对 Scott 模型完全抽象. [依记忆, 未核] — Plotkin, *LCF considered as a programming language*, TCS 5(3) (1977) 223–255, [DOI 10.1016/0304-3975(77)90044-5](https://doi.org/10.1016/0304-3975(77)90044-5)
- Capretta 的延迟单子在类型论里用余归纳表示可能不停机的计算, 两个计算可以交错 "赛跑". [依记忆, 未核] — Capretta, *General recursion via coinductive types*, LMCS 1(2) (2005) [链接未核]; 其商的选择问题见前轮 R3 (Chapman–Uustalu–Veltri)
- Konečný–Park–Thies 的实数比较 `x < y` 被公理化为半可判定 (Kleenean 值), 相等时 Kleenean 无定义; 分情况只在 Kleenean 有定义时进行. [读原文] — [arXiv:2202.00891](https://arxiv.org/abs/2202.00891)

### Inferences
- **(2) 对应形状.** S2 (保留要见证: 见证找到时保留就有定义), S4 (层号比较或存在可保留槽位, 若它们是 "存在某个有限证据" 型), S1 (上确界 ≥ 找到后的值).
- **(3) 移植草图.**
  - 设 P x ⇔ ∃n. Q x n, Q 可判定, 且由 Q x n 能构造 P x 的见证. 定义 `out x = lim (λ n → if 找到(x, n) then chain_n ⊕ keep(见证) else chain_n)`, 其中 `找到(x, n)` 检查 Q x 0 … Q x n. 值: P 不成立时 = 链的值; P 成立时 ≥ 保留的值. 都 ≥ 参照.
  - 相邻项合法性: 切换时不 "换掉" 链而是 "加上" 保留 (单调累加), 让相邻项按树的合法性步进.
  - 我们的哪些 P 是这种形状 (待查): S 型的 "存在可保留的槽位" 若槽位按 ℕ 编号, 则是 Σ⁰₁; 层号比较若要先找一个字面公共上界 (例如塔 `tw n` 的某一站), 则 "找到公共上界之后用 `bdec` 判定" 就是 Q x n. 后者只在 "层号 ≤ tw n" 本身可判定 (例如层号带了站号证据) 时成立.
  - Kleene 的 O 有一个类比: 一个记号以下的前驱集合 c.e. 且线性, 所以在固定上界之下比较可由并行搜索完成 (需要停机, 即 MP). [依记忆, 未核: Rogers 1967 §11.7] 放进 ℕ-极限后不需要停机, 这正是本想法与 "字面公共上界" (`bdec`) 的接口.
- **(4) 最便宜的实验.** 玩具: `α : ℕ → Bool`, P := ∃k. α k ≡ true, 保留类型上要 k 与证明. 写 `out` 并证 `chain ≼ out` 与 `P → keep ≼ out`. 再挑一个仓库里真实的 S 型 P, 判断它是否 Σ⁰₁ (查定义, 不编译).
- **(5) 冲突.** (i) `sig→lpo` 与 `full→dec` 说的是 **头部** 观察; 这里头部恒为极限, 第 n 项的头部只反映可判定的 "到 n 为止找到没有", 不揭示 P. 纸面上看不冲突, 但要逐条核 `full→dec` 的 "能保留处都保留" 是否被本构造满足 (本构造只在极限意义上保留, 不在每一项保留, 可能正好落在该否定定理之外). (ii) E 型 P (字面相等, S3) 一般是 Π⁰₁ 型, 不是 Σ⁰₁, 本想法不直接适用, 见 C. (iii) Ω-分支 (S6) 上 "对一切 c" 型的 P 不可枚举. (iv) 累加给基本列带来毛刺 (作者 11-04 的提醒: 累加不等于自然), FGH 值可能与参照不同, 但序数值验收不受影响.

### Gaps
- 没有找到 "布劳威尔树极限作为 Rosolini/Sierpiński 式并" 的明确文献陈述; 这一对应是判断.

## 想法 C: 试错学习, 更新过程与 Ershov 层级: "默认 + 改判" 代替判定

### Takeaway
从 Hilbert 的 ε-替换法到 Avigad 的更新过程, 再到 Aschieri–Berardi 的学习式可实现性, 经典证明里的排中律被解释为 "先猜一个默认值, 遇到反例就改判", 改判次数由序数控制 (Ershov 层级, 序数改判上界). 移到树上: 第 n 项用第 n 阶段的猜测; 布劳威尔极限取上确界, 对下界而言 "上确界 ≥ 最终猜对之后的值", 所以不必知道何时猜对.

### Cited Findings
- Avigad 证明算术的 1-一致性等价于某类 "更新过程" 的不动点存在, 这类过程隐含在 ε-替换法里; 嵌套更新过程总有有限不动点. [检索摘要] — [Avigad, *Update procedures and the 1-consistency of arithmetic*, MLQ 48 (2002)](https://www.andrew.cmu.edu/user/avigad/Papers/update.pdf)
- Aschieri–Berardi 对 HA + EM1 (Σ⁰₁ 排中律) 给出学习式可实现性: 原子实现子是 "学习主体", 个体随时间演化, 实现子可影响其演化; 语义建立在 Avigad 的不动点结果上. [检索摘要] — [Aschieri, Berardi, *Interactive Learning-Based Realizability for Heyting Arithmetic with EM1*, LMCS 6(3) 2010](https://lmcs.episciences.org/1061)
- Aschieri 的博士论文把超限更新过程与一致性强度对应, 例如 U(ω) 对应 PA 的 1-一致性, U(ω·2) 对应初等分析. [检索摘要] — [Aschieri, *Learning, Realizability and Games in Classical Arithmetic*, arXiv:1012.4992](https://arxiv.org/abs/1012.4992)
- Freivalds–Smith 引入用构造性序数界定学习机的改判次数; Ambainis–Jain–Sharma 研究语言识别的序数改判复杂度; 修正文法 (correction grammars) 恰好刻画 Ershov 层级中的相应类. [检索摘要] — Ambainis, Jain, Sharma, *Ordinal mind change complexity of language identification*, TCS (1999) [只见他文书目, 卷期与链接未核]; [*Learning correction grammars* (作者 Carlucci, Case, Jain 依记忆)](https://www.comp.nus.edu.sg/~sanjay/paps/corgram.pdf); Freivalds, Smith, *On the role of procrastination in machine learning*, Information and Computation 107 (1993) [依记忆, 未核]
- 试错谓词与极限可计算性: Putnam 1965 (trial and error predicates), Gold 1967 (identification in the limit); Shoenfield 极限引理: Δ⁰₂ = 极限可计算. [依记忆, 未核] — Putnam, JSL 30 (1965) 49–57; Gold, Information and Control 10 (1967) 447–474

### Inferences
- **(2) 对应形状.** S3 (相等是 Π⁰₁: "到第 n 层为止一致" 是可判定的逐阶段猜测), S4, S1.
- **(3) 移植草图.**
  - 对 Δ⁰₂ 型的 P (有可判定的 `guess x n : Bool`, 极限上等于 P), 定义 `out x = lim (λ n → row(guess x n) 的第 n 个近似)`, 改判时累加而不替换. 值是上确界, 不是 "最终值", 对下界足够.
  - **以树本身作改判计数器** (Ershov 的 α-c.e.): 每次改判沿被折叠的树走一步, 递归是结构递归, 不依赖 "何时猜对". 这给了一种用良基数据代替判定的组织方式.
  - E 型 P 的阶段猜测: "孩子下标在前 n 个 ℕ-分支, 深度 n 以内字面一致". 难点是保留在 "只是近似相等" 时能否执行 (保留在类型上要真相等). 需要一个 "精度 n 的保留" 运算: 只交接前 n 项. 这是本想法成败所在.
  - 与 A 的关系: A 给证法 (对一切神谕一致), C 给一个具体神谕族 (逐阶段的猜测) 及把它们合起来的极限.
- **(4) 最便宜的实验.** 纸面先做: 在仓库现有的 E 型行 (`rowE-same`, `rowE-off`) 上, 写出 "精度 n 的交接" 的类型, 看它是否需要真相等的证据. 若不需要, 玩具里编译 `lim` 版本并证 ≥.
- **(5) 冲突.** (i) `viaE→dec` 与 `sep→wdec`: 经证据函数派发即判等; 本想法的派发是逐阶段的, 不是经证据函数, 应不冲突, 但 "精度 n 的交接加回退" 可能落入 `sep→wdec` 的 "可观察回退" 前提, 要逐条核. (ii) Ω-分支 (S6) 上没有阶段: 只能在交替路线把不可数层表示成对角 ℕ-极限的那一层用. (iii) 累加的毛刺, 同 B.

### Gaps
- 未找到把 "学习式实现子" 用于构造序数值 (而不是自然数见证) 的文献.
- Ershov 层级对序数记号的依赖 (Ambainis 1995 *The power of procrastination ... depends on used ordinal notations*) 未读; 若改判计数器依赖记号的选择, 与纲领 4 的关系要另看.

## 想法 D: 软比较, 重叠分情况与 Kleenean 的 select (可计算分析)

### Takeaway
精确实数计算从不判定 x < y, 而用 "多值的软比较": 给精度 ε, 只承诺 x < y+ε 或 y < x+ε 中给出一个成立的, 两者都真时随便给. 可移植的是这个结构: **找两个都可见证且析取可构造地证明的性质, 它们重叠, 重叠处两种行为都可接受**. 但对序数, "在值上留固定松弛" 的软比较仍推出 LPO (纸面论证如下), 所以松弛必须放在表示的精度上, 不能放在值上.

### Cited Findings
- `select : Π(x,y : K). (⌈x⌉ ∨ ⌈y⌉) → M(⌈x⌉ + ⌈y⌉)`: 两个 Kleenean 中经典地至少一个为真, 就在单子 M 中非确定地选出; M 只对子单元类型可消去 (`elimM`). [读原文] — [Konečný, Park, Thies, arXiv:2202.00891](https://arxiv.org/abs/2202.00891)
- 软比较 `x <_k y` 并行运行两个偏测试, 哪个先停可以随运行而变; 类型论版本 `mSplit : Π(x,y,ε). 0<ε → M((x<y+ε)+(y<x+ε))`. [读原文] — [同上](https://arxiv.org/abs/2202.00891)
- 同组的后续工作说, 外延地识别实数时, 非确定性是不可避免的效应. [检索摘要] — [Konečný, Park, Thies, *Formalizing hyperspaces for extracting efficient exact real computation*, arXiv:2410.13508](https://arxiv.org/abs/2410.13508); [MFCS 2023 版](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.MFCS.2023.59)
- Brattka–Gherardi 把 Weihrauch 归约推广到多值函数; 弱可计算的类对复合封闭, 证明用了 Kleene 三值逻辑的计算版本; 单值的弱可计算运算其实已经可计算. [检索摘要] — [Brattka, Gherardi, *Weihrauch degrees, omniscience principles and weak computability*, JSL 76(1) (2011) 143–176](https://arxiv.org/abs/0905.4679)
- HoTT 书的 Cauchy 实数用 Lipschitz / 非扩张映射的延拓定义 min 与 max, 再用 max 定义 ≤, 不按 x < y 或 y < x 分情况. [检索摘要, 二手来源] — [PlanetMath 对 HoTT 书 §11.3.3 的转述](https://planetmath.org/1133thealgebraicstructureofcauchyreals); [Cubical Agda 实数形式化 arXiv:2604.24782](https://arxiv.org/abs/2604.24782)

### Inferences
- **(2) 对应形状.** S3, S4 (两种 P 都换成重叠的一对), S7 (重叠使头部观察不再与 P 等价).
- **(3) 移植草图.**
  - 形状: 找可判定 (或可见证) 的 A_n, B_n, 满足 (a) A_n ∨ B_n 可构造地成立, (b) A_n 下保留可执行且 ≥ 参照, (c) B_n 下链 ≥ 参照; A_n 与 P 不等价 (否则 `obs→dec`). 然后 `lim_n` 合并各精度.
  - 候选 A_n, B_n: "两个孩子下标在深度 n 以内字面一致" 与 "在深度 n 以内分开" (ℕ-分支部分的有限比较可判定). 这把 E 型的 Π⁰₁ 相等换成每个精度上的二值判定; 难点仍是 (b): 只是 "到深度 n 一致" 时保留能否执行.
  - Brattka–Gherardi 的 "单值的弱可计算运算已可计算" 提醒: 多值性只有在输出 **不必** 由输入的值唯一决定时才有用. 我们的情况正是如此 (只要 ≥ 参照, 不同的码都可接受), 所以中间层可以 "多值" (依赖码而不是值), 不违背单值性.
  - **纸面论证: 值上的固定松弛是禁忌.** 设 s : ℕ → Bool, 令 β = lim_n (若 s 在 n 以内出现 true 则 ω+4 否则 n), α = ω+2. 未出现时 β = ω, 出现时 β = ω+4. 于是 "α ≤ β+1 或 β ≤ α+1" 的任一个判定都判定 "s 出现 true", 即 LPO. 松弛换成任何固定的有限量或倍数, 同样构造. 结论 (判断): 序数没有 "模" (Cauchy 实数自带收敛速率), 软比较的松弛只能放在表示的精度 (深度, 阶段) 上.
- **(4) 最便宜的实验.** (i) 把上面的纸面论证编译成一条否定定理 `softslack→LPO` (几十行, 只用 ℕ-极限的玩具树), 作为本想法的配对否定. (ii) 正面: 对只含 ℕ-分支的码, 编译 "深度 n 的三值比较" 并检查 (b).
- **(5) 冲突.** 壁垒定理 (有界三歧 ⇒ LPO) 与 (i) 的纸面论证都说明: 软比较不能落在值上. `sep→wdec` (可观察回退 ⇔ 弱判等) 要逐条核: 精度 n 的回退是否就是该定理里的 "可观察回退".

### Gaps
- `select` 在 Coq 中是公理; 我们不能加公理. 可移植的只是 "重叠覆盖 + 依赖码的选择" 这一结构, 不是 M 单子本身. 在无公理的 Agda 里, 依赖码的选择就是普通函数, 不需要 M (判断).
- 本轮未读 Bridges–Vîţă 的 located 集与近似分裂原理 (依记忆: Bridges, Vîţă, *Techniques of Constructive Analysis*, Springer 2006), 它们可能给出 "加位置数据" 的现成形状.

## 想法 E: 可搜索 (紧) 的下标类型: 让 "对一切孩子" 的检查可判定

### Takeaway
Escardó 证明某些无穷类型 (ℕ∞, 由带无穷远点的和迭代得到的 "紧序数") 在 MLTT 中无公理地满足全知原理: 对可判定谓词, 存在性可判定; 由此 "两个函数 ℕ∞ → ℕ 相等或不等" 可判定. 可移植的问题是: 能否在中间层把某些 ℕ-极限的下标换成 ℕ∞ (把极限点也放进下标), 使 "孩子字面相等" 在离散的影子上可判定.

### Cited Findings
- ℕ∞ (递减的二进制序列) 上的 LPO 成立: 对一切 p : ℕ∞ → 2, "有 x 使 p x = 0" 或 "没有"; 不用连续性; 推论包括 "任意两个函数 ℕ∞ → ℕ 相等或不等", "每个函数 ℕ∞ → ℕ 有可求的最小值点". [读原文] — [Escardó, CCC 2015 幻灯片](https://martinescardo.github.io/.talks/ccc-2015.pdf)
- 可搜索 ⇔ 有居民且全知; 可搜索类型对 Σ 封闭; 对 Π 一般不封闭 (ℕ∞ → 2 在连续与有效模型中不全知), 但对子单元类型为下标的 Π 封闭 ("micro Tychonoff"); 可数族加无穷远点的不交和仍可搜索, 迭代给出可搜索序数. [读原文] — [同上](https://martinescardo.github.io/.talks/ccc-2015.pdf)
- 这些集合是构造意义的序数 (字典序), 对可判定子集良基, 超限归纳限于可判定谓词; 简单类型可达 ε₀ 以下任意序数. [检索摘要] — [Escardó, *Infinite sets that satisfy the principle of omniscience in any variety of constructive mathematics*, JSL 78(3) (2013) 764–784](https://projecteuclid.org/euclid.jsl/1389032274)
- TypeTopology 中同一套序数码有两种解释: 离散 (Δ) 与紧 (Κ); 紧解释里和多了一个非孤立的顶点, 正是它使可搜索成为可能; 离散解释里可搜索是禁忌; 经典地 squashed sum 等于序数和加 1. [检索摘要] — [TypeTopology, Ordinals.NotationInterpretation1](https://martinescardo.github.io/TypeTopology/Ordinals.NotationInterpretation1.html) [本轮访问返回 503]; [Escardó, *Compact totally separated types*, arXiv:2609.10447](https://arxiv.org/abs/2609.10447); [compact ordinals 幻灯片](https://martinescardo.github.io/.talks/compact-ordinals.pdf)
- Escardó 2008 的可穷尽集与高阶计算 (原始来源). [依记忆, 未核] — Escardó, *Exhaustible sets in higher-type computation*, LMCS 4(3) (2008)

### Inferences
- **(2) 对应形状.** S3 (相等), S6 (对一切孩子的量化). 不对应 S4 的层号比较 (紧序数的序本身不可判定, 判断依据: ℕ∞ 上 "x = ∞" 不可判定, 那是 LPO).
- **(3) 移植草图.**
  - 中间层的 ℕ-极限改为 ℕ∞-极限: 一族 f : ℕ∞ → 树, 极限点 f ∞ 是 "到达极限后的值". View 只把它读成 ℕ-极限 (限制到 ℕ ⊂ ℕ∞); 要求 f ∞ ≼ 上确界, 值不变.
  - 收益: 若两个子对象的 **离散影子** (例如层号的有限编码, 标签, 某一层的分支模式) 是 ℕ∞ → ℕ 的函数, 则它们相等可判定 (Escardó 的推论 2). 保留只需要影子相等时, E 型 P 就判定了.
  - "顶点使可搜索成为可能" 与我们 "极限的极限点" 对应: 我们的树没有把极限点放进下标, 这可能正是对一切孩子的量化不可判定的原因之一 (判断).
- **(4) 最便宜的实验.** 在仓库外临时文件里, 用 `--safe --without-K` 写出 ℕ∞ 与它的全知性 (几十到一两百行, TypeTopology 有现成证明可对照), 再对一个具体的影子函数检验 "相等可判定". 然后纸面检查: 我们的 E 型 P 是否只依赖某个离散影子.
- **(5) 冲突.** (i) 树本身不离散, "函数到树" 的相等仍不可判定; 只对影子成立. (ii) Ω-分支的下标是全体低层树, 不紧; 只能用于交替路线里 Ω 的对角 ℕ-极限表示. (iii) 壁垒定理: 紧序数没有可判定的序, 所以不给有界三歧, 纸面看不触壁垒; 但若有人用它导出层号的三歧, 立即对照 `¬tri`.

### Gaps
- TypeTopology 页面本轮返回 503, 紧序数的具体定义与定理名未核.
- 未查到可搜索序数在序数值 (布劳威尔树) 意义下能到多高, 与我们的层号是否相容.

## 想法 F: 偏元素的包络: dominance, 沿嵌入延拓与 (左) Kan 延拓

### Takeaway
"保留只在 P 有证据时有定义" 在领域论里就是一个偏元素 (定义域为 P 的命题). 有三种不判定地把偏元素 "补全" 的标准做法: (i) 以命题为下标的上确界 (偏元素与全元素的并); (ii) Escardó 的 "沿嵌入延拓类型族", 嵌入像之外取平凡值, 不判定一个点是否在像里; (iii) 单调包络 (左 Kan 延拓的逐点公式): 在 x 处取 "一切满足 P 且 ≤ x 的 y 上 keep(y) 的上确界". 对下界而言 (iii) 正是最小的单调延拓.

### Cited Findings
- Escardó–Knapp 以 dominance 定义偏元素: 偏元素是一个定义域命题加上在该命题下的值. [检索摘要] — [Escardó, Knapp, CSL 2017](https://drops.dagstuhl.de/opus/volltexte/2017/7682/)
- 宇宙的内射性: 给 A 上的类型族 X 与嵌入 e : A → B, 可延拓成 B 上的族 Y 使 Y(e a) ≅ X(a), 像之外的点 Y(b) ≅ 1; 若各 X(a) 可搜索, 则各 Y(b) 可搜索 (用 micro-Tychonoff). [读原文] — [Escardó, CCC 2015 幻灯片](https://martinescardo.github.io/.talks/ccc-2015.pdf)
- 以子单元类型为下标的可搜索类型之积仍可搜索 (micro-Tychonoff), 这是 "以命题为下标" 的构造在可搜索性下的表现. [读原文] — [同上](https://martinescardo.github.io/.talks/ccc-2015.pdf)
- 实数的 min/max 由 Lipschitz 延拓得到: 在可判定的有理数上定义, 再延拓到全体, 不在实数上分情况. [检索摘要, 二手] — [PlanetMath 转述 HoTT 书 §11.3.3](https://planetmath.org/1133thealgebraicstructureofcauchyreals)
- 左 Kan 延拓的逐点公式 (沿 i 的延拓在 x 处是 comma 范畴上的余极限; 在偏序中即 "一切 i(y) ≤ x 的 y 上的上确界"). [依记忆, 未核] — Mac Lane, *Categories for the Working Mathematician*, 第 X 章

### Inferences
- **(2) 对应形状.** S2 (偏分支) 为主, S6 (上确界的下标是低层树).
- **(3) 移植草图.**
  - (i) **命题下标的上确界**: 若树允许 "以 Σ c. P c 为下标的 Ω-分支" (守卫域), 则 `chain ⊕ sup_{(c,p)} keep(c,p)` 就是 "链与偏保留的并", 不需判定. 这与仓库已有的守卫域机制同形, 新的只是读法: 它是 dominance 意义下的偏元素的并.
  - (ii) **沿嵌入延拓**: 保留的分支函数 g 定义在层号 μ 的树上; 想要的是一个定义在 "目标以下合法的下标" 上的分支, 在 μ 真的低于目标时与 g 一致, 否则取平凡值 (0). Escardó 的构造在像之外取 1, 而且不需要判定一个点在不在像里. 移到树上需要: 从 "目标以下的下标" 到 "μ 层的下标" 的纤维是命题 (嵌入), 然后以纤维为下标取上确界.
  - (iii) **单调包络**: keep*(x) = sup { keep(y) : y ≤ x, P(y) }, 用守卫的 Ω-分支实现. 与想法 A 合起来: A 要的 "保留的全定义优超者" `keep*`, 最小的候选正是这个包络 (判断).
- **(4) 最便宜的实验.** 纸面: 在仓库现有守卫域上写出 (ii) 的纤维, 检查它是否是命题、是否只用到字面公共上界. 编译: 用 Bool 守卫的玩具, 证 `P → keep ≼ chain ⊕ envelope`.
- **(5) 冲突.** (i) 守卫域为空的退化结点 (下界不合法, 常值极限): 前几轮在全合法域上求封闭时反复得到 "谓词太宽" 的否定 (`no-start-all`, `no-carry-Ω₂`, `no-K2′`); 包络在 P 不成立时正好产生空守卫. 按最佳实践, 应先在带证据的读回域上陈述. (ii) View: 以 Σ c. P c 为下标的上确界要归入 "Ω-极限 (按低层合法树分支)", 下标类型不是全体低层树, 要说明它如何读成 Ω-极限 (例如对不满足 P 的 c 取 0, 但这又要判定). (iii) "不可数下标不能作可数层的构造子" (`Toy.loop`): 包络的下标是低层树, 只能出现在允许 Ω-分支的层.

### Gaps
- 未找到在布劳威尔树或序数值上做 "偏元素的并" 的文献; 对应是判断.
- (ii) 中 "截断/收缩" 方向 (从任意下标到 μ 层下标的全函数) 可能本身要比较层号; 未查出可用的构造.

## 想法 G: 抽象解释: 条件未知时取两个分支的并, 用 widening 保证收敛

### Takeaway
静态分析里, 守卫条件在抽象域上不可判定时, 标准做法是取两个分支抽象值的并 (过近似, 对 "不低于" 方向的结论是可靠的), 并用 widening 算子在迭代不稳定时跳到更粗的值. 对我们: 设计一个 P 可判定的 "抽象域" (三值: 一定低于, 一定不低于, 未知), 只在 "一定" 时按单边处理, "未知" 时两边都做 (和).

### Cited Findings
- Cousot–Cousot 的抽象解释: 用格上的不动点近似程序语义, 控制流汇合处取并, widening 保证迭代有限步稳定. [依记忆, 未核] — Cousot, Cousot, *Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints*, POPL 1977, [DOI 10.1145/512950.512973](https://doi.org/10.1145/512950.512973)
- Brattka–Gherardi 的复合封闭证明使用 Kleene 三值逻辑的计算版本; Konečný–Park–Thies 的 Kleenean 是同一想法在类型论中的形态 (真, 假, 未定义). [检索摘要 / 读原文] — [Brattka, Gherardi, arXiv:0905.4679](https://arxiv.org/abs/0905.4679); [arXiv:2202.00891](https://arxiv.org/abs/2202.00891)

### Inferences
- **(2) 对应形状.** S1 (过近似可接受), S2 (只在 "一定低于" 时保留).
- **(3) 移植草图.** 三值测试 `t : 结点 → {低于, 不低于, 未知}`, 要求可靠性: `t x = 低于 → P x` (给见证), `t x = 不低于 → ¬P x`. 行: 低于 → 保留; 不低于 → 链; 未知 → 链 ⊕ (可得的部分保留). t 可以由 "字面公共上界存在且 `bdec`" 实现: 有公共上界时给确定答案, 否则未知. widening 的对应: 当迭代 (链) 不收敛到可比较的形状时, 直接跳到下一个 Ω-层的上界 (超出可接受).
- **(4) 最便宜的实验.** 有限测试: 在规范读回域 (塔 `tw n`, Ω̂ 的带证据坐标) 的样本上数 "未知" 出现的位置; 若 "未知" 只出现在保留缺陷之外, 三值版本就闭合了保留缺陷 (标为有限测试, 不是证明).
- **(5) 冲突.** "未知" 处若保留无定义 (S2), 只能走链, 回到现状. 本想法的价值取决于 "未知" 的范围; 它与 `full→dec` 不冲突, 因为它不要求 "能保留处都保留".

### Gaps
- 未查抽象解释里 "欠近似" (under-approximation, 用于证明可达性) 的文献, 那个方向可能更贴近 "只要下界".

## 想法 H: 动态求值 (D5): 分裂语境, 不分裂值

### Takeaway
计算机代数里, 零测试在代数扩张上不可判定时, Duval 等人的动态求值不去判定, 而是把计算分裂成两支: 一支把元素当作零 (在商环里继续), 一支当作可逆; 结果在每一支里都正确. 构造代数把它系统化为 "动态方法", 用层或站点模型给语义. 移到树上: 把 P 的两种可能作为两个语境, 输出一棵 "语境树", 只在闭项上 (P 在那里能算出来) 合并.

### Cited Findings
- Della Dora, Dicrescenzo, Duval 的 "动态求值" (D5 原则) 用于不做因子分解地计算代数数; 零测试不可判时计算分裂, 一支加约束 "为零", 另一支 "非零". [检索摘要] — [van der Hoeven, *Directed evaluation* (转述 D5)](https://www.texmacs.org/joris/direval/direval.html); 原文 Della Dora, Dicrescenzo, Duval, *About a new method for computing in algebraic number fields*, EUROCAL 85 [依记忆, 未核]
- 构造代数中, 一般不能判定多项式在域上的不可约性; 有工作给出特征 0 域的代数闭包的站点模型, 可视为 Duval 意义的动态求值的模型. [检索摘要, 作者未核] — [arXiv:1404.4549](https://arxiv.org/abs/1404.4549)
- 动态求值被用于 Newton–Puiseux 定理的构造性证明, 构造三角可分代数. [检索摘要] — [arXiv:1304.6770](https://arxiv.org/abs/1304.6770)

### Inferences
- **(2) 对应形状.** S2, S4.
- **(3) 移植草图.** 中间层的对象带一个 "语境": 一组关于层号的假设 (μ < ν 或 ¬(μ < ν)). 折叠在遇到不可判定的比较时不选, 而是产出 `(P → 树) × (¬P → 树)` 形状的结点; 序数值定理在每一支里分别证 (经典地总有一支成立, 但每一支的定理本身是构造的). 闭项层面, P 由具体树算出 (闭项上层号是字面的), 语境树坍缩成一棵树.
- **(4) 最便宜的实验.** 纸面: 列出现有终点闭项 `endᶻ` 构造中所有被默认为链的比较, 看它们在闭项上是否都能靠计算判定. 若是, 动态求值版本就是 "定义里分裂, 闭项上归约".
- **(5) 冲突.** (i) 纲领 1 要求最终定义是布劳威尔树 (或有 View); `(P → 树) × (¬P → 树)` 不是 View 的四种形状之一, 必须在闭项上消去, 这与已有的证书路线 (`Carry` 等) 高度重合, 新意有限. (ii) 一般的 (非闭) 对象上不能消去.

### Gaps
- Lombardi–Quitté 的书 (*Commutative Algebra: Constructive Methods*) 中关于动态方法的章节未读; 其中 "逻辑上的动态定理" 是否给出 "在两支都成立的结论可以无分裂地读出" 的元定理, 可能直接对应 "值的定理在两支都成立就可无分裂地使用".

## 想法 I: 有限候选表: Herbrand 析取, 无反例解释, Lifschitz 可实现性

### Takeaway
经典证明的计算内容常常不是一个见证, 而是一张有限的候选表, 保证其中至少一个可用 (Herbrand 定理, Kreisel 的无反例解释); Lifschitz 可实现性把这种 "有限多个候选" 做成实现子, 正好实现 LLPO. 对下界: 把有限候选表加起来就是一个界.

### Cited Findings
- 无反例解释: 前束式公式经典有效当且仅当其 Herbrand 化有效; 定理 4.14 给出相应的项. [读原文] — [Ferreira §4.5](https://webpages.ciencias.ulisboa.pt/~fjferreira/proof_interpretations.pdf); Kohlenbach, *On the no-counterexample interpretation*, JSL 64 (1999) [书目取自 Ferreira 文末, 卷号依记忆]
- Rathjen–Swan 把 Lifschitz 可实现性推广为一族形式拓扑 L_n, 原始的 Lifschitz 模型对应 L_2, 并证明 LLPO_{n+1} 严格弱于 LLPO_n. [检索摘要] — [Rathjen, Swan, *Lifschitz realizability as a topological construction*, JSL (2020), arXiv:1806.10047](https://arxiv.org/abs/1806.10047)
- van Oosten 把 Lifschitz 可实现性表示为有效拓扑斯中 Lawvere–Tierney 拓扑上的层, 构造用到 Lifschitz 对有限集的编码. [检索摘要] — [同上 (引言转述)](https://arxiv.org/abs/1806.10047); 原文 van Oosten, *Lifschitz' realizability*, JSL 55 (1990) [依记忆, 未核]

### Inferences
- **(2) 对应形状.** S1.
- **(3) 移植草图.** 先写一个用排中律 (对 P) 的经典下界证明; 对它做无反例解释或 Herbrand 抽取, 得到有限个不读 P 的候选项 t₁ … t_k (每个都是全定义的树), 定义输出为 t₁ ⊕ … ⊕ t_k. 这是 "从经典证明机械地得到 A 的 `fold*`" 的路径; 候选表的长度给出 "两边都做" 要做几份.
- **(4) 最便宜的实验.** 纸面: 把 "保留缺陷" 的经典修复 (P 成立就保留) 写成一段经典证明, 手工做 Herbrand 抽取, 看候选是否全定义.
- **(5) 冲突.** 候选必须是全定义的项; 若唯一合理的候选就是 "保留" 本身 (偏, S2), 抽取会给出带 P 证据的项, 回到原处.

### Gaps
- 未找到对序数值或树值的函数做 Herbrand 抽取的例子.

## 想法 J: 控制算子与回溯实现子: 先答 "否", 遇到见证再改口

### Takeaway
Griffin 与 Krivine 的经典可实现性把 A ∨ ¬A 实现为: 先回答 ¬A (交出一个函数), 若这个函数日后被应用到 A 的见证上, 就跳回去改答 A 并带上该见证. 我们的 Ω-极限正是 "交出一个函数, 由观察者提供下标". 可移植的问题: 观察者提供的下标 c 是否能充当 P 的见证, 使分支在 c 处 "改口".

### Cited Findings
- Griffin 把 call/cc 类型化为 Peirce 律, 给出经典逻辑的 Curry–Howard 对应. [依记忆, 未核] — Griffin, *A formulae-as-types notion of control*, POPL 1990, [DOI 10.1145/96709.96714](https://doi.org/10.1145/96709.96714)
- Aschieri 的论文把学习, 可实现性与博弈 (回溯博弈) 联系起来. [检索摘要] — [arXiv:1012.4992](https://arxiv.org/abs/1012.4992); Coquand 的回溯博弈语义 (*A semantics of evidence for classical arithmetic*, JSL 60 (1995)) [依记忆, 未核]

### Inferences
- **(2) 对应形状.** S2, S7.
- **(3) 移植草图.** 在 Ω-分支处, 分支函数 `λ c → chain(c) ⊕ (若 c 自带 P 的证据则 keep 否则 0)`; "c 自带证据" 要求下标类型携带证据 (带证据的读回域), 而且是 **观察者** 给的, 不是折叠去判定的.
- **(4) 最便宜的实验.** 纸面: 对照 `branch→wdec` 的前提, 看 "证据随下标而来" 是否落入它的范围.
- **(5) 冲突.** `branch→wdec` (经分支派发推出弱判定) 与 "开新行前的先验检查" 第 2 条 (孩子下标类型上有没有证据函数) 直接相关; 很可能这就是那条否定已经覆盖的形状, 列在这里只为完整, 前景最低.

### Gaps
- 未查经典可实现性里 "实现子输出的是数据而不是函数" 时回溯如何表示 (Krivine 的 "数据类型的经典实现" 问题).

## 想法 K: 几乎满关系与析取良基: 不判定 "哪一个度量下降" 也能证停机

### Takeaway
终止性分析里, Podelski–Rybalchenko 的转移不变式说: 只要转移关系包含在有限多个良基关系之并的传递闭包里, 就停机, 无需判定每一步是哪一个下降; Vytiniotis–Coquand–Wahlstedt 把它构造化为 "几乎满关系" (almost-full), 在 Coq/Agda 中可用. 对我们: 若 "试保留, 不行再链" 的递归需要停机证明而 "哪种情形" 不可判定, 可以用几乎满关系代替按情形的度量.

### Cited Findings
- Vytiniotis, Coquand, Wahlstedt, *Stop When You Are Almost-Full: Adventures in Constructive Termination*, ITP 2012, LNCS 7406, 250–265: 把程序终止技术与 Ramsey 论证连起来, 在类型论中完全构造地发展, 基于 Bezem–Veldman 与 Richman–Stolzenberg. [检索摘要] — [researchr 条目](https://researchr.org/publication/VytiniotisCW12); [coq-community/almost-full](https://github.com/coq-community/almost-full); [Agda 的直觉主义 Ramsey 定理 (Wahlstedt)](https://wiki.portal.chalmers.se/agda/Main/IntuitionisticRamseyTheorem)
- Podelski, Rybalchenko, *Transition invariants*, LICS 2004. [依记忆, 未核] — [DOI 10.1109/LICS.2004.1319598](https://doi.org/10.1109/LICS.2004.1319598)

### Inferences
- **(2) 对应形状.** 不对应值的形状, 对应 "无公理停机" (纲领 2) 在多路派发时的证明负担.
- **(3) 移植草图.** 若 B 或 C 的构造中, 递归调用有时沿 "保留" 的结构下降, 有时沿 "链" 的结构下降, 而哪一种不可判定, 可用 "两个良基关系之交几乎满" 的引理统一证停机, 不必把派发写进度量.
- **(4) 最便宜的实验.** 只在 B 或 C 的玩具遇到停机检查失败时再试.
- **(5) 冲突.** 无直接冲突; 但我们的递归都是对树的结构递归, 停机通常由检查器直接保证, 本想法可能用不上 (判断).

### Gaps
- 未读正文, 不确定几乎满关系在 `--without-K` 下的可用性 (Agda 版本存在, 选项未核).

## 问题 Z: 跨想法的观察与下一步建议

### Takeaway
11 个想法可以归成三种 "不判定" 的手段: 以界代判 (A, G, I), 把判定推迟到极限或阶段里 (B, C, D, E), 把偏分支补全或延后到闭项 (F, H, J). 我们已有的手段 (一致目标, 字面公共上界, 以复合代替派发) 大致落在第三种; 前两种是相对新的方向, 实验成本也最低.

### Cited Findings
- 在单调函数解释中, 二选一 (LLPO) 不可实现而其界可实现 (λw.1 与 max). [读原文] — [Ferreira §4.2](https://webpages.ciencias.ulisboa.pt/~fjferreira/proof_interpretations.pdf)
- 精确实数计算中非确定性被认为不可避免, 并以多值的软比较实现. [读原文 / 检索摘要] — [arXiv:2202.00891](https://arxiv.org/abs/2202.00891); [arXiv:2410.13508](https://arxiv.org/abs/2410.13508)
- ℕ∞ 的全知性在一切构造数学变体中成立, 不用连续性. [读原文] — [Escardó, CCC 2015](https://martinescardo.github.io/.talks/ccc-2015.pdf)

### Inferences
- **建议的配对** (按 "构造与否定配对" 的约定, 判断): (1) A 的玩具 (神谕一致的优超) 与 D 的否定 `softslack→LPO` 同批派, 两者共用 "只含 ℕ-极限的玩具树" 接口; (2) B 的玩具与一份纸面清单 (仓库里哪些 P 是 Σ⁰₁ 型, 哪些是 Π⁰₁ 型) 同批; (3) F 与 A 的合并问题: "保留的全定义优超者" 是否就是守卫包络, 交给下一轮审查先挑战.
- **一个统一读法** (判断): 我们要的不是 "P 的判定", 而是 "对 P 的一切可能真值一致成立的下界". proof mining 的单调解释, 抽象解释的并, 学习式实现子的极限, 都是这个读法在各自领域的实例. 把目标定理写成 "∀ 神谕 → 参照[神谕] ≼ 输出" 可能比写成 "参照 ≼ 输出" 更容易找到证法, 因为它迫使输出不依赖 P.
- **注意**: 这些想法都不触及 "树侧该有的值没有定义" 这个已知障碍; 它们只回答 "已知参照值时怎样不判定地达到它".

### Gaps
- 未覆盖: 赋值论 / 有效描述集合论中的 "一致化" (uniformization) 与 Σ¹₁ 有界性, 可能对 Ω-分支 (S6) 有启发; 游戏语义中的并行策略; 超限计算 (无限时间图灵机) 的极限规则. 本轮工具调用预算内未查.
- Kohlenbach 书中有没有关于 "序数值的界" 或 "超限递归的优超" 的章节, 未核; 若有, 是想法 A 最直接的文献.
