# X3 滞后的支配与对层一致的定理: 跨领域可移植的想法

范围说明 (不是结论): 本篇按简报的要求发散地收集 "能移植的想法", 不找我方问题的一模一样的先例. 每条想法给五项: (1) 原领域的技术与出处; (2) 对应下面形状的哪一面; (3) 移到我方的具体草图; (4) 最便宜的实验; (5) 可能与已编译否定结果的冲突 (只标出, 不据此丢弃). 第 (2) 到 (5) 项全部是**判断**, 不是定理. 上一轮已调查的 Buchholz 1987 (≪_k, Lemma 3.2(b)), Schwichtenberg 1993 (<_k), Fairtlough 1992 (路径), Setzer Lemma 3.3, Freund Thm 3.10, Strahm 2000, Fernández-Duque–Weiermann 不重复; 个别地方以新角度引用时注明 "见 R1".

我方形状 (中性表述, 供对照): 参照树 r 按规范基本列展开为 r[0], r[1], …; 我方树 t 展开为 t[0], t[1], …; 只要下界 value(t) ≥ value(r); ≼ 已允许任意下标平移 (∀n ∃m). 逐项配对 r[n] ↔ t[n] 已被否定: 局部 t 较弱 (某个子计算在参照保留结点处走链), 欠账要到外面一层或几层极限才还上; 简化模型里滞后随嵌套深度大约翻倍. 希望有一条对结构归纳, 对层 (层号本身是树: Ω, Ω_Ω, Ω_{Ω_Ω}, …) 一致的定理.

## 问题一: 局部落后, 外层追上: 不逐步对应的两个无穷过程, 怎样证一个支配另一个

### Takeaway
最可移植的是三类装置. (i) **把见证的选择从关系里拿出来**: 用一个显式映射 e 把参照的每个位置送到我方 "已经还清欠账" 的位置, 只要求沿参照的一步严格上升, 滞后被 e 的选择吸收 (精化映射, wqo 下界的线性化). (ii) **把滞后显式记账**: 带良基度量的模拟 (CompCert 的 `fsim_index`/`fsim_order`, Namjoshi 的秩函数), 按嵌套深度分量的欠账向量 (Leike–Heizmann 的 nested ranking, Jurdziński 的 progress measure), 以序数为预算的步进索引 (transfinite step-indexing). (iii) **把滞后做成归纳构造子**: eutt 式 "有限多步不同步, 然后同步" 的混合定义, 在我方纯归纳的场合不需要度量. 一个对我方特别要紧的观察 [判断]: ≼ 是归纳关系, 右侧取孩子天然良基, 所以显式度量只在 "把当前不等式推迟到外层" (向外走) 这一步才必需; 设计关系时应把这一步单独做成规则.

### Cited Findings

#### 想法 A (排名 #1): 显式见证映射 —— 沿参照一步严格上升的映射支配恒等

(1) 原领域与出处.
- 精化映射 (refinement mapping): 实现的状态到规格的状态的函数; Abadi–Lamport 证明在合理假设下, 给低层规格加辅助变量 (history, prophecy) 后精化映射一定存在 — [Abadi, Lamport, *The Existence of Refinement Mappings*, TCS 1991 (Microsoft Research 摘要页)](https://www.microsoft.com/en-us/research/?p=145187); 1988 技术报告目录里有 "prophecy variables that add stuttering" 一节 — [SRC RR 29](https://ftp.mirrorservice.org/sites/www.bitsavers.org/pdf/dec/tech_reports/SRC-RR-29.pdf).
- wqo 理论里求极大序型下界的办法是把一个序数记号 (线性序) 经保序映射放进偏序的某个线性化; "线性化" 定义为从线性序到偏序的 order-reflecting 满射 — [Freund, *Bachmann-Howard Derivatives*, arXiv:2105.09915](https://arxiv.org/pdf/2105.09915). 同一传统里, Friedman 树的极大序型早先只有下界 ψ₀Ω_n, 后来才被精确刻画; 对序列的情形, 某个自然的线性化并**不**达到极大序型 — [Rathjen, Van der Meeren, Weiermann, AML 2017 (White Rose 预印本)](https://eprints.whiterose.ac.uk/117847/1/ArticleGapsequencessubmittedtoAMLRevisedVersion2.pdf); [同上, ar5iv 1505.01359](https://ar5iv.arxiv.org/html/1505.01359).
- "严格单调映射 f 满足 f(α) ≥ α" 是序数论的标准事实 [本轮未查到具体出处, 按常识引用].

(2) 对应的面. 逐项配对把 e 固定成 "r[n] ↦ t[n]"; 想法 A 让 e 自由选择我方位置, 可以把参照的内层结点直接送到我方外面一层已经追上的位置. 滞后完全进入 e 的定义, 证明义务只剩局部的一步.

(3) 草图. 在验收文件里, 对参照树 R 的子树 (或路径) 定义 e : Sub(R) → 我方树, 只证三条局部引理:
- `e-suc : e(x) ≺ e(suc x)`;
- `e-lim : ∀ n → e(f n) ≺ e(lim f)`;
- `e-Ω : ∀ c → e(g c) ≺ e(limΩ g)` (同一个 c, 字面相同的下标).
通用引理 `dom : ∀ x → x ≼ e(x)` 对 R 结构归纳即得 (零平凡; 后继用 x ≼ e(x) ≺ e(suc x); 两种极限逐孩子用传递性), 与层无关, 十几行. 最后再证 `e(R) ≼ t`. 关键在 e 的选法: 若 t 在某 Ω-分支走链而参照保留结点 X, 就令 e(X) 取 "外层下一个下标处" 的我方子树 (即 ∀n∃m 里的 m+1), 而不是同一下标处的子树. 与 Fairtlough 的路径 (见 R1) 的不同在于: 这里只要求 e 沿参照的每一步严格上升, 不要求 e 保持基本列或路径结构.

(4) 最便宜的实验. 临时目录里一份纯 `.agda`: 写出与具体系统无关的 `dom` 引理 (泛化到任意满足三条局部引理的 e), 再在 "滞后翻倍" 的简化模型上手写 e (深度 d, 下标 n 送到外层下标约 2^d·n 的位置), 看三条局部引理哪一条过不去. 过不去的那一条正是 "必须向外推迟" 的精确位置.

(5) 可能冲突. `e-Ω` 要求 e(limΩ g) 是在与参照**同一个下标类型**上分支的 Ω-极限; 若我方的孩子下标类型带证据或坐标, 需要下标之间的证据函数, 落入 "开新行前的先验检查" 第二条; 若要按孩子的层号决定 e 的值, 对上 `obs→dec` 一族 (`branch→wdec`, `hand→wdec`). `e-lim` 只要求每个孩子严格低于父结点, 不要求我方 ℕ-极限的项按值递增, 因此不触 `BrwViewNeg.strict→LPO`. e(f n) 与 e(lim f) 都是我方的树, 它们之间的 ≺ 最好由字面路径给出 (公共上界就是 e(lim f) 本身).

#### 想法 B (排名 #2): 带良基度量的 "最终恢复" 模拟

(1) 原领域与出处.
- CompCert 的 `fsim_properties` 以索引类型、良基序 `order` 与 `match_states` 为参数, 单步条件为 "`Plus L2 s2 t s2' \/ (Star L2 s2 t s2' /\ order i' i)`": 目标要么至少走一步, 要么走零步或多步但索引下降. 变体有 `forward_simulation_star_wf` (口吃步须让 L1 状态上的良基度量下降), `forward_simulation_opt`, `forward_simulation_plus`, `forward_simulation_step` (逐步); 特别是 `forward_simulation_eventually`: 源程序可以多走若干步 (`Eventually`) 再恢复 `match_states`, 索引取 `index * nat` 的字典序. 两个模拟的合成 `compose_forward_simulations` 取乘积索引 `(index' * index)`, 序为 `lex_ord (clos_trans _ order') order` — [CompCert, `common/Smallstep.v` 文档](https://compcert.org/doc/html/compcert.common.Smallstep.html); 论文版见 [Leroy, *A formally verified compiler back-end*, JAR 2009](https://xavierleroy.org/publi/compcert-backend.pdf) [PDF 本轮未能解析出文字, 以 Coq 文档为准].
- Namjoshi 的 well-founded bisimulation: 秩函数 rank : S×S×S → W 取值于良基集, 条款 (2b) 源走一步而对方不动时秩下降, (2c) 对方走一步而源不动时秩下降; 原文说要求 "the mapping decrease with each stuttering step", 从而每段口吃有限, 且只需检查单步 (§2 定义, p. 287) — [Namjoshi, *A simple characterization of stuttering bisimulation*, FSTTCS 1997](https://kedar-namjoshi.github.io/papers/Namjoshi-FSTTCS-1997.pdf). 后续工作说这一表述 "solely relies on local reasoning" — [Bisimulation Learning, arXiv:2405.15723](https://arxiv.org/pdf/2405.15723).

(2) 对应的面. "局部弱, 若干层之后追上" 正是 `forward_simulation_eventually` 的形状: 匹配关系暂时断开, 由一个良基索引保证有限步内恢复. 嵌套的滞后对应模拟的合成: 合成后的索引是乘积的字典序, 深度 d 的嵌套给出 d 重字典序, 翻倍的滞后被字典序吸收.

(3) 草图. `Sim : I → Ref → Our → Type`, I 取 (还需外推几层, 本层内还差几步) 的字典序 (ℕ×ℕ 或以布劳威尔树为第二分量). 三条规则: 同步 (两边都是 ℕ-极限, ∀n ∃m 且索引任意重置); 口吃 (我方多展开一步, 第二分量降); **推迟** (当前不等式整体交给外层上下文, 第一分量降, 第二分量可任意重置). 健全性 `Sim i r t → r ≼ t` 对 (r 的结构, i) 的字典序良基归纳. [判断] 由于 ≼ 的右侧取孩子本来就良基, 前两条规则其实不需要度量; 度量只为 "推迟" 这一条存在, 所以 I 的第一分量就是 "欠账要到外面第几层才还".

(4) 最便宜的实验. 在简化模型 (两层嵌套, 逐项配对已失败) 上写出 Sim 与健全性证明, 只实现 "推迟" 规则一处; 看推迟到外层后外层的同步规则能否接住.

(5) 可能冲突. "推迟" 要知道外层上下文, 关系因此依赖上下文; 若决定是否推迟要看分支对目标是 "低/同/高" 中的哪一种, 而这一分类不是字面的, 就对上 `hand→wdec`, `viaE→dec`. 若推迟时要比较内层欠的结点与外层我方结点, 按 "律带公共上界" 须给字面公共上界 (两者同在外层上下文之下, 一般可给). CompCert 的合成用传递闭包与字典序, 在构造性下没有问题.

#### 想法 C (排名 #3): 按嵌套深度分量的欠账向量 (nested ranking, progress measure)

(1) 原领域与出处.
- Leike–Heizmann 的 nested ranking template (Def. 4.7, §4.2): 参数 δ > 0, 函数 f₁,…,f_k, 条件 f_k(x) > 0, f₁(x′) < f₁(x) − δ, 且对 i = 2,…,k 有 f_i(x′) < f_i(x) + f_{i−1}(x). 原文说一个分量 "cannot increase by more than the value of the previous phase's" 函数; 前一分量耗尽后它开始下降. Lemma 4.9: nested 是 multiphase 的特例; multiphase (Def. 4.2) 要求 f_i 在前一阶段结束后才必须下降 — [Leike, Heizmann, *Ranking Templates for Linear Loops*, LMCS 11(1) 2015, arXiv:1503.00193](https://ar5iv.labs.arxiv.org/html/1503.00193); [LMCS 页面](https://lmcs.episciences.org/797).
- Jurdziński 的 small progress measures: progress measure 是获胜策略的见证, 是完全格上单调算子的前不动点, 因此有最小的 progress measure 且可直接计算 — [Jurdziński, STACS 2000, LNCS 1770, 290–301 (摘要页)](https://www.dcs.warwick.ac.uk/people/academic/Marcin.Jurdzinski/Papers/Jur00-STACS.abstract). [按优先级逐分量比较、较不重要的分量可重置的具体约定, 本轮未核原文, 凭记忆.]

(2) 对应的面. "滞后随嵌套深度翻倍" 与 f_i′ < f_i + f_{i−1} 同形: 内层欠账可以增长, 但增量受外层欠账的余额约束, 外层欠账严格下降. progress measure 的 "外层事件发生时内层分量可重置" 对应 "外层极限追上后, 内层欠账一笔勾销".

(3) 草图. 欠账向量 D = (D₁, …, D_k) 按**语法嵌套深度** (路径上穿过的 Ω-分支构造子个数) 编号, 不按层号的值编号. 关系 `Sim D r t`; 规则: 深度 d 的 ℕ-极限处, D_d 下降, 或 D_d 增加不超过 D_{d−1} 而 D_{d−1} 下降; 穿过一个外层极限时, 比它深的分量重置. 良基性取定长向量的字典序 (标准库有字典序良基的构造), 深度无界时把 D 编成一棵布劳威尔树 (类 ω^ω 的势). Jurdziński 的 "最小 progress measure 可迭代求出" 提示: 简化模型里可以先用不动点迭代算出每层的最小欠账表, 再决定模板.

(4) 最便宜的实验. 纸面或脚本: 在简化模型里列出深度 d、下标 n 时所需的最小下标平移 L(d, n), 检查是否满足 L(d+1, ·) ≤ L(d, ·) + L(d−1, ·) 一类的 nested 不等式 (有限测试). 满足就直接得到度量的形状.

(5) 可能冲突. 若欠账分量按层号 (树) 编号, 决定 "哪一分量" 需要比较层号, 对上 `¬tri`, `Trich₂→WLPO`; 用语法嵌套深度编号可避开. 当前阶段记录里 "跨层单调接口被否定, 根源是位置摊平" 一条要对照: 欠账向量若把不同层的位置压平到同一坐标, 可能重蹈覆辙, 应保持向量按深度分开.

#### 想法 E (排名 #5): 把有限滞后做成归纳构造子 (eutt 式混合定义)

(1) 原领域与出处.
- Interaction Trees 支持 "equivalence up to weak bisimulation" 的等式理论 (eutt); tau 是弱互模拟忽略的内部步 — [Xia et al., *Interaction Trees*, POPL 2020, arXiv:1906.00046](https://arxiv.org/abs/1906.00046v2). [eutt 在每个余归纳步内用归纳构造子吸收有限多个 tau, 这一定义细节本轮未核原文, 凭记忆.]
- Danielsson 把许多 up-to 技术写成保尺寸的函数, 并说这一类与 Pous 的 "functions below the companion" 很接近; 附 Agda 代码 — [Danielsson, *Up-to Techniques using Sized Types*, POPL 2018](https://www.cse.chalmers.se/~nad/publications/danielsson-up-to-using-sized-types.html).

(2) 对应的面. "有限但无界的局部滞后, 之后同步" 不需要显式度量: 归纳类型本身保证滞后有限.

(3) 草图. 我方完全是归纳的, 所以只需 μ 而不需 ν: `data Sim : Ref → Our → Type` 带 `sync-lim : (h : ℕ → ℕ) → (∀ n → Sim (f n) (g (h n))) → Sim (lim f) (lim g)`, `lagR : Sim x (g m) → Sim x (lim g)` (我方多展开), `sync-Ω : (∀ c → Sim (f c) (g c)) → …` (同一个 c), 以及想法 B 的 "推迟" 构造子. 健全性对 Sim 结构递归, 停机由检查器保证.

(4) 最便宜的实验. 三十行左右的临时 `.agda`, 只含构造子与健全性; 然后试着把已被否定的逐项配对实例改写成带 `lagR` 的 Sim 项, 看缺的是哪个构造子.

(5) 可能冲突. Danielsson 的原法依赖 sized types; [据我所知, 新版 Agda 中 `--sized-types` 与 `--safe` 不兼容, 未核实], 所以只借形状, 不借 sized types. "推迟" 构造子会把问题带回想法 B/C 的上下文与度量.

#### 想法 F (排名 #6): 中间参照: 把滞后搬到参照侧

(1) 原领域与出处. CompCert 把编译拆成多遍, 每遍一个前向模拟, 用 `compose_forward_simulations` 合成 (乘积索引, 字典序) — [CompCert `Smallstep.v`](https://compcert.org/doc/html/compcert.common.Smallstep.html). 组合数学里 α-large 集合的划分下界以 Hardy 层级定义 "大", 给出 α 关于 β, m, r 的下界 (即每一层的显式损耗) — [Bigorajska, Kotlarski, *Partitioning α-large sets: some lower bounds*, Trans. AMS 358 (2006) 4981–5001](https://www.ams.org/tran/2006-358-11/S0002-9947-06-03883-9/); 推广到 ε_ω 以下 — [De Smet, Weiermann, arXiv:1001.2437](https://arxiv.org/pdf/1001.2437) [两篇只读了摘要, 损耗常数未核].

(2) 对应的面. 逐项配对在 r 与 t 之间失败, 但可能在 t 与一个 "带滞后的参照" r̃ 之间成立; 剩下的 r ≼ r̃ 完全是参照侧的事, 那里记号的序可判定, 研究与验收文件允许用.

(3) 草图. 在记号侧写另一套基本列 S̃: 在参照保留结点、我方走链的那一类情形, 让 S̃ 也走链. 分两步: (i) t 与 tree_{S̃} 逐项一致 (标签式检查, 但对 S̃ 而不是对规范系统 S); (ii) 记号侧的一般引理: 两套都 "正确" (项都在下面且共尾) 的基本列给出互相 ≼ 的树, 证明对记号归纳, 用记号的可判定序. 这就是 "序数值验收: 树与过基本列验收的树互相 ≼" 的一个具体实现, 中间的那棵树换成了 S̃ 的树.

(4) 最便宜的实验. 只在逐项配对被否定的那一个最小情形写 S̃ 的一条规则, 检查 (i) 在该情形是否逐项成立.

(5) 可能冲突. (i) 是对 S̃ 的 `Lab` 式检查; AGENTS 说过 `Lab` 的树就是记号的翻译, 所以只能放在验收文件, 并在翻译账上写明 S̃ 来自我方规则 (方向是树到记号, 不是记号到树). (ii) 对 Ω-共尾的记号, 两套基本列的分支下标类型必须相同, 否则又要跨下标比较 (`noBT`). 此外 wqo 文献里 "自然的线性化不达到极大序型" 的例子提醒: 中间参照本身也可能损失强度.

#### 想法 G (排名 #7): 以序数为预算的步进索引 (transfinite step-indexing, later credits)

(1) 原领域与出处.
- Svendsen–Sieczkowski–Birkedal 指出步进索引把每个逻辑步绑到一个具体归约步上, 这一绑定不必要; 用超限索引放松, 允许每个具体步对应有限但任意多个逻辑步; 第一分量数具体归约, 第二分量数下一个具体步之前的逻辑步, 取字典序 [据检索摘要, HAL 原页被拦, 细节未核] — [*Transfinite Step-Indexing: Decoupling Concrete and Logical Steps*, ESOP 2016](https://hal.archives-ouvertes.fr/hal-01408649v1).
- Spies–Krishnaswami–Dreyer 用超限步进索引 "compute compositional termination bounds" (摘要); 引言说先前的安全终止证明要用户给出步数上界 n, 他们改为组合地推断每个表达式贡献的界; 并说 Schwinghammer 等人先用超限索引处理 may/must 等价, Svendsen 等人用它允许每步计算有限多次索引下降 (§1, p. 13:2–13:3) — [*Transfinite Step-Indexing for Termination*, POPL 2021](https://www.cl.cam.ac.uk/~nk480/transfinite-step-indexing.pdf).
- 可数非确定性的 must-等价要用 ω₁ 索引的关系 (作者注明最小非递归序数也够) — [Birkedal, Bizjak, Schwinghammer, LMCS 9(4) 2013](https://lmcs.episciences.org/940).
- Transfinite Iris: 有限索引不满足 "existential property", 因而只能证安全性; 换成超限索引后可证终止与保终止的精化 — [Transfinite Iris 项目页](https://iris-project.org/transfinite-iris/).
- Later credits 把 "消去一个 later 的权利" 变成可拥有的资源 — [Spies et al., ICFP 2022](https://plv.mpi-sws.org/later-credits/).

(2) 对应的面. 三处对应: 每步的滞后是 "有限但事先不知多少" (索引 ω·k 在极限处降到 ω·(k−1)+n, n 看到上下文后再选); Ω-分支对应可数非确定的选择 (所以预算要升一层, 对应 ω₁ 索引); ∃m 的见证对应 existential property.

(3) 草图. 带预算的关系 `r ≼[β] t`, β 本身是一棵布劳威尔树 (同一类型, 自给自足). 我方 ℕ-极限处预算从 lim 降到它的某个孩子, 孩子的下标在看到参照的下标 n 之后才选, 这就是 "看了 n 再定局部滞后". 嵌套深度 d 处预算约为 ω^d; Ω-分支处预算是上一层的树 (同一个 c 上分支), 对层一致. 根上 `r ≼[β₀] t → r ≼ t`, 预算只约束证明结构.

(4) 最便宜的实验. 在简化模型里把预算取 ω·2 (两层嵌套), 写出 `≼[_]` 的归纳族与健全性.

(5) 可能冲突. 预算的下降必须是 "取 β 的字面孩子", 不能是 "证出 β′ ≺ β", 否则又需比较 (见 R3 关于 "公共上界必须是数据" 的结论). Ω-层预算在 c 上分支, 只允许同一个 c 配对; 跨 c 的预算比较对上 `noBT`.

#### 想法 I (排名 #9): 分级关系与滞后函数的代数

(1) 原领域与出处.
- 函数式大步语义给解释器加时钟使之成为全函数, 发散等价于对每个初始时钟都超时 — [Owens, Myreen, Kumar, Tan, *Functional Big-Step Semantics*, ESOP 2016](https://bibtex.github.io/ESOP-2016-OwensMKT.html); 编译正确性的常见陈述是在目标侧把时钟加上一个存在量化的 ck 再求值, 因为状态关系要求两边时钟相等 — [Dafny 到 CakeML 的验证编译器, arXiv:2512.05262](https://arxiv.org/pdf/2512.05262) [CakeML 后端原文中的引理形状未核].
- Vojtáš 的广义 Galois–Tukey 连接是关系系统之间的一对映射, 满足关系间的蕴涵; 由此得到 dominating/bounding 数之间的不等式 — [arXiv:2410.18595](https://arxiv.org/pdf/2410.18595); Blass 的范畴 PV 是 Vojtáš 的 GT 的对偶, 即 de Paiva 的 Dialectica 范畴 — [Blass, *Questions and answers*, arXiv:math/9309208](https://arxiv.org/abs/math/9309208).
- 新角度引用 (见 R1): Buchholz 1987 Lemma 3.4 说 a ≪_k b, k ≤ m ⇒ a ≪_m b, 即 k 越大越宽松.

(2) 对应的面. 把 "滞后" 当一等数据, 有合成律; 翻倍就是对分级做一次运算. Galois–Tukey 的观点是: ∀n∃m 的证明就是一对映射, 下标平移函数就是 "答案映射", 证明的传递性就是映射的合成.

(3) 草图. ℕ-层: `Dom h r t := ∀ n → r[n] ≼ t[h n]`; Ω-层: 分级是下标类型上的映射, 我方只能取恒等 (同一个 c). 律: `Dom h r s → Dom k s t → Dom (k ∘ h) r t`; 折叠律 `Dom h r t → Dom (Φ_ℓ h) (ψ r) (ψ t)`, Φ_ℓ 在简化模型里约为 "加倍". 深度 d 的滞后就是 Φ^d(h), 一条定理说 Φ 的性质, 对层一致. 也可把 Buchholz 的 k 当作分级: 每深一层把 k 换成 2k.

(4) 最便宜的实验. 用想法 P 的数据把 Φ 拟合出来, 看它是否在所有测到的深度上同形.

(5) 可能冲突. 若要用 "h ≤ h′ 时 Dom h ⊆ Dom h′", 需要 t[·] 对下标弱单调 (t[m] ≼ t[m+1]). `BrwViewNeg.strict→LPO` 只否定严格递增; 弱单调能否对读回域成立要先查, 按 AGENTS "量化域先取带证据的读回域" 只在规范实例上要求. 不能要求时, 只用精确的 h, 不做放宽.

#### 想法 J (排名 #10): 欠账位, 预言变量与后向模拟

(1) 原领域与出处.
- Etessami–Wilke–Schuller 在一个奇偶博弈框架里统一 direct, fair 与新提出的 delayed simulation; delayed simulation 下复制者可以晚一些访问接受态, 商化后保持语言 (fair simulation 不保持); 用 Jurdziński 的算法求解 — [ICALP 2001 / SIAM J. Comput. 34(5) 2005](https://www.research.ed.ac.uk/en/publications/fair-simulation-relations-parity-games-and-state-space-reduction-/).
- Lynch–Vaandrager 统一陈述 refinement, forward, backward, 前后混合模拟, 以及 history 与 prophecy 关系 (后两者是 Abadi–Lamport 辅助变量的抽象), 并给出健全与完备结果 — [Information and Computation 121(2) 1995](https://dspace.mit.edu/handle/1721.1/149207).
- 延迟博弈: 一方可以推迟落子以获得对对方未来落子的前瞻; ω-正则条件下所需前瞻有指数上界且指数下界是紧的 — [Klein, Zimmermann, LMCS 2017, arXiv:1412.3701](https://arxiv.org/pdf/1412.3701).

(2) 对应的面. delayed simulation 的 "待兑现义务" 就是 "欠账, 以后再还"; prophecy/后向模拟对应 "当前位置该配给谁, 要看外层以后怎么展开".

(3) 草图. (a) 欠账位: `Sim r t ob`, ob : Maybe (参照子树); 我方走链而参照保留结点 X 时置 ob := X; 下一个外层极限的同步规则必须先兑现 ob (证 X ≼ 外层我方结点). (b) 预言: 先固定外层恢复所用的下标 m, 再做内层匹配, 即把外层的 ∃m 提到内层之前, 让内层关系以 m 为参数. (c) 后向: 从我方每个位置出发定义它覆盖的参照位置集合, 证覆盖集向下封闭且共尾.

(4) 最便宜的实验. 在被否定的逐项配对反例里标出 "欠下的是哪个参照结点, 在第几层还上", 只给这一种情形加 ob 位.

(5) 可能冲突. 兑现 ob 时比较的两个对象要有字面公共上界 (律带公共上界); 两者都在外层上下文之下, 一般可给. 覆盖集若要求对 Ω-分支的不同 c 作比较, 对上 `noBT`; 只做同一个 c 的覆盖则无此问题.

#### 想法 N (排名 #14): 势函数, 多重集与信用: 局部损失以后偿还

(1) 原领域与出处. Later credits 把消去 later 的权利当作资源, 可在分离逻辑里拆分转移 — [ICFP 2022 程序页](https://icfp22.sigplan.org/details/icfp-2022-papers/11/Later-Credits-Resourceful-Reasoning-for-the-Later-Modality). 摊还分析的势方法 (Tarjan 1985), 多重集序 (Dershowitz–Manna 1979: 一个元素可换成有限多个更小的元素), 分离逻辑中的时间信用 (Charguéraud–Pottier) [三条本轮未在线核对, 按已知书目引用, 无链接].

(2) 对应的面. 局部欠账记成显式的 "债", 外层兑现; 一笔大债可以拆成有限多笔小债.

(3) 草图. 关系 `r ≼ t + Σ D`, D 是欠下的参照子树的列表; 规则允许把 D 中一项换成有限多项更小的 (多重集下降, 保证记账终止); 外层极限处要求我方下一项 t[m+1] ≽ t[m] + Σ D ("外层的余量付清内层的债"). 根上 D = [].

(4) 最便宜的实验. 在简化模型里检查 "外层下一项的余量覆盖内层所欠" 这一条不等式是否对所有测到的深度成立.

(5) 可能冲突. Hessenberg 自然和在布劳威尔树上一般需要 Cantor 范式与比较, 构造性下不可用; 只能用普通加法, 债放右边. 比较欠下的 X 与我方结点要有公共上界.

#### 想法 O (排名 #15): up-to 技术的健全性教训

(1) 原领域与出处. "bisimulation up to" 在强情形顺畅, 在弱情形要改用 up to expansion 或 almost-weak bisimulation — [Sangiorgi, Milner, *The problem of "weak bisimulation up to"*, CONCUR 1992](https://www.research.ed.ac.uk/en/publications/the-problem-of-weak-bisimulation-up-to/); expansion 是 Arun-Kumar–Hennessy 的效率前序 (Acta Informatica 29(9), 1992) [据同一检索结果的转述]. Pous 用 companion 统一 up-to 技术与 parameterized coinduction — [Pous, *Coinduction All the Way Up*, LICS 2016](https://lics.siglog.org/2016/Pous-CoinductionAlltheWa.html).

(2) 对应的面. 用上下文吸收局部不匹配 ("up to context"); 以及一个警告: 带滞后的关系再 "up to 带滞后的关系" 可能不健全.

(3) 草图. 若采用想法 B/G 的度量或预算, 不要随意加 "up to ≼" 规则 (在度量下降的证明里前后复合 ≼ 可能把度量重置, 与弱互模拟 up to 弱互模拟不健全同形); 健全的做法是 up to 一个从不滞后的结构关系 (如字面路径, 或 Buchholz 的 ≪_k 一类, 见 R1), 或只在度量部分之外复合 ≼. "up to context" 的版本: 允许内层只证 `R ⊆ b(C(R))`, C 是折叠的外层上下文.

(4) 最便宜的实验. 在加任何 "up to" 规则之前, 先在简化模型里找一个让度量无限重置的反例; 找不到再写健全性证明.

(5) 可能冲突. 与已编译否定结果不直接冲突; 纯归纳的 ≼ 证明里传递性永远健全, 风险只出现在度量或预算式的证明.

#### 想法 P (排名 #16, 但应最先做): 数据驱动的对齐

(1) 原领域与出处. Churchill–Padon–Sharma–Aiken 从具体执行里找两条迹的对齐, 构造乘积程序, 用测试学不变式, 再交 SMT; 例子是 GNU C 手工向量化的 `strlen` — [PLDI 2019](https://theory.stanford.edu/~aiken/publications/papers/pldi19.pdf).

(2) 对应的面. 在证明之前先测出滞后函数 m(n, d) 的实际形状.

(3) 草图. 对小的 n, m, d 计算 r[n] 与 t[m] (研究文件里可借记号把树读回成项再比较), 求使 r[n] ≼ t[m] 的最小 m, 列表并拟合 (是 2^d·n, n + 2^d, 还是更大).

(4) 最便宜的实验. 它本身就是实验, 产出是想法 B, C, G, I 的参数. 标为有限测试.

(5) 可能冲突. 只是测试, 不是证明; 读回比较用到记号, 只能在研究文件里做.

#### 想法 Q (排名 #17): 约化对: 内层弱, 外层严

(1) 原领域与出处. 项重写的 dependency pair 方法用约化对 (≳, >): 重写规则只需弱下降, 严格下降只在 dependency pair 上要求 (Arts–Giesl, TCS 2000) [本轮未在线核对, 无链接].

(2) 对应的面. 不要求内层严格追上, 只在外层的同步点要求严格.

(3) 草图. 把关系拆成一对: 内层只证带滞后的弱关系, 严格的 ≺ 只在参照做严格一步、我方必须兑现的同步点证明. 与想法 J 的欠账位合用.

(4) 最便宜的实验. 在想法 E 的 Sim 里把构造子分成 "弱" 与 "严" 两组, 看健全性证明是否只需在严组用 ≺.

(5) 可能冲突. 无直接冲突; 注意 "严格" 要求不能落到我方 ℕ-极限的相邻项之间 (`strict→LPO`).

### Inferences
- [判断] 十二条想法可以归为三种机制: 见证的选择脱离关系 (A, J), 滞后显式记账 (B, C, G, I, N, Q), 滞后做成构造子 (E). A 与 E 最便宜, 可以先在简化模型里各写一份临时文件; B, C, G 是 "推迟到外层" 那一步需要度量时的三种记账口径, 应在 P 的数据出来后再选.
- [判断] 简化模型里 "滞后约每层翻倍", 在 C 的 nested 模板 (f_i′ < f_i + f_{i−1}) 与 B 的乘积字典序之下都是有限的, 不构成障碍; 真正的风险是 "推迟" 规则是否需要按层的低/同/高分情形, 这一点决定会不会撞 `obs→dec` 一族.
- [判断] 想法 F 不改定义, 只把滞后移到记号侧, 符合 "第 4 层不反过来改前 3 层"; 代价是它只给验收, 不给 "树自足" 的进展, 翻译账上要单列.
- [判断] 几种原领域都有一个共同教训: 局部度量 (Namjoshi, Leike–Heizmann) 的价值在于 "只检查单步". 对我方意味着: 若一条一致定理能写成 "每条折叠规则让度量如何变化" 的有限张表, 就把逐站证明变成了对规则形状的有限检查 (见问题二想法 H).

### Gaps
- CompCert JAR 2009 原文的 PDF 本轮无法解析成文字, 有关模拟图的论文表述以 Coq 文档代替; 论文里关于 "无限口吃" 问题的原话未核.
- Svendsen–Sieczkowski–Birkedal 2016 的正文本轮被拦 (HAL 返回机器人验证, core.ac.uk 403), 字典序索引的描述来自检索摘要.
- eutt 的确切定义 (归纳与余归纳的嵌套方式), Jurdziński 的分量比较约定, Arun-Kumar–Hennessy 的 expansion 的定义, 都凭记忆或二手转述, 未核原文.
- Bigorajska–Kotlarski 的具体损耗常数 (是否恰为 "每层翻倍") 只读了摘要, 不能断言与我方翻倍同形.
- Tarjan 1985, Dershowitz–Manna 1979, Charguéraud–Pottier, Arts–Giesl 2000 本轮没有在线核对.

## 问题二: 对一整个层级证一条一致的定理, 而不是逐站证明

### Takeaway
可移植的有四种形状. (i) **开放递归加良基打结**: 把第 ℓ 层的定理写成以 "所有更低层的定理" 为参数的一步, 再对层树的结构良基递归打结 (Kovács 的广义宇宙层级, Abel–Öhman–Vezzosi 的参数化逻辑关系). (ii) **有限规则形状上的全局条件**: 规则只有有限多种形状, 把 "欠账如何在规则间转移" 画成有限张图, 用 size-change / 循环证明的全局迹条件一次判定, 再转成一个度量 (Sprenger–Dam 说循环证明与树形证明可互相翻译). (iii) **基本引理式的一致性**: 把折叠写成抽象接口上的项, lax / pre-logical relation 的基本引理对一切项一次成立, 而且这类关系可以合成. (iv) **层间换算律**: 像 Schmerl 公式那样, 只证一条 "内层的迭代换成外层的一步" 的换算律, 再迭代.

### Cited Findings

#### 想法 D (排名 #4): 开放递归 + 在层树上良基打结

(1) 原领域与出处.
- Kovács 给累积宇宙层级的语法与语义, 层号 "may come from any set equipped with a transitive well-founded ordering", 并用归纳-递归建模超限层级; 层号可作一等类型 — [Kovács, *Generalized Universe Hierarchies and First-Class Universe Levels*, CSL 2022, arXiv:2103.00223](https://arxiv.org/abs/2103.00223); [LIPIcs 版](https://drops.dagstuhl.de/opus/volltexte/2022/15748/). [摘要只说 IR 建模超限层级; "第 j 层由所有 i < j 的宇宙作参数定义" 的细节未核正文.] 对应代码库 `AndrasKovacs/universes` 已在本地 CodeGuide 里 (见 R3); 新角度是借它的**证明组织**, 不是借定义.
- Abel–Öhman–Vezzosi 在 Agda 里形式化转换判定, 正确性靠一个 Kripke 逻辑关系, 该关系以项的等价为参数; 参数化的基本引理实例化两次 (典范性与单射性一次, 算法完备性一次); 依赖归纳-递归但不依赖 UIP; 约一万行 — [*Decidability of Conversion for Type Theory in Type Theory*, POPL 2018](https://www.cse.chalmers.se/~abela/popl18.pdf).

(2) 对应的面. 简报要的 "一条对层一致的定理": 写一次 `Step`, 对层树打结.

(3) 草图. `Step : (ℓ : Lv) → (IH : ∀ ℓ′ → ℓ′ ⊏ ℓ → Thm ℓ′) → Thm ℓ`, ⊏ 取层树的**结构**子项关系 (龙骨上的字面下降), `thm = wfRec Step`. 仿 Abel 等人: 第 ℓ 层的关系 (如想法 B 的 Sim 或想法 I 的 Dom) 以更低层的关系包为参数, Ω-分支情形用参数里给的低层关系处理分支下标. 把滞后函数作为 Thm 的输出: Step 由低层的滞后算出本层的滞后, 即想法 I 的 Φ 写在 Step 里. 参数化基本引理实例化两次的手法提示: 同一个 Step 可实例化为 "参照与我方" 一次, "我方与我方 (不同下标)" 一次.

(4) 最便宜的实验. 取两站已有的逐站证明, 把共同部分抽成带 IH 参数的 Step, 看两站能否都由同一个 Step 实例化得到 (只做类型检查, 不做新数学).

(5) 可能冲突. ⊏ 必须是结构的而非值的 ≺; Step 内部不能按 "ℓ′ 与 ℓ 是否同层" 的值比较分情形 (`dec→WLPO`, `¬tri`). 归纳-递归在 `--safe` 下可用 [判断, 未专门核对版本]; Kovács 的层号只到可数, 不含 Ω-共尾元, 不触壁垒 (见 R3); 我方的层号若含 Ω-共尾元, 要对照 `Barrier` 的前提逐条核.

#### 想法 H (排名 #8): 有限规则形状上的全局迹条件 (循环证明, size-change, almost-full)

(1) 原领域与出处.
- Brotherston–Simpson 的 LKIDω 允许非良基的无穷证明, 用全局迹条件保证健全: 每条无穷路径上 "some inductively-defined predicate is unfolded infinitely often along the path"; 他们猜想归纳与正则的无穷下降等价 — [LICS 2007 版](https://core.ac.uk/download/28964889.pdf); [JLC 2010 版](https://core.ac.uk/download/28962429.pdf).
- Sprenger–Dam 给出一阶 μ-演算中循环证明与树形证明之间的有效翻译, 证明两者等价 — [FoSSaCS 2003, LNCS 2620, 425–440](https://bibtex.github.io/FoSSaCS-2003-SprengerD.html).
- Size-change 原理: 若每条无穷调用序列都迫使某些数据无穷下降, 程序终止; 可由 Büchi 自动机判定, PSPACE-难 — [Lee, Jones, Ben-Amram, POPL 2001](https://bibtex.github.io/POPL-2001-LeeJB.html); [Wikipedia 条目](https://en.wikipedia.org/wiki/Size-change_termination_principle).
- Vytiniotis–Coquand–Wahlstedt 指出 disjunctive well-foundedness, size-change 与 wqo 共享相近的 Ramsey 式论证, 并在构造性类型论里用 almost-full 关系处理 — [ITP 2012, LNCS 7406, 250–265](https://researchr.org/publication/VytiniotisCW12).

(2) 对应的面. 我方折叠的规则形状有限 (零, 后继, ℕ-极限, Ω-极限 × 低/同/高), 欠账在规则之间的转移也就只有有限种; 全局条件一次检查, 对一切层成立, 替代逐站.

(3) 草图. 对每种规则形状画一张 "欠账转移图": 欠账向量 (想法 C) 的各分量经这条规则是严格降, 不增, 还是 "增量不超过外层分量". 求这些图在合成下的闭包 (有限), 检查每个幂等的环上是否有某分量严格降. 若成立, size-change 理论保证存在一个 (字典序或析取的) 度量; 把这个度量写进 Agda, 一次良基归纳, 对层一致. 循环证明的读法: 逐站证明之间的 "同形" 就是循环证明里的回边, Sprenger–Dam 的翻译提示回边可以换成对近似序数的归纳.

(4) 最便宜的实验. 纸面: 十二张图 (4 种构造子 × 3 种层关系), 手算闭包与幂等环. 属纸面分析, 不是定理.

(5) 可能冲突. 图是按 "低/同/高" 分情形画的; 若证明在运行时要知道是哪一情形, 对上 `obs→dec` 一族. AGENTS 的 "树的语言" 说规则形状只说效果, 不是可执行的分情况, 所以图应按 "效果" 而不是按分支画, 是否可行未知. Ramsey 式的 size-change 健全性证明是经典的, 构造性版本要走 almost-full 关系.

#### 想法 K (排名 #11): lax / pre-logical relation 与参数性: 基本引理一次给出一致性

(1) 原领域与出处. Lax logical relation 是逻辑关系的范畴化推广, 保持积类型但不必保持指数; 普通二元逻辑关系不能合成; Kinoshita–Power 给出 lax 关系可合成的条件; Honsell–Sannella 的 pre-logical relation 保留基本引理且可合成 — [Plotkin, Power, Sannella, Tennent, *Lax Logical Relations*, ICALP 2000, LNCS 1853, 85–102](https://era.ed.ac.uk/items/7935f804-4808-44a9-aac4-eaf53cf2ef37); [TYPES 邮件列表 Sannella 的说明](https://lists.seas.upenn.edu/pipermail/types-list/2006/001053.html).

(2) 对应的面. 一致性: 基本引理对一切由接口生成的项成立, 层只是项的一部分; 合成: 经中间模型 (想法 F) 传递时需要关系可合成, 普通逻辑关系做不到.

(3) 草图. 把折叠写成抽象接口 (零, 后继, ℕ-极限, 第 ℓ 层的 Ω-极限, 第 ℓ 层的折叠) 上的项, 这正是 AGENTS 所说 "按层号分级的模拟接口". 定义参照模型与我方模型之间的 lax 关系 R: 零、后继保持; ℕ-极限 lax 保持 (R(f n, g(h n))); Ω-极限只在**同一个 c** 上保持 (指数类型上不要求保持, 即 "lax at exponentials"). 基本引理: 每个闭的折叠项在两个模型里 R-相关, 一次证完.

(4) 最便宜的实验. 写出接口记录, 检查现有的逐站引理是否恰为 "基本引理在某个构造子处的一个情形"; 若是, 一致性已在形状上成立, 剩下打结 (想法 D).

(5) 可能冲突. 基本引理在 Ω-分支函数处若要求 "相关的参数映到相关的结果" 而参数不是同一个 c, 就要跨下标比较, 对上 `noBT`, `dec→WLPO`; 所以 Ω-下标类型上只能取对角关系. 折叠对高层参数不按值单调 (已知), 所以 R 不能是值的 ≼ 本身, 只能是更细的结构关系.

#### 想法 L (排名 #12): 层间换算律 (Schmerl 公式, reflexive induction)

(1) 原领域与出处. Beklemishev 的章节给出 Schmerl 精细结构关系的更一般版本, 以及一致反射与局部反射层级之间的新的保守性结果 — [Beklemishev, *Proof Theoretic Analysis by Iterated Reflection*, Springer 2015 章节](https://doi.org/10.1007/978-3-319-22156-4_9); Beklemishev–Pakhomov 得到不同复杂度层次的迭代反射之间的保守关系, 称为 Schmerl 公式的类比 — [arXiv:1908.10302](https://arxiv.org/abs/1908.10302v1); 一篇关于反射秩的论文反复使用 Schmerl 的 reflexive induction, 并报告 α 次迭代 Π¹₁ 反射的证明论序数是 ε_α — [escholarship PDF](https://escholarship.org/content/qt1159j6ck/qt1159j6ck.pdf?t=pzmpu4). [Schmerl 公式的确切陈述本轮未核原文.]

(2) 对应的面. 只证一条 "相邻两层之间" 的换算律, 再迭代; 内层的无界迭代在外层被换成一个固定的序数增量, 这正是 "内层欠账在外层极限还上".

(3) 草图. 寻找形如 "第 ℓ 层上长度为 n 的链, 被第 ℓ⁺ 层上以 (n 的某个序数变换) 为参数的一步所支配" 的换算律, 一次证明, 作为想法 D 的 Step 的核心. reflexive induction 的读法: 假设对一切更低层的换算律已成立 (作为函数参数), 证本层; 在 Agda 里就是良基递归, 内容在于 Step 的陈述应取换算律的形状.

(4) 最便宜的实验. 在简化模型里核对 "内层长度 n 的链 ≼ 外层的一步" 时外层参数需要多大 (纸面或有限测试).

(5) 可能冲突. 原领域是理论间的保守性, 移植只是形状上的类比 [判断]. 无已知的直接冲突.

#### 想法 M (排名 #13): 遗传上界 (hereditary majorization)

(1) 原领域与出处. Howard 引入可上界性, Bezem 推广为强可上界性, 给有限型算术加 bar recursion 提供模型; Kohlenbach 1992 提出逐点的遗传上界并讨论其与通常概念的关系; 单调函数解释用 Bezem 的强可上界泛函 — [检索汇总: arXiv:1512.07113 等](https://arxiv.org/pdf/1512.07113); [Ferreira, *Proof interpretations* 讲义](https://webpages.ciencias.ulisboa.pt/~fjferreira/proof_interpretations.pdf) [具体定义本轮未逐字核].

(2) 对应的面. 只要下界, 所以见证只需上界而不需精确; 更高层的滞后是 "滞后的滞后" (对分支下标的泛函), 遗传上界按类型递归, 对层一致.

(3) 草图. 按层递归定义 `Maj_ℓ`: ℕ-层上 h* 上界 h (Bezem 式, 要求 h* 单调); Ω-层上滞后是从低层下标到滞后的泛函, H* 上界 H 当且仅当对一切 c* 上界 c 有 H* c* 上界 H c. Howard 式定理: 每个折叠都遗传可上界, 对折叠结构归纳.

(4) 最便宜的实验. 检查简化模型里的滞后函数是否单调 (Bezem 要求), 以及 "翻倍" 是否是它的上界.

(5) 可能冲突. "c* 上界 c" 在 Ω-层需要低层树上的序; 只作前提使用, 不判定, 但 Howard 式定理需要折叠对 c 单调, 而折叠对高层参数不按值单调 (已知; 当前阶段记录里跨层单调接口已被否定). 所以只能对结构关系而不是对 ≼ 做上界, 风险较大.

### Inferences
- [判断] D 与 K 互补: K 给 "对一切项一次成立" 的形状 (基本引理), D 给 "对一切层一次成立" 的打结. 合起来就是: 接口 + 参数化基本引理 + 层树上的良基递归. 这与 AGENTS 的 "按层号分级的模拟接口, 满足哪些律就有值" 同形, 区别在于把滞后函数作为基本引理的输出, 而不是要求逐项一致.
- [判断] H 是把 "逐站证明之间的同形" 机械化的唯一候选: 它把对层的一致性归约为对有限多种规则形状的检查. 它与 D 可以合用: H 给出度量, D 用这个度量打结.
- [判断] L 与 M 主要提供陈述的形状 (换算律, 遗传上界), 能否直接用要看折叠对参数的单调性; 已知折叠对高层参数不按值单调, 所以两者都要换成结构关系上的版本.

### Gaps
- Kovács 正文中 "第 j 层由所有更低层的宇宙为参数定义" 的具体写法未核; 是否已有 "定理 (而不只是定义) 按层良基打结" 的公开 Agda 例子, 本轮未找到.
- Schmerl 公式与 reflexive induction 的确切陈述未核原文.
- 是否有人把 size-change 图用于证明 "支配" 而不是 "终止", 本轮未找到; 想法 H 的这一部分是纯纸面构想.
- Honsell–Sannella pre-logical relations 原文未读, 可合成性的条件以二手说明为准.

## 问题三: 排名总表与最便宜实验的顺序

### Takeaway
按 "可移植性 × 与已知否定的冲突风险 × 实验成本" 综合排名 (判断). 前四名: A 显式见证映射, B 带度量的最终恢复模拟, C 欠账向量, D 开放递归加层树打结. 实验顺序应先做最便宜的 P (测出滞后表), 再做 A 与 E (各一份几十行的临时文件), 由结果选 B/C/G 中的哪种记账口径, 最后用 D (必要时加 H) 把它做成对层一致的一条定理.

### Cited Findings
- 排名所依据的原领域事实分别见问题一与问题二各条的出处; 本节不引入新的事实.

### Inferences
- [判断] 排名总表 (编号与上文一致):

| 排名 | 想法 | 主要对应的面 | 最便宜实验 | 主要冲突风险 |
|---|---|---|---|---|
| 1 | A 显式见证映射 (精化映射, wqo 线性化下界) | 摆脱逐项配对 | 通用 `dom` 引理 + 简化模型手写 e | Ω-下标的证据函数; `branch→wdec` |
| 2 | B 带良基度量的最终恢复 (CompCert, Namjoshi) | 欠账推迟到外层 | 简化模型 + "推迟" 规则 | 推迟是否需分 低/同/高; `hand→wdec` |
| 3 | C 欠账向量 (nested ranking, progress measure) | 滞后随深度增长 | 纸面拟合 L(d+1) ≤ L(d) + L(d−1) | 按层号编号会撞 `¬tri`; 位置摊平 |
| 4 | D 开放递归 + 层树打结 (Kovács, Abel–Öhman–Vezzosi) | 对层一致 | 两站证明抽成一个 Step | ⊏ 须结构化; 壁垒前提逐条核 |
| 5 | E 归纳的滞后构造子 (eutt, Danielsson) | 有限局部滞后 | 三十行 Sim + 健全性 | sized types 不可用 |
| 6 | F 中间参照 (多遍编译的合成) | 把滞后搬到记号侧 | 只对最小反例写 S̃ 一条规则 | 属 `Lab` 式, 只进验收; 翻译账 |
| 7 | G 序数预算 (transfinite step-indexing, ω₁ 索引) | 未知的有限滞后; Ω-分支 | 预算 ω·2 的归纳族 | 预算下降须字面; `noBT` |
| 8 | H 有限规则形状上的全局迹条件 (SCT, 循环证明, AF) | 对层一致 | 十二张转移图手算 | 图按分支画会撞 `obs→dec` |
| 9 | I 分级关系与滞后代数 (CakeML 时钟, Galois–Tukey, ≪_k 的 k) | 滞后作一等数据 | 由 P 的数据拟合 Φ | t[·] 弱单调要先查; `strict→LPO` 只否定严格 |
| 10 | J 欠账位, 预言, 后向模拟 (delayed simulation, Lynch–Vaandrager) | 以后再还; 依外层而定 | 给最小反例加 ob 位 | 公共上界; 跨 c 覆盖撞 `noBT` |
| 11 | K lax / pre-logical relation | 基本引理一次成立, 可合成 | 接口记录 + 对照逐站引理 | Ω-下标只能取对角 |
| 12 | L 层间换算律 (Schmerl) | 一步换算再迭代 | 纸面核对 "内层链 ≼ 外层一步" | 只是形状类比 |
| 13 | M 遗传上界 (Howard–Bezem, Kohlenbach) | 只要上界; 高层滞后 | 检查滞后函数单调性 | 折叠对高层参数不单调 |
| 14 | N 势, 多重集, 信用 | 局部损失以后偿还 | 检查 "外层余量 ≥ 内层所欠" | 自然和不可构造 |
| 15 | O up-to 的健全性 (expansion, companion) | 防止不健全的 "up to" | 先找度量无限重置的反例 | 无直接冲突 |
| 16 | P 数据驱动对齐 (程序对齐) | 先测出滞后函数 | 列表 L(d, n) | 只是测试 |
| 17 | Q 约化对: 内弱外严 (dependency pairs) | 严格只在同步点 | Sim 构造子分弱严两组 | 严格不能落在相邻项之间 |

- [判断] 建议的实验顺序与理由: (1) P: 一切记账口径都要滞后表作参数, 成本最低. (2) A 与 E 并行: 两份临时文件互不依赖, A 的通用引理与层无关, E 的健全性纯结构递归; 两者都能精确指出 "必须向外推迟" 的那一步. (3) 若 (2) 都卡在推迟, 用 P 的数据在 B, C, G 中选: 滞后表满足 nested 不等式就选 C, 只需两三层就选 B 的乘积字典序, 需要 "看了 n 再定" 的就选 G. (4) 用 D 把选定的关系写成对层一致的 Step 并打结; 若各站的 Step 不同形, 再用 H 的转移图找统一度量.
- [判断] 与 AGENTS 纲领的关系: A, B, C, E, G, I, J 都是验收侧的新关系与定理, 不改树, 折叠或合法性的定义 (符合 "第 4 层不反过来改前 3 层"); F 显式用记号, 只能进验收文件并记翻译账; D, H, K 是证明组织方式, 若做成, 是 "闭包定理与阶段无关" 这一进展判据的直接候选.
- [判断] 穷尽性: 以上三种机制 (见证脱离关系, 显式记账, 构造子化) 是否已覆盖一切可行的证法, 是判断, 不是定理; 下一轮应先挑战它, 例如找一种既不选见证也不记账的证法 (如直接证折叠对某个新的结构序单调).

### Gaps
- 排名是判断, 没有任何一条在本轮做过实验.
- 我方简化模型中 "滞后约每层翻倍" 的具体数据本轮没有拿到, 所以 C 与 I 的适配只是形状上的推测.
- 是否已有工作在布劳威尔树或树序数上用 "沿一步严格上升的映射" 证下界 (想法 A 的形式), 本轮未专门检索.
