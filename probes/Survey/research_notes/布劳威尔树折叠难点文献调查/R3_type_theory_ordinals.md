# 类型论中的序数: 布劳威尔树, 高阶数类, 比较禁忌与机检形式化 (R3)

> 记号. 难点 1 = 不可判定的派发 (比较两个孩子或两个层号); 难点 2 = 值语义 (内涵树, 非规范树, 想要的值); 难点 3 = 只要下界, 要阶段无关的整体定理. 可信度标记: **[读原文]** 本轮读了原文对应页或代码; **[检索摘要]** 只见检索结果或页面摘要, 未读全文; **[未核]** 凭记忆或二手转述, 未能核实. **[本地已有]** 指已在 `probes/Survey/OrdinalNotationsGuide.md`, `probes/Survey/CodeGuide.md`, `probes/Survey/code/TypeTheoryTrees.md` 或 `archive/` 的探针里出现过. 每条后面的 "可借" 是本轮的判断, 不是文献的陈述. 本轮没有运行 Agda, 没有构建任何外部代码.

## Q1. Kraus, Nordvall Forsberg, Xu 等人的布劳威尔树: 变体, 禁忌, 构造地成立的性质, 不靠判定的技巧

### Takeaway
KNFX (TCS 2023) 把 "比较任意两棵树" 的每一种形式 (≤, <, =, 三歧, ≤ 的分裂, 与 ω·2 判等) 都证成与 LPO 等价, 与 ω 判等与 WLPO 等价; 同时证明 "零/后继/极限" 的分类与 "是否有限" 构造地可判定, 靠的是把极限限制为严格递增序列, 并用 encode-decode 的 `Code` 给出 ≤ 的可用刻画. 2026 年的后续 (LICS 2026) 把 "判定" 换成 "给出一个序数, 命题成立当且仅当它 ≥ α", 这是 "以构造代替派发" 的现成数学框架.

### Cited Findings
- **定义 (Brw, QIIT).** 点构造子 `zero`, `succ`, `limit : (ℕ →< Brw) → Brw` (只收**严格递增**序列), 路径构造子 `bisim : f ≈ g → limit f = limit g`, 外加集合截断; ≤ 与 Brw 互归纳定义, 构造子为 `≤-zero`, `≤-trans`, `≤-succ-mono`, `≤-cocone` (x ≤ f k → x ≤ limit f), `≤-limiting` ((∀k. f k ≤ x) → limit f ≤ x); 定义 x < y := succ x ≤ y. 序列的模拟 f ≾ g := ∀k ∃n. f k ≤ g n, 双向模拟即 bisimilar (§3.2, 式 16–24). [读原文] 难点 2 — [Kraus, Nordvall Forsberg, Xu, *Type-theoretic approaches to ordinals*, TCS 957 (2023), arXiv:2208.03844](https://arxiv.org/abs/2208.03844)
- **为何要求严格递增.** 限制为严格递增序列, 就避免把零或后继写成极限 (否则如 a = limit(λi.a)); 去掉这一限制要加强 `bisim` 去见证反对称, 作者说那一版 "significantly harder to work with" (§3.2, §6.7). 可借: 把 "形状" 写进构造子的前提, 使分类可判定. [读原文] 难点 1 — [同上](https://arxiv.org/abs/2208.03844)
- **构造子可区分 (Lemma 30)**: 用 `isZero : Brw → hProp` 这类区分族证明 zero ≠ succ x ≠ limit f, 路径构造子只等同极限, 所以义务平凡. [读原文] — [同上](https://arxiv.org/abs/2208.03844)
- **≤ 的 encode-decode 刻画 (§6.2).** 定义 `Code : Brw → Brw → hProp`, 按两参数的构造子递归: `Code (succ x) (limit f) := ∃n. Code (succ x) (f n)`, `Code (limit f) (succ y) := ∀k. Code (f k) (succ y)`, `Code (limit f) (limit g) := ∀k ∃n. Code (f k) (g n)` 等 (式 78–84), 与 `toCode`, `Code-trans`, `Code-refl`, `Code-cocone` 互定义. 由此得 Lemma 32 (x < limit f → ∃n. x < f n), Lemma 33 (limit f ≤ limit g → f 被 g 模拟), Lemma 34; 再得 < 良基 (Thm 35), ≤ 反对称 (Thm 36). [读原文] 难点 2 — [同上](https://arxiv.org/abs/2208.03844)
  - 可借: 我方树上的 `≼` 若是归纳定义的 (带 trans 构造子), 反演 "x ≺ Ω-极限 ⇒ 存在某分支" 不是免费的; 用一个**按两树结构递归定义的 `Code`** 并证 `toCode`/`fromCode`, 是不用 funext 得到反演原理的标准做法. 在无路径构造子的普通 W-树上, `Code` 的定义只需结构递归, 比 QIIT 版简单 [判断].
- **抽象禁忌 (Thm 17).** 任一有零、后继、严格递增序列极限的结构, 若有可判定相等, 则 WLPO. 证明用 "跳跃序列" t↑: 在 t 首次出现 tt 处跳到 ω. [读原文] 难点 1 — [同上](https://arxiv.org/abs/2208.03844)
- **Brw 的可判定部分 (Thm 46).** 是否有限可判定; 对有限 n, (n ∼ _) 与 (_ ∼ n) 对 =, <, ≤ 都可判定. [读原文] — [同上](https://arxiv.org/abs/2208.03844)
- **Brw 的禁忌 (Thm 48–53).** 以下等价: LPO; ∀x,y. Dec(x ≤ y); Dec(x < y); ∀x. Dec(ω < x); Dec(x = y); ∀x. Dec(x = ω·2) (Thm 48, 工具是 Lemma 47: limit s↑ ≤ ω·2, 且 ∃k. s_k = tt ⇔ limit s↑ = ω·2 ⇔ ω < limit s↑). 与 ω 判等 ⇔ WLPO (Thm 49); n ≥ 2 时与 ω·n 判等 ⇔ LPO (Thm 50); 相等在 ω 处稳定, 在 ω·n (n ≥ 2) 处稳定推出 MP (Thm 51); LPO ⇔ 三歧 ⇔ ≤ 的分裂 (Thm 53); 减法存在 ⇔ LPO (Thm 45). [读原文] 难点 1 — [同上](https://arxiv.org/abs/2208.03844)
- **上确界与并 (Thm 54, 55).** y 有限或 y = ω 时, 二元并 x ⊔ y 可计算 (有限性可判定); 对一切 x 计算 x ⊔ (ω+1) 推出 WLPO, LPO 推出它存在. 一般序列的上确界只对严格递增序列给出. [读原文] 难点 1 — [同上](https://arxiv.org/abs/2208.03844)
- **另一种 QIIT (§6.7).** 用路径构造子 `antisym : x ≤ y → y ≤ x → x = y` (仿 partiality monad 的构造) 得 Brw′; 作者证了 Brw ≃ Brw′, 但直接证 Brw′ 良基没做成. [读原文] 难点 2 — [同上](https://arxiv.org/abs/2208.03844)
- **三种序数的关系.** Cnf → Brw → Ord (外延良基序) 有典范保序映射, 从 "更可判定" 到 "更不可判定"; Cnf 与 Brw 的结果在 cubical Agda 形式化 (摘要). Cnf 没有上确界, 有界严格递增序列的极限推出 WLPO (Thm 29). [读原文] — [同上](https://arxiv.org/abs/2208.03844)
- **α-可判定 (LICS 2026).** 定义 P 为 α-decidable 当且仅当 ∃x : Brw. P ↔ x ≥ α. 可判定 ⇔ 1-可判定 ⇔ ω-可判定; 半可判定 ⇔ (ω+1)-可判定; α-可判定命题对二元合取封闭, (ω·n + k)-可判定的对二元析取封闭; 半可判定族的可数交是 ω²-可判定, 可数并在不设可数选择时只有 (ω·3)-可判定. 全部在 Cubical Agda (Agda 2.8.0) 形式化. [读原文, 第 1–6 页] 难点 1 — [de Jong, Kraus, Mohammadzadeh, Nordvall Forsberg, *Generalized Decidability via Brouwer Trees*, LICS 2026, LIPIcs 59](https://drops.dagstuhl.de/storage/00lipics/lipics-vol380-lics2026/LIPIcs.LICS.2026.59/LIPIcs.LICS.2026.59.pdf); [arXiv:2602.10844](https://arxiv.org/abs/2602.10844). [本地已有: `probes/OCF/Barrier.lagda.md` 的文献注已引此文, 但未用其技巧]
  - **取整 (§2.3).** ⇑, ⇓ : Brw → Brw^{zl} (到 "零或极限"): ⇑(succ x) := x + ω, ⇓(succ x) := ⇓x, 极限不动; 二者保 ≤ (Lemma 2); 每个 α 可写成 λ + n, λ 非后继, n 有限 (Lemma 3); 对非后继 λ 有 α ≤ λ ↔ ⇑α ≤ λ 等 (Lemma 4). [读原文] 难点 1, 2
  - **≤ 的刻画 (Lemma 1).** succ α ≤ succ β ↔ α ≤ β; α < limit f → ∃n. α < f n; limit f ≤ succ α → limit f ≤ α; limit f ≤ limit g → f 被 g 模拟. [读原文]
  - **设置.** 工作在 HoTT; 正文说 Brw 的性质 "heavily relied on" univalence 得到 (引 KNFX); 但作者也说原则上可在带 funext 与命题截断的 MLTT 里做, 只要把 Brw 及其性质作为假设. 不假设命题 resizing. 目录显示 §5, §6 讨论二元最小值、最大值的不可构造性, §8 讨论可数选择 [只读了目录, 未读这几节]. 代码库: [bitbucket nicolaikraus/constructive-ordinals-in-hott](https://bitbucket.org/nicolaikraus/constructive-ordinals-in-hott/) [链接取自论文首页, 未打开].
- **会议版.** *Connecting Constructive Notions of Ordinals in Homotopy Type Theory* (MFCS 2021) 是上文的前身. [检索摘要] — [arXiv:2104.02549](https://arxiv.org/abs/2104.02549)
- **de Jong, Kraus, Nordvall Forsberg, Xu, *Set-Theoretic and Type-Theoretic Ordinals Coincide* (LICS 2023).** 在 Aczel 解释 (的 HoTT 版) 下, 构造性集合论的 "遗传传递集" 序数与 HoTT 的 "传递良基外延关系" 序数等价; 再推广到覆盖一切集合的有序结构; Agda 形式化. 与三个难点的关联弱. [检索摘要] — [arXiv:2301.10696](https://arxiv.org/abs/2301.10696)
- **本地已知的部分.** `probes/Survey/code/TypeTheoryTrees.md` §E 只把 KNFX 当作 BedrockInstitute/QIITOrd 的来源, 并判定 QIIT 不能当我方的树 (商化毁掉基本列). 上面 Thm 17, 45–55, `Code` 与 LICS 2026 的技巧不在本地指南里. [本地已有, 部分]

### Inferences
- **我方 "obs→dec" 一族与壁垒定理有现成的同类.** KNFX Thm 17 (判等 + 严格递增极限 ⇒ WLPO) 与 Thm 48 (判 ω < x ⇒ LPO) 是同一个跳跃序列引擎. 我方配对否定可以直接复用 "limit s↑ ≤ ω·2, 且 ω < limit s↑ ⇔ ∃k. s_k" 这个探针, 不必每次重造 [判断].
- **"在一个固定的界之内" 比较是可判定的, 跨树比较不可判定.** KNFX 的可判定结果都是 "与一个固定的有限树或 ω 比较"; Q2 的 Escardó Δ 解释与 Q4 的 Kovács `cmpO₁` 都是 "同一个界内部的位置可比较". 三处合起来, 给我方 "被比较的两个下标要带字面公共上界的证据" 一个文献上的支撑, 也说明这条路的边界: 公共上界必须是**数据** (一条路径的端点), 而不是由 ≤ 证出来的命题 [判断].
- **α-可判定给出 "以复合代替派发" 的语言.** 把 "节点层号 j 是否低于目标 k" 这类问题, 改写成 "构造一棵树 x_{j,k}, 使条件成立当且仅当 x_{j,k} ≥ α"; 折叠在这个位置不分情况, 而是把 x_{j,k} 作为一个参数喂进去 (例如作为迭代次数或极限的下标), 让值随条件单调. LICS 2026 的封闭性定理 (合取封闭, 可数交是 ω²-可判定) 正是这种复合的代数 [判断, 未在我方树上试].
- **取整 ⇑/⇓ 是构造的规范化.** "每个树 = 非后继 + 有限" (Lemma 3) 不判定任何比较, 可以当作读回域的一个廉价规范形 [判断].
- 我方 View 不要求 ℕ-极限按值严格递增 (那会推出 LPO, 见 AGENTS 纲领 1 与 `BrwViewNeg.strict→LPO`); KNFX 要求严格递增, 但那是**构造子的前提** (数据携带证明), 不是从中间层推出来的. 两者不矛盾 [判断].

### Gaps
- KNFX 正文 §4.2 的 "classifiability induction" 与 §8 的 Cnf → Brw → Ord 映射细节未读; §6.4 的分类定理是否需要 univalence 未核.
- LICS 2026 的 §5–§8 (二元 min/max 的不可构造性, 可数选择) 只看了目录.
- 两篇文章的代码库没有打开 (bitbucket), 无法核对 Agda 选项, 也不知道是否有 `--safe`.

## Q2. Escardó 与 de Jong 的单值基础序数 (TypeTopology): 禁忌, 算术, 不可数族的上确界

### Takeaway
TypeTopology 在 univalent 设定下给出任意 (含不可数) 小族的上确界, 代价是集合商与 univalence; 同时证明 "上确界保持可判定性" 一类性质推出 EM. 对我方更有用的是 Escardó 的 "Brouwer 码的离散解释": 固定一个码 b, 它的离散解释 Δ b 的元素有可判定相等且三歧; 而对一切码都要求紧致或要求两种解释一致, 都等价于 LPO. 这是 "固定界内可比较, 跨界不可比较" 的又一个精确版本.

### Cited Findings
- **`Ordinals.Taboos` (de Jong).** 若每个离散序数都三歧, 则 DNE, 加 funext 得 EM; 若离散下标族的三歧序数的上确界都离散, 则 EM (前提: 命题截断, Set-Replacement, univalence). [检索摘要: 读的是模块页的工具摘要] 难点 1 — [TypeTopology, Ordinals.Taboos](https://martinescardo.github.io/TypeTopology/Ordinals.Taboos.html)
- **`Ordinals.OrdinalOfOrdinalsSuprema` (de Jong).** 对任意 I : 𝓤 与族 I → Ordinal 𝓤 构造上确界: 取 Σ i. ⟨α i⟩, 以 "初始段相等" (α i ↓ x = α j ↓ y) 为等价关系做集合商, 按初始段包含排序, 证明它是最小上界. 假设 univalence, funext, propext, 集合商; 对 I 没有可数性要求 (页面对比了 KFX2021 只处理弱递增 ℕ-族). 页面说另有 Escardó 不用集合商的构造 [被截断, 未读]. 上确界最终所在宇宙层的处理未读到. [检索摘要, 读了页面前 10 万字符] 难点 2 — [TypeTopology, Ordinals.OrdinalOfOrdinalsSuprema](https://martinescardo.github.io/TypeTopology/Ordinals.OrdinalOfOrdinalsSuprema.html)
- **`Ordinals.BrouwerCodesDiscreteAndCompactInterpretations` (Escardó).** Brouwer 码 Z, S, L (L 收 ℕ-序列). 两种解释: 紧致解释 Κ (L ↦ 压扁和 ∑¹) 与离散解释 Δ (L ↦ 后继和 ∑₁). 证明: 每个 Κ b 有点紧致, 是 Cantor 型的收缩, 全分离; **每个 Δ b 离散 (可判定相等), 是 ℕ 的收缩, 且三歧**; ι : Δ b → Κ b 稠密, 保序且反射序; ι 对一切码都是等价 ⇔ LPO; 一切 Δ b 紧致 ⇔ LPO; 页面明说任一无穷离散序数的紧致性等价于 LPO. 选项 `--safe --without-K`, funext 作参数, 个别结果另用 propext, univalence 只在后面一节. [检索摘要, 读了页面前 10 万字符] 难点 1 — [TypeTopology, Ordinals.BrouwerCodesDiscreteAndCompactInterpretations](https://martinescardo.github.io/TypeTopology/Ordinals.BrouwerCodesDiscreteAndCompactInterpretations.html)
- **`Ordinals.InductiveRecursiveCodesInterpretations` (Escardó, 2022-03, 标为草稿).** 码 E 与离散解释 Δ 归纳-递归地同时定义, 构造子有 ⌜𝟙⌝, ⌜ω+𝟙⌝, ⌜+⌝, ⌜×⌝, 以及 ⌜Σ⌝ ν (A : ⟨Δ ν⟩ → E): **分支在一个先前码的解释的元素上**. Δ ν 有可判定相等 (ℕ 的收缩) 且三歧; Κ ν 紧致; 一切 Δ ν 紧致 ⇔ LPO. `--safe --without-K`, funext 作参数. [检索摘要] 难点 1, 高阶分支 — [TypeTopology, Ordinals.InductiveRecursiveCodesInterpretations](https://martinescardo.github.io/TypeTopology/Ordinals.InductiveRecursiveCodesInterpretations.html)
- **模块清单.** Ordinals 目录还有 `SimulationsLowerSets`, `SupremaPreservation`, `CompactnessOfSuprema`, `FailureOfTrichotomy`, `BrouwerCodesIntoInductiveRecursiveCodes`, 以及 de Jong, Kraus, Nordvall Forsberg, Xu 的 `Exponentiation`, `BoundedOperations`, `ArithmeticReflection`. 这些只看到名字. [检索摘要] — [TypeTopology, Ordinals.index](https://martinescardo.github.io/TypeTopology/Ordinals.index.html)
- **Escardó 2010/2011 的 ordinals 笔记.** System T 中 Church 编码的序数 O X, MLTT 中的 Brouwer 树 B; ε₀ 在 System T 中不可定义而在 MLTT 中可定义; B 上的外延相等 `≣` 归纳定义; 若干 "练习" 以 postulate 写出 (所以那份文件不是无公设的). 基于 Coquand, Hancock, Setzer 1997 与 Hancock 的 lenses. 没有到 ε₀ 以上, 没有塌缩. [检索摘要] — [Escardó, *Ordinals in Gödel's system T and in Martin-Löf type theory*](https://martinescardo.github.io/papers/ordinals/ordinals.html)
- **本地已知的部分.** 本地指南没有 TypeTopology 的条目 (检索 `TypeTopology`, `Escard` 在 `probes/Survey` 下无命中). [本地未有]

### Inferences
- **离散解释 = "位置" 的可判定世界.** Δ b 的元素是码 b 内部的位置; 它们可比较. 我方 Ω-节点分支在 "下一层的一切合法树" 上, 那不是任何固定码的 Δ, 所以这里的可判定性不能直接搬过去. 能搬的形状是: 让需要比较的两个下标都**表示为同一个码里的位置** (这正是 "字面公共上界" 的意思), 比较就落在 Δ 里 [判断].
- **IR 码的 ⌜Σ⌝ 是 "沿先前序数的元素分支" 的无判定写法.** 它与我方 "Ω-节点按低层合法树分支" 的差别在于: ⌜Σ⌝ 的分支类型是一个**已给定**的 ν 的解释, 规模受 ν 控制; 我方分支类型是整层. 若把我方高层节点的分支改写为 "沿某个已构造的上界码的位置分支", 就落入 ⌜Σ⌝ 的形状; 代价是 Ω-节点不再遍历整层, 是否还有 Ω 的强度要由值定理决定 [判断, 未试]. 注意这与纲领 1 的 "Ω-极限按低层合法树分支" 的要求可能冲突, 动手前要对照.
- **想要的值可以落在 Ordinal 𝓤, 但只能作为条件结果.** `OrdinalOfOrdinalsSuprema` 说明: 若允许 univalence 与集合商, 则 |Ω-节点 f| := sup_c |f c| 是可定义的, 树到 Ordinal 𝓤 的 "想要的值" 存在且对一切树定义. 这超出我方选项 (只准 funext 作前提, 不开 univalence), 所以只能作为验收文件里的 "条件" 语义, 或者作为纸面的参照 [判断].

### Gaps
- `Ordinals.Taboos` 是否有关于 "比较两个序数是否可判定" 或 LPO/WLPO 形式的禁忌, 本轮只见工具摘要, 未逐条核.
- Escardó 不用集合商的上确界构造未读到.
- 是否有 TypeTopology 模块处理 "高阶数类" 或在码上定义 Veblen/塌缩函数: 未发现, 未穷举.

## Q3. 高阶数类与广义树 (W-型, 归纳-递归): Palmgren, Hancock, Setzer, Rathjen–Griffor–Palmgren, Dybjer–Setzer; 在高阶树上定义函数而不判定序; 是否有类型论里按高阶布劳威尔树递归定义的塌缩 ψ

### Takeaway
类型论文献里的高阶数类大多只用来**表示**或**证明良基** (W-型 Ω_{k+1} = μX. 1 + X + X^ℕ + X^{Ω_k}, 宇宙层次, Mahlo 宇宙), 不在树上定义塌缩. 在树上定义塌缩并不判定序的, 是经典的 Wainer 学派 "树序数" (tree ordinals): 层号是自然数, 由类型确定, 所以 "低于/同层/高于" 是语法的, 不需判定; 它们处理值与单调性的办法是 "结构化" 谓词 (弱 Bachmann 性质) 与按参数序列取路径的关系 ≺_ζ̄. 类型论里按层号为可数序数的高阶树递归定义 ψ 的, 本轮只找到 Kovács 的 gist (本地已试过).

### Cited Findings
- **Hancock 的数类写法.** N = μX. 1 + X; Ω = μX. 1 + X + (N → X); Ω₂ = μX. 1 + X + (N → X) + (Ω → X); Ω₃ 同理. 他提出 Ω_ω 及以上要更强的类型结构 (宇宙). 讲义的下界部分用他的 "lens" 概念在 System T 与宇宙里构造大序数; 讲义自称不完整. [读原文, 第 10–11 页与目录] 高阶分支 — [Hancock, *(Ordinal-theoretic) Proof Theory*, MGS 2008 讲义](https://martinescardo.github.io/events/MGS08/notes/proofTheory.pdf)
- **Hancock–Setzer 的 Γ₀ 页面 (1997 起, 1999 更新).** 在 MLTT 中用 "有点非标准的宇宙序列" 构造到 Γ₀ 的序数; NextU 算子把一族基础集合在类型构造下闭合成宇宙; Veblen φ 由导数算子构造; 用 lens 式谓词变换证良基; 定义了一个对可及性递归的比较 ≼, 不声称可判定. [检索摘要] 难点 1, 3 — [Hancock, Setzer, *veblenU*](https://www.dcs.ed.ac.uk/home/pgh/veblenU.html)
- **Hancock 2003 笔记: 沿自身初始段分支的树.** 类型 `Omega` 有零, 后继, 以及在 `Seg a` (a 的初始段, 对 a 递归定义) 上的上确界. [检索摘要, 我的转述来自 WebFetch, 未逐行读] 高阶分支 — [Hancock, *Ordinals and Programs* (notes)](https://www.dcs.ed.ac.uk/home/pgh/ordinals.html)
- **Hancock 博士论文 (2000).** *Ordinals and Interactive Programs*, LFCS 报告 ECS-LFCS-00-421; 最后一部分在 "带 ℕ 与外部宇宙序列的 Martin-Löf 型论" 里构造可证序数. [检索摘要, 未读全文] — [LFCS 报告页](https://publish.lfcs.inf.ed.ac.uk/reports/00/ECS-LFCS-00-421)
- **Coquand, Hancock, Setzer, *Ordinals in type theory*, CSL 1997 特邀报告.** LICS 2026 把它列为类型论里研究布劳威尔树序数的早期工作; Coquand 主页说三人分析了带一个宇宙的 MLTT 的序数. 讲稿 PostScript 链接见 Coquand 页面. [检索摘要, 讲稿未读] — [Coquand, *Ordinals in Type Theory*](https://www.cse.chalmers.se/~coquand/ord.html)
- **Rathjen, Griffor, Palmgren, *Inaccessibility in constructive set theory and type theory*, APAL 94 (1998) 181–200.** 研究 Mahlo 的 π-数, 系统 CZFπ (各超限阶的不可达集), 可在带二阶宇宙算子的外延 Martin-Löf 型论 MLQ 中解释. 不涉及树上的塌缩. [检索摘要] — [McMaster 记录](https://experts.mcmaster.ca/scholarly-works/1710871); 后续开放问题见 [Takahashi, arXiv:2402.15074](https://arxiv.org/abs/2402.15074v2). [本地已有: `OrdinalNotationsFS.md` 与 `AgdaStrength.md` 已记; `czf-in-mahlo` 在 CodeGuide]
- **Setzer (Mahlo 宇宙, ordinal systems, 1998 的良序证明), Dybjer–Setzer (归纳-递归, 2024 扩展谓词 Mahlo 宇宙), Palmgren (超宇宙).** [本地已有: `AgdaStrength.md`, `NotationWF.md` (Setzer 2000 *Ordinal systems part 2* 已读图), CodeGuide §3 (Dybjer–Setzer 仓库未取得)]. 本轮未发现其中有 "在高阶树上递归定义塌缩" 的内容 [检索摘要, 未穷举].
- **Wainer 学派的树序数 (Fairtlough 1992 博士论文, 导师 Wainer).** [读原文, 第 12–18 页]
  - Def 1.1: 对 n < ω, Ω_n 由规则归纳生成: 若 α : I → Ω_n, I = ∅, {0} 或 Ω_k (k < n), 则 α ∈ Ω_n; I = Ω_k 时 α 是极限, dom(α) = Ω_k. Ω₀ = N, Ω₁ 是可数树, Ω₀ ⊂ Ω₁ ⊂ … (把树与其图等同). rank 按 sup 递归.
  - Def 1.2: 子树序 ≺ 是 α(ζ) ≺ α 的传递闭包; Def 1.3: lev(α) 为最小的 k 使 α ∈ Ω_k.
  - **Def 1.4 (按参数序列取路径).** 对 ζ̄ ∈ Π_{k<n} Ω_k, 令 α(ζ̄) = 0 / α′ / α(ζ_k) (按 α 为零 / 后继 / 定义域为 Ω_k 的极限); ≺_ζ̄ 是 α(ζ̄) ≺_ζ̄ α 的传递闭包; α[ζ̄] := {β : β+1 ⪯_ζ̄ α} 是有限且被 ≺_ζ̄ 线性序的集合, G_α(ζ̄) 是其基数 (推广的慢增长层级). 意思是: **每一层的分支由参数 ζ_k 事先给定, 于是从 α 往下只有一条确定的路**. Def 1.6 的 P_ζ̄(α) (取路径上的前驱) 引自 Cichon 1985.
  - **Def 2.2 (结构化).** α 是结构化的, 若对每个定义域为 Ω_k 的极限 γ ⪯ α 与每个 ζ̄, η ∈ ω_k[ζ̄] 蕴含 γ(η) ∈ γ[ζ̄]. 作者说它是 Bachmann 性质的弱形式, 由 Dennis-Jones 与 Wainer (1984) 引入.
  - Lemma 3.3 与 Cor 3.4: 结构化的 α ∈ Ω₁ 满足 α(≺) = ∪_x α[x], 且被 ≺ 良序; 因而 {G_β : β ≺ α} 按支配关系线性序. Thm 3.5 (Dennis-Jones–Wainer): 结构化树是其慢增长函子的直接极限.
  - 作者另指出: 对 lev(α) ≥ 2 的树, 一般 α(≺) ≠ ∪_ζ̄ α[ζ̄], 即高层树的全部子树不能被这些路径覆盖.
  - 来源: [Fairtlough, *Ordinal Complexity of Recursive Programs and their Termination Proofs*, PhD thesis 1992, LFCS ECS-LFCS-92-196](https://www.lfcs.inf.ed.ac.uk/reports/92/ECS-LFCS-92-196/) (扫描版 PDF). 难点 2, 3
- **Wainer 学派的塌缩函数.** Wainer 在 Logic Colloquium '95 的文章说, 如何构造大的结构化树序数这个问题, 把人引向证明论里的塌缩函数 [检索摘要, 原文取不到]. Buchholz–Wainer 1987 (*Provably computable functions and the fast growing hierarchy*), Wainer 1989 (*Slow growing versus fast growing*, JSL 54), Wainer 1999 (*Accessible recursive functions*, BSL 5(3):367–388), Fairtlough–Wainer 1998 (*Handbook of Proof Theory* 第 III 章) 与 Schwichtenberg–Wainer 2012 (*Proofs and Computations* 第 5 章) 据我记忆在树类 Ω_k 上定义了塌缩 φ_k : Ω_{k+1} → Ω_k, 规则是 "低层极限逐点, 本层 Ω_k-极限用输出作下标对角化". **这一条未能核实, 全文都没取到** [未核]. — [Wainer, *Accessible Segments of the Fast Growing Hierarchy*, LC'95](https://projecteuclid.org/ebooks/lecture-notes-in-logic/Logic-Colloquium-95--Proceedings-of-the-Annual-European-Summer/chapter/Accessible-Segments-of-the-Fast-Growing-Hierarchy/lnl/1235415914); [Wainer, *Accessible recursive functions*, BSL 1999](https://www.cambridge.org/core/journals/bulletin-of-symbolic-logic/article/accessible-recursive-functions/0971F2F0B2A95CBC99DFB474693E6754)
- **Aczel 1972, *Describing ordinals using functionals of transfinite type*, JSL 37(1):35–47.** 用以 Ω 为基的超限型泛函描述 Ω 以下的序数, 并与 Bachmann 的方法 (用 Ω₂ 以下的描述来描述 Ω 以下的序数) 比较. 付费, 未读. [检索摘要] 高阶函数 — [Cambridge](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/describing-ordinals-using-functionals-of-transfinite-type/DE718F4C4A43BEEFFFD18B37EB182EEF), DOI 10.2307/2272543. 检索摘要还提到后来有人只取 "遗传膨胀的" 泛函; 那条转述来自 Danner 1999 ([arXiv:math/9908127](https://arxiv.org/abs/math/9908127), *Transfinite iteration functionals and ordinal arithmetic*, 引入泛函上的新等价关系), 检索摘要误把作者写成 Setzer [已核: 作者是 Norman Danner].
- **Kovács 的 gist "Large countable ordinals and numbers in Agda".** 层号 l : O₁ (可数序数的树, `lim` 带 `lim-incr` 严格递增证明); `_<_` 是**归纳定义的路径** (`suc*`, `suc`, `lim* n`, `lim n p`), 即 a < l 的证明是进入 l 的一条有限路径; `cmpO₁ : a < c → b < c → (a < b) ⊎ (b < a) ⊎ (a ≡ b)` 对两条进入**同一个界 c** 的路径做模式匹配, 在 `lim*` 处用 `cmpℕ` 比较下标, 得到可判定三歧. 树类型 `O l El` 有 `zero`, `suc`, `lim`, `Lim i (p : i < l) (El i p → O l El)`, `El` 对路径 p 递归. 塌缩 `ψ< p` 在 `Lim i q a` 处对 `cmpO₁ q p` 分三支: 低于目标保留 (`Limᵁ`), 高于目标走链 (`lim λ n → ψ< p (a (iterℕ n (ψ< q ∘ a) (Ω _)))`), 同层取 `lfp (ψ< p ∘ a ∘ …)` (从 0 迭代 "输出作下标" 的不动点). 例子标注 `ψ 2 0` 为 Bachmann–Howard, `ψ (ω₀ + 1) 0` 为 TFB 等; 页面下有一条自称 AI 分析的评论认为 ω 以上的标注不成立 [未核]. 文件头 pragma 为 `--postfix-projections --without-K --safe`, 头部注释又说真 Agda 会报正性错误 [两句并存, 原样记录, 未核哪个版本过检]. [读原文代码片段] 难点 1 — [gist AndrasKovacs/8d445c8457ea0967e807c726b2ce5a3a](https://gist.github.com/AndrasKovacs/8d445c8457ea0967e807c726b2ce5a3a). [本地已有: `archive/probes/OCF/Kovacs/FINDINGS.md`: 单层复刻到 BHO 编译通过, 多层的 `cmpᵁ` 在 Lim/Lim 情形撞无界三歧; `EBOHandbook.md` 也提到社区 gist 回复. CodeGuide 未列此 gist]

### Inferences
- **树上塌缩不判定的经典办法是 "层号是类型, 不是数据".** Wainer 学派与 Hancock 的 Ω_k 都按自然数 k 分层, 节点属于哪一层由定义域 Ω_k 语法地给出, 三分 (低/同/高) 是对 k 的比较, 在 ℕ 上可判定. 我方的困难来自层号本身是树 (到 Ω_Ω 与 Ω_{Ω_Ω}), 这一点文献里只有 Kovács 处理, 他的办法是 "层号作为进入公共界的路径", 而且层号只到可数 (O₁ 中没有 Ω-共尾元), 所以不触壁垒定理 [判断]. 本地档案证实多层时撞墙.
- **Fairtlough 的 ≺_ζ̄ 是 "带参数的路径序", 对难点 2 有直接用处.** 在高层树上, 给每一层预先指定分支 ζ_k, 就把树压成一条路; 单调性 (支配) 先对这条路陈述, 再对参数量化. 这把 "两孩子是否相同" 这个问题换成 "两孩子是否沿同一个参数路径可达", 后者是结构的 [判断]. 他关于 lev ≥ 2 时路径覆盖不了全部子树的注记提醒: 对 Ω₂ 以上, 只按路径陈述的定理不能推出关于全部子树的结论, 读回域要按路径选 [判断].
- **"结构化" 就是一个读回域谓词.** Def 2.2 量化的是 "每个极限子树沿每个参数路径", 不是 "一切合法树"; 正面定理 (Lemma 3.3, Cor 3.4) 只对结构化树陈述. 这与我方 "量化域先取带证据的读回域" 的最佳实践同形 [判断].
- 没有找到 "Ω-节点在整层上分支, 塌缩在类型论里按树递归定义, 层号可达 Ω" 的前人工作 [判断, 检索非穷举]; 这与 CodeGuide §3 "有实现折叠树的仓库? 所读的都没有" 一致.

### Gaps
- Wainer 学派塌缩函数的原始定义 (Buchholz–Wainer 1987, Wainer 1989, Schwichtenberg–Wainer 2012 第 5 章) 未取得全文, 规则形状未核.
- Palmgren 1992 (*Type-theoretic interpretation of iterated, strictly positive inductive definitions*) 与 Palmgren 的 *On universes in type theory* 本轮未检索到全文, 只作背景.
- Hancock 博士论文与 Coquand–Hancock–Setzer 1997 讲稿未读.
- Feferman 1970 *Hereditarily replete functionals over the ordinals* 本轮未检索, 未核.

## Q4. 证明助手中的大可数序数与快速增长层级 (CodeGuide 以外); 规范形与基本列的处理; 有无在树上而非记号上定义塌缩

### Takeaway
CodeGuide 以外新增的机检工作不多: Isabelle AFP 的 *Countable Ordinals* (经典, 商类型上到 Veblen 层级), KNFX 的 cubical Agda 代码库, TypeTopology 的 Ordinals 目录, Eremondi 的 SMB-树 (本地已试). 在树上 (而非记号上) 定义塌缩的机检代码, 本轮只找到 Kovács 的 gist (本地已试). 没有找到 Coq/Rocq 中 Buchholz ψ 的形式化.

### Cited Findings
- **Isabelle AFP *Countable Ordinals* (Brian Huffman, 2005).** 定义良序的可数序数类型; 有连续函数, 正规函数, 超限递归函数, 最小不动点, 导数, 序数算术 (含指数与对数), Cantor 范式, 正规函数上的 Veblen 层级. 预备数据类型据检索摘要为 `ord0 = ord0_Zero | ord0_Lim "nat ⇒ ord0"`, 良基性依赖子项关系 [源码未读]. Isabelle/HOL, 经典. [检索摘要] 难点 2 — [AFP: Countable Ordinals](https://devel.isa-afp.org/entries/Ordinal.html); [OrdinalVeblen 理论](https://devel.isa-afp.org/browser_info/current/AFP/Ordinal/OrdinalVeblen.html)
- **Eremondi, *Strictly Monotone Brouwer Trees for Well-founded Recursion Over Multiple Arguments*, CPP 2024.** SMB-树: 与 Brouwer 树构造子同签名的函数, 满足全部 Brouwer 树不等式; 有计算最小上界的 max, 其 join 对后继分配, 能计算**任意序列** (不必递增) 的极限; 动机是多参数良基递归; Agda, 代码在 Zenodo (doi 10.5281/zenodo.10204397). [检索摘要] 难点 1 — [arXiv:2312.06962](https://arxiv.org/abs/2312.06962). [本地已有: `archive/probes/OCF/PastBTBO/SMB/FINDINGS.md`: `indMax` 编译通过, 判定 "不能绕过 BoundedTrich 障碍, 强度增益 0"]
- **KNFX 的 cubical Agda 代码** (Cnf, Brw, 及 LICS 2026 的 α-可判定). [读原文中的声明; 仓库未打开] — [bitbucket nicolaikraus/constructive-ordinals-in-hott](https://bitbucket.org/nicolaikraus/constructive-ordinals-in-hott/)
- **Fernández-Duque, Weiermann, *Fundamental sequences and fast-growing hierarchies for the Bachmann-Howard ordinal* (arXiv 2022, v5 2024).** 证明 Buchholz 给 ϑ 的基本列系统满足多种正则性, 包括 Bachmann 性质; 部分推广到 ϑ 的变体 (含一个对可数序数不用加法的变体); 由此相应 Hardy 函数有自然的单调性, 并支配沿 ϑ(ε_{Ω+1}) 原始递归定义的一切函数. 纸面, 未形式化. [检索摘要] 难点 3 — [arXiv:2203.07758](https://arxiv.org/abs/2203.07758)
- **Buchholz, Cichon, Weiermann, *A uniform approach to fundamental sequences and hierarchies*, MLQ 40 (1994) 273–286.** 基本列与 Hardy 层级的抽象处理, 讨论 Bachmann 性质. 维基百科 "Fundamental sequence" 条目把它标成 Weiermann 一人, 页码 177–190, 与 core.ac.uk 记录不符, 以后者为准 [检索摘要, 原文 403]. — [core.ac.uk](https://core.ac.uk/download/12164728.pdf). [本地已有: CodeGuide §3 与手册引 BCW 的 (B2)]
- **Wilken, *Fundamental sequences based on localization* (arXiv 2024).** 自述放在 BCW 的抽象框架中. [检索摘要, 只见标题与一句] — [arXiv:2410.15953](https://arxiv.org/abs/2410.15953)
- **已在本地指南的:** hydra-battles (Castéran 等, Coq, ε₀ 完整, Γ₀ 草稿), Mathlib `ONote`, cj-xu/OrdinalNotations, coquand/agda-ordinal-analysis-id1, BedrockInstitute/QIITOrd, koteitan/googology-lean (EBO), AndrasKovacs/universes, czf-in-mahlo 等. 见 `probes/Survey/CodeGuide.md` §2 与 `OrdinalNotationsGuide.md` §5.4. [本地已有]
- **Coq/Rocq 中 Buchholz ψ 或一般塌缩函数的形式化:** 一次检索未找到. [检索摘要, 非穷举]

### Inferences
- 文献里的机检工作对规范形与基本列的处理分两类: 记号侧 (hydra, Mathlib, googology-lean) 在**项**上写基本列, 规范形是可判定谓词; 树侧 (AFP, KNFX, TypeTopology) 根本没有基本列, 极限是数据或商. 只有 Kovács gist 在树上同时有塌缩与基本列 (树的 `lim` 本身就是基本列) [判断].
- Fernández-Duque–Weiermann 的结论模式 "Bachmann 性质 ⇒ Hardy/FGH 单调并支配" 是我方 "FGH 沿 ≼ 单调" 的经典版本; 他们是在记号上证, 不在树上 [判断].
- SMB-树说明 "公共上界作为构造出来的数据" 是可得的 (max 可计算, 严格单调), 不可得的是 "最小上界 + 判定". 本地档案已判它不解决有界三歧 [本地已有].

### Gaps
- AFP *Countable Ordinals* 的源码 (商的构造方式, 是否有基本列) 未读.
- Lean 侧本轮未做新检索 (本地 CodeGuide 已覆盖较多); 是否有 2026 年新的 Lean/Agda 树侧塌缩形式化, 未查.
- KNFX 与 LICS 2026 的仓库未打开, 无法核对是否 `--safe`.

## Q5. 针对内涵树的技巧 (难点 2): 模拟商, W-型的外延塌缩, 带证明的基本列, 规范形谓词, 用来陈述单调性的证明相关序

### Takeaway
把布劳威尔 W-树按双向模拟商掉并保留 `limit`, 一般需要可数选择或改用 QIIT; QIIT 又毁掉基本列 (本地已判). 因此文献给我方的可用工具是 setoid 层面的: 归纳定义的 ≤ 加递归定义的 `Code` 刻画, 序列间的模拟 ≾, 结构化/Bachmann 谓词作读回域, 以及按参数路径的 ≺_ζ̄. 构造性集合论方面, Taylor 的 plump 序数说明 "让后继单调" 需要加强传递性, 并且有界性与有向性要遗传地定义.

### Cited Findings
- **商掉延迟单子需要可数选择.** Chapman, Uustalu, Veltri 把延迟单子按弱双模拟商掉, 定义单子乘法时假设了 propext 与可数选择, 期刊版论证对可数选择的需要是内在的; Altenkirch 等人用 HIT/QIIT 得到不需选择的 partiality monad; 结果在 Agda 形式化. [检索摘要] 难点 2 — [Chapman, Uustalu, Veltri, *Quotienting the delay monad by weak bisimilarity*, MSCS 29(1) (2019) 67–92](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/quotienting-the-delay-monad-by-weak-bisimilarity/EC1E1F7E7692C991FCDE85C61673C799)
- **QIIT.** KNFX 的 Brw 与 LICS 2026 都依据 Altenkirch, Capriotti, Dijkstra, Kraus, Nordvall Forsberg 的 QIIT 规范; KNFX §6.7 的 `antisym` 版本仿 partiality monad 的构造. [读原文中的引用] — QIIT 原文 [arXiv:1612.02346](https://arxiv.org/abs/1612.02346) [编号取自检索结果, 未打开]
- **递归 HIT 的语义.** Lumsdaine 与 Shulman 在很广的设定下构造 HIT 的模型, 指出递归 HIT 的解释问题对普通递归归纳类型 (ℕ, W-型) 也会出现. 我原想引用的 "无选择时无穷元运算的自由代数可能不存在" (Blass 1983) 本轮**未找到出处**. [检索摘要] — [Lumsdaine, Shulman, *Semantics of higher inductive types*, MPCPS 169 (2020) 159–208, arXiv:1705.07088](https://arxiv.org/abs/1705.07088)
- **KNFX 的 ≤ 与模拟.** 见 Q1: 归纳 ≤ 的五个构造子, `Code` 的递归刻画, 序列模拟 ≾ 与 bisimilarity; Lemma 33: limit f ≤ limit g 推出 f 被 g 模拟. [读原文] — [arXiv:2208.03844](https://arxiv.org/abs/2208.03844)
- **HoTT 书的模拟 (外延良基序之间).** f : X → Y 单调, 且 y ≺ f x 时有 x₀ ≺ x 使 f x₀ = y; X ≤ Y 是模拟的类型, 是命题 (KNFX §3.3, §7 转述 HoTT 书 Def 10.3.11, Cor 10.3.13, Lem 10.3.16). [读原文] 难点 2 — [arXiv:2208.03844](https://arxiv.org/abs/2208.03844)
- **Taylor, *Intuitionistic sets and ordinals*, JSL 61 (1996) 705–744.** 传递外延良基关系给出直觉主义序数并支持超限归纳, 但不有向, 后继性质差; 把传递性加强为 plumpness 使后继单调; 有向性必须遗传地定义; plump 序数增长很快; 某些秩函数可不用替换公理, plump 秩看来不行. [检索摘要] 难点 2 — [PDF (作者主页)](https://www.paultaylor.eu/ordinals/intso.pdf); 后续 [Wang, *Some notes on plump ordinals*, arXiv:2601.23070](https://arxiv.org/abs/2601.23070) [只见检索摘要].
- **Fairtlough 的 "结构化" 与 ≺_ζ̄.** 见 Q3. [读原文]
- **本地已有的同类工具.** Coquand 的 `Inf/Ord.agda` 以归纳的逐点关系代替极限处的 `≡`; Aczel 式外延相等 `≐` 按 W 递归定义 (czf-in-mahlo); cj-xu 的 "函数的图代替递归函数" 与内在标准形; Mathlib "基本列返回分类, 规格单独写"; hydra 的 Σ 共尾. 见 `CodeGuide.md` §1(f)(h), `code/TypeTheoryTrees.md` §E, §G. [本地已有]

### Inferences
- **不要指望 "商掉内涵差异" 来定义想要的值.** 选项 `--safe --without-K` 下没有商类型; 用 setoid 模拟商时, `limit`/Ω-极限在商上的提升需要选择 (Chapman–Uustalu–Veltri 的情形是延迟单子, 结构同型: 一个可数分支构造子), QIIT 能避开选择但毁掉基本列. 所以 "对一切树定义值" 的可行形式只剩: 值是树到 setoid (或到某个参照树类型) 的函数, 并证明它尊重 ≼ [判断].
- **单调性的陈述对象可以是 "带参数的路径", 不必是全局序.** 在 Ω-节点处, 改为对 "每个低层参数 c" 陈述 "沿 c 的分支, 值单调", 即 Fairtlough 的 ≺_ζ̄ 形状. 这不需要比较两个孩子, 只要对同一个参数取两次分支 [判断].
- **`Code` 是我方 ≼ 的反演原理的现成模板**: 按两树结构对角递归, 在 (后继, Ω-极限) 处给 ∃c, 在 (Ω-极限, Ω-极限) 处给 ∀c ∃c′, 并证明 `toCode`/`fromCode`. 我方的树无路径构造子, 定义不需要 `bisim` 那部分的互递归 [判断, 未试].
- Taylor 的 plump 条件对应 "后继单调" 与 "有向性遗传" 两件事. 我方若遇到 "≼ 下后继不单调" 或 "两个上界没有公共上界", 可以试遗传地加一个 plump/有向条件到读回域谓词里 [判断, 未试].

### Gaps
- "无选择时 W-型按双模拟的商不能带 limit" 的一般定理, 本轮只找到延迟单子的同类结果, 没有找到对布劳威尔树本身的陈述 (Blass 1983 未找到).
- 在树上 (非记号) 以 "带证明的基本列作数据" 来陈述 FGH 单调性的类型论工作: 本轮未找到 (经典的 Wainer 学派是纸面的).
- Taylor 原文本轮未打开, 只用了检索摘要.
