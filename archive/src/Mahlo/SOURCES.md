# 当前文献依据与适用边界

> 文献本体与重取脚本在 [Sources/](Sources/README.md)。本文件按 RESEARCH.md 节号记每份材料**支持什么、不能据此声称什么**。

2026-09-09 核对。当前未确认一篇完成“Mahlo 宇宙规则 → 自动基本列 → 精确 FGH 校准”全链条的文献；未找到不等于不存在。下列资料按它们在本目标中的用途保留。

| 来源 | 使用位置 | 不能直接推出 |
|---|---|---|
| [Setzer, Extending Martin-Löf Type Theory by One Mahlo-Universe](https://csetzer.github.io/articles/mahlo.pdf)，§3–5 | 原始 Mahlo 规则、参考记号的比较／SC／合法性及独立序数分析依据 | 已有从规则自动提取基本列的算法 |
| [Setzer, Universes in Type Theory Part I](https://csetzer.github.io/articles/modeltypetheoryinaccessiblemahlo.pdf)，§2.1、5.3–5.4 | 模型上界与理论版本审计；注意 KPM⁺ 和 LF 范围 | 等强度就是所需有效证明翻译或基本列转换 |
| [Takahashi 2025](https://lmcs.episciences.org/16822/pdf)，§2.1、Example 2.1、Appendix A | 规则的明确呈现、常值重编码；核对额外宇宙与 Acc | 宿主 Agda 的全部能力等于原 MLM；闭包等式就是下降关系 |
| [Dybjer–Setzer, Predicativity of the Mahlo Universe in Type Theory](https://csetzer.github.io/articles/dybjerSetzerWeylVolume2025/dybjerSetzerWeylVolume2025Final.pdf)，§1–2、Appendix B | 内外宇宙与消去权限 | 可把内部 Mahlo 宇宙当普通归纳类型遍历 |

以下为方法候选，尚未接入 K1/K2。保留入口不代表恢复其旧探索路线：

- [Towsner, Ordinal Analysis by Transformations](https://www.math.cmu.edu/~hpt/pubs/transformations.pdf)，§1–2：调查先生成证明变换、避免预置序数的路径。需另行给出 Mahlo 规则的变换、下降及基本列；其归纳定义系统不能直接视为 MLM。
- [Setzer, Proof Theory of Martin-Löf Type Theory – An Overview](https://csetzer.github.io/articles/overviewProofTheoryTypeTheory2004.pdf)，§2：审计有限表示如何生成无限推导的前提；语法更长仍可能下降，但必须有独立的高度分析。

- [Hancock, Ordinals and Interactive Programs](https://www.lfcs.inf.ed.ac.uk/reports/00/ECS-LFCS-00-421/ECS-LFCS-00-421.pdf)：调查交互／可达性结构是否能从宇宙规则生成前驱。必须核查其是否已经要求输入前驱系统。
- [Freund, Computable Aspects of the Bachmann–Howard Principle](https://arxiv.org/pdf/1809.06774)：调查统一坍缩生成所需的输入结构。把宇宙规则变成其输入，以及基本列输出，都是另需证明的桥梁。
- [Kraus–Nordvall Forsberg–Xu, Type-Theoretic Approaches to Ordinals](https://fredriknf.com/papers/ordinals_tcs2023.pdf)：审计无限分支、序数上确界及可判定表示之间的区别。
- [Aguilera–Pakhomov–Weiermann, Functorial Fast-Growing Hierarchies](https://arxiv.org/pdf/2201.04536)：弱有限指示系统的范数给出下降接口与 \(B_D\)。提供输出端契约，不提供从宇宙规则到指示系统的翻译。
- [Rathjen, The Recursively Mahlo Property in Second Order Arithmetic](https://onlinelibrary.wiley.com/doi/abs/10.1002/malq.19960420106)（MLQ 42: 59–66）：递归 Mahlo 与 β-模型反射的层级刻度。原文未取得，只用摘要级陈述。
- [Fernández-Duque–Weiermann, Fundamental sequences and fast-growing hierarchies for the Bachmann–Howard ordinal](https://arxiv.org/pdf/2203.07758)：在基本列已经生成后，参考其正则性与增长认证方法；不作为 Mahlo 基本列输入。

旧证明枚举、原始递归增长和高阶返回类型的论文记录留在归档，不列为当前执行依据。新的文献调查必须说明它补上“宇宙规则到基本列”的哪一箭头。

本轮定位：Setzer 印刷页 6–7 的 Definition 3.3、3.5、3.6 与 Freund Definition 1.2 支持 [RESEARCH.md §27](Archive/RESEARCH-early.md#27-更具体的正向连接固定截断点的两条坍缩不等式) 的局部不等式核对。该对应是本项目的推导，不是两篇文献已经证明的 Mahlo 提取定理；固定记号上的 SC 尚未成为随任意线性序变化的自然支撑。

后续核对：RESEARCH.md §29 展开 Setzer 的完整形成条件，补入截断点自身的 SC/G 依赖；§30–31 的切开、支撑重建及筛选条件引理是本项目的纸面推导。Freund（所链预印本）Definition 1.1、4.1 与 Theorem 4.3 用来区分输入支撑结构和输出坍缩界，不提供 MLM 到该输入的翻译。

RESEARCH.md §32 的实例使用 Takahashi Example 2.1 的常值重编码；参数交换障碍及其适用边界是本项目的独立证明。Freund §1 的态射明确是序嵌入，不是全部上下文重命名。§34 的下一实例使用 Takahashi Example 2.2 的真实宇宙生成算子，不引用其带额外 Acc 的后续层级作为已获结果。

主代理复核：Takahashi Example 2.2 及 §2.1 支持 RESEARCH.md §35 的局部反射方程。解码相等只支持相容分析的相等替换，不提供前驱域或共尾列。初稿 FS-1/FS-2 不是文献结论，其不共尾论证已撤回；详见 §38。未复核的综述强度简化论断不作为本轮证明依据。

本轮核对：Takahashi Appendix A 的宇宙嵌入／res 计算规则及 Example 2.1–2.2 支持 RESEARCH.md §41–43 的具体等式。Atom/Cong/Trans 是本项目的证书模式，完整前提检查仍未定义；不要把文献规则存在误称为检查器完成。本轮只分析外部推导，不添加对象理论未给出的宇宙消去。局部传输尚未接到 Towsner 的全局进展条件，也没有序数下降或共尾结论。

§45 主代理复核：[Buchholz 的 KPM 分析](https://epub.ub.uni-muenchen.de/3848/1/3848.pdf) §1–2 与印刷页 6 定理／推论；[无穷推导记号](https://epub.ub.uni-muenchen.de/3846/1/13.pdf) §2.3、2.8；Freund Definition 4.1、Theorem 4.3。Rathjen 1991 的存档本轮未能由主代理打开，精确转写不作已复核前提。常值 dilator 例子是本项目从定义的推导，用来纠正统一坍缩具有固定 BH 输出上限的误判，不是 Mahlo 提取方案。

§46 核对：[Freund, arXiv:1809.06759v3](https://arxiv.org/pdf/1809.06759) Definition 3.1、3.2、3.5–3.6、4.2、4.5，Theorem 4.6、9.7；导论中 Kleene–Brouwer 使良基搜索树成 dilator。此文把 KP 公理变成沿 \(X\) 的搜索树，不是 MLM 提取器，也不定义基本列。前印本 [1704.01662](https://arxiv.org/pdf/1704.01662) 作者声明已过时。Girard 的 \(\Pi^1_2\leftrightarrow\mathrm{Dil}(D)\) 完备性不登记为本项目进展。

§46 主代理已核查 Proposition 3.6、Lemma 3.10 在 KB 论证中的使用、Definition 4.5、Theorem 4.6、Proposition 4.9 与 Theorem 4.11。修正了“语义满足关系必是构造输入”以及“MinU 可直接插入”的过强表述；MLM 的保强度逻辑呈现与枝→模型定理尚缺。

§47 主代理核查：[Setzer 1996](https://csetzer.github.io/articles/uppermahlo.pdf) Definition 3.1、4.3–4.4；[Part I](https://csetzer.github.io/articles/modeltypetheoryinaccessiblemahlo.pdf) Definition 5.2、印刷页 26–29。保留统一阶段界及反射闭包机制，撤回初稿的直接保强度声称、L_w 混用和“有名字／全部函数”的错误模型二分。

§48 的条件统一界是主代理基于 Part I 页 26–27 的最小闭包阶段／代码加入定义，以及页 14 的模型嵌入归约所作推导。θ 已满足闭包是前提；没有从文献取得可计算的 C(β)，也没有一般 f 或基本列结论。Grok 初稿关于有限推导无法求界的断言已撤回。

§49 主代理再次核查 Part I Definition 3.1、§3.2、§4.1、§5。保留条件界与对象层子宇宙构造；纠正最小阶段、Σ 嵌入方程、U_α 索引，并撤回对象算子与阶段函数的直接等同。未证明内部阶段打包是必需条件。Setzer 综述只能作为模型／既定 OT 分析的补充来源，本轮没有从中取得规则生成的 C 或基本列。

§50 主代理核查 Takahashi Example 2.1–2.2、Appendix A 的 Uf inΠ、Uf inres0/1；原文证明内部闭包，没有给整阶段提升失败的反例。§50 的条件闭包引理由 §48 加族阶段局部性直接推出，并非原文新增定理。撤回“选定界越界即实际闭包失败”与语法深度自动分层的推断。下一轮目标为同文 Definition 2.3 的高阶算子，而非重复常值实例。

§51 对象构造取 [Takahashi Definition 2.3、Example 2.4](https://lmcs.episciences.org/16822/pdf) 与 Appendix A 的 MinN_n、Min+、MinΣ、MinU；\(h^M\) 的四支是原文 \(+\) 消去定义。阶段／Fam／普通闭包沿用 Part I Definition 3.1、5.2 与 §48 的 \(C\)。组合引理与 \(\theta(\xi)=C(\max(\sigma,\tau,\Phi(\xi)))\) 是本项目在给定 \(\Phi\) 下的充分条件推导，不是 Takahashi 已证的序数定理，也不生成 \(C\) 或 \(\Phi\)。Example 2.4 作非空有限下标实例；\(z=\widehat N_M\) 的变体检验小类型下标。缺口“一族 \(\Phi_n\mapsto\) 共同 \(\Phi\)”不是文献结论。

§51 主代理核查 Definition 2.3 的四分支与 fM 指标公式；补上 κ+3<M 及 C 的阶段前提。非恒定 q_n 及与 g 混合的共同界为本项目基于自然数归纳、普通和闭包与 §48 的条件推导，不是文献给出的基本列或强度定理。初稿 \(\lambda w.\mathrm{const}(q_n)\) 的类型笔误已改为 \(\lambda w.q_n\)。

§52 主代理核查 Kohlenbach, Proof Interpretations, Chapter 4：Definition 4.3、4.5、Lemma 4.8、Proposition 4.10、Theorem 4.11／Remark 4.12、Corollary 4.13。保留有限类型 majorization 和有界参数统一取界的准确范围；未验证 MLM／MinU 的迁移。Howard 1972 DOI 全文访问失败，撤回其精确共尾构造作为已核实依据。Θ 与阶段见证的有效生成仍未证明。

§53 主代理核查 Setzer 1996 Definition 3.1、4.3(b)、4.4、Lemma 4.5。纠正 →* 为函数空间关系；注明 Inacc 参数在原文两处的不一致；撤回未验证的 φ_g 等价式及完整 Δ₀ 生成声称。FAM/K 模板为本项目基于给定 PER／解码数据的有界公式构造，未包含模型历史的生成与有效见证。

§54 主代理核查 Positive Inductive-Recursive Definitions, Definition 2.1–2.2、Example 2.6、3.6，以及 Dybjer–Setzer 2025 页2对内部 Mahlo 超出普通 IR 的陈述。更正 IR⁺ 可使用非离散底范畴及 Π 可在 Set≅ 上处理。两个有限例／幂函子反例为本项目从定义作出的推导，不是所有规则提取技术的排除定理。

§55 主代理以 Takahashi Example 2.2、Appendix A 的 res 形成规则检验标签候选。严格低标签限制会拒绝重复 res，为本项目对候选的具体反例；并非对原 MLM 的反例。原始语法重命名只支持支撑自然性，没有建立有序进展或强度校准。

§56 核对：[Freund–Rathjen, arXiv:2112.08005](https://arxiv.org/pdf/2112.08005) Definition 1.1、1.4、2.5–2.6，Theorem 1.6，Corollary 1.7、2.2；[Freund, arXiv:2006.12111](https://arxiv.org/pdf/2006.12111) 导论与 Theorem 6.7 的 2-ptyx 不动点；[Rathjen, arXiv:2010.12453](https://arxiv.org/pdf/2010.12453) 对一型 WOP→\(\omega\)-模型、二型坍缩→\(\beta\)-模型的分界。Theorem 1.6 的 (iv) 是迭代容许集，不是递归 Mahlo 或 MLM；Example 1.5 使用 Buchholz \(\mathrm{OT}\) 作实例。\(\psi_\nu(D)\) 由 dilator 生成比较，仍预填 \(\nu\) 与 \(D\)，不提供从宇宙规则到 \(D_f\) 的翻译，也不定义基本列。2-ptyx 的 \(\Pi^1_2\)-归纳等价式不能用来从类型层猜测 Mahlo 强度。MinU 全局义务与 \(\forall D.\) 良基闭点的对应是本项目的接入尝试，不是原文已证的 MLM 提取定理。

§57 核对：[Aguilera–Pakhomov–Weiermann, arXiv:2201.04536](https://arxiv.org/pdf/2201.04536) §2 的 \(\mathsf{LO}\)／有限函子／\(\subseteq\)-保持／指示系统定义，§3 的 \(N\alpha=\min\{n\mid\alpha\in D(n)\}\)、\(B_\alpha\) 定义、Definition 3 与 Lemma 4 的 \((n,\alpha)\)-正规形，Definition 8 的形式坍缩、Lemma 13 的自然同构、Remark 14 的 ptyx 说明、Theorem 16 与 Lemma 18（后者同时给出弱有限的含义及 \(\hat D\) 补参数构造）。引理 A–D 与命题 E（范数基本列的下降、非降、共尾，以及 \(B_\lambda(n)=B_{\lambda[n]}(B_{\lambda[n]}(n))\)）是本项目从这些定义作的推导，不是原文陈述的定理；原文也没有给出 \(B\) 与 CONTRACT 的 \(F\) 的逐点换算。Theorem 16 表明 \(D\mapsto B_D\) 虽是 ptyx，强度仍只有 \(\Pi^1_1\text{-CA}_0\)，可作"类型层级不给强度"的第二个实例。

§57 的 Rathjen 1996（MLQ 42: 59–66）只用摘要级陈述："递归 Mahlo 性对应二阶算术中某种 β-模型反射，并由此刻画相对 superjump 泛函可计算的实数"。Wiley、ACM、PhilPapers 与 Semantic Scholar 四条路径本轮均未取得原文或完整摘要字段，故检索摘要中更精确的 \(\Delta^1_2\text{-CA}+\mathrm{BI}\) 加 \(\Pi^1_3\) 语句 β-模型反射形式记为**待核**，不作推理前提。§57.2 只依据"闭点／链型原则"与"反射型原则"的结构差别，以及 §56 已核的 Freund–Rathjen Theorem 1.6(iv)、Corollary 1.7 的右端层级。本轮检索未找到递归 Mahlo 层级的良序原则或 dilator 刻画；未找到不等于不存在。

§57.1 的 \(D_g\)（项 \(c(x)+k\)，\(k\le3\)）是本项目按 §48 的 \(B_g(\beta)=C(\beta)+3\) 作的构造，用来证明界项级读法给出零强度的弱有限 dilator；"界数据欠定比较规则"同为本项目论证，不是文献结论，也不排除其他形式的 \(D_f\)。

§58 的观察 G、命题 F、命题 H 均为本项目从 [APW arXiv:2201.04536](https://arxiv.org/pdf/2201.04536) 的定义所作的推导，不是原文陈述的定理。命题 F 使用原文 Lemma 18 的补参数构造，作用于 §45 的常值 dilator；原文用该构造把任意指示系统化为弱有限的，本项目用它测量“弱有限 + 序型正确”的可满足性。命题 H 的两个系统 \(D_1,D_2\) 与 \(n+2^n\)／\(n+2^{\Theta(n^2)}\) 的计算是本项目的构造与验算。原文导言自述所定义的确切函数依赖于所选序列、只有“自然”的选择才规则，且已知的合理定义在充分封闭的序数处一致——“自然”与“合理”在原文未形式化，本项目据此把举证责任留给“一致”一方，并**未**证明该偏离在 \(\alpha_M\) 处仍然存在。Kreisel 1952（原文 Theorem 1）与 Buchholz 的 \(\Pi^1_1\text{-CA}_0\) 版本在 §58.3 只作典范性义务的模板引用，不作 MLM 结论。

§58 本轮再次尝试 Wiley、ACM 与 Semantic Scholar 三处取得 Rathjen 1996 原文或完整摘要字段，均未成功；§57.2 的待核标记维持不变。

§59 核对：[Arai, Lectures on Ordinal Analysis, arXiv:2304.00246](https://arxiv.org/pdf/2304.00246) §2 的 \(\mathrm{RM}_i\) 定义与"\(V\in\mathrm{RM}_2(\mathrm{RM}_2)\) 当且仅当 \(V\) 递归 Mahlo"、同节"对 KPM 只需两步坍缩 \(\alpha\mapsto\sigma=\psi_M(\alpha)\in\mathrm{RM}_2\) 与 \((\sigma,\beta)\mapsto\psi_\sigma(\beta)\)"；Lemma 3.26.1 及其证明（子项集可充当有限的 \(K(\alpha)\)）；Definition 3.36 的 \(E,K_\delta,k_\delta\) 与注记 \(K_\delta(\alpha)<a\iff\alpha\in H_a(\delta)\)。该讲义的 \(\mathrm{OT}(\Pi_3)\) 是 \(\Pi_3\)-反射的记号系统，强于 Mahlo；本项目只取与层级无关的结构事实，**不**把它当作 \(\mathrm{OT}(M)\)。Setzer 的 mahlo.pdf 本轮无法抽取文本（自定义字体编码），其逐条定义仍未取得。§59.2 的"写成 \(\psi_\nu(D)\) 需要不动点条件"与 §59.3 的两端同形是本项目的判断，不是文献结论，也不是不可能性证明。

§60 的命题 J、推论 K、命题 L、命题 M 均为本项目从 APW 的指示系统定义与 Lemma 18 所作的推导。命题 M 用到 \(2^\omega\) 的形式二进制 Cantor 范式序型为 \(\omega\)。命题 L 只陈述补参数后各骨架的**最小**范数等于其枚举位次，没有证明"按复杂度枚举所得范数与符号计数在 FGH 层面等价"——后者仍是未证事项。§60 对 §58.1 的修正限于"弱有限性不是额外负担"，§58.1 关于廉价性的结论不变。

§61–§64 全部是本项目在给定参考记号系统上的推导，不引用新文献：§61.1 命题 N（函子化的充分条件）关掉 §30 的缺口；§61.2 的结算表按 CONTRACT §4 逐项，其中 C1 依赖 Setzer／Rathjen 的既定良序证明与序数界，本项目未重证；§62 的引理 A–C 与命题 P 给出 C4 及可计算阈值 \(|\beta|\)；§63 的命题 Q、命题 S、定理 R 与 §64 的命题 T 给出 C5 的归约。APW 的 Lemma 4 只用于承担 C2 的正则性。定理 R 与命题 T 的前提（范数可比性、低层吸收、参考指派的范数有界性与共尾模数）都**未**对具体的 \(\mathrm{OT}(M)\) 核对，因为 Setzer mahlo.pdf 的文本本轮未能抽取。C6 的 Kreisel 型刻画未处理。以上均不改变 CONTRACT 的 E 未满足这一事实。

§65–§66 核对：[Setzer, mahlo.pdf](https://csetzer.github.io/articles/mahlo.pdf) §3（印刷页 5–7）的 Preliminaries 3.1、Definition 3.2 的 (T′1)–(T′7) 与 \(\mathrm{length}\)、Definition 3.3 的"按 \(\mathrm{length}(a)+\mathrm{length}(c)\) 递归同时定义 \(\prec'\) 与有限集 \(\mathrm{SC}_\kappa,\mathrm{sc}_\kappa,\mathrm G_\kappa\)"、Lemma 3.4、Definition 3.5(a)(b)、Definition 3.6 的 (OT1)–(OT6)；以及印刷页 19 的 Theorem 5.14。该 PDF 用 Ghostscript 6.0 的 Type 3 位图字体，`pdftotext` 抽不出文本，本轮改为 `pdftoppm` 渲染后逐页读图取得，因此所有引用都是**读图转写**，不是文本抽取，复核时应对照原页。已发现并记录一处印刷下标不一致（(T′2) 的 length 求和范围，见 §65.1），按自洽读法执行。

命题 U（length 层有限）、\(\lambda_M=\psi_{\Omega'_1}\Omega'_{\mathrm M+\omega}\) 的形成条件展开与 \(\mathrm{length}(\lambda_M)=8\)、§66.4 的三条下界与 \(F_0,F_1,F_2\) 的手算，均为本项目的推导与验算。端点项所denote的序数等于其下方初始段的序型这一点依赖原文的良序证明，本项目未重证；MLM 强度的上界方向依赖 [Se96a]，同样未重证。[Bu90] Buchholz, *Wellordering proofs for systems of fundamental sequences*（1990 草稿）仅从参考文献表得知，未取得，不作依据。

§67–§69 的新引用同为 mahlo.pdf 的读图转写：印刷页 8 的 Definition 3.7、Lemma 3.8（(c) 的证明按 \(\mathrm{length}(a)\) 归纳）与 **Definition 4.1(a)(b) 的 MLM 完整符号表**（已抄入 [INPUT.md §2bis](INPUT.md)）；印刷页 18 的 Lemma 5.7（按 \(\mathrm{length}(x)\) 归纳，情形含 \(\psi_{\Omega_{c+1}}c,\psi_{\mathrm M}b,\psi_{\psi_{\mathrm M}b}c\)）、Lemma 5.8、**Definition 5.9**（\(\mathrm{Univ}(u_0,v_0)\) 丢弃 \((x_1,y_1)\) 返回固定族，即常值算子）；印刷页 19 的 Definition 5.12、Lemma 5.13（\(\mathcal W_{S(i)}=\mathrm W(\mathcal W_i)\cap\Omega_{\mathrm M+S(i)}\)）。

命题 V（进步性）与推论 W 为本项目推导；其引用 Theorem 5.14 的方式有三条未完成的形式化义务，已在 §67.2 列出。§67.3 指出 C6 的反向依赖 C5，这是本项目的判断。§68.1 的构造子对应表分"已核"与"推断"两栏，推断栏（\(\mathrm U(f,g)\leftrightarrow\psi_{\mathrm M}b\) 等）**不是**原文陈述。§69 的否定结论（\(\mu\) 不能按语法树递归）由 \(v_0:\mathrm T(u_0)\to\mathrm V\) 的上确界直接得到，与 §10–§11 的旧结论同源；§69.4 的"\(\Omega'\) 对应族的上确界、\(\psi\) 对应坍回"同样是推断，不是原文陈述。[Bu92] Buchholz, *A simplified version of local predicativity* 仅从参考文献表得知，未取得。

§70 核对：[Arai, arXiv:2304.00246](https://arxiv.org/pdf/2304.00246) §1 的 Definition 1.7（原文标注出自 [Buchholz86]）、Proposition 1.8（尤其 1.8.6 的 \(\gamma\in\mathcal H_\alpha(\beta)\iff\mathrm{SC}(\gamma)\subseteq\mathcal H_\alpha(\beta)\)）、Definition 1.16 的控制条件 (3) 与四条规则（特别是 \((\bigwedge)\) 的 \(\mathcal H_\gamma[\Theta\cup k(i)]\vdash^{a(i)}_b\)、\(a(i)<a\)）、Lemma 1.17–1.19。这些是 \(\mathrm{KP}\omega/\Omega\) 的呈现，**不是** MLM 的；§70.3 的四条迁移缺口是本项目的清单，不是文献结论。[Bu92] Buchholz, *A simplified version of local predicativity*（Proof Theory, CUP 1992, 115–147）本轮仍未取得全文，只经由 Arai 的呈现使用同一机制。§70.4 把 K1 分成"手工"与"自动"两层，是本项目的判断；把后者对应到 Towsner 的纲领同样是判断，不表示该纲领已覆盖 MLM。

§71–§73：§71 的无穷演算设计（项、层次 \(|t|\)、支撑 \(k(t)\)、\((\bigwedge)\) 的分支检验、(Mahlo) 规则）与 §72 的论证（\(\varphi_{f,g}\) 即 §48–§51 的条件界；\(\mathrm R\)-递归展开 \(\widehat{\mathrm U}\) 的反例排除按项归纳）全部是本项目的设计与推导，**不是**任何文献已给的 MLM 演算；§71.5 列出的五条义务一条未证。§73 核对 [Towsner, Ordinal Analysis by Transformations](https://www.math.cmu.edu/~hpt/pubs/transformations.pdf)（APAL 投稿本 2008-02-27）的摘要、导论与 Definition 3.1–3.4：通用证明系统（推理符号、元数、前提／结论式、本征变量）、truncated／augmented 系统与 \(\Theta(d)\)。作者自述目标系统强度为递归不可达一档、确切强度未知，并称更强不动点的迭代形式"难以描述"、推广到完整 \(\mu\)-演算是"hope"。本项目据此判断该纲领自动化的是序数的预先设计而非推理规则的设计，且尚未到达 Mahlo——这是判断，不是原文陈述。§73.3 对 CONTRACT §1 的重读（允许预先固定覆盖某规则类的通用方法）是对本项目自己契约文本的解读；§73.4 据此指出 §71.2 把 \(\mathsf{OT}\) 当输入，作为 E 的一步无效。

§74 的命题 X（\(F_\omega\) 吸收初等函数）与 §75 的命题 Y（提取器不可能全域）均为本项目的推导。命题 X 用到 §65.1 的 length 表与 §62 的引理 A、C；\(\omega[n]=\lfloor n/2\rfloor\) 依赖"自然数 \(k\) 在 \(\mathsf{OT}\) 中为 \(k\) 个 \(1\) 的和、length 为 \(2k\)"这一读法（见 §65.1 记录的 (T′2) 下标不一致）。命题 Y 是标准的对角线论证（把停机问题归约到"端点是否为极小元"），其中的公理族 \(A_e=\mathrm{PA}\cup\{\neg\mathrm{Halt}(e,e,n)\}_n\) 是本项目所构造；证明系统的可判定呈现沿用 Towsner Definition 3.1 的形状。命题 Y **不是**不可能性定理：它只排除全域提取器，不排除限定规则类的提取器；§75.2 的判据（类上一致性须有统一论证）是本项目由该证明读出的判断。

§76 核对：[Arai, arXiv:2304.00246](https://arxiv.org/pdf/2304.00246) §5 的 Proposition 5.1、5.2，**Definition 5.3 的五条**（\(\mathcal H_a(X)\) 的 Skolem 闭包含 \(\psi^{\vec\nu}_\sigma(b)\)；Mahlo 类 \(Mh^a_k(\alpha)\)（\(2\le k<N\)，\(\vec\nu\) 长度 \(N-k\)，\(Mh^a_k(\vec\nu)=\bigcap_{i\ge k}Mh^a_i(\nu_i)\)，为 \(\Pi_{k+1}\)-类）；\(\psi_\sigma(a)\) 与 \(\psi^{\vec\nu}_\sigma(a)\) 的 min 定义式），Lemma 5.4–5.6；§6 把有限向量推广为有限支撑函数 \(f:S^+\to\mathrm{ON}\)、关系 \(f<_c\xi\) 与 Veblen 函数 \(\tilde\theta_b\)，并给出"\(k\) 指示 \(\Pi_k\)-公式或 Mahlo 算子 \(M_k\)、\(\nu_k\) 对应推导高度"的读法。

**本节撤回本项目此前的两处断言**：§73.5 的"没有找到覆盖反射规则类的统一坍缩定理"与 §75.4 中 (b) 的"未知"标注。该装置存在，且其配方（Skolem 闭包 + \(\psi_\sigma(a)=\min\{\kappa:\mathcal H_a(\kappa)\cap\sigma\subset\kappa\}\)）不随 \(N\) 变、数据结构由反射层级决定。这是**集合论**的 \(\Pi_N\)-反射族；§76.4 的三条迁移限制（不得用翻译替代、MinU 须证为某 \(M_k\)-反射的实例、不得输入 \(\psi\) 记号）是本项目的判断，不是原文陈述。原文也**没有**对 MLM 或任何类型论作此分析。

§77 的定位（MinU 是 \(M_2\)-型反射、\(N=3\)、向量长度 1）是本项目由三处已核事实读出的**判断**：§47 已核的 Setzer Part I 页 26–29 的两次收集论证、§59.1 已核的 Arai \(M_k(\mathcal X)\) 记法与 \(\mathrm{RM}_2(\mathrm{RM}_2)\)、§66.1 已核的"对 KPM 只需两步坍缩"。三处层数一致是检验，不是证明；原文**没有**把 MinU 等同于任何 \(M_k\)-反射。§77.3 关于 \(|\mathrm{KPM}|=\psi_{\Omega_1}(\varepsilon_{\mathrm M+1})\) 与 \(\alpha_M=\psi_{\Omega_1}(\Omega_{\mathrm M+\omega})\) 的比较，前者未在本项目核过原文，只作对照；结论只依赖 §66.1 的 Theorem 5.14 与 §66 已核的 Definition 5.12／Lemma 5.13。§77.4 的三条差距与 §77.5 的三步路径同为本项目的判断。

§78–§80 全部是本项目的设计、更正与检验，不引用新文献。§78.2 把 \(C\) 消解为 \(\mathrm{Refl}(\mathrm{Univ}(\cdot))\)，依据是 Definition 4.1 已核的事实"MLM 的宇宙只有 \(\mathrm V\) 与各 \(\mathrm U(f,g)\)，普通宇宙构造子全带 \((f,g)\) 参数"加 Definition 5.9 的常值算子；这是判断，不是原文陈述。§78.3 的序数增量表是设计，未证。**§79.1 更正 §69.1 的一处混同**：\(\mathrm{Univ}(q)=\mathrm{const}(q)\) 是常值算子，§48 的 \(g\) 是宇宙生成映射 \(q\mapsto(\widehat{\mathrm U}(\mathrm{Univ}(q)),\mathrm s_{\mathrm{Univ}(q)})\)，两者的 \(\varphi\) 形状不同。§79.2 的基础情形是一行推导；§79.3 依赖 (Refl) 结论的封闭性，尚未有该规则的可采纳性证明，故是条件性的。§80 的检验中 \(c\)（单次 Refl 的序数增量）取作未定常数，其值须由坍缩引理 (ii-b) 定出，故 §80.3 的 \(a=\omega\cdot c\) 是条件性结论。§80.2 指出 \(\psi_{\mathrm M}\) 不连续、\(\mathsf{OT}\) 只指示可数多序数，因此"对层取上确界"在演算里不可行——这是本项目的论证。

§81 的 [NormFGH.lagda.md](Hierarchy/NormFGH.lagda.md) 是本项目的形式化，不依赖任何文献结论：它把 §62 的引理 A–C 与命题 P 转写为 Agda 并机器检验（Agda 2.8.0 + standard-library 2.4，`--safe --cubical-compatible`，无 postulate、无洞、无终止绕过）。文件中的 `FSNorm` 是**记录类型（假设）**，不是构造；\(\mathsf{OT}\) 能否实例化它由 §65 在纸面上论证，未形式化。因此该文件不构成 CONTRACT 的 E 的任何证据，只机器检验了 C4。

§82 核对：[Buchholz–Cichon–Weiermann, *A Uniform Approach to Fundamental Sequences and Hierarchies*](https://epub.ub.uni-muenchen.de/3849/1/16.pdf)，Math. Log. Quart. 40 (1994) 273–286。核到：§1 的 (B1)–(B6) 与 Lemma 1、Lemma 2；导论的 Cichon 定义 \(\alpha[n]_C=\max\{\beta<\alpha:N\beta\le N\alpha+n\}\)、不提基本列的 Hardy 层级、以及 (EMP)；§3 的 Theorem 4（(a) 带范数 Bachmann 系统、(b) \(p(\lambda+n)=N\lambda[n]\)、(c) 层级的范数形式）；§4 的通用配方（有限函数符号 + 原始递归良序 + 零常量 + 和符号 ⟹ 计数范数满足 Theorem 4 的假设）及其“所有迄今证明论用过的记号系统都满足”的说明。文本经 OCR，转写已逐条比对，复核宜对照原页。

**本条同时是一次归属更正。** [RESEARCH.md §57](RESEARCH.md) 的命题 E 与 §62 的引理 B、C、命题 P 此前标为“本项目的推导”；它们确是本项目独立推出，但**不是新结果**——Cichon 的方法与 BCW 的 (EMP) 已有同一内容。各节已加更正注记，[NormFGH.lagda.md](Hierarchy/NormFGH.lagda.md) 亦已加注。

**以及一处实质修正**：本项目用绝对范数界 \(\|\beta\|\le n\)，文献用相对界。绝对界一般不满足 Bachmann 性质 (B2)（§82.3 给出反证），故 §61.2 结算表中 C2 的“正则性”一栏降级。修正办法是现成的：按 Theorem 4 改用 \(p(\alpha+n)\) 形式的界。BCW 的框架固定在 \(\tau=\omega^\omega\cdot\tau_0\)；\(\alpha_M\) 是否落在其适用范围、以及 Setzer 的 \(\mathrm{length}\) 与 BCW 的计数范数是否互相受控，本轮均**未**核对。

§83 是**本项目基于 §65.1 已核签名所作的核对**，不是 BCW 或 Setzer 任一方陈述过的结论：BCW 范数在 \(\mathsf{OT}\) 上的具体写法 \(N=\#\{\varphi',\psi,\Omega'\}+\#\mathrm M\)（把原文的“\(\omega\)-型函数符号”理解为生成加法主元的那些）、§4 配方五条结构条件的逐条比对、有限性论证（每个 \(0\)-叶必是 \(\varphi'/\psi/\Omega'\) 的参数，因 \(0\notin\mathsf P'\)）、以及 \(N\le2\,\mathrm{length}\)、\(\mathrm{length}\le4N\) 的边数计算，均为本项目推导。\(\tau=\alpha_M\) 合乎 \(\omega^\omega\cdot\tau_0\) 依赖 \(\alpha_M\) 为 \(\varepsilon\)-数，这一点本项目未重证。以上均未形式化。

§84 是本项目的形式化推广与定义重述：[NormFGH.lagda.md](Hierarchy/NormFGH.lagda.md) 的 `FSNorm` 增加抽象预算 `bud` 与两条公理 `bud-mono`、`bud-lift`，使 §62 的引理 A–C 与命题 P 对绝对界与相对界同时成立并机器检验（`agda --safe`，无 postulate／无洞）。**Bachmann 性质 (B2) 不在该形式化内**，它由 BCW Theorem 4(a) 保证，依赖 `bud` 的具体形状。§84.2 的大数最终形式与 §84.3 的结算表为本项目所作；其中 C1 依赖 Setzer 的 Theorem 5.14 与 [Se96a] 的上界，本项目未重证。

§85 的 [OTNorm.lagda.md](Hierarchy/OTNorm.lagda.md) 是本项目的形式化：按 §65.1 已核的 (T′1)–(T′6) 定义项语法（加法主元 \(\mathsf P'\) 单列类型，使“和的分量必属 \(\mathsf P'\)”成为类型层面的事实），并机器检验 \(N t+1\le 2\,\mathrm{length}\,t\) 与 \(\mathrm{length}\,t\le 2\,N t+1\)（`--safe`，无 postulate／无洞）。**本条订正 §83.4 的两处**：原写的 \(\mathrm{length}\le4N\) 在 \(t=0\) 处失效，且常数偏松。§83 的其余部分（BCW §4 的五条结构条件、有限性论证、Theorem 4 的假设、\(\tau=\alpha_M\) 的适用范围）仍是纸面核对，未形式化；\(\prec\) 未形式化。

§86 是本项目对 §65.1 已核定义的展开，**不是** Setzer 陈述过的引理：由 (≺′5) 的第二支加 \(\mathrm{sc}_{\mathrm M}(b)=\mathrm{SC}_{\mathrm M}(b)\) 与 \(a\preceq'A:\iff\exists x\in A.\,a\preceq'x\)，推出 (OT4) 在 \(\pi=\mathrm M\) 时第一个合取项 \(\mathrm{SC}_{\mathrm M}(b)\prec\psi_{\mathrm M}b\) 无条件成立，判据只剩 \(\mathrm G_{\mathrm M}(b)\prec b\)。(≺′5) 的四支、\(\mathrm{sc}_\kappa\) 与 \(\mathrm{SC}_\kappa,\mathrm G_\kappa\) 的子句均为读图转写（mahlo.pdf 印刷页 6–7），复核宜对照原页。论证依赖“\(\mathrm{SC}_{\mathrm M}(b)\) 的元素都是 \(\psi\)-项”这一读法。

§87 的 [Bachmann.lagda.md](Hierarchy/Bachmann.lagda.md) 形式化 [BCW 1994](https://epub.ub.uni-muenchen.de/3849/1/16.pdf) **Lemma 1(a)** 的极限情形（`--safe`，无 postulate／无洞），接口只取该证明用到的 (B3)、(B4) 与序的传递性、三分法。**本条同时收紧本项目先前的一处说法**：§57.3、§61.2、§65.3 把"不需判定零／后继／极限"说得过宽——那只在**计算**层成立；证明基本列构成 Bachmann 系统要用序的三分（见 §87.1）。未形式化：由 Cichon 定义推出 (B3)、(B4)（BCW Theorem 4(a)）；\(\prec\) 本身；\(\mathsf{OT}\) 上的实例化。

§88 在 [Bachmann.lagda.md](Hierarchy/Bachmann.lagda.md) §4 追加 `CichonFS` 接口与 `B3-from-max`：由 [BCW 1994](https://epub.ub.uni-muenchen.de/3849/1/16.pdf) Theorem 4 的极大性定义机器检验出 (B3)（`--safe`，无 postulate／无洞）。本项目的观察是**这一步不依赖任何序数结构**（无后继／极限／良基性），只用序的反自反、反对称与 \(\mathbb N\) 上 \(\le\) 的可判定性；原文把 (B3) 放在 Theorem 4(a) 里一并证，未单独指出这一点。仍缺 (B4)，它依赖 Theorem 4(b) 与后继／极限结构，未形式化。

§89 在 [Bachmann.lagda.md](Hierarchy/Bachmann.lagda.md) §5 追加 `CichonFS⁺`（加后继、极限与 [BCW 1994](https://epub.ub.uni-muenchen.de/3849/1/16.pdf) 对 \(p\) 的假设），机器检验 Theorem 4(b) 的下界方向、(B4)，并由 `CichonFS⁺` 造 `BSys` 实例闭合整条链：Cichon 极大性定义 ⟹ (B3)∧(B4) ⟹ (B2) 的极限情形（`--safe`，无 postulate／无洞）。接口中的 `fs-max`、`lim-sucC` 等仍是**假设**；真实 \(\mathsf{OT}\) 是否满足要先形式化 \(\prec\)，未做。非极限情形由 (B1) 平凡，不在形式化内。

§90 在 [OTNorm.lagda.md](Hierarchy/OTNorm.lagda.md) §7 追加 §83.3 中 \(\mathsf{OT}\) 特有的两条并机器检验：直接子项的 \(\mathrm{len}\) 严格更小；和的分量个数受 \(\mathrm{len}\) 控制（后者仍靠 \(\mathsf P'\) 的类型层面约束）。“有限签名上受界语法树有限多”是通用归纳，本项目不把它算作对 \(\mathsf{OT}\) 的核对，未形式化。

§103 核对 [Setzer, Universes in Type Theory Part I](https://csetzer.github.io/articles/modeltypetheoryinaccessiblemahlo.pdf)（2005-07-08 版，32 页，**该 PDF 文本可抽取**）§2.5：模型为 PER 模型（原文明述）、Definition 2.6 的 \(\mathrm{Clos}_\to,\mathrm{Flat},\mathrm{PER}\)、\([\![\mathrm N]\!]\) 与 \([\![\Sigma]\!]\) 的显式定义（\(\Pi,\mathrm W,+,\mathrm{Id}\) 原文称“similarly”）、Definition 2.7 的 \(\mathrm{Correct}\)、以及 soundness 元定理 \((\mathrm{ML}'\vdash\Gamma\Rightarrow\theta)\to\mathrm{KP}'\vdash\mathrm{Correct}(\Gamma\Rightarrow\theta)\) 与原文关于它**必须**是元定理的说明。**基段的完整证明在 [Se93]（Setzer 博士论文），本项目未打开**，故 (H4) 只能记为“陈述与框架已核、证明在已注明来源中未复核”。

同节另核出一段本项目先前未注意的内容：原文对每个 set \(A\) 指派序数 \(o(A)\ge3\) 使 \([\![A]\!]_\rho\in L'_{o(A)}\) 且**与环境 \(\rho\) 无关**，子句为 \(o(\mathrm N)=3\)、\(o(\Sigma)=\max+2\)（\(\Pi,+,\mathrm{Id},\to,\times\) 同）、\(o(\mathrm W)=(\max)^{+}+1\)（\(\alpha^+\) 为下一个容许序数，理由是 \([\![\mathrm W]\!]\) 由迭代算子定义）。这是一个**现成的、规则制导的序数指派**，本项目 §78.3 想列的增量表在基段已由原文给出。§103.3 据此修正 §78.2 的“阶段运算代数只由后继与 Refl 生成”为 \(\{+2,(\cdot)^{+},\mu\}\)。

§104 核对 A. Setzer, *An upper bound for the proof theoretical strength of Martin-Löf Type Theory with W-type and one Universe*（33 页草稿，1996，[1papdiss.pdf](https://csetzer.github.io/articles/1papdiss.pdf)，文本可抽取）：§6 开头对主引理用途的说明、**Lemma 6.1（Main lemma）的三条陈述与“对推导归纳、按最后一条规则分情形”的证明方式**、Lemma 5.10（代换引理，五条）、Lemma 5.11、Definition 5.12、Definition 4.8–4.9（解释与项对关系）、Theorem 7.14（含**内涵版** \(i1\)）。

**边界**：该文处理 MLTT + W 型 + **一个**宇宙，不是 MLM；本项目据 §98.1（基段在 \(\mathcal C\) 上固定）主张基段情形可转写，但**转写未逐行执行**。该文是 1996 年草稿，非正式发表。Lemma 6.1 的证明本项目只核到陈述与证明方式，**未逐个情形复核**。

§107 复核 [Setzer 1996](https://csetzer.github.io/articles/1papdiss.pdf) §6 的证明正文。**关键发现**：原文自述“We treat only some examples of the rules, covering the more complicated ones”——该引用**不能**读作“全部情形已在印刷品中验证”；§104.3、§106.4 的表述据此收紧。实际做了的情形已逐条检出（见 §107.1 的表），其中**全部基段消去规则在列**。

**本项目据此自我更正**：§106.2 的转写引理原称基段情形只依赖三样东西，读过 \((\mathrm W^{I,=})\) 的证明后发现漏了第四样——原文该情形用到 \(\mathrm{level}(\cdot)\)、\(I_n\)、以及 \((\Delta_0\text{-coll})\) 与 \(\mathrm{Ad}(L_{I_n})\)。更正后四条假设仍都不提宇宙，转移结论不变。这与 §103.3 由 \(o(\mathrm W)=(\max)^{+}+1\) 推出的“代数含 \((\cdot)^{+}\)”互相印证。原文的宇宙情形 \((\mathrm U^I),(\pi^{I,=}),(\sigma^E)\) 针对其单个宇宙（不可达 \(I\)），**不**转移到 MLM，由本项目的命题 Z 取代。

## §113（目标 3）

**来源**：Setzer, *Universes in Type Theory Part I — Inaccessibles and Mahlo*, §5.2（文本可抽取，非读图）。

**支持**：
- \((\mathrm{KPM})^+\) 的定义（\(\mathrm{KP}\omega\) + 一个递归 Mahlo 集 + 其上有限多个容许）与 (Mahlo) 公理的 \(\Delta_0\) 形式——逐字引用。
- "we need \(<\omega\) many admissibles in order to interpret the basic set constructions on top of \(V,T_V\)"——逐字引用。
- Theorem 5.3 (a)(b)(c)：可建模、\(|\mathrm{MLW}+(\mathrm{Mahlo})|\le|(\mathrm{KPM})^+|\)、内涵版亦成立。
- Theorem 5.4：等号，反向据其 [30]（= mahlo.pdf 的发表版）。

**不能据此声称**：
- \(|(\mathrm{KPM})^+|\) 的**数值**。Part I 未在已读段落给出，本项目**未取得** Arai [3][4] 或 Rathjen 的 KPM 序数分析。C1 的"不超报"因此未核。
- [30] 本身未打开；Theorem 5.4 的反方向只是转引。
- §113.2 的"逐字吻合"是**形状与定义的一致**，不是把本项目的定理 S′ 等同于原文的 Theorem 5.3 之证明——两者是同一构造的两次独立给出，本项目未逐行比对原文的模型构造。

## §114（目标 4）

**来源 1**：Buchholz–Cichon–Weiermann 1994，页 283–284（**读图转写**，`pdftoppm -r 170` 后视觉读取；OCR 文本在第 4、7 条上残缺，故以图为准）。

**支持**：
- \(\mathcal T(M)\) 与 \(<\) "defined as in RATHJEN [10]"，"characteristic for the theory KPM formalizing a recursively Mahlo universe"——逐字。
- 范数七条、\(\alpha[x]_M:=\max\{\beta<\alpha:N\beta\le3^{3^{N\alpha+x+1}}\}\)——逐字。
- Corollary：\(\bigcup\{\mathrm{PR}[\{H_\alpha\}]:\alpha\in\mathcal T(M)\}=\mathrm{PR}[\mathcal R(\mathcal M,\prec_{\mathcal M})]\)，及"every function provably total in KPM"被某 \(H_\alpha\) 支配——逐字。
- §4 配方的条件与 Remark "(4)–(7) are satisfied if for example \(p(\alpha):=f(2^{N\alpha})\)"——逐字。

**来源 2**：Arai, arXiv:2304.00246 页 38–39，Definition 5.3 与 §5.1（**文本抽取**，`pdftotext -layout`）。

**支持**：Definition 5.3 的五条子句、\(Mh^a_k(\vec\nu)=\bigcap_{i\ge k}Mh^a_i(\nu_i)\)、\(\mathrm{lh}(\vec\nu)=N-k\)、子句 4 的 \(\xi_k\dot+\Lambda^{\xi_{k+1}}c\) 形式。§114.2 的"\(N=3\) 时子句 4 变空"是**本项目由指标范围推出**，不是原文陈述。

**不能据此声称**：
- \(\mathsf{OT}^{\times}\cong\mathcal T(M)\)。**Rathjen [10] 未取得**，\(\mathcal T(M)\) 的签名只能从 BCW 的七条范数反推；§114.4 的"多出两个符号"与 §114.7 的 \(Z\) 一栏标推测。
- \(\prec\) 的任何性质。BCW 配方还有两条（项集与良序的原始递归性），本项目两条分支均未核。
- C6 的反向已完成。114.1 的 Corollary 是**对 \(\mathcal T(M)\)** 陈述的，搬到 \(\mathsf{OT}^{\times}\) 需先立两者的关系。

## §115–§116（更正与收口）

**来源 1**：Setzer, *Extending Martin-Löf Type Theory by One Mahlo-Universe*（mahlo.pdf），**首页摘要与引言，读图转写**。

**支持**：
- "We show that the proof theoretical strength of MLM is ≥ ψ_{Ω₁}Ω_{M+ω} … **Together with [Se96a] it follows |MLM| = ψ_{Ω₁}(Ω_{M+ω})**."——逐字。§113.5 的端点数值缺口据此关闭。
- 引言第三段关于 W-type 的归纳定义需要"closed under the step to the next admissible"——逐字，作为 §110（目标 5）的独立交叉检验。

**不能据此声称**：本项目独立推导了 \(|(\mathrm{KPM})^+|\)。这是**校准侧引用**（CONTRACT §1 明许），不是重证。

**来源 2**：Arai, arXiv:2304.00246 **§2**（`pdftotext -layout`，文本可抽取）。

**支持**：
- §2.1 开头："Let us consider the simplest case \(N=3\), i.e., **an ordinal analysis of set theory KPΠ₃**"。
- **Definition 2.2**（＝ Def 5.3 在 \(N=3\)）：\(Mh^a_2(0)\) 为极限序数，\(\xi>0\) 时的递归条件，\(\psi^\xi_\pi(a)\) 的 min 刻画，\(\psi_\Omega(\alpha)\)。
- §2.2 的合式条件 (9)：\(\nu=m_2(\kappa)<m_2(\sigma)\)、\(SC_K(\nu)\subset\kappa\ \&\ \nu\le b\)，以及 \(m_2(\Omega)=1\)、**\(m_2(K)=\varepsilon_{K+1}\)**。
- Theorem 3.1：KPΠ₃ 证 \(OT(\Pi_3)\) 到每个 \(\alpha<\psi_\Omega(\varepsilon_{K+1})\) 的良基性。
- §1 的 \(\mathrm{RM}_i\) 记法与"对 KPM 只需两步坍缩 \(\psi_M\)、\(\psi_\sigma\)"。

**本项目的推导（非原文）**：\(m_2(K)=2\)。原文未对 KPM 写出 \(m_2(K)\) 的值；§115.2 由 \(\mathcal O^\flat\iff M\in\mathrm{RM}_2(\mathrm{RM}_2)\) 与 Def 2.2 子句 2 的逐层展开算出。与原文"两步坍缩"那句吻合，但**吻合是检验，不是依据**。

**来源 3（仅旁证）**：维基 *Rathjen's psi function*。给出 \(\mathcal T(M)\) 的序型 \(\psi_\Omega(\chi_{\varepsilon_{M+1}}(0))\) 与 \(|\mathrm{KPM}|=\psi_\Omega(\psi_{\chi_{\varepsilon_{M+1}}(0)}(0))\)。该页自称是简化版并声明不确定其是否给出有效记号，**本项目只作旁证，任何结论不以其为依据**。

**Rathjen [10]（*Proof-theoretic analysis of KPM*, Arch. Math. Logic 30 (1991) 377–403）本轮仍未取得**：Leeds 主页与 Springer 直链均连接失败。故 \(\mathcal T(M)\) 的完整签名仍是从 BCW 的七条范数反推的。

**\(K_a\) 的递归**（§116.2）：形状取自 §59.2 已核的 Arai \(K_\delta(\alpha)\) 与 §65.4 已核的 Setzer \(\widetilde{\mathrm C}_a(b)\)，是这一族记号系统的标准做法；**本项目未从任一原文逐条转写**，写下的是标准形式，实现与验证未做。

## §117（\(\prec\) 的原料）

**来源**：Buchholz, *A note on the ordinal analysis of KPM*, in: Oikkonen–Väänänen (eds.), **Logic Colloquium '90**, Springer Lecture Notes in Logic 2 (1993), pp. 1–9。取自 epub.ub.uni-muenchen.de/3848。**§1 全文读图转写**（该 PDF 是 ABBYY OCR，数学部分乱码，以 `pdftoppm -r 170` 渲染图为准）。§56 引过此文，但只读到摘要级内容。

**支持**（全部逐字）：
- \(SC(\gamma)\) 的四条递归；"Every uncountable cardinal is strongly critical"。
- **Definition 1.1**：\(\mathrm R\)、\(M^\Gamma\)、\(SC_{\mathrm M}\)、\(\Omega_\sigma:=\aleph_\sigma\)、\(\Omega_0:=0\)；**"\(\boldsymbol\Omega:=\) the function \(\sigma\mapsto\Omega_\sigma\) restricted to \(\sigma<\mathrm M\)"**；Remark \(\forall\kappa\in\mathrm R(\kappa=\Omega_\kappa\ \text{or}\ \kappa\in\{\Omega_{\sigma+1}\})\)。
- **Definition 1.2**：\(C(\alpha,\beta)\) 的闭包定义与 \(\mathrm{dom}(\psi|\alpha)\)；\(\psi_\kappa\alpha\) 的 min；\(\mathcal D_\kappa(\alpha)\) 的**两支**（\(\kappa=\mathrm M\) 支要求 \(\beta\in\mathrm R\)）。
- **Lemma 1.2**：\(C^n\) 的三支归纳刻画。
- **Lemma 1.3**：(a) \(C_\kappa(\alpha)\cap\kappa=\psi_\kappa\alpha<\kappa\)；(b) \(\kappa<\mathrm M\Rightarrow\psi_\kappa\alpha\notin\mathrm R\)；(c) \(\psi_\kappa\alpha\in SC\)。
- **Lemma 1.4**：(a) \(\gamma\in C(\alpha,\beta)\iff SC(\gamma)\subseteq C(\alpha,\beta)\)；(b) \(\Omega_\sigma\in C\iff\sigma\in C\)；(c)(d)(e)。

**据此可以声称**：§116.2 的 \(K_a\) 递归有出处（不再是"标准做法，未逐条转写"）；§115.2 的两符号读法与 \(\mathcal D_\kappa\) 的两支一致；\(\mathcal I\) 对记号系统的贡献是"去掉 \(\sigma<\mathrm M\) 的限制"。

**不能据此声称**：
- \(\prec\) 的子句表。**本文没有记号系统**——它直接在序数上工作（假设弱 Mahlo 基数存在），§3 的 Definition 3.1 是推导分析用的 \(sc_\kappa\)，不是比较规则。
- **§117.7 的情形分割是本项目本轮的推导，不是原文陈述**，且**未与 Rathjen [10] 或 Setzer Definition 3.3 核对**。其中三条断言（(2a)、(2b) 的两个等价、\(\xi=\eta\) 支的断言）各自附了证明，但只有本项目的一次检查。
- \(\mathsf{OT}^{\times}\) 与 Buchholz 的序数系统的同构。本文的对象是序数不是项。

## §118（子句表的核对）

**来源**：Setzer, mahlo.pdf 印刷页 6–7，**读图转写**。Definition 3.3 的 (≺′1)–(≺′11)、三个有限集 \(\mathrm{SC}_\kappa/\mathrm{sc}_\kappa/\mathrm G_\kappa\) 的递归、Lemma 3.4、Definition 3.5(a)(b)、Definition 3.6 的 (OT1)–(OT6)。

**支持**：§118.1 转写的内容；Lemma 3.4 的原话 "Proof: easy, but very long."

**这份材料的地位（要紧）**：它是**参考分支的**子句表。CONTRACT §1 规定，若算法实际读取了目标答案就必须报告为参考系统实现。因此：

- **允许**：用它**检验**本项目从配方推出的子句表（§118.3 即此，并因此捉到两处错误）。
- **禁止**：把它抄进 \(\mathsf{OT}^{\times}\)。抄了，\(\prec\) 就不是提取的产物，E 破。
- 次序是实质的：§117.7 的推导**在本节核对之前**完成并已写入，可回溯查证。

**不能据此声称**：\(\mathsf{OT}^{\times}\) 上的 \(\prec\) 已确定。已确定的是**要推成什么样子**。

## §121（E 的机器检验）

**无新文献。** 本节把已有的纸面推理形式化，不引入新来源。

`spec` 的三条子句各自的辩护出处：`levelOf` ← §112.1–112.2（\(\forall F\) 的范围决定公式类；原始依据是 §47 已核的 Setzer Part I 与 §59.1 已核的 Arai \(\mathrm{RM}_i\) 记法）；`degOf` ← §115.2（Buchholz Def 1.2.2 的 \(\mathcal D_\kappa\) 两支，§117.4 已核）；`indFormOf` ← §111.4（\(\mathrm V\) 无消去子，§97.1 由 INPUT.md §2bis 的签名穷举可见，§46 已核 Dybjer–Setzer 的不一致性结果）。

**不能据此声称**：
- `spec` 的子句是**正确**的读出。本文件证明它是函数、敏感、作用域干净；三条子句的正确性是 C1 的问题（§97.3 的分离）。
- 非 MLM 成员（`oneU`／`superU`／`takahashi`）的输出与文献已知强度相符。**未核对**——§95.7 风险 1 的正面检验仍未做。
- E 已证明。E-2（绑定／代换／计算相容）是关于 PER 模型的元定理，不进 Agda。

## §122（形式化类型宇宙）

**来源**：mahlo.pdf 印刷页 8–13，**读图转写**。Definition 4.1(a)–(i)、Preliminaries 4.2、Definition 4.3（含 Π 的三条等式版规则示例、Mahlo 宇宙的全部规则）、Definition 4.4–4.6、Lemma 4.7。

**支持**：`Rules.lagda.md` 的签名与元数（4.1(a) 逐字）；b-对象三种形状（4.1(b)）；判断与缩写约定（4.1(g)，页 10 第一条修改）；Mahlo 规则 V_I、T_I、N̂_{k,V,I/=}、Π̂_{V,I/=}（「Similarly for N̂, Σ̂, Ŵ, +̂, Î」）、Û_I、Û_=、U_T、s_I、Ass_I、Ass_=、Res0_I/=、Res1_I/=、N̂_{k,f,I/=}、Π̂_{f,I/=}（「Similarly for …」）——页 10–11 逐字。γ 表来自 Definition 4.6(b)(e)。

**不能据此声称**：基段规则逐字（原文转引 [Se93] 的 ML_J，**未取得**；`Rules` §4 按标准 Martin-Löf 形状录入，`elim` 只保留主前提与动机）；代换、α-等价、上下文推导规则（4.1(b) 说「in the usual way」，未录）。(Res0_I) 原文印作 `r = r' : U_{s,t}`，按上下文读作 `U_{f⃗}`。

**实验**：`scratchpad/postest/MahloIR.agda`——Agda 2.8.0 `--safe` 对 Setzer 式 `û` 构造子报 `NotStrictlyPositive`；同目录 `SuperIR.agda`（对给定 F 封闭）通过。

**Dybjer–Setzer, *The extended predicative Mahlo universe in Martin-Löf type theory*, JLC 34(6) 2024**（仅摘要，WebFetch）：其 Agda 模型「go beyond IIRD」。旁证标准 IR 到不了 Mahlo；未读正文。

## §123（路线 C）

**mahlo.pdf §5，页 14–19，读图**：Lemma 5.1–5.13、Definition 5.9（Univ）、5.12（\(\mathcal W_i\)）、Theorem 5.14。支持：Mahlo 宇宙的使用点只有 Lemma 5.10（\(f:=(x_1,y_1)\widehat{\mathrm N}_{\mathrm V}\)，\(g:=(x_1,y_1,z_1)\,z_1\in_{\mathrm V}E_{u_0,v_0}\)）与 Lemma 5.11 对它的调用；其余转引 [Se98]。

**Dybjer–Setzer 2003**（APAL 124；ScienceDirect 与 PhilPapers 均 403，**仅搜索摘要**）：外部 Mahlo 宇宙可由 IR 定义，IR 强度 ≥ KPM，模型在 ZFC＋Mahlo（＋0-不可达）。未读原文。

**[Se98] Setzer, *Well-ordering proofs for Martin-Löf type theory*, APAL 92 (1998) 113–159**：已取得（csetzer.github.io/articles/2papdiss.pdf，55 页，Ghostscript 6.0 但**文本可抽取**）。本轮只查了结构，未读内容。**[Se93]** 博士论文（weor0.pdf，142 页）同上。

**实验**：`Probe/MahloParam.agda` 通过；`Probe/IRUniv.agda.txt` 终止检查失败；`Probe/MahloIR.agda.txt` 正性失败。

**不能据此声称**：路线 C 已走通——只证实了它唯一的 Mahlo 步骤在 `--safe` 里可定义；Lemma 5.13 对 \(n\) 的一致性（§123.5）是本项目的推测，未验。
