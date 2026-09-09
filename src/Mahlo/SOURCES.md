# 当前文献依据与适用边界

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
- [Fernández-Duque–Weiermann, Fundamental sequences and fast-growing hierarchies for the Bachmann–Howard ordinal](https://arxiv.org/pdf/2203.07758)：在基本列已经生成后，参考其正则性与增长认证方法；不作为 Mahlo 基本列输入。

旧证明枚举、原始递归增长和高阶返回类型的论文记录留在归档，不列为当前执行依据。新的文献调查必须说明它补上“宇宙规则到基本列”的哪一箭头。

本轮定位：Setzer 印刷页 6–7 的 Definition 3.3、3.5、3.6 与 Freund Definition 1.2 支持 [RESEARCH.md §27](RESEARCH.md#27-更具体的正向连接固定截断点的两条坍缩不等式) 的局部不等式核对。该对应是本项目的推导，不是两篇文献已经证明的 Mahlo 提取定理；固定记号上的 SC 尚未成为随任意线性序变化的自然支撑。

后续核对：RESEARCH.md §29 展开 Setzer 的完整形成条件，补入截断点自身的 SC/G 依赖；§30–31 的切开、支撑重建及筛选条件引理是本项目的纸面推导。Freund（所链预印本）Definition 1.1、4.1 与 Theorem 4.3 用来区分输入支撑结构和输出坍缩界，不提供 MLM 到该输入的翻译。

RESEARCH.md §32 的实例使用 Takahashi Example 2.1 的常值重编码；参数交换障碍及其适用边界是本项目的独立证明。Freund §1 的态射明确是序嵌入，不是全部上下文重命名。§34 的下一实例使用 Takahashi Example 2.2 的真实宇宙生成算子，不引用其带额外 Acc 的后续层级作为已获结果。

主代理复核：Takahashi Example 2.2 及 §2.1 支持 RESEARCH.md §35 的局部反射方程。解码相等只支持相容分析的相等替换，不提供前驱域或共尾列。初稿 FS-1/FS-2 不是文献结论，其不共尾论证已撤回；详见 §38。未复核的综述强度简化论断不作为本轮证明依据。

本轮核对：Takahashi Appendix A 的宇宙嵌入／res 计算规则及 Example 2.1–2.2 支持 RESEARCH.md §41–43 的具体等式。Atom/Cong/Trans 是本项目的证书模式，完整前提检查仍未定义；不要把文献规则存在误称为检查器完成。本轮只分析外部推导，不添加对象理论未给出的宇宙消去。局部传输尚未接到 Towsner 的全局进展条件，也没有序数下降或共尾结论。

§45 主代理复核：[Buchholz 的 KPM 分析](https://epub.ub.uni-muenchen.de/3848/1/3848.pdf) §1–2 与印刷页 6 定理／推论；[无穷推导记号](https://epub.ub.uni-muenchen.de/3846/1/13.pdf) §2.3、2.8；Freund Definition 4.1、Theorem 4.3。Rathjen 1991 的存档本轮未能由主代理打开，精确转写不作已复核前提。常值 dilator 例子是本项目从定义的推导，用来纠正统一坍缩具有固定 BH 输出上限的误判，不是 Mahlo 提取方案。

§46 核对：[Freund, arXiv:1809.06759v3](https://arxiv.org/pdf/1809.06759) Definition 3.1、3.2、3.5–3.6、4.2、4.5，Theorem 4.6、9.7；导论中 Kleene–Brouwer 使良基搜索树成 dilator。此文把 KP 公理变成沿 \(X\) 的搜索树，不是 MLM 提取器，也不定义基本列。前印本 [1704.01662](https://arxiv.org/pdf/1704.01662) 作者声明已过时。Girard 的 \(\Pi^1_2\leftrightarrow\mathrm{Dil}(D)\) 完备性不登记为本项目进展。

§46 主代理已核查 Proposition 3.6、Lemma 3.10 在 KB 论证中的使用、Definition 4.5、Theorem 4.6、Proposition 4.9 与 Theorem 4.11。修正了“语义满足关系必是构造输入”以及“MinU 可直接插入”的过强表述；MLM 的保强度逻辑呈现与枝→模型定理尚缺。

§47 主代理核查：[Setzer 1996](https://csetzer.github.io/articles/uppermahlo.pdf) Definition 3.1、4.3–4.4；[Part I](https://csetzer.github.io/articles/modeltypetheoryinaccessiblemahlo.pdf) Definition 5.2、印刷页 26–29。保留统一阶段界及反射闭包机制，撤回初稿的直接保强度声称、L_w 混用和“有名字／全部函数”的错误模型二分。

§48 的条件统一界是主代理基于 Part I 页 26–27 的最小闭包阶段／代码加入定义，以及页 14 的模型嵌入归约所作推导。θ 已满足闭包是前提；没有从文献取得可计算的 C(β)，也没有一般 f 或基本列结论。Grok 初稿关于有限推导无法求界的断言已撤回。
