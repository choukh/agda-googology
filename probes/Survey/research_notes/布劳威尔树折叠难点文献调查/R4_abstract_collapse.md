# R4 与记号无关的抽象坍缩: 超限型泛函, dilator 与 ptyx, Bachmann–Howard 原则, ordinal systems, 有限树刻画

覆盖情况 (先读本地指南的结果). `OrdinalNotationsGuide.md` 与 `CodeGuide.md` **不含**本篇任何一条: 它们管 EBO, ψ_I, χ, M 的记号与机检代码, 以及 Buchholz 的 distinguished sets ($W_u$). 已在仓库别处出现过的: (i) Setzer 1998 的 "from below" 定理在 `probes/Survey/AgdaStrength.md` §5.5 与记忆条目里; (ii) Setzer *Ordinal Systems* 两篇在 `archive/src/Mahlo/RESEARCH.md` §125 里被当作良序证明 (路线 B) 的蓝本, 原文缓存在 `archive/src/Mahlo/Sources/`, 是 Type 3 字体, 要读图; (iii) Freund arXiv:1809.06759, Freund–Rathjen arXiv:2112.08005, Freund arXiv:2006.12111, Rathjen arXiv:2010.12453, Aguilera–Pakhomov–Weiermann arXiv:2201.04536 在 `archive/src/Mahlo/SOURCES.md` §45–§58 核对过, 但那是 **Mahlo 语境**, 结论是 "$D\mapsto B_D$ 是 ptyx, 强度仍只有 $\Pi^1_1$-CA₀, 类型层级不给强度". 本篇把这些材料对着本项目的三类困难重读; 下文凡标 "[已在 archive]" 的条目, 原始核对都在那里.

标记约定: [读正文] 读过原文的相关段落 (ar5iv 的 HTML, 缓存文本, 或本地 PDF 渲染的图); [读节选] 只读到出版社页的节选或摘要; [只见书目] 只确认了存在与出处; [推断] 是本篇的判断, 不是文献结论; [未核] 是记忆里有, 本轮没有核到原文.

## 问题 1. Aczel 的超限型泛函, Feferman 的 hereditarily replete 泛函, 及 Weiermann 的函子化: 怎样不比较不可数对象就描述 ψ 级序数, 能否推广到 Ω_Ω

### Takeaway
这一支的共同装置是把 "Ω 层" 换成 "定义在可数序数上的高一型泛函": Ω 不作为对象出现, 只作为泛函的定义域. 它在 Bachmann–Howard 一级有成熟结果. 对本项目最有用的有三点: Feferman 的 "相对范畴性" (两项的序由其参数的序决定), Aczel 只取 "遗传膨胀" (hereditarily inflationary) 泛函来保证值语义规整, Danner 的反例说明单调性不够. 没有找到把这条路推广到 Ω_Ω 或 Ω_{Ω_Ω} 的文献.

### Cited Findings
- **Aczel 1972** [读节选]. P. Aczel, "Describing ordinals using functionals of transfinite type", *JSL* 37(1) (1972) 35–47, DOI 10.2307/2272543. 原文自述目标是比较另一条描述可数序数的路与 Bachmann 方法, 用的是 "functionals of transfinite type based on Ω"; 对照的 Bachmann 方法是一族正规函数 $\varphi_\delta:\Omega\to\Omega$, 从 $\varphi_0(\lambda)=\omega_1+\lambda$ 起 — [Cambridge 页](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/describing-ordinals-using-functionals-of-transfinite-type/DE718F4C4A43BEEFFFD18B37EB182EEF). 全文付费, 本轮未读; 用这条路到底到哪个序数, 本轮**未核**.
- Aczel 的超限型结构: 极限层的函数空间取为低层函数空间的**乘积**, 后继层为了统一也这样取; Aczel 只用 **hereditarily inflationary** 泛函 — 据 [Danner, arXiv:math/9908127](https://arxiv.org/abs/math/9908127) §2 的转述 [读正文].
- Danner 给出反例: 迭代泛函 $I_\alpha$ 满足 $I_0 f x = x$, $I_{\alpha+1}fx=f(I_\alpha f x)$, 极限处取 lim sup. 对坏函数, $I_\omega(I_2 f)(0)\neq I_{2\omega}f(0)$; 对**只单调**的二型泛函 (交换两个函数), 同一对应也会失败. Danner 引入一个泛函上的新等价关系来恢复 "迭代 ↔ 序数算术" 的对应. Aczel 取遗传膨胀泛函也是为了这一点, 但这要求 "pure" 型结构, 且常值泛函不在里面 — [arXiv:math/9908127](https://arxiv.org/abs/math/9908127) [读正文].
- **Feferman** [只见书目 + 二手转述]. S. Feferman, "Hereditarily replete functionals over the ordinals", in *Intuitionism and Proof Theory* (Myhill 编, North-Holland 1970) 289–301. 据 Rathjen 综述 §4.1: 一族函数是 **replete** 指每个序数在它们下的闭包仍是序数; Feferman 把这一概念推广到序数上的有限型泛函 — [Rathjen, arXiv:2010.12453](https://arxiv.org/abs/2010.12453) [读正文].
- 同一综述 §1 与 §4.1 说, Feferman 公理化方法的支点 ("the fulcrum") 是 **effectively relatively categorical**: 两个项在不可达点上的序, 可以从它们参数的序判定 — [arXiv:2010.12453](https://arxiv.org/abs/2010.12453) [读正文].
- **Schmidt 1975** [读节选]. D. Schmidt, "Bounds for the closure ordinals of replete monotonic increasing functions", *JSL* 40(3) (1975) 305–316, DOI 10.2307/2272156. 对 n 元 replete 单调递增函数的闭包序数给出界, n>2 时最优; 函数 $f$ 在 $\mathrm{Cl}_f(0)$ 上给出一套记号 — [Cambridge 页](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/bounds-for-the-closure-ordinals-of-replete-monotonic-increasing-functions1/FD393DD7FB4F28CA1D6F8FBB1CDF5786). 具体界在公式图里, 本轮读不到.
- **Weiermann 的 η₀ 刻画** [二手]: Van der Meeren–Rathjen–Weiermann 的导言说, Weiermann 证明了 Bachmann–Howard 序数 η₀ 可以刻画为一类 "essentially monotonic increasing functions" 的闭包序数 — [arXiv:1411.4481](https://arxiv.org/abs/1411.4481) 摘要与导言. 原论文本轮没有定位到, 函数类的精确定义**未核**.
- **Weiermann 1994** [读节选]. A. Weiermann, "A functorial property of the Aczel–Buchholz–Feferman function", *JSL* 59(3) (1994) 945–955, DOI 10.2307/2275919. 范畴取可数序数与严格递增映射, dilator 指保持直接极限与拉回的函子. 结论: 二元 Aczel–Buchholz–Feferman 函数的无不动点版本, 当 $\gamma>\max\{\beta,\delta,\omega\}$ 时是 dilator, 证明是初等计算 — [Cambridge 页](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/functorial-property-of-the-aczelbuchholzfeferman-function/94EFFD822FC8125BE28714485A631E15). 定义在公式图里, 哪个变元作函子变元本轮读不到.

### Inferences
- [推断] 难点 1. Feferman 的 "相对范畴性" 正好是 "派发不判定" 的正面形式: 新项之间的序 (对本项目来说是折叠里 "同一孩子 / 层号在下" 这类判断) 只由参数之间的序决定. 对本项目的含义是: 这类判断的输入应当是一组带字面关系证据的参数 (公共上界, 同一框架), 不是两棵裸树. 这与 AGENTS 的 "律带公共上界" 同向, 但文献里参数的序是可判定的, 我们没有. 所以能借的是 "判断只看参数之间的关系" 这一形状, 不是判定过程.
- [推断] 难点 2. Aczel 用 "遗传膨胀" 划出值语义规整的子域, Danner 证明 "只单调" 不够并改用等价关系. 两件事都对应本项目 "量化域先取带证据的读回域" 的做法: 在全体树上要求 "该有的值" 沿每条规则单调, 文献的经验是要靠一个比单调更强的遗传条件 (inflationary), 或者靠商掉一个等价. 可以试的候选: 在读回域上加 "遗传膨胀" 型谓词 (每个分支函数在其定义域上 ≥ 自变量, 逐层遗传), 而不是只加单调性.
- [推断] 难点 1 与 Ω_Ω. 超限型结构 "极限层 = 低层的乘积" 与本项目 "Ω 结点在某层上对一切低层合法树分支" 同形: 型的层级就是层号. 若层号本身是这个结构里的对象 (Ω_Ω 的情形), 型就要依赖型层的值, 相当于 "层号是树" 的宇宙. 文献里没有找到这一步.
- [推断] 难点 3. Weiermann 1994 的形状是 "坍缩函数对一个变元是 dilator". 对本项目, 若折叠对低层下标的嵌入是自然的, "沿嵌入单调" 就是自然性的推论, 不必逐站证. 这只是候选, 要在树上写出 "嵌入" 的意义才能检验.

### Gaps
- Aczel 1972 的主定理 (泛函描述到哪个序数, 是否恰为 Bachmann–Howard 序数) 本轮没有读到原文, 只读到节选与 Danner 的转述. 付费墙.
- Feferman 1970 与 Weiermann 的 "essentially monotonic" 原文本轮未取得. 后者的出处本轮也没有定位 (只见 1411.4481 的引用).
- Weyl 与 Veblen 式由泛函生成正规函数层级的近年复兴, 以及 Jervell 用泛函描述序数的工作, 本轮没有检到具体文献 (Jervell 的有限树一条见问题 4).
- 没有找到任何把超限型泛函推广到 Ω_Ω 或 Ω_{Ω_Ω} 类比的文献. 未找到不等于不存在.

## 问题 2. Girard 的 dilator 与 ptyx, Freund 的 Bachmann–Howard 不动点, 导数与迭代, Aguilera–Pakhomov–Weiermann 的函子化 FGH: 哪些装置能统一地 (对层号一致地) 定义坍缩

### Takeaway
这一支给出三件可借的东西. (a) **支撑与正规形**: 每个元素都写成 "有限框架 + 框架上的形状", 比较两个元素只看它们支撑的并. 这是 "字面公共框架" 的标准形式. (b) **泛性质定义的坍缩**: Bachmann–Howard 不动点与导数用 "初始不动点" 定义, 与具体项系统无关, 唯一到唯一自然同构, 判据是 "生成 + 高度函数", 对每一层用同一条. (c) **Aguilera–Pakhomov–Weiermann 证明: 把二元 FGH 看作 ℕ 上的函子, 再延拓到线序, 得到的恰是坍缩函数的记号系统**. 这把本项目 "折叠是 FGH 的推广" 变成了一条已发表的定理. 文献里层号一律是可判定的参数 ($n$, 给定良序 $\nu$, 迭代阶段); 没有找到在不可判定层号上派发的装置.

### Cited Findings
- **Girard 的 dilator** [只见书目, 定义经 Freund 转述]. J.-Y. Girard, "Π¹₂-logic, part 1: Dilators", *Ann. Math. Logic* 21(2) (1981) 75–219 (书目取自 APW 参考文献, 缓存 `archive/src/Mahlo/Sources/apw-ffgh.txt`). Freund–Rathjen 的转述 [读正文]: predilator 是线序上的函子, 带自然变换 $\mathrm{supp}:D\Rightarrow[\cdot]^{<\omega}$ 与支撑条件; predilator 由它在有限序上的值决定; 每个 $\sigma\in D(X)$ 有唯一正规形 $\sigma=D(e)(\sigma_0)$, 其中 $e:n\to X$ 是嵌入, $(n,\sigma_0)$ 属于迹 $\mathrm{Tr}(D)$ (支撑满). Dilator 即把良序送到良序的 predilator, 等价于 Girard 的 "保持直接极限与拉回" — [Freund–Rathjen, arXiv:2112.08005](https://arxiv.org/abs/2112.08005) §1 [读正文].
- **Girard–Vauzeilles 的函子式 Bachmann 层级** [读节选]. J.-Y. Girard, J. Vauzeilles, "Functors and ordinal notations II: A functorial construction of the Bachmann hierarchy", *JSL* 49(4) (1984) 1079–1114, [DOI 10.2307/2274263](https://doi.org/10.2307/2274263). 摘要: 用 Π¹₂-logic 函子式地构造 Bachmann 层级, 所得函数层级与通常 Bachmann 集合高 $\varepsilon_{\Omega+1}$ 的 $\psi_x$ 层级逐一相同, 并说明这些函子可作序数记号. Part I (Veblen 层级) 在 *JSL* 49 (1984) 713–729 — [Cambridge Part I](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/functors-and-ordinal-notations-i-a-functorial-construction-of-the-veblen-hierarchy/6AE212CAD2B7BCEDF0E7E43D57926361). 全文付费; [HAL 存本](https://hal.archives-ouvertes.fr/hal-00003496) 被反爬虫页挡住, 未读.
- **Vauzeilles Part IV** [读节选]. J. Vauzeilles, "Functors and ordinal notations IV: The Howard ordinal and the functor Λ", *JSL* 50(2) (1985) 331–338, DOI 10.2307/2274218. 节选描述一个从 gardens (GAR) 到 $\mathrm{DIL}_\Omega$ 的函子 $S_\Delta$: 在每个共尾度为 Ω 的步骤迭代 "变元等同" 运算 Δ — [Cambridge 页](https://cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/functors-and-ordinal-notations-iv-the-howard-ordinal-and-the-functor/51F423DA4F87624B045082579C2E257D). Λ 的定义与 Howard 序数怎样得到, 节选没有; 本轮**未核**.
- **Bachmann–Howard 坍缩的支撑条件** [读正文]. 对 dilator $D$, 坍缩 $\vartheta:D(X)\to X$ 要求: (1) 若 $\sigma<\tau$ 且 $\mathrm{supp}(\sigma)$ 在 $\vartheta(\tau)$ 之下, 则 $\vartheta(\sigma)<\vartheta(\tau)$; (2) 对一切 $\sigma$, $\mathrm{supp}(\sigma)$ 在 $\vartheta(\sigma)$ 之下. 最小不动点 $\vartheta(D)$ 相对 $D$ 可计算. Theorem 1.3: 在 RCA₀ 上, $\Pi^1_1$-概括等价于 "每个 dilator 有良基的 $\vartheta(D)$" — [arXiv:2112.08005](https://arxiv.org/abs/2112.08005). 同一条件对经典 $\vartheta$ 的表述 (Rathjen 综述 Def 3.1–3.2): $\vartheta$ 不保序, 但当 $\alpha<\beta$ 且 $\mathrm{supp}_\Omega(\alpha)<\vartheta(\beta)$ 时 $\vartheta(\alpha)<\vartheta(\beta)$ — [arXiv:2010.12453](https://arxiv.org/abs/2010.12453). 主定理原文: [Freund, arXiv:1809.06759](https://arxiv.org/abs/1809.06759), 证明 Rathjen 与 Montalbán 的猜想 [已在 archive §46].
- **按良序 ν 迭代** [读正文]. Freund–Rathjen 的 ν-坍缩是嵌入 $\pi:X\to\nu\times D(X)$, 带 ⊲ 的良基条件与值域条件 $\mathrm{rng}(\pi)=\{(\alpha,\tau): G_\alpha(\tau)\text{ 在 }\tau\text{ 之下}\}$, 其中 $G_\alpha$ 是第 α 层的支撑闭包. 项形如 $\psi_\alpha(a,\sigma)$, $\alpha<\nu$ 标层; $\psi_\nu(D)$ 上的序**先比层号 α**, 再比支撑之并上的 $D$-值. Theorem 1.6: ν 无穷时, 一切 $\psi_\nu(D)$ 良基等价于沿 ν 的 $\Pi^1_1$-递归 (在 ATR₀^set 上也等价于 ν 长的容许集序列). Example 1.5: 取 $D=\omega(\cdot)$ 时 Buchholz 的 OT 是一个 (ω+1)-不动点. Corollary 2.10: $\psi_\nu(D)$ 良基则 $\mu<\nu$ 时 $\psi_\mu(D)$ 良基 — [arXiv:2112.08005](https://arxiv.org/abs/2112.08005) [已在 archive §56].
- **Bachmann–Howard 导数** [读正文]. A. Freund, "Bachmann–Howard derivatives", [arXiv:2105.09915](https://arxiv.org/abs/2105.09915); 期刊版在 [*Arch. Math. Logic*](https://link.springer.com/doi/10.1007/s00153-022-00851-5). 内容:
  - Def 2.5: $D$ 在线序 $X$ 上的 Bachmann–Howard 不动点是 $(Z,\iota,\vartheta)$, 其中 $\iota:X\to Z$ 是序嵌入, $\vartheta:D(Z)\to Z$, 且**每个 $\iota(x)$ 都在每个 $\vartheta(\sigma)$ 之下**, 外加 $\vartheta$ 与支撑的比较条件. Def 2.8: 初始不动点.
  - Theorem 2.9 (初始性判据): $Z=\mathrm{rng}(\iota)\cup\mathrm{rng}(\vartheta)$, 并且有高度函数 $h$, 使 $z\in\mathrm{supp}(\sigma)$ 时 $h(z)<h(\vartheta(\sigma))$.
  - Def 2.10: 导数 $\vartheta D$ 是一个 dilator, 对每个 $X$ 给出初始不动点, 且 $\iota,\vartheta$ 对 $X$ 自然. Prop 2.13: 同一 $D$ 的两个导数之间有唯一的、与结构映射相容的自然同构.
  - §3: $T^0_0=\mathrm{Id}$, $T^0_{n+1}$ 取 $T^0_n$ 的导数. $T^0_n(1)$ 与 Van der Meeren–Rathjen–Weiermann 的坍缩函数系统 $T_n[0]$ 一致, 后者推广 Rathjen 给 Bachmann–Howard 序数的记号. Theorem 3.10 对每个 $n$ 作这一认同.
- **APW: 函子化的快速增长层级** [读正文, 缓存 `archive/src/Mahlo/Sources/apw-ffgh.txt`]. J. P. Aguilera, F. Pakhomov, A. Weiermann, "Functorial fast-growing hierarchies", [arXiv:2201.04536](https://arxiv.org/abs/2201.04536); 据检索结果, 期刊版是 *Forum of Mathematics, Sigma* (2024) ([TU Wien 存本](https://repositum.tuwien.at/bitstream/20.500.12708/209705/1/2024-Forum%20of%20Mathematics%2c%20Sigma-vor.pdf), 版本信息未逐字核). 内容 [已在 archive §57–58]:
  - 以范数代替基本列: 对指示系统 $D$, $N\alpha$ 是记号里自然数参数的严格上确界; $B_\alpha(n)=\sup\{B_\beta\circ B_\beta(n):\beta<\alpha\wedge N\beta\le n\}\cup\{n+1\}$.
  - 每个 $m<B_D(n)$ 有唯一 "n-正规形" $m=B_{\alpha_k}\cdots B_{\alpha_1}(n)$; 由此 $B_D$ 是 ℕ (严格递增映射) 上的函子 (Corollary 7), 进而唯一延拓为线序上的有限函子. 导言原话: 这些表示式 "can be given transfinite parameters".
  - Definition 8 给出同一对象的 "形式坍缩" 写法: $B_D(A)$ 是含 $a^\star$ ($a\in A$) 与 $\psi(0)$ 的最小线序, 并且当 $\alpha_{k+1}<\alpha_k$ 且 $\alpha_{k+1}\in D(C\restriction\psi(2^{\alpha_1}+\dots+2^{\alpha_k}))$ 时, 含 $\psi(2^{\alpha_1}+\dots+2^{\alpha_{k+1}})$. 条件 "新参数落在当前坍缩值之下那一段的 $D$ 里" 与 FGH 里的 "$N\beta\le n$" 相对应. 序的条款: 一切 $a^\star$ 在一切 $\psi(t)$ 之下, $\psi$ 之间按 $2^{D(C)}$ 的字典序比.
  - Lemma 13: 范数正规形的 $\hat B_D$ 与坍缩写法的 $B_D$ 自然同构. Theorem 2/16 (ACA₀ 上): $\Pi^1_1$-CA₀ ⇔ "对一切 dilator $D$, $B_D$ 是 dilator". 导言: $\Pi^1_1$-CA₀ 的 Kreisel 型定理里 $B_{\varepsilon_0}$ 换成 $B_{\psi_0(\aleph_\omega)}$ (Buchholz), $\psi_0(\aleph_\omega)$ 是 Takeuti 序数.
  - Remark 14: $D\mapsto B_D$ 可延拓为 predilator 范畴上保拉回的函子, 即一个 ptyx.
  - 文中提到 Wainer 早先在树序数上证明过二元 FGH 某一版本的函子性: S. Wainer, "Accessible recursive functions", *Bull. Symb. Logic* 5 (1999) 367–388 (缓存文本 §3 末与参考文献 [19]).
- **AFRW** [读节选]. Aguilera, Freund, Rathjen, Weiermann, "Ackermann and Goodstein go functorial", *Pacific J. Math.* 313(2) (2021): Veblen 正规函数层级与 Ackermann 函数沿直接极限的延拓密切相关 — [MSP 页](https://msp.org/pjm/2021/313-2/p01.xhtml).
- **更高型** [读节选]. 2-ptyx 是 dilator 的一致变换; 在 ℕ 上的 $\Pi^1_2$-归纳等价于 "满足某正规性条件的 2-ptyx 都有不动点" — [Freund, arXiv:2006.12111](https://arxiv.org/abs/2006.12111) 摘要 [已在 archive §56]. Rathjen 综述 §1: 形如 "X 良序 ⇒ f(X) 良序" 的原则是 Π¹₂ 的, 单靠它到不了 $\Pi^1_1$-概括, 所以要用基于坍缩的高阶原则 — [arXiv:2010.12453](https://arxiv.org/abs/2010.12453).
- 其它题名 [只见书目]: Freund, "A categorical construction of Bachmann–Howard fixed points", [arXiv:1809.06769](https://arxiv.org/abs/1809.06769); "Induction on dilators and Bachmann–Howard fixed points", [arXiv:2412.13051](https://arxiv.org/abs/2412.13051). 内容未读.

### Inferences
- [推断] 难点 1, 最直接的一条: **"在目标之下: 保留" 对应 $\iota$, "同层: 以输出作下标对角" 对应 $\vartheta$.** 在 Freund 的不动点 $(Z,\iota,\vartheta)$ 里, "每个 $\iota(x)$ 在每个 $\vartheta(\sigma)$ 之下" 是对一切元素一致的字面回答, 不对单个 $x$ 判定. 一个元素属于哪一类, 由它是哪个构造子造的 ($\iota$ 还是 $\vartheta$) 决定, 不靠比较. 对本项目的含义: 把折叠的类型写成对低层部分 $X$ **参数化** (低层只是不被检视的参数), "该保留" 由来源 (构造子标签) 回答, 不由层号比较回答. 这与 AGENTS 先验检查第 3 条 "按存在性保留" 及台账里的 provenance 方案同向. 文献在这里给的是一个现成的泛性质模板 (Def 2.5, 2.8, 2.10).
- [推断] 难点 1. dilator 正规形 $D(e)(\sigma_0)$ 是 "公共框架证据" 的标准形式: 两元素先拉回到 $\mathrm{supp}\,\sigma\cup\mathrm{supp}\,\tau$ 这个有限框架, 再在 $D(n)$ 里比较. 文献里框架内的相对序是可判定的; 本项目里不可判定, 所以框架要作为**证据随对象携带** (例如一个有限的低层树列表, 带它们之间字面的 ≼ 链), 而不是现算. 这正是 AGENTS 里 "被比较的两个下标必须有字面的公共上界" 的结构化版本: 公共上界换成公共有限框架.
- [推断] 难点 1 与目标 "树自足". APW 的定理说的是: 二元 FGH ($B_{\alpha+1}=B_\alpha\circ B_\alpha$, 极限处用范数约束) 作为函子延拓到线序, 就是坍缩. 本项目最佳实践第 1 层说 "折叠是 FGH 在更高层次的推广", APW 给的是同一句话的定理版, 而且方向是 "FGH 唯一决定坍缩". 能借的形状: 让折叠在 Ω 层的行为由它在 ℕ 层 (有限序) 的行为经直接极限唯一决定, 而不是另写一条 Ω 规则. dilator "由有限序上的值决定" 与交替路线 "不可数层在对象层以对角 ℕ-极限表示" 同向. 要检验的是: 布劳威尔树上的 Ω 结点分支函数是任意函数, 不是 dilator, 所以要么限制分支函数 (只允许 "自然的" 分支), 要么只在读回域上用这一刻画.
- [推断] 难点 2. Freund 的导数由泛性质定义, 两个实现之间有唯一自然同构 (Prop 2.13). 对纲领第 4 条 (最终定义与记号无关) 的含义: 坍缩可以先写成 **接口** (初始不动点的泛性质), 任何项系统只是它的一个模型, 由唯一性互相同构. Theorem 2.9 的判据 "Z 由 ι 与 ϑ 生成 + 有高度函数" 可读作读回域的定义: 规范对象就是由构造子生成且带高度证据的对象. 非规范树落在判据之外, 不需要在它们上面定义 "该有的值".
- [推断] 难点 3. 导数对每个 $n$ 用同一泛性质 (Theorem 3.10), $T^0_{n+1}$ 由 $T^0_n$ 经同一运算得到, 闭包与保持定理对阶段一致. 这与 "闭包定理与阶段无关" 的判据同形. 对 Ω_Ω, 需要沿内部序数做超限次导数: 后继取导数, ℕ-极限取直接极限 (用 Corollary 2.10 型的嵌入), Ω-极限 "对一切低层树取余极限". 最后一步文献里没有.
- [判断] 文献里层号都是可判定的: $\psi_\nu(D)$ 的序先比 $\alpha<\nu$ ($\nu$ 是给定线序), 导数按 $n$ 迭代. 本项目要的是层号本身是树、不可判定的情形, 文献没有提供. 壁垒定理说明这不是工程问题. 能借的只是 "层号由构造阶段或参数位置字面给出" 这一组织方式.
- [判断] archive §57 的结论 "$D\mapsto B_D$ 是 ptyx, 强度只有 $\Pi^1_1$-CA₀ (ψ₀(Ω_ω) 一级)" 对本项目仍有效: 升一型本身不升强度; 强度来自迭代深度与层号的范围.

### Gaps
- Girard 原文 (Π¹₂-logic, ptykes 的定义, 2 型 ptyx 与更高坍缩的对应, Λ 函子) 本轮没有读到. "2 型 ptyx 对应 Bachmann–Howard 或 ID₁" 一类说法是记忆, **未核**, 不应引用.
- Girard–Vauzeilles II 的具体手段 (Ω 作函子变元, Ω 共尾步骤用变元等同) 只来自 Part IV 节选的一句, 未读全文.
- 没有核到哪篇文献把 Bachmann–Howard 导数沿超限 (尤其内部生成的) 序数迭代, 或给出 Ω_Ω 级的 dilator 刻画. Freund–Rathjen 的 ν 是外给的良序.
- Freund 的 "higher Bachmann–Howard principles" (arXiv:1704.01662) 本轮只见题名; archive §46 记作者已声明该预印本过时.

## 问题 3. Setzer 的 ordinal systems: 不用基数怎样处理层, 降序列与有限信息的作用

### Takeaway
Setzer 把记号系统抽象成结构 $(T,\prec,\prec',k,\mathrm{length})$: 每个记号带有限的分量集 $k(t)$. 迭代版 ($n$-OS, σ-OS) 把层做成**不同的类 $T_i$**, 每个元素对每一层各有一个有限分量集 $k_{i,j}$. 层是类别下标, 不是被比较的对象. 良序证明对 $n$ 用同一条 "相对化" 引理逐层下降. 作者自述 σ-OS "without the use of cardinals" 达到 ID_σ. 对本项目, 能借的是三件事: 层作为类, 逐层的有限分量记录, 以及 "比较只看两元素分量之并" (Setzer 自己说这一条有 Π¹₂-logic 的味道).

### Cited Findings
- 出处 [读正文, 本地缓存 PDF 渲染页]: A. Setzer, "Ordinal systems", in *Sets and Proofs* (Cooper, Truss 编, CUP 1999); 作者 2001-01-26 更正版 [PDF](https://csetzer.github.io/articles/ordsyscor010124.pdf) (缓存 `archive/src/Mahlo/Sources/setzer1999-ordinal-systems.pdf`). Part 2: "Ordinal systems part 2: One inaccessible", *Logic Colloquium '98* (CUP 2000), [PDF](https://csetzer.github.io/articles/ordsystwo.pdf), [Cambridge 页](https://resolve.cambridge.org/core/books/logic-colloquium-98/ordinal-systems-part-2-one-inaccessible/283CDDF366319450B06407BA6B5F07C3).
- 摘要 (p.1): ordinal systems 把 Cantor 正规形、Veblen 函数、Schütte Klammer 符号一类较直谓的方法推广到 Bachmann–Howard 序数; σ-ordinal systems 不用基数, 以基本直谓的方式达到 ID_σ 的强度; 文中用 "extended Schütte Klammer symbols" 定出 σ-OS 的精确强度.
- p.3 "Technical advantages": 这一方法把不影响强度的性质与达到强度所必需的结构性质分开; 良序证明只针对抽象结构做, 具体记号系统只在验证 "它是一个 (n-, σ-) ordinal system 的实例" 时出场; 附带一次得到**一整族**记号系统的良序证明.
- p.6 动机与 Def 2.1: OS-structure 是五元组 $(T,\prec,\prec',k,\mathrm{length})$, $k:T\to_\omega T$ 给出有限分量集, $\prec'$ 是 "新记号被引入的顺序". 要求 $k(t)\prec t$; 若 $s\prec t$, 则或者 $s\preceq k(t)$ (在某个分量之下), 或者 $s\prec' t$ (先被引入); $\mathrm{length}(a)<\mathrm{length}(b)$ 对 $a\in k(b)$.
- Theorem 2.3: elementary ordinal systems 的序型小于 Bachmann–Howard 序数.
- §2.4 构造性良序证明: 令 $\mathrm{Acc}:=\mathrm{Acc}_\prec(T)$, $\mathrm{Acc}':=k^{-1}(\mathrm{Acc})$, 对 $\prec'$ 归纳并对 length 作副归纳, 正文约六行. 原文说该证明可在直觉主义 ID₁ 或带可达部分的类型论里形式化.
- Lemma 2.8(e) (OFG 化为原始递归 OS 的条件): 对 $\hat k(a)\cup\hat k(b)\subseteq T$, 由 $\prec$ 在 $\hat k(a)\cup\hat k(b)$ 上的限制, 原始递归地决定 $a,b$ 是否属于 $T'$, 以及是否 $a\prec' b$. 原文评注: 这一条件 "have some flavor of Π¹₂-logic".
- Def 3.1(c) $n$-OS: 对 $i,j,l<n$, (n-OS 1) 每个 $\mathcal F_i$ 满足 OS 条件; (n-OS 2) $l<j$ 时 $k_{j,l}\circ k_{i,j}\subseteq k_{i,l}$; (n-OS 3) 若 $A_i\subseteq T_i$ 关于 $\prec$ 良序 ($i<n$), 则 $T_l\restriction_{i<n}A_i$ (第 $l$ 层中各层分量都落在 $A_i$ 里的元素) 关于 $\prec'$ 良序. 主序数是 $(T_0,\prec)$.
- Def 3.2 相对化的 $n$-OS: 多一个外给的线序 $T_{-1}$ 与 $k_{i,-1}:T_i\to_\omega T_{-1}$. Lemma 3.3: (n+1)-OS 对良序的 $A\subseteq T_0$ 相对化后是 $n$-OS; 1-OS 是 OS; $n$-OS 良序; elementary $n$-OS 的 (d) 可在 KPω 加 $n-1$ 个容许集 $x_1\in\dots\in x_{n-1}$ 的存在里证. 证明对 $n$ 作元归纳.
- Example 3.7 与 Remark 3.8(b) (p.21): "cardinality based" 的 $n$-OFG 里 $\mathrm{eval}_{i+1}$ 取 $\Omega_{i+1}$ 的幂和, 用来与传统基数方法对照; 把 $\Omega_i$ 换成第 $i$ 个容许序数 $\Omega_i^{\mathrm{rec}}$ 需要额外条件.
- p.3 "Future developments": 作者已有覆盖一个递归不可达与一个递归 Mahlo 序数强度的 ordinal systems.
- 已在仓库: `archive/src/Mahlo/RESEARCH.md` §125 记 Part 2 引言 — 单个只引用更小者的系统止于 Veblen 型扩张, 越过 Bachmann–Howard 要多个系统互相引用; Part 2 给两种良序证明, 构造性的一种用 distinguished sets. "from below" 定理 (Setzer 1998) 与它不给布劳威尔树上界的读法, 见 `probes/Survey/AgdaStrength.md` §5.5.

### Inferences
- [推断] 难点 1. $n$-OS 里 "元素在哪一层" 是它所属的类 $T_i$, 跨层关系只经有限分量映射 $k_{i,j}$ 表达, 从不比较两个层号. 对本项目: 若层号做成类型的下标 (龙骨 Ω, Ω_Ω, …), 每个对象带 "各层的有限分量集" 作 provenance, 那么 "槽位与目标是否同一孩子" 可以改问 "槽位的第 $j$ 层分量集里有没有目标的那个孩子", 这是对有限的、字面记录的数据的问题. 到 Ω_Ω 时层号是树, 类族要以树为下标, Setzer 的 σ-OS 用的是外给的 σ. 这一步文献里没有.
- [推断] 难点 1. Lemma 2.8(e) 的 "两元素的序只由 $\prec$ 在 $k(a)\cup k(b)$ 上的限制决定", 与 dilator 的支撑原则是同一件事: 判断的输入是两元素的有限分量之并. 本项目的 "字面公共上界证据" 可以细化成: 带上 $k(a)\cup k(b)$ 这个有限集里各元素之间的字面关系证据.
- [推断] 难点 3. Lemma 3.3 的形状 "(n+1) 层系统对良序参数相对化就是 n 层系统" 是一条与阶段无关的一步定理, 对 $n$ 元归纳即得全体. 对本项目的值下界, 候选的对应陈述是: 第 $n+1$ 层的树对一个低层良序 (或低层读回域) 相对化后, 落在第 $n$ 层的读回域里, 且值的下界随之传递. 这比逐站证明更接近 "闭包定理与阶段无关".
- [推断] 这套抽象的用途与本项目相反: Setzer 要的是良序证明 (记号的序已可判定), 本项目的树良基是白给的, 缺的是派发与值. 所以要借的是组织方式 (层作类, 有限分量, 相对化归约), 不是良序论证本身.

### Gaps
- σ-OS 的定义页与 "extended Schütte Klammer symbols" 的强度计算 (p.22 以后) 本轮没有读. σ 是否必须是外给的可判定良序, 以 Def 3.1 的模式推断为 "是", 未核原文.
- Part 2 (一个不可达) 里怎样处理 "层号由系统内部生成" 本轮没有重读; `archive/src/Mahlo/Sources/renders/ordsys2-*.png` 有 22 页渲染图可供下一轮读.

## 问题 4. 坍缩函数的有限树刻画: Kruskal 型树, gap 条件, 标签扮演 Ω 层; patterns of resemblance

### Takeaway
有限树一侧有两种做法. 一种是**良拟序的极大序型**: 带标签的有限树在嵌入下的极大序型等于坍缩序数. 例如 $\mathcal T(\mathcal B(\cdot))$ 的极大序型是 Bachmann–Howard 序数; Friedman 的带 gap 条件的标号树对应 Ω_n 级. 另一种是 Freund 的重构: gap 条件由 "一致 Kruskal 定理" 的反复应用得到, 标签 $i$ 就是结点被引入时的迭代阶段, 每多一次导数就加一个新的底层标签. 对本项目, "标签 = 引入阶段" 是现成的 provenance 形式. gap 条件可读作 "比较只能穿过层不低于自身的区域", 是一种局部性约束.

### Cited Findings
- **Van der Meeren–Rathjen–Weiermann 2017** [读正文]. "An order-theoretic characterization of the Howard–Bachmann-hierarchy", *Arch. Math. Logic* 56 (2017) 79–118, DOI 10.1007/s00153-016-0515-6, [arXiv:1411.4481](https://arxiv.org/abs/1411.4481). 内容:
  - 广义树 $\mathcal T(\mathcal W)$: 结点 ∘ 的孩子由 "构造" $W$ (由 $\cdot$, 可数 wpo, $+$, $\times$, $*$, $\mathcal B$ 组成) 的裸项 $w(t_1,\dots,t_n)$ 给出; 序是使 ∘ 最小并尊重构造子嵌入序的最小自反传递关系.
  - Theorem 4.1 与 §4: $o(\mathcal T(\mathcal B(\cdot)))=\vartheta(\varepsilon_{\Omega+1})=\eta_0$ (Bachmann–Howard 序数). 迭代 $*$ 构造子得 $o(\mathcal T(\cdot{*}\cdots{*}))=\vartheta(\Omega_{2n-1}[\omega])$, 对 $n$ 取上确界是 η₀.
  - 一般猜想: $\Omega^3\le o(W(\Omega))\le\varepsilon_{\Omega+1}$ 时 $o(\mathcal T(\mathcal W))=\vartheta(o(W(\Omega)))$, 即 "把 Ω 代入构造, 再坍缩".
  - Friedman 树 $\mathbb T_n$: 标签取自 $\{0,\dots,n-1\}$; 弱 gap 嵌入要求保标签、保序, 并且像与其孩子的像之间的结点标签不低于孩子的标签. 文中说 Friedman 完整 gap 序的极大序型是 $\psi\Omega_\omega$, 并猜想 $n$ 个标签的情形由第 $n$ 个正则基数描述.
  - 工具: 极大序型由 de Jongh–Parikh 定理保证可达; 左集 $L(x)$; 拟嵌入把 wpo 性质与序型上界传过去. $o(\mathcal B(X))=\varepsilon_{\overline{o(X)}}$.
- **Rathjen–Van der Meeren–Weiermann 2017** [读节选]. "Ordinal notation systems corresponding to Friedman's linearized well-partial-orders with gap-condition", *Arch. Math. Logic* 56(5–6) (2017) 607–638, [arXiv:1505.01359](https://arxiv.org/abs/1505.01359). 定出无加法 θ 函数记号系统的序型, 并说明 Friedman 序的极大序型可以由基于特定二元 θ 函数的记号系统达到. Weiermann 猜想坍缩函数 $\vartheta_i$ 给出这些 wpo 的极大线性延拓, $n=2$ 已证.
- **Freund, 从 Kruskal 到 gap 条件** [读正文]. "From Kruskal's theorem to Friedman's gap condition", [arXiv:2003.02714](https://arxiv.org/abs/2003.02714); 期刊版 *Math. Struct. Comput. Sci.*, [Cambridge 页](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/abs/from-kruskals-theorem-to-friedmans-gap-condition/1A7BBDDFBA8ED29D94918B14788D46F2). 内容:
  - PO-dilator: 偏序上的函子, 带支撑变换与支撑条件; normal 指 $\sigma\le\tau$ 蕴涵 $\mathrm{supp}(\sigma)\le^{\mathrm{fin}}\mathrm{supp}(\tau)$.
  - $W$ 在 $X$ 上的 Kruskal 不动点 $(Z,\iota,\kappa)$; 初始不动点 $\mathcal TW(X)$ 由变元 $\bar x$ 与项 $\circ(a,\sigma)$ 构成; Theorem 3.5 的初始性判据基于高度函数. Kruskal 导数 $\mathcal TW$ 对 $X$ 自然 (Def 4.1, Thm 4.2).
  - 迭代: $\mathbb T_0(X)=X$; $\mathbb T^-_{n+1}$ 是 $M\circ\mathbb T_n$ 的 Kruskal 导数 ($M$ 为有限多重集); $\mathbb T_{n+1}=\mathbb T_n\circ\mathbb T^-_{n+1}$. Prop 5.3: $\mathbb T_n(\emptyset)$ 同构于强 gap 条件下的 $n$-标号树.
  - 标签: 同构 $\pi^n$ 把 $\mathbb T_n$ 的标签 $i$ 送到 $\mathbb T_{n+1}$ 的 $i+1$. 每次新导数加一个新的底层标签 0, 已有标签整体上移; 标签 0 的叶来自新一阶段的导数.
  - gap 条件来自 Def 5.2 的序条款 (根标签比较 $j\ge i$); Lemma 6.3: 在标签 0 的根下 gap 条件自动成立.
  - 强度: 每个固定 $n$, $\mathbb T_n(\emptyset)$ 是 wpo 来自 $n$ 次应用一致 Kruskal 定理; 对一切 $n$ 一致需要 Π¹₂-归纳. 一致 Kruskal 定理在 RCA₀ 加链-反链原理上等价于 $\Pi^1_1$-CA₀ (Freund–Rathjen–Weiermann).
  - 原文没有出现 "Ω" 或 "坍缩层" 的说法; "标签 = 层" 是读法, 不是原文陈述.
- **一致 Kruskal–Friedman 定理** [读节选]: 等价于 $\Pi^1_1$-超限递归, 也等价于 gap 条件下坏序列的一个极小性原理 (Kříž 用过) — "Reverse mathematics of a uniform Kruskal–Friedman theorem", [arXiv:2112.08727](https://arxiv.org/abs/2112.08727) (据检索摘要). 一致 Kruskal 定理的综述: [arXiv:2208.00209](https://ar5iv.labs.arxiv.org/html/2208.00209) [只见题名].
- **Jervell** [读节选]. H. R. Jervell, "Finite trees as ordinals", CiE 2005, LNCS 3526 (DOI 10.1007/11494645_26): 给有限树一个良序, 与序数的一个初始段一一对应, 全体树的上确界是小 Veblen 序数 — [ResearchGate PDF](https://www.researchgate.net/profile/Herman_Jervell/publication/221652708_Finite_Trees_as_Ordinals/links/56d82e3208aebe4638b32871.pdf), [2008 讲稿](https://www.mathematik.uni-muenchen.de/~math/archiv/2008/buchholz/download/~gamma0/Buchholz/slides/jervell.pdf). 强度低于坍缩层级.
- **Patterns of resemblance** [读节选]. Carlson 的 patterns 用 Σ₁-初等性 ($\le_1$, $\le_2$ 关系) 描述大的可计算序数. Wilken, "Pure patterns of order 2" ([arXiv:1608.08421](https://arxiv.org/abs/1608.08421), *APAL* 2018): pure patterns of order 2 是结构 $\mathcal R_2$ 的有限同构型; 所涉证明论序数记作 $1^\infty$, 对应 $\Pi^1_1$-CA₀ / KPℓ₀ (据检索摘要); Carlson 证明它们在 covering 下良拟序. Wilken, "Pure Σ₂-elementarity beyond the core" ([arXiv:1710.01870](https://arxiv.org/abs/1710.01870), *APAL* 172, 2021). Freund, "Patterns of resemblance and Bachmann–Howard fixed points", *Selecta Math.* 28 (2022) art. 19, [arXiv:2012.10292](https://arxiv.org/abs/2012.10292): 证明 Montalbán 问题 27, 把相对化 patterns 联到 $\Pi^1_1$-概括, 证明归约到相对化 Bachmann–Howard 序数.

### Inferences
- [推断] 难点 1. Freund 的重构里, 标签就是 "这个结点由第几次导数引入" 的字面记录, 由构造给出, 从不比较. 本项目的 "provenance / 框架" 数据可以照这个形状设计: 每个 Ω 结点 (或其分支下标) 带一个由构造过程填写的阶段标签; 下一层的树类型 $=\,$ 本层类型与新一阶段导数的复合 ($\mathbb T_{n+1}=\mathbb T_n\circ\mathbb T^-_{n+1}$). 这样层号是 "第几层函子", 是类型结构的一部分.
- [推断] 难点 1. gap 条件 "像与其孩子的像之间的结点标签不低于孩子的标签" 是对比较的局部性约束: 两个子树只能经过层号不低于它们的区域相比. 这与壁垒的教训同向: 不允许跨低层分支比较 (对应 `noBT`, `dec→WLPO` 一族). 可试的对应: 把 "同一孩子" 的判断限制在一条 gap 型路径上, 路径上每个结点的层号证据字面可得.
- [推断] 难点 2. VdM-R-W 的猜想形式 $o(\mathcal T(\mathcal W))=\vartheta(o(W(\Omega)))$ 给出一种不依赖记号的 "该有的值": 树类型的值是 "构造 W 在 Ω 处取值, 再坍缩". 对本项目, Ω 结点的分支函数相当于 W, 折叠的 "该有的值" 可以试着定义成 "分支在 Ω 处的值经坍缩", 极大序型 (de Jongh–Parikh) 给出与线性化无关的内在值. 不过 wpo 的序型证明在文献里用记号作下界见证, 方向与我们相反.
- [推断] 难点 3. 极大序型的上界工具 (左集, 拟嵌入) 是对构造的一步定理, 对构造参数一致. 下界在文献里靠嵌入记号, 这对本项目只能作验收.
- [判断] patterns 的 $\le_1,\le_2$ 把 "层" 表为序数之间的初等性关系, 是另一种不用 Ω 指标的写法. order 2 的强度据摘要在 $\Pi^1_1$-CA₀ 一级 (ψ₀(Ω_ω) 一级, 后一换算本轮未核), 远低于 Ω_Ω, 且关系本身不可判定 (在本项目语境下), 只作参照.

### Gaps
- 把 Friedman 标号树的极大序型逐 $n$ 定成 $\psi_0(\Omega_n)$ 级的文献 (含 $n\ge3$) 本轮没有核到; VdM-R-W 自述是猜想, $n=2$ 已证.
- 标签取自良序 (而非 $\{0..n-1\}$) 的一致 Kruskal–Friedman 定理细节只读到检索摘要. 其标签是外给良序, 不是内部生成的序数.
- "pure patterns of order 2 的序数 = ψ₀(Ω_ω)" 是常见说法, 本轮只核到 "$1^\infty$ 对应 $\Pi^1_1$-CA₀/KPℓ₀".

## 问题 5. 层号本身是序数, 规则对层号一致, 又不判定层号之间的序: 有没有达到 Ω_Ω 或 Λ 级的先例

### Takeaway
本轮没有找到这样的先例. 能找到的统一构造都把层号放在可判定的位置: 自然数 $n$ (导数迭代, $n$-OS, $n$ 个标签), 外给的良序 ν (Freund–Rathjen 的 $\psi_\nu(D)$, σ-OS, 良序标签的 Kruskal–Friedman), 或语法项 (Buchholz, EBO). 文献能提供的是三种 "不判定层号" 的组织方式: 层号作类或类型下标, 层号作构造阶段标签, 低层作不被检视的参数. 外加一条一致性原理: 用泛性质定义, 对层一致. 在 Ω_Ω 处, 层号要由系统内部的对象给出, 这正是壁垒定理禁止 "以比较代替" 的地方.

### Cited Findings
- Freund–Rathjen $\psi_\nu(D)$: 层号 $\alpha<\nu$, ν 是给定良序; 项的序先比层号 — [arXiv:2112.08005](https://arxiv.org/abs/2112.08005) [读正文].
- Freund 的导数: 阶段按自然数 $n$ 索引, 每步用同一构造; 摘录里没有超限或以基数索引的阶段 — [arXiv:2105.09915](https://arxiv.org/abs/2105.09915) [读正文].
- APW 的坍缩以任意线序 $A$ 为参数, 不用不可数基数或 Ω 层级作指标; Lemma 17 里的 "Ω" 是 $B_D(A)$ 中最大的良序初始段, 不是不可数序数 — [arXiv:2201.04536](https://arxiv.org/abs/2201.04536) [读正文].
- Setzer: σ-OS 不用基数达到 ID_σ (σ 外给); $n$-OS 的层是类 $T_i$ — [Ordinal Systems PDF](https://csetzer.github.io/articles/ordsyscor010124.pdf) [读正文].
- Freund 的 Kruskal→gap: 标签由迭代阶段给出, 对一切 $n$ 一致需要 Π¹₂-归纳 — [arXiv:2003.02714](https://arxiv.org/abs/2003.02714) [读正文].

### Inferences
- [推断] 难点 1 对 Ω_Ω 的出路 (候选, 都未经检验):
  1. **层号作递归参数, 不作比较对象.** 仿导数迭代, 对层号树 $\ell$ 递归定义第 $\ell$ 层的对象类型: 零给基础; 后继取导数 (泛性质); ℕ-极限取直接极限 (需要 Corollary 2.10 型的跨层嵌入); Ω-极限 (层号本身是 Ω 结点) 取 "对一切低层树的余极限". 对象属于哪一层由它所在的类型决定. 风险: 这一步需要跨层嵌入的一致性, `stage-current` 记的 "跨层单调接口被否定 (对任意 D 推出 LPO)" 很可能就落在这里, 要先对照那条否定定理的前提.
  2. **低层作参数 (ι 构造子).** 第 $\ell$ 层的折叠对低层部分参数化, "在目标之下: 保留" 由 ι 标签回答, 不判定.
  3. **阶段标签作 provenance.** 每个分支下标带 "由哪一层的哪次构造引入" 的标签, 派发只读标签字面相等 (与 AGENTS "层号字面相等" 的存在性保留同向).
- [推断] 难点 2. 三种组织方式都把 "该有的值" 只放在规范生成的对象上 (初始不动点, 迹元素, 生成且有高度). 这支持 AGENTS 现行 "量化域先取带证据的读回域" 的做法, 并给出一个可以直接仿写的读回域定义: Freund Theorem 2.9 的 "生成 + 高度函数".
- [推断] 难点 3. 文献里阶段一致的定理都有 "一步定理 + 对阶段归纳" 的形状: Setzer Lemma 3.3, Freund Theorem 3.10, Kruskal→gap 的 $n$ 次应用. 对一切 $n$ 一致时, 元理论强度要上升 (Π¹₂-归纳, 元归纳). 本项目若要对层号树一致, 相应的是对层号树的结构归纳. Agda 里这是普通递归, 不额外要公理; 前提是每一步都写成对结构参数的一步定理, 这与 AGENTS "提供信息的标志: 写成对结构参数的一步定理" 一致.
- [判断] 逐条速查 (来源 × 难点 × 可借装置 × 构造性 × 强度):

| 来源 | 难点 | 可借装置 | 构造性 | 强度 |
|---|---|---|---|---|
| Aczel 1972 | 2, (1) | 超限型泛函, 极限层取乘积; 只取遗传膨胀泛函 | 经典集合论 (Ω 作定义域) | Bachmann 方法一级, 精确结论未核 |
| Danner 1999 | 2 | 只单调不够的反例; 以等价关系恢复迭代↔算术 | 经典 | 低 (算术层面) |
| Feferman 1970 (经 Rathjen) | 1 | replete; "相对范畴性": 新项的序由参数的序决定 | 未读 | 未读 |
| Weiermann 1994 | 3, 1 | 无不动点的 ABF 坍缩对某变元是 dilator (函子性) | 初等计算 | Bachmann 层级 |
| Girard–Vauzeilles 1984/85 | 1 | 函子式 Bachmann 层级; Ω 共尾步骤用变元等同 | Π¹₂-logic, 细节未读 | 到 $\psi(\varepsilon_{\Omega+1})$ 一级 |
| Freund 1809.06759, Freund–Rathjen 2112.08005 | 1, 2 | 支撑条件 $\mathrm{supp}\,\sigma<\vartheta\tau$; 正规形; 按 ν 分层且层号外给 | 构造 RCA₀ 可计算, 良基要 Π¹₁-CA | Π¹₁-CA₀; 沿 ν 的 Π¹₁-递归 |
| Freund 2105.09915 | 1, 2, 3 | 初始不动点 $(Z,\iota,\vartheta)$, ι 一律在下; 初始性判据 (生成 + 高度); 唯一自然同构; 对 $n$ 一致 | 构造是项系统 | $T_n[0]$ 系统 (VdM-R-W) |
| APW 2201.04536 | 1, 3, 树自足 | FGH 作 ℕ 上函子, 延拓即坍缩; 范数代基本列; $N\beta\le n$ ↔ 参数落在坍缩值之下 | ACA₀ 内可构造, 主定理要 Π¹₁-CA₀ | ψ₀(Ω_ω) 一级 (Π¹₁-CA₀) |
| Setzer 1999/2001 | 1, 3 | 有限分量集 $k$; 引入序 $\prec'$; 层作类 $T_i$ 与 $k_{i,j}$; 相对化归约 n+1→n; 比较只看 $k(a)\cup k(b)$ | 有构造性良序证明 | elementary OS < BHO; σ-OS 到 ID_σ |
| VdM-R-W 2017 | 2 | 极大序型作内在值; $o(\mathcal T(\mathcal W))=\vartheta(o(W(\Omega)))$ (猜想) | 经典 wpo 理论 | η₀ |
| Freund 2003.02714 | 1 | 标签 = 引入阶段; $\mathbb T_{n+1}=\mathbb T_n\circ\mathbb T^-_{n+1}$; gap 条件作比较局部性 | RCA₀ 系 | 每个 $n$ 在 Π¹₁-CA₀ 内 |
| Patterns (Carlson, Wilken, Freund) | 1 (参照) | 层表为 $\le_1,\le_2$ 初等性关系 | 经典 | $1^\infty$ (Π¹₁-CA₀/KPℓ₀) |
| Jervell 2005 | — | 有限树上直接给良序 | 构造 | 小 Veblen 序数 |

### Gaps
- 没有找到层号由系统内部生成 (Ω_Ω, Ω_{Ω_Ω}, Λ 级) 且不判定层号序的统一构造. 检索只用了通用术语, 范围有限; 未找到不等于不存在.
- 题目点名的 Bachmann 层级的高数类推广 (如 Isles, Pfeiffer 把 Bachmann 方法推广到更高数类) 与 Weiermann 的 "Ω_ξ 到大序数" 的坍缩, 本轮没有检索到可读材料, 是否存在对层号的非判定处理**未核**.
- Freund 2412.13051 (对 dilator 的归纳与 BH 不动点) 只见题名; 若其中有超限次导数, 会直接关系到上面的出路 1, 值得下一轮读.
