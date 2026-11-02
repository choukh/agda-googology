# 从 EBO 经 I 到 M 的序数记号与基本列: 文献调研

> **本文是证据记录, 按调查时间顺序写成, 不是结论. 查结论看 [OrdinalNotationsGuide.md](OrdinalNotationsGuide.md).** 后面的小节取代前面的: §12 (尤其 §12.14) 取代 §7、§9、§11 及文首结论中与之冲突的说法. 已知过时之处就地标了 **[更正 → §n]**, 原文保留.

> 调研日期 2026-11-02. 对象: 能从 EBO 一路走到 Mahlo 的序数记号, 以及定义在其上的基本列.
> 来源标记: **[原文]** 我读了一手来源 (论文、作者页、代码仓库); **[本项目已核]** `archive/src/Mahlo/SOURCES.md` 已读过, 此处不重复; **[推断]** 我自己的推理; **[测试]** 我的脚本在有限样本上的结果, 不是证明; **[转述]** 只见二手来源或搜索摘要; **[社区]** 未经同行评审.
> 读图转写的地方单独说明. 图中公式我是逐条读的, 但没有第二人复核.

## 结论

**存在, 但只在社区层面, 没有证明.** Denis Maksudov 的页面 *OCF and ordinal notation based on a weakly Mahlo cardinal* 给出了递归项集、递归序、以及逐条的结构性基本列, 从 0 开始, 经 EBO、不可达层级, 过 M, 到 $\psi_{\chi(0,0)}(\chi(\varepsilon_{M+1},0))$ 为止. M 处的分派写得很明确 (见 §3.3). 这正是用户要找的形状. 页面没有任何证明, 也没有人核查过的记录 [原文]. **[更正 → §12.14 Q2]** 这句只对 M 层仍成立. EBO 段已有机检 (§12.1), I 层有人工证明 (§12.8).

**正式文献到不了.** 有证明的结构性基本列, 我找到的最高点是 Wilken 在 $\Pi^1_1\text{-CA}_0$ 强度上的系统, 带 Bachmann 性质 [转述, 读了摘要与章节结构]. 它低于 EBO. **[更正 → §12.1]** 把范围放宽到未发表的机检工作, EBO 已有定理级的结构列. 在 M 处, 正式文献里只有 Buchholz–Cichon–Weiermann 1994 的范数定义 $\alpha[x]=\max\{\beta<\alpha: N\beta\le\dots\}$ [本项目已核], 那是有界搜索, 不是结构规则. Rathjen 1990、1991 与 Setzer 的 OT_I、OT_M 都没有基本列. Takaki 2005 明说 $\mathcal T(M)$ 上的典范基本列还在建立之中 [原文]. 这是"我没找到", 不是"不存在": 德语文献 (Pfeiffer 1992、Wemheuer 1994、Buchholz 1990 草稿) 没有取得.

**本次的三个新事实.**

1. **Maksudov 的 Mahlo 系统字面上有缺陷, 小补丁可修.** 我把它独立转写成脚本测试. 字面版在三处出错: 序的第 10.5.3 条有等号缺口, 造成三歧失败; 规则 20、规则 18 的输出可以落在项集之外. 打三个小补丁后, 6000 个主项、35931 步展开全部通过 (输出在项集内、严格递减、ω 型单调), 所有分支都走到 [测试]. 这不是良基性证明.
2. **它不是 EBO 基本列的保守扩张.** EBO 的项可以保序地嵌进去 (3000 项, 40000 对比较无一例不一致 [测试]), 但基本列只有 64% 逐项相同. 差异集中在小下标, 共三类 (§4). 我认为可以修补, 但修补后的系统没人写过.
3. **"EBO 到 OT_I 的序嵌入"这条第 3 层路线看起来是通的.** 映射只有三行, 像是纯字典序的. 3000 项、8978 步展开无一例离开 OT, 60000 对比较无一例不一致 [测试]. 见 §8.

**首要缺口.** `googology.fandom.com` 对抓取一律返回 HTTP 402. 我没有绕过它, 因此 Hyp cos、p進大好きbot、Deedlit、C7X 的博客全文都没有读到, 只有搜索摘要. 其中可能有比 Maksudov 更好的东西, 尤其是 p進大好きbot 的 *Rathjen-type Ordinal Notation*. 清单见 §10. **[更正 → §11, §12]** 后经用户授权用其 Chrome 读到了.

---

## 对照表

"结构性"指按项的形状逐条定义的规则; "范数式"指 $\max\{\beta<\alpha:N\beta\le\dots\}$ 这类有界搜索. EBO、I、M 三列分别回答该系统在这一层有没有结构性基本列.

| 系统 | 来源 | 强度上限 | EBO | I | M | 正确性状态 | 原样扩张 EBO 规则? | 与我方的关系 |
|---|---|---|---|---|---|---|---|---|
| Buchholz 1986 | APAL 32, 195–207; [epub](https://epub.ub.uni-muenchen.de/3841/1/3841.pdf) | 下标 $v\le\omega$ | 否 (到 $\Omega_\omega$ 段) | 否 | 否 | 同行评审, 引理已证 | 是 EBO 规则的祖先, 有差异 (§2.1) | 历史源头 |
| Extended Buchholz (Maksudov 基本列, p進大好きbot 记号) | [作者页](https://sites.google.com/site/travelingtotheinfinity/the-extension-of-buchholz-s-function), 2017-04 / 2020-07 | $\psi_0(\Lambda)$ | 是 | 否 | 否 | 社区, 无证明 | 就是它 | `EBO.lagda.md` 的来源 |
| $T_W$ (Maksudov, 用 Hyp cos 的函数) | [Wiki 表](https://googology.miraheze.org/wiki/List_of_systems_of_fundamental_sequences), [作者页](https://sites.google.com/site/travelingtotheinfinity/hypcos-s-notation-with-weakly-inaccessibles) 2017-08 | $I_\nu$ 的不动点 $\lambda$ | 是 | 是 | 否 | 社区, 无证明, 正规形是语义条件 | 否, 三处差异 (§4) | I 层规则的最简参照 |
| $T_A$ (Maksudov), Jäger 函数页 | [Wiki 表](https://googology.miraheze.org/wiki/List_of_systems_of_fundamental_sequences), [Cantor's Attic](https://neugierde.github.io/cantors-attic/J%C3%A4ger%27s_collapsing_functions_and_%CF%81-inaccessible_ordinals) | $\psi_{I(1,0,0)}(0)$ | 是 | 是 | 否 | 社区, 无证明 | 否 | 与 $T_W$ 同型 |
| **Maksudov Mahlo 系统** | [作者页](https://sites.google.com/site/travelingtotheinfinity/ocf-and-ordinal-notation-based-on-a-weakly-mahlo-cardinal) (两张长图), 博客日期 2021-02-10 [转述] | $\psi_{\chi(0,0)}(\chi(\varepsilon_{M+1},0))$ | 是 | 是 | **是** | 社区, 无证明; 我的测试见 §3.4 | 否, 三类差异 (§4), 但序嵌入成立 [测试] | **最接近需求** |
| Rathjen $T(M)$ | [1990](https://web.archive.org/web/20231208185422/http://www1.maths.leeds.ac.uk/~rathjen/Ord_Notation_Weakly_Mahlo.pdf), [1991](https://web.archive.org/web/20231207051454/http://www1.maths.leeds.ac.uk/~rathjen/KPM-Ordinal-Analysis.pdf), AML | KPM 所需 | 否 | 否 | 否 | 同行评审; 良序证明另见 Rathjen 1994 (未读) | 否, 有 φ | 序的权威来源, 无基本列 |
| BCW 1994 在 $\mathcal T(M)$ 上 | MLQ 40, [epub](https://epub.ub.uni-muenchen.de/3849/1/16.pdf) | KPM | 范数式 | 范数式 | 范数式 | 同行评审 | 否 | 唯一有证明的 M 层基本列, 但不是结构性的 |
| Setzer OT_I / OT_M | 见 SOURCES.md | $\psi_{\Omega_1}\Omega_{I+\omega}$ / $\psi_{\Omega_1}\Omega_{M+\omega}$ | 否 | 否 | 否 | OT_I 良序已机检 (我方 7500 行); OT_M 只有纸面 | 否, 有 φ | 第 3 层目标 |
| Takaki 2004/2005 | RIMS 1437, [PDF](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1437-11.pdf) | $\mathcal T(M)$ 内部 | 否 | 否 | 个例 | 2005 为研讨会讲义 | 否 | 只处理后继型 ptro 的表示 |
| Wilken 2024 | CiE 2024; 扩展版 [arXiv:2410.15953](https://arxiv.org/abs/2410.15953), ScienceDirect 有条目 | $\Pi^1_1\text{-CA}_0$ | 否 (低于 EBO) | 否 | 否 | 同行评审, 证 Bachmann 性质 | 否, 用 ϑ | 正确性证明的样板 |
| BMS / 0-Y / 1-Y | [Hunter](https://arxiv.org/abs/2307.04606); [Lean](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean); [Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) | 与 ψ 的比较未证 | 自带展开 | 未证对应 | 未证对应 | Hunter 为预印本; Lean 机检 (README 自述) | 否, 不是 ψ 记号 | 机检规模的参考, 不是标尺 |
| Taranovsky $C$ | [arXiv:1610.04633](https://arxiv.org/abs/1610.04633) | 猜想到高强度 | 可定义 | 可定义 | 可定义 | 良基性未证, 强度是猜想 [转述] | 否 | 无关 |

Pfeiffer 1992、Wemheuer 1994、Schütte 的 Klammersymbole、Duchhardt、Stegert、Arai 的 O(μ)、Weiermann、Carlson、Madore 都未读全文, 不进表, 见 §10.

**[更正 → §12.1, §12.8, §12.9]** 上表 Extended Buchholz 一行的 "社区, 无证明" 已过时: koteitan `ExBuchholz` 有机检. $T_W$ 一行的 "语义条件" 由 みずどら 的递归标准形解决 (§12.8). 表中未列 *Rathjen-type*、Exmachina、`bms-rathjen`, 见 §12.14 Q1.

---

## 1. 正确性判据

**Bachmann 性质与正则性.** BCW 1994 的 (B1)–(B6)、Lemma 1、Theorem 4 已由 SOURCES.md §82 核过, 我方 `Bachmann.lagda.md` 还机检了其中一段, 这里不重复. 要点是: Cichon 式的范数基本列在相对界下自动给出 Bachmann 系统, 绝对界则不行. Rathjen 在 *The Realm of Ordinal Analysis* 里说得很直接: 只有考虑序数代数性质的"自然"指派, 得到的层级才可用于组合独立性结果 [原文].

**没有"唯一正确"的基本列.** 我读到的文献都把正确性当作一组可验证的性质, 而不是一个唯一答案 [推断]. 对结构性规则, 实际要证的是四件事: 输出仍是规范项; $a[x]<a$; 递增且共尾; Bachmann 性质或正则性. Buchholz 1986 的 Lemma 3.2、3.3 证了前两件的原型 [原文]. Wilken 证了第四件 [转述]. 到 EBO 以上, 这四件都没有人证过. **[更正 → §12.1, §12.8]** 前三件在 EBO 上已机检, I 层有人工证明; 第四件 (经典义的 Bachmann 性质) 在 EBO 以上仍未见.

**对 M 的特殊要求.** 这一点放在 §3.3 结合规则讲.

## 2. EBO 这一段

### 2.1 Buchholz 1986

§3 的 $\mathrm{dom}(a)$ 与 $a[z]$ 就是我方规则的祖先 [原文, 读图, 印刷页 203–204]: $\mathrm{dom}(D_{u+1}0)=T_u$ 且 $(D_{u+1}0)[z]=z$; $(D_\omega 0)[n]=D_{n+1}0$; 参数后继给 $(D_v b[0])\cdot(n+1)$; 参数共尾度低于或等于当前层时 $a[z]=D_v b[z]$; 否则走 $D_u$ 迭代. Lemma 3.2 给 $a[z]<a$ 与单调性, Lemma 3.3 给 $a[z]\in OT$. 这一节的目的是证 $\mathrm{PRWO}(\psi_0\varepsilon_{\Omega_v+1})$ 的不可证性, 用到 Buchholz 的另一篇文章.

**存疑.** ([ ].4)(ii) 我放大读到的是 $a[n]:=D_v b[D_u b[1]]$. 如此读法右边不依赖 $n$, 不可能是对的基本列, 所以要么是扫描问题, 要么印刷有误 [推断]. 社区页面说扩展版把这条规则改成了 Buchholz 另一篇 *Relating ordinals to proofs in a perspicuous way* 第 6 页的规则 6, 但编号写作 ([ ].5)(ii), 与我读到的不合 [社区]. 我没能打开那篇原文 (链接 404). **[更正 → §12.9]** 是编号问题, 被替换的就是 ([ ].4)(ii).

**与我方的差异**: 下标只到 $\omega$; $\omega[n]=n+1$ 而我方 $\omega[n]=n$; 后继参数乘 $n+1$ 而我方乘 $n$; 不可数共尾的迭代写法不同. $\Omega_0=1$ 与我方相同.

### 2.2 谁造了 EBO

函数与基本列是 Maksudov 的, 页面写明基本列定义于 2017 年 4 月, 记号定义于 2020 年 7 月, 并引用 Deedlit 的帖子和 p進大好きbot 的记号 [原文]. Wiki 说递归比较与基本列的显式算法出自 p進大好きbot, 并有 koteitan 的计算器 [社区]. "EBO" 这个词的出处我没查到: Maksudov 页面不用这个名字, 我见到的最早用法是 kanrokoti 的博客标题里的 "EBOCF" [社区]. **[更正 → §12.13]** Fandom 词条 *Extended Buchholz's function* 的 "EBO in Japanese Googology" 回答了这个问题. 另有未证的期望: Extended Weak Buchholz (不取加法闭包) 与它极限相同, 尚未证明 [社区].

**与我方逐条比对.** Maksudov 页面的规则 1–8 与 `EBO.lagda.md` §5.1–5.3 的规则 1–6 对应, 共尾度分派条件一致, 只是把 $\psi_\nu(0)$ 的正规叶和奇异叶拆开写 [原文, 本人比对]. 我方补上的哑值分支 (§9) 对方没有, 因为对方的 $\eta$ 可以取不可数下标.

## 3. Maksudov 的系统: 到 I 与到 M

### 3.1 I 层: $T_W$ 与 $T_A$

规则取自 Wiki 表的 wikitext [社区, 我直接读了原文本]. $\Omega_\alpha$ 是第 α 个不可数基数, $I_\alpha$ 是第 α 个弱不可达, $I_0=\Omega_0=0$. π 只取 $\Omega_{\nu+1}$ 或 $I_{\mu+1}$, 闭包为 $+,\Omega,I,\psi$. 相对 EBO 新增的只有这几条:

- $\psi_{I_{\nu+1}}(1)[0]=I_\nu+1$, $[\eta+1]=\Omega_{\alpha[\eta]}$;
- $\psi_{I_{\nu+1}}(\beta+1)[0]=\psi_{I_{\nu+1}}(\beta)+1$, $[\eta+1]=\Omega_{\alpha[\eta]}$;
- $\pi[\eta]=\eta$, 共尾度为 π;
- $I_\nu[\eta]=I_{\nu[\eta]}$ ($\nu$ 极限);
- 系统极限 $\lambda[\eta+1]=I_{\lambda[\eta]}$.

**一个直接的对应** [推断]: 按定义 $\psi_I(1)$ 是最小 Ω-不动点, 即我方的 Λ. 其序列是 $1,\Omega_1,\Omega_{\Omega_1},\dots$, 与 $\Lambda[n+1]$ 逐项相同, 下标差 1. 所以在这个系统里 $\mathrm{EBO}=\psi_{\Omega_1}(\psi_I(1))$.

$T_A$ 把 $I_\nu$ 换成两参数 $I(\alpha,\beta)$, 多了后继与极限的分派 (rules 5–12), 形状与 §3.3 的 χ 规则相同.

**局限.** 正规形写作语义条件 (如 $\gamma\in C(\gamma,\psi_\pi(\gamma))$), 不是递归判定 [原文]. Wiki 的 WNF 第 1 条写的是 $P_B$, 疑为 $P_W$ 笔误. 这些段落都没有证明. **[更正 → §12.8]** I 层的递归标准形在 みずどら 的系统里已有.

### 3.2 Wiki 表上的 Mahlo 段不是结构性的

同一张 Wiki 表的 weakly Mahlo、α-weakly Mahlo、weakly compact 三节只给 $\alpha[n]=\max\{\beta<\alpha:L(\beta)\le L(\alpha)+n\}$ [原文], 与我方 `Inacc/FGH` 的范数搜索同型. 只看这张表会以为社区也没有结构性的 M 层规则. 结构规则在 Maksudov 的另一个页面上.

### 3.3 Mahlo 系统的定义

页面是两张长图, 下面是我读图所得, 用我的话转述. 引用参考文献只有 Rathjen 1990、Jäger 1984、Rathjen 1991. 页面未署名; 网站自述 "Traveling To The Infinity", Wiki 把这个网站归于 Denis Maksudov. 作者的一句自述是 "That simplifies creation of recursive ordinal notation and system of fundamental sequences".

**函数.** $\chi_\alpha:M\to M$ ($\alpha<\varepsilon_{M+1}$) 由 $B(\alpha,\beta)$ 定义, 闭包含 $0,M$、和、$\chi_\eta(\xi)$ ($\eta<\alpha$)、M 之上的 $\omega^\delta$, 以及小于已有正则基数的所有序数. $\chi_\alpha$ 枚举 $\{\kappa:\kappa\notin B(\alpha,\kappa)\wedge\alpha\in B(\alpha,\kappa)\}$ 的闭包. 性质: $\chi(0,\alpha)=\aleph_{1+\alpha}$; $\chi(\alpha,0)$ 与 $\chi(\alpha,\beta+1)$ 是正则的; 在某不动点以下 $\chi(\alpha,\beta)$ 等于 Jäger 的 $I(\alpha,\beta)$. $\psi_\kappa(\alpha)$ 定义为 $C_\kappa(\alpha)$ 外的最小者, 其中 $C_\kappa$ 从 $\kappa^-\cup\{\kappa^-,M\}$ 出发. $\kappa^-$ 是 κ 的前一个位置: $\chi(\alpha,\beta+1)^-=\chi(\alpha,\beta)$, $\chi(\alpha,0)^-=\alpha^*$. $\alpha^*$ 是 α 在 M 以下的最大主项分量. 这是对 Rathjen 原定义的改写, 去掉了 φ 和 Φ.

**项与序.** 项 $\mathcal T$: $0,\widetilde M$, 和, $\tilde\psi_r(a)$, $\tilde\chi(a,b)$, $\tilde\omega^a$ ($a\rhd\widetilde M$). $\tilde 1=\tilde\psi_{\tilde\chi(0,0)}(0)$. 形成条件: $\tilde\chi(a,b)$ 要求 $G(a,b)=1$ 且 $b\lhd\widetilde M$; $\tilde\psi_p(a)$ 要求 $p\in\mathcal R$、$K_p(a)\lhd a$、$a\lhd\widetilde M$. 页面声称 $K_r(c)\lhd e\iff o(c)\in C_{o(r)}(o(e))$, 以及 $(\mathcal T,\lhd)\cong(T,<)$, 都没有证明.

**基本列 (图中定义 11).** 记 $\mathrm{tp}(a)$ 为共尾型:

| 编号 | 项 | 共尾型 | 展开 |
|---|---|---|---|
| 1–2 | 和 | 末项的 | 改末项 |
| 4 | $\tilde 1$ | 1 | $0$ |
| 5 | $\psi_{\chi(0,b)}(0)$, $\mathrm{tp}(b)=1$ | ω | $\chi(0,b)^\ominus\times n$ |
| 6 | $\psi_{\chi(0,b)}(c)$, $\mathrm{tp}(c)=1$ | ω | $\psi_{\chi(0,b)}(c[0])\times n$ |
| 7–9 | $\psi_{\chi(b,c)}(d)$, $\mathrm{tp}(b)=1$, $(c,d)$ 为基底 | ω | $a[0]=$ 基底 $+1$ 或 $0$, $a[n]=\chi(b[0],a[n{-}1])$ |
| 10–12 | 同上, $\omega\le\mathrm{tp}(b)<M$ | $\mathrm{tp}(b)$ | $\chi(b[x],\text{基底})$ |
| **13–15** | 同上, $\mathrm{tp}(b)=M$ | ω | $a[0]=$ 基底 $+1$ 或 $0$, $a[n]=\chi(b[a[n{-}1]],0)$ |
| 16–18 | $\omega^b$ | 随 $b$ | $M\times n$, $\omega^c\times n$, $\omega^{b[x]}$ |
| 19 | $\chi(b,c)$, $\mathrm{tp}(c)\in\{0,1\}$; $M$ | 自身 | $x$ |
| 20 | $\chi(b,c)$, $\omega\le\mathrm{tp}(c)<M$ | $\mathrm{tp}(c)$ | $\chi(b,c[x])$ |
| 21 | $\psi_p(b)$, $\omega\le\mathrm{tp}(b)<p$ | $\mathrm{tp}(b)$ | $\psi_p(b[x])$ |
| 22 | $\psi_p(b)$, $p\le\mathrm{tp}(b)=r$ | ω | $\psi_p(b[c_n])$, $c_0=\psi_r(0)$, $c_{m+1}=\psi_r(b[c_m])$ |

**M 的分派回答了调研问题 3** [原文 + 推断]:

- ψ 的参数都小于 M (形成条件), 所以 $\mathrm{tp}(b)=M$ 根本不会出现在 ψ 的参数上. 规则 22 里的 r 永远是 $\mathcal R$ 的元素, 不需要 $\psi_M$.
- M 的共尾度只在 χ 的**第一参数**上起作用. $\chi(b,\cdot)$ 的 $b$ 共尾 M 时, 走规则 13–15: 用当前序列的前一项 $a[n-1]$ 作下标, 取 $b[a[n-1]]$. 这相当于把 γ-链搬到 χ 的第一参数上, 正是 Π-反射式的"对角回去". 规则 7–9、10–12、13–15 按 $\mathrm{tp}(b)$ 是 1、ω 型、M 三分, 这就是 ψ_χ 的分派.
- 正则基数 $\chi(b,0)$、$\chi(b,c+1)$ 共尾度等于自身, 其基本列就是恒等 (规则 19). 这与 $\Omega_{\nu+1}$ 同型. $\mathcal R$ 里所有 r 的处理都一样.
- 所以 cof(M)=M 没有带来新的困难形状, 代价落在序和形成条件上: $r^\ominus$、$K_r$、$a^\star$、$G$ 都依赖共尾度, 与基本列同时递归 ($r^\ominus$ 要用 $b[0]$). 这与 Setzer 的 SC、G 同类.

### 3.4 我的测试

脚本是我从图独立转写的 (约 200 行 Python), 不是页面作者的代码. 从 103 个种子 (含 $\chi(M,0)$、$\chi(M+1,0)$、$\chi(\omega^{M+1},0)$、$\chi(\chi(M,0),0)$ 及其上的 ψ) 出发, 按大小优先对展开取闭包, 主项大小上限 300 节点. 每步检查: 输出在 $\mathcal T$ 内; $a[x]\lhd a$; ω 型序列单调. 另随机抽样检查三歧与传递. 敏感性检查: 把规则 13 故意改错, 脚本立刻报出 notMono 失败. 限制: 只取小下标 $n\le 2$ 和少数不可数下标样本; 规则 16–18 只在嵌套时被走到; 大小上限以外没有覆盖.

**字面版的三处失败.**

| 编号 | 现象 | 例子 | 补丁 |
|---|---|---|---|
| P1 | 10.5.3 写 $\tilde\chi(a,b)\lhd c^\star$, 等号时两个方向都不成立, 三歧失败, 进而 $a[x]\not\lhd a$ | $\chi(M,0)$ 与 $\chi(\chi(M,0)+1,0)$ 互不小于 | 改为 $\unlhd c^\star$ |
| P2a | 规则 20 不检查 $G$, 输出可不是规范项 | $\chi(0,I+I)[0]=\chi(0,I)$, 而 $\chi(0,I)=I$ | $G(b,c[x])=0$ 时取 $c[x]$ |
| P2b | 规则 18 在 $b[x]\unlhd M$ 时 $\omega^{b[x]}$ 不合形成条件 | $\omega^{M+M}[0]=\omega^M$, 应为 $M$ | 取 $M$; $b[x]<M$ 时另定 |

页面第 11 节末尾的注记声称 $a[x]\in\mathcal T$, 字面上因此不成立. P2a、P2b 都不改序数值, 只是规范化. P1 是序的修正, 我由语义判断 $\chi(c,d)>c^\star$, 所以应取等号 [推断]. P1 也可能是作者笔误而非我的误读, 请对照原图. **[更正 → §12.3]** 博客文本字面确认 P1, 不是读图错误. §12.7 另有独立印证.

**打补丁后**: 6000 主项、35931 步, 全部通过, 无失败. 走到的分支计数: 规则 5 (61)、6 (35)、7 (73)、8 (17)、9 (6)、10 (1192)、11 (111)、12 (10)、13 (7)、14 (35)、15 (5)、19 (1726)、20 (1751)、21 (259)、22 (711). 抽样的三歧、传递无失败.

这只说明规则在样本上自洽, 不证良基性, 也不证 $\mathcal T$ 的序型等于所声称的值.

## 4. 能否与 EBO 逐项一致 (调研问题 4)

**结论: 序嵌入可以, 逐项一致不行, 但差异只有三类, 都在小下标.** 以下比对都是在规则文本的转写上跑的, 不是运行 Agda.

| 系统 | $\Omega_0$ | $\psi$ 在 $0$ 处 | γ-链起点 | 闭包 | φ |
|---|---|---|---|---|---|
| 我方 EBO | $1$ | $\psi_u(0)=\Omega_u$, $\psi_0(0)=1$ | $\Omega_\mu$ | $+,\psi$ | 无 |
| Buchholz 1986 | $1$ | 同左 | 见 §2.1 | $+,D_v$ | 无 |
| $T_W$ | $0$ | $\psi_\pi(0)=1$ (对所有 π) | $1$ | $+,\Omega,I,\psi$ | 无 |
| Maksudov Mahlo | $\chi(0,\alpha)=\aleph_{1+\alpha}$ | $\psi_{\Omega_1}(0)=1$; $\psi_{\Omega_{\nu+1}}(0)=\Omega_\nu\cdot\omega$ | $\psi_r(0)$ | $+,\chi,\psi$, M 上 $\omega^\delta$ | 无 |
| Setzer OT_I | $\Omega_0=0$, 且在 Fi 上 $\Omega_a=a$ | $\psi_{\Omega_1}0$ 很大 | 无基本列 | $+,\varphi,\Omega,\psi,I$ | 原语 |
| Rathjen / Buchholz 1993 | $0$ (Buchholz) | 同类 | 无基本列 | 含 φ | 原语 |

**$T_W$ 对 EBO** [测试]. 翻译 $\tau$: $\psi_u(0)\mapsto\Omega_{\tau u}$, $\psi_u(a)\mapsto\psi_{\Omega_{\tau u+1}}(\tau a)$. 对 22 个种子的闭包比较 $\tau(t[n])$ 与 $\tau(t)[n]$ (种子里有 6 个非标准形, 见 §8, 对规则比对无影响):

| 修正 | 一致 / 不一致 (共 2400 步) |
|---|---|
| 不修正 | 1714 / 686 |
| A: γ₀ 取 $\Omega_\mu$ | 2044 / 356 |
| B: $\Omega_0=1$ | 1839 / 561 |
| C: $\psi_{\Omega_{\nu+1}}(0)=\Omega_\nu$ | 2070 / 330 |
| A + B | 2169 / 231 |
| A + B + C | **2400 / 0** (项上限放宽到 3000, 仍 9000 / 0) |

所以 EBO 与 $T_W$ 的 EBO 段规则相同, 只差这三处约定. 差异 C 不只是改写: $\psi_\pi(\omega)[0]=\psi_\pi(0)$ 在 $T_W$ 里是 1, 在 EBO 里是 $\Omega_\nu$. $T_W$ 在 I 层新增的规则不受这三处影响 [推断].

**Mahlo 系统对 EBO** [测试]. 翻译要多一个 $-1+$: $\psi_u(0)\mapsto\chi(0,-1+\tau u)$, $\psi_0(a)\mapsto\psi_{\chi(0,0)}(\tau a)$, $u\ne 0$ 时 $\psi_u(a)\mapsto\psi_{\chi(0,-1+(\tau u+1))}(-1+\tau a)$. 这里 $-1+$ 去掉有限部分开头的一个 1. 依据是 $\psi_{\Omega_{\nu+1}}(c)$ 对应 Buchholz 的 $\psi_\nu(1+c)$ [推断]. 在打了 §3.4 三个补丁的版本上, 3000 个 EBO 项全部落在 $\mathcal T$, 40000 对比较序无一例不一致. 但基本列只有 5726 / 8967 逐项相同. 例如 $\psi_0(\Omega_2)[0]$ 在 EBO 是 $\psi_0(\Omega_1)$, 在 Mahlo 系统是 $\psi_{\Omega_1}(\psi_{\Omega_2}(0))=\psi_{\Omega_1}(\Omega_1\cdot\omega)$. $\Omega_\omega[n]$ 在 EBO 是 $\Omega_n$, 在 Mahlo 系统是 $\Omega_{n+1}$. 共尾与极限相同, 只是序列错位 [推断].

**怎么转换.** 要逐项一致, 只能改 Mahlo 系统的底层, 不能改 EBO: 把 $\psi_{\chi(0,\nu)}$ 换回 Buchholz 式 ($\psi_\nu(0)=\Omega_\nu$), 把 γ₀ 换成 $\Omega_\mu$, 令 $\Omega_0=1$, 并相应改 $r^\ominus$ 与规则 5、6、8、9. 这个改动是否破坏 $K_r$、$G$ 的等价性, 没有人检查过, 我也没有试.

**φ 的问题.** Setzer 与 Rathjen 的系统以 φ 为原语, ψ 的值整体被抬高 ($\psi_{\Omega_1}0$ 已是 φ-闭包, 至少是 $\Gamma_0$ 量级 [推断]), 所以与 EBO 没有值上的逐项对应, 只能有序嵌入. φ 在社区系统里不是原语, 由 ψ 表达.

## 5. 其它正式文献

**Rathjen 1990 与 1991** [原文, 全文 grep 与部分精读; OCR 有噪声]. 这两篇原文 SOURCES.md 记为未取得, 本次经 Wiki 给的 Wayback 链接拿到了作者在 Leeds 的副本. 1990 年文的目的是给出足以处理 KPM 的记号系统, 引言梳理了谱系: Buchholz 的 ψ, Buchholz–Schütte 做到第一个弱不可达 $I_0$ 以下, Jäger 扩到 $A_0$, Pohlers 做 θ 版本, Schütte 用 Klammersymbole 再扩展. 1991 年文说其 §2 的系统本质上就是 $T(M)$. 两篇文本都未出现 "fundamental", 基本列不是其内容. $\chi_\alpha$、$\mathrm R=\{\chi_a 0\}\cup\{\chi_a(\beta+1)\}$ 的结构与 Maksudov 一致, 后者是其简化. 另一个社区页提醒: 简化版 ψ 能否给出记号并不确定, 原版才确知可以 [社区]. 这条警告针对简化 OCF, Maksudov 的改写同样属于此类风险 [推断].

**BCW 1994 的 $\mathcal T(M)$ 实例** [本项目已核]. 见 SOURCES.md §114: $\alpha[x]_M:=\max\{\beta<\alpha:N\beta\le 3^{3^{N\alpha+x+1}}\}$, 并给出 KPM 可证全函数被 $H_\alpha$ 支配的推论. 这是唯一有证明且到达 M 的基本列, 代价是非结构性. 社区 Wiki 表里 Mahlo 段的范数式也引它作依据 [原文].

**Takaki** [原文, 引言]. 2005 年文在 $\mathcal T(M)$ 上定义 ptro, 只给出后继型 ptro 作为某规范序列极限的表示, 且写明典范基本列的建立还在进行中. 引文 [Ta04] 当时"to appear in AML", 我没有读.

**Wilken 2024** [转述: 摘要与章节结构, 经抓取工具摘要, 未逐句读证明]. 对 ϑ 型相对化记号定义基本列, 证 Bachmann 性质, 引入范数与 Hardy 层级; 在 Bachmann–Howard 以下与 Buchholz 的指派一致; 作者称同时定义的版本可向更大序数推广. 这是最好的正确性证明样板, 但起点是 ϑ, 不是 ψ, 且停在 $\Pi^1_1\text{-CA}_0$. Fernández-Duque–Weiermann (arXiv:2203.07758) 在 Bachmann–Howard 以下证正则性 [本项目已核].

**Buchholz 主页** [原文]. 列有 *Ordinal notations and fundamental sequences* (2003-03-10)、*A survey on ordinal notations around the Bachmann-Howard ordinal* (2015)、*Relating ordinals to proofs*, 但链接均 404. 其中没有 Buc90.

**Buc90** (*Wellordering proofs for systems of fundamental sequences*, Draft, München, 1990). Setzer 1998 引它, 称是其良序证明的主要基础, 并为避开基本列作了改动 [原文]. 其余一概未知: 多次检索只见书目, 没有全文; Buchholz 主页未列. 所以它到底覆盖到什么强度, 我说不出来. 它的标题暗示 Buchholz 手上有带基本列的良序证明方法, 若能取得, 对 Maksudov 系统的证明最直接 [推断].

**未找到基本列的来源.** Takeuti 的序数图、Arai 的 O(μ)、Stegert、Duchhardt: 本次只见书目或未检索到相关内容, 检索很薄, 不能下结论.

## 6. 社区系统: BMS 及其同类

**Hunter, arXiv:2307.04606v3** [原文]. 证 BM4 全序且序即字典序, 再用稳定序数的反射性质把数组映到序数, 由此得良序. 无期刊信息. 注意 arXiv 摘要页与搜索结果的作者字段曾不一致, 本次抓到的摘要页与 PDF 均为 Rachel Hunter. 序型: 文中自述整体尚未仔细用序数函数估计, 只给"预期", 且不是用 ψ、I、M 表达, 而是用 Σₙ-稳定. Wiki 称有一位用户 (p進大好きbot, 2023) 对证明正确性表示过怀疑 [社区], 这条早于下面的 Lean 工作.

**Lean 形式化** [原文, 读 README 与文档; 我没有构建]. [EgoFakeFantasy/BMS-Well-Ordering-Lean](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean) 自述给出 BM4 严格良序的无条件定理 (ZFC / 可构造层次版, 入口 `bm4_strictWellOrder_l`), 并在 2026-10-10 增加每个固定高度 H 的 Z₂ 推导. [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) 自述证明 0-Y 与 BMS 序同构, 以及 1-Y 良序, 公理审计只依赖 `propext`、`Classical.choice`、`Quot.sound`. [koteitan/bms-paper-formalization](https://github.com/koteitan/bms-paper-formalization) 是 Isabelle 计划, 未见完成.

**强度与 I、M 的关系.** 未证, 且有争议的余地. Pair Sequence 对应 Buchholz 序数已证 (p進大好きbot, 2018, 经 Hunter 转述; Lean/Isabelle 见 §7). 三行以上的 ψ 对应只有 Wiki 上的展开表, 相关 Wiki 页也说这些分析未经证明 [转述]. 我没有查到任何严格的"BMS 片段 = $\psi(I)$"或"$\psi(M)$"定理. 本调研的结论: BMS 不能当标尺, 它只是另一种基本列系统, 且与 ψ 的比较本身就是开放问题 [推断].

**其它.** [hzyhhzy/column-ordinal-notations-hzy](https://github.com/hzyhhzy/column-ordinal-notations-hzy) 收集了大批列式记号及 Lean 或纸面良序证明, 明确区分候选、失败与伪序, 是诚实的社区工作, 但都不是 ψ 记号, 与 EBO 没有逐项关系 [原文, 读 README]. [hypcos/notation-explorer](https://github.com/hypcos/notation-explorer) 有多种记号的展开器, 含 `cOCF.js` (solarzone 写), 我只看了开头, 未判断其强度. [AzertyWasTaken/Ordinals](https://github.com/AzertyWasTaken/Ordinals) 的统计表里有 $\psi(\Lambda)$、$\psi(M_\omega)$ 等强度标签, 来源是其 `analysis.txt`, 属社区估计, 我未核 [社区]. Taranovsky 的良基性未证, FOM 帖子里作者自述没有完整的 gap 指派 [转述].

## 7. 机器检查的记号: 到哪了

| 工作 | 系统 | 强度 | 基本列 | 状态 |
|---|---|---|---|---|
| Mathlib `SetTheory/Ordinal/Notation` | Lean 4 | $\varepsilon_0$ | 有 (`fundamentalSequence`, 带 `fundamentalSequenceProp`) [原文] | 主线库 |
| [SteveWmoc/lean-ordinal-analysis](https://github.com/SteveWmoc/lean-ordinal-analysis) | Lean 4 | $\varepsilon_0$, 带通用接口 | 有, 证共尾 [README] | 个人 |
| [vihdzp/ordinal-notation](https://github.com/vihdzp/ordinal-notation) | Lean | 未知 | 未知 | README 写 "under construction" |
| hydra-battles (Castéran) | Coq | $\varepsilon_0$; $\Gamma_0$ 在旧包 coq-cantor [转述] | README 提及 Ketonen–Solovay 机制; 基本列细节未核 | 未构建 |
| Grimm | Coq | 未读 | 未读 | 未取得, 不作判断 |
| [cj-xu/OrdinalNotations](https://github.com/cj-xu/OrdinalNotations) | Cubical Agda | $\varepsilon_0$ | 未核 | Nordvall Forsberg–Xu–Ghani |
| [koteitan/pss-proof](https://github.com/koteitan/pss-proof) | Isabelle、Lean 4 | Buchholz 序数段 | 有 (Pair Sequence 展开; 含 Buchholz 1986 Lemma 3.2a、3.3 及 *Relating ordinals* 规则 6 的文件) | README 称无 `sorry`, 有构建期审计; 我未构建 |
| [EgoFakeFantasy/…](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean) | Lean 4 | BMS 整体 | 自带展开 | 见 §6, 无 ψ 比较 |
| [hyperpolymath/echo-types](https://github.com/hyperpolymath/echo-types) | Agda | Buchholz 语法脚手架 | 否 | 注释写 scaffolding |
| 我方 `archive/src/Mahlo/Inacc/` | Agda `--safe` | $\psi_{\Omega_1}\Omega_{I+\omega}$ | 只有范数搜索 | 良序机检 |
| 我方 `probes/OCF/Align/EBO.lagda.md` | Agda `--safe` | $\psi_0(\Lambda)$ | 规则式, 有递减证书 | 标准形上的良基性未做 |

**[更正 → §12.9]** 上表过时, 新表见 §12.9. hydra-battles 的 Γ₀ 在 `Gamma0/*.v` 标 draft; `ExBuchholz` 未列.

我的搜索范围内, 机检的 ψ 型记号带结构性基本列, 最高是 koteitan 的 Buchholz 段 (若其 README 属实). 我方 EBO 的定义已高于它, OT_I 的良序也高于它. Isabelle AFP 与 Kovács 的工作本次没有重新检索. **[更正 → §12.9]** 这段结论是错的: 最高是 `googology-lean` 的 EBO, 其基本列是定理级的; 我方 EBO 与它平级, 不高于它. Kovács 见 §12.12.

## 8. 对第 3 层路线的影响: EBO 嵌入 OT_I

**映射** [推断 + 测试]:

$$\tau(\mathbf 1)=\varphi'_0 0,\qquad \tau(\psi_u(0))=\Omega'_{\tau u}\ (u\ne 0),\qquad \tau(\psi_u(a))=\psi_{\Omega'_{\tau u+1}}(\tau a)\ (a\ne 0),$$

和逐项映射. 这不保值, 只保序. 第 3 层只需要序.

**为什么它是字典序的** [推断]. 像集里没有 $\psi_I$、$I$, φ 只有 $\varphi'_0 0$. 按 `Order.lagda.md` 的子句, 比较只会用到 (≺′1)(≺′2) 的和的字典序、(≺′5) 的 $\psi$ 对 $\psi$ 先比层再比参数、(≺′6) 的 $\psi_\pi b\prec\kappa\iff\pi\preceq\kappa$、(≺′9) 的 $\Omega'$ 对 $\Omega'$, 以及 φ′₀0 落到最底的 (≺′11). 这与 EBO 的 `_<ᵀ_` (§2) 完全同构. (OT5) 只要求参数非 0、不在 Fi′, 像集自动满足. (OT4) 的 $G_\pi$ 在像集上就是 Buchholz 的 $G_u$ 加上层的部分.

**测试** [测试]. 我把 `Order`、`Closure` 里相关子句转写成 Python.

- 22 个 EBO 种子中 6 个的像不在 OT, 全是 $\psi_0(\psi_1(\Omega_2))$ 这种非 Buchholz 标准形 (此处 $\Omega_2\not<\psi_1(\Omega_2)$), OT 拒绝它们是对的.
- 从其余 16 个种子对 EBO 规则取闭包: 3000 项、8978 步, **无一步离开 OT**, 也即"标准形对展开封闭"在样本上成立.
- 60000 对比较, EBO 字典序与 $\prec'$ **无一例不一致**. 所有 $t[n]$ 的像都在 $t$ 的像之下.

缺陷: 这里"标准形"正是用 OT 条件筛的, 不是独立写的 EBO 标准形谓词; 也没有在 Agda 里跑. **[更正 → §11, 指南 §8]** 独立的谓词后来有了 (`EBOI` 的 `isOTᵉ`), `eboi/test3.py` 测了它与 OT 的一致性, `SetzerTest.agda` 在 Agda 上跑了 Setzer 定义.

**要做的义务.**

1. 在 EBO 上写标准形谓词 (Buchholz 的 $G_u(a)<a$, 带层). **[更正 → §11]** 谓词已有.
2. $\tau$ 严格保序 (对项大小归纳, 预计是几十行的字典序论证).
3. $\tau$ 保标准形, 核心是 $G_{\Omega'_{\tau u+1}}(\tau a)$ 与 $\tau(G_u(a))$ 的对应. 注意 (G5) 无条件地把 $\Omega'_c$ 降到 $c$, 而 (G4) 多了层上的 $G_\pi(c)$, 这里要小心比较.
4. 标准形对 `fsn↓` 封闭 (Buchholz Lemma 3.3 的 EBO 版). 这条不依赖 $\tau$, 也是最费力的一条, 它决定 FGH 能否只在标准形上跑. **[更正 → §12.11]** 这条已有 Lean 机检的句法证明可照搬, 见指南 §5.2.
5. $\tau t\prec\psi_{\Omega'_1}(\Omega'_{I+n})$, 由 (≺′5)(≺′6)(≺′10) 得到.

然后 `archive/src/Mahlo/Inacc/Theorem.lagda.md` 的 `wellfounded : ∀ n {y} → OT y → y ≺ endpt n → Acc y` 沿 $\tau$ 拉回, 给出 EBO 标准形的 Acc, FGH 就不再依赖燃料或假设.

**边界.** 对 I 层 (不只是 EBO) 的嵌入要处理 $\psi_I$: Setzer 的 $\psi_I 0$ 已是 Ω-不动点, 而 $T_W$ 的 $\psi_I(0)=1$、$\psi_I(1)=\Lambda$, 下标差一 [推断], 也未测试. Setzer 只有一个 $I$, 而 $T_W$ 有 $I_\nu$, 只有 $I$ 的片段才可能嵌入. **[更正 → `EBOI` §10]** 后来测了: 单 $I$ 片段上 τ 无下标错位, 样本无反例. 这条路不提供基本列: OT_I 自身仍只有范数搜索.

## 9. 建议的标尺与开放缺口

**标尺建议** [判断]: 以 **Maksudov Mahlo 系统 (带 P1、P2a、P2b)** 作为规则形状的参照, 不作为正确性的依据. **[更正 → §12.14 Q4]** 已改: EBO 段以 `ExBuchholz` 校准, I 层看 みずどら, χ、M 层看 KawamoYurase 重写. 底层保留 `EBO.lagda.md` 不动, 按 §4 的三类差异改写其下层. 分阶段:

1. **I 片段.** $T_W$ 只取 $I_1$, 加 A、B、C 修正, 成为 EBO 的保守扩张. **[更正 → `EBOI` §10]** 这样不是保守扩张: 到 I 层不与 $T_W$ 逐项一致, 差 $1+a$ 偏移. 现行标尺是 `EBOI`. 这一段新增的规则很少 (§3.1), 与 EBO 的对应已由测试支持, 良基性可以走嵌入 OT_I.
2. **χ 层.** 引入 $\chi(b,c)$ 与 $\mathrm{tp}(b)\in\{1,\omega\text{ 型}\}$ 的分派.
3. **M 层.** 加规则 13–15 与 $\tilde\omega$. 良基性只能指向 OT_M 或 $T(M)$, 这些只有纸面证明, 我方未机检.

Wilken 的结构可作为 Bachmann 性质证明的模板. BCW 的范数基本列留作 M 层的对照, 可用来测试结构规则是否被其支配.

**开放缺口.**

- 没有人证过 Maksudov 系统的任何一条: 项封闭、递减、$(\mathcal T,\lhd)\cong(T,<)$、$K_r$ 的等价. 我的测试只覆盖小样本. (对 Maksudov 系统仍成立; 不要读成对 EBO 成立, 见 §12.1.)
- Maksudov 对 Rathjen 函数的简化是否与原系统序同构, 未知. 即便规则自洽, $\mathcal T$ 的序型也未被核实.
- 修补后的"逐项扩张 EBO"的版本尚不存在 (§4 末).
- 结构性 M 规则与 BCW 范数基本列的关系, 没有任何比较结果.
- P1 需要对照原图复核, 也可与 Rathjen 的序或 Setzer Def 3.3 比较后确认. **[更正 → §12.3]** 字面已核, 正确性仍只来自语义判断.

## 10. 没能取得或未读

| 材料 | 情况 |
|---|---|
| Fandom 博客 | 已经用户授权的 Chrome 读取, 见 §11、§12. 仍缺: Hyp cos *OCF vs Array Notation* 这一标题不存在; Hyp cos 其它 OCF 帖只看了长度. Miraheze 显示校验页, 跳过 |
| Buchholz 1990 草稿 | 2026-11-02 重试: 仍只有书目 (Setzer 的 *Ordinal Systems, Part 2* 等引用), 2025 年一篇 arXiv 文章称 "Buchholz system" 出自它 [转述]. 未取得 |
| Buchholz 2003 *Ordinal notations and fundamental sequences*、*Relating ordinals to proofs*、2015 综述 | 重试: `OrdNotFS.pdf`、`f7june.pdf` 在现址 404; 搜索索引有 `f7june.pdf` 的片段但打不开. *Relating* 刊于 Feferman 文集 (LNL 15, 2002), 2015 综述只有 DOI, 都未取得. koteitan 的 `lean/Buchholz-rel-ord` 已细读: 他们也没有原稿, 只按引文转录规则 6 (§12.9) |
| Buchholz 1986 ([ ].4)(ii) | 已读, 读法存疑 (§2.1). koteitan 的转录支持 "这条被规则 6 替换" (§12.9), 但印刷原文仍未第二人核查 |
| Rathjen 1994 (AML 33(1), 35–55, KPM 良序证明, DOI 10.1007/BF01275469) | 重试: 只有书目与摘要, Springer 付费, 未绕过. 摘要: 直接基于递归大序数做记号系统 [转述]. 另 *Proof theory of reflection* (APAL 68) 有公开副本, 未读 |
| Pfeiffer 1992 (MLQ 38(1), 431–456)、Wemheuer 1994 (Hannover) | 重试: 仍只有书目. Pfeiffer 英文题名 *A Notation System for Ordinal Using ψ-Functions on Inaccessible Mahlo numbers*, 接 Jäger 1984 的 $I_{\alpha\beta}$ 之后加弱不可达 Mahlo 层级, 有无基本列不明 [转述]. Wemheuer 的题名是 Π₃-Mahlo 数上的记号系统 (Math Genealogy) |
| Jäger 1984、Schütte 的 Klammersymbole、Duchhardt、Stegert、Weiermann、Carlson、Arai O(μ)、Grimm | 未读. Stegert (Münster, 2011 结业) 只见馆藏记录, 没有 PDF, Exmachina 的帖子表明能取得 (§12.10). Duchhardt 重试未命中 |
| 日文 Wiki 上 mrna 的「降下段階配列表記」「多変数段階配列表記」、kanrokoti 的 KumaKuma ψ | 已读概要, 见 §12.8. 比这些更重要的是 みずどら 与 KawamoYurase 的帖子, 也在 §12 |

**测试脚本** 已存入 `probes/Survey/scripts/`: `cmp.py` (EBO 对 $T_W$), `mnot.py` (Maksudov Mahlo 系统, 含补丁开关), `emb.py` (EBO 对 OT_I 与 Mahlo 系统的序嵌入, 须在该目录下运行). 这些是有限样本测试, 不是证明. 另有 `eboi/` (`EBOI` 的测试). 命令与预期数字见[指南 §8](OrdinalNotationsGuide.md#8-复现). 注意 §4 的 2400 步表要把 `cmp.py` 第 167 行的上限 `3000` 改成 `800`, 默认跑的是 9000 步.

---

## 11. 补读: Fandom 博客 (2026-11-02, 经用户授权用其 Chrome 读取)

上文 §10 的 HTTP 402 缺口部分补上. 以下均为 [原文][社区], 用我的话转述, 公式读自页面的 MathML 源码; 未经第二人复核. 博客内容 CC-BY-SA.

**1. p進大好きbot, *Ordinal Notation Associated to Extended Buchholz's OCF*** ([链接](https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Ordinal_Notation_Associated_to_Extended_Buchholz%27s_OCF)). 这是 EBO 记号的直接出处. 项是 `()`, `⟨X₁,X₂⟩`, 主项序列; 序是字典序, 全序但作者注明在全部项上不是良序. **它给出了显式标准形谓词**: `G(X,Y)◃Z` 递归定义 (Y = ⟨W₁,W₂⟩ 且 X ≤ W₁ 时要 W₂ < Z 并递归到 W₁、W₂; W₁ < X 时平凡真; 和逐项), `⟨X₁,X₂⟩ ∈ OT` 当且仅当两分量在 OT 且 `G(X₁,X₂)◃X₂`, 和要求单调不增. 这正是 §8 义务 1 所需的独立谓词, 不必再用 OT_I 条件筛. 基本列规则与 `EBO.lagda.md` 同型, 含第 6 条的 γ-链 (起点 ⟨Z[0],0⟩, 即 Ω_μ). 作者**声称** OT 对 [n] 封闭、(OT,<) 与序数同构, 写的是 "by the construction", 页面无证明. 所以 EBO 的良基性在这里是依赖 ZFC 语义的声称, 不是证明. **[更正 → §12.1, §12.4]** 博客本身仍如此, 但这条声称已由 koteitan 机检.

**2. p進大好きbot, *Rathjen-type Ordinal Notation*** ([链接](https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Rathjen-type_Ordinal_Notation), 2019). **这是比 Maksudov 更完整的 M 层候选.** 函数 φ^i_a(b) (i = 0 为 Veblen, i = 1 为 Rathjen 的 Φ, i = 2 为弱 a-Mahlo 枚举)、χ^κ_a(b)、ψ_κ(a), 外加度数 deg. 有递归的项集、序、标准形 OT、dom、完整的结构性基本列, FGH 也定义了; 另有 Naruyoko 的 GitHub 实现 (页面提到, 我没能打开链接核对) (**[更正 → §12.5]** 后来读了). 作者的三点自述须当真: 强度未知; 基本列算法 "possibly" 有误; 标准形依赖作者未发表的 OCF, 其假设的公理 schema 可能不相容. 它保留 Rathjen 的约束 a ∈ B(a, χ_a(b)), 并指出社区常见的 "简化" 会丢掉序的可计算性, 这对 Maksudov 的简化版是直接的警示. 以 φ 为原语, ψ_{Ω₁} 从 Γ 数开始 (页面分析表), 所以与 EBO 不逐项对应, 与 OT_I 同一路数.

**3. p進大好きbot, *Cheatsheet on Properties of OCFs*** ([链接](https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Cheatsheet_on_Properties_of_OCFs), 2019). Buchholz、扩展 Buchholz、Rathjen 弱 Mahlo ψ 的展开表 (作者说可能多错). **重要边界**: 依 Rathjen 1990 Theorem 6.3, T(M) ∩ M 只到 ψ_{χ_{φ₁(M+1)}(0)}(0) 量级, 作者判断此点以上的社区 "分析" 没有真实算法支撑, 不可复现, 连 ∈ 的可判定性都未知. 另外强调 Rathjen 1990 的 ψ、Realm 的简化 ψ、KPM 论文的 ψ 是三个对象, 社区常混.

**4. Hyp cos, *General fundamental sequences for OCFs*** ([链接](https://googology.fandom.com/wiki/User_blog:Hyp_cos/General_fundamental_sequences_for_OCFs)). 不是结构规则: 按生成层数 L 取 α[n] = max{β<α | L(β) ≤ L(α)+n}, 与归档的范数基本列同类, 而且作者自己指出不够 "正则" (例子里 ω[n] 成倍增长). 对我们无新东西.

**5. Denis Maksudov, *FS for Hypcos's notation (with weakly inaccessibles cardinals) up to Ψ(M²)*** ([链接](https://googology.fandom.com/wiki/User_blog:Denis_Maksudov/FS_for_Hypcos%27s_notation_(with_weakly_inaccessibles_cardinals)_up_to_%CE%A8(M%5E2))). T_W 的博客原版. C 集闭包含 +、Ω_γ、I_γ、ψ_π; **标准形是语义的** ("若 α 可写成 …"), 不是递归谓词, 这一点 EBO 的 G 条件是强得多的. I 层规则的形状: ψ_{I_{ν+1}}(1) 与 ψ_{I_{ν+1}}(β+1) 都是 ω-序列, 下一项是对前一项取 Ω, 起点分别是 I_ν+1 与 ψ_{I_{ν+1}}(β)+1 (页面文本里 "Iν+1" 的上下标有歧义, 这里按 I₀ = 0 给出 ψ_{I₁}(1) = Λ 的读法); cof(β) = ρ ≥ π 时是我方规则 6 的同型. ψ_π(0) = 1.

**6. 其余.**
- Deedlit11, *Ordinal Notations V: Up to a weakly Mahlo cardinal*: 只教 OCF 定义与记号直观, 全文没有 "fundamental" 一词 (文本搜索), 对基本列无用.
- p進大好きbot, *Googological Open Problems on OCFs*: 把 "为社区 OCF 构造序数记号" 列为公开问题, 这样大数的可计算性才有保证. 另说明 PSS 的停机证明用了 Buchholz OCF, 而两边基本列差异造成繁重的保序论证; 这与我们层 4 的代价同类.
- *Full References of Arguments on Ordinal Notations with Large Cardinals*: 作者问社区分析者用什么公理, 答复多为无特定公理. 只读了开头.
- Paradajx 的对照文只是 FGH 步骤展开, 无新规则. C7X 的 *OCFs/Non Hyp cos-style*、*New Issue on Traditional Analyses*、*Ordinal Notation Associated to a Proper Class of Ordinals* 未读. **[更正 → §12.13]** 前一篇后来读了, 无基本列. *New Googological Ruler* 只读了结构, 无规则.

**对本报告结论的修正.**
- §9 的标尺建议**需要加限定**: M 层还有 *Rathjen-type* 这个带完整结构规则与实现的候选, 它保留 Rathjen 约束, 序的可计算性论证更严肃, 但不与 EBO 逐项对应, 强度与基本列正确性作者都不担保. Maksudov 系统作规则形状参照仍最贴近 EBO 的写法, 但它正是 *Rathjen-type* 作者批评的 "简化" 一类, 其序的正确性更可疑. 两者应对照使用, 不能单选其一当依据.
- §8 义务 1 现在有现成的 EBO 标准形谓词 (上文 1). 它只是声称, 仍要自证封闭性. **[更正 → §12.11]** 封闭性已有 Lean 证明可参照.
- 结论不变: 没有任何一套从 EBO 到 M 的带结构性基本列的系统有证明. **[更正 → §12.14 Q2]** 对全段仍真, 但易误读: EBO 段已机检, I 层有人工证明.


---

## 12. 全面补读

> 2026-11-02. 本节读取方式: GitHub 经 `gh` 只读 (未构建、未运行任何仓库代码), Fandom 经用户授权的 Chrome. 标记同前. "grep 无 sorry" 指我抓下该目录源码后的文本检索, 不等于我重放了 Lean 检查.

> **钉住的提交** (2026-11-02 默认分支头; 全表与许可证见[指南 §5](OrdinalNotationsGuide.md#5-机检索引)): koteitan/googology-lean `6da2de5`, koteitan/bms-rathjen `7bde9d7`, koteitan/pss-proof `d1be91f`, Naruyoko/googology `958ac91`, EgoFakeFantasy/BMS-Well-Ordering-Lean `3a4a945`, Phyrion1343/1Y-Well-Ordering-Lean `03d794f`, zball-bz/btbms-formalization `4f31c78`, coquand/agda-ordinal-analysis-id1 `1f977e0`, coquand/agda-mahlo-universe `199a725`, SteveWmoc/lean-ordinal-analysis `0aa3551`, takahashi-yt/czf-in-mahlo `b8aa846`, BedrockInstitute/QIITOrd `7def431`. 前三者的克隆是本节读的; 其余只读了 README 或文件树, 那时的头未记录, 这里的是事后取的.

### 12.1 头条: koteitan/googology-lean 已机检 EBO 的标准形封闭与良基性

[koteitan/googology-lean](https://github.com/koteitan/googology-lean) (Lean 4 + mathlib, 2026-11-02 仍在更新) 的 `Googology/Notation/ExBuchholz/` 形式化的正是 p進大好きbot 的 EBO 记号 (Ω₀ = 1, 项 `nil | cons a b t`, 无 φ, 与我方 `EBO.lagda.md` 同族) [原文, 读 README 与源码树]. **这改写了 §9、§11 "没有人证过" 的说法, 至少在 EBO 这一段.** README 声明为定理、无假设的项:

- `OTLt_wf`: 标准形上的序良基; 全部项上的序不良基 (`not_wellFounded_lt`).
- `OTFS_thm`: Buchholz Lemma 3.3 的 EBO 版, `z ∈ dom a → a[z] ∈ OT`, 经 3.4、3.5、3.6 (`Trian_fs_thm`) 和 `G` 上的 Bachmann 性质 (`bachmann`). **这正是 §8 义务 4.** 证明见 `Closure.lean` (87 KB).
- `fs_lt`, `fs_mono`, `exists_lt_fs_numeral` (共尾), `rank_exbOT_eq_val` (展开秩等于序数值).
- `val_lt_val`, `valEquiv`, `existsUnique_OT_of_lt_psi_Lam`: `val` 是标准形到 $C_0(\Lambda)$ 的序同构, 所以 p進大好きbot 只"声称"的同构在此成为定理.
- 我抓取 `ExBuchholz/` 与 `InaccPsi/` 的 31 个 `.lean` (13628 行) 文本 grep: 无 `sorry`, 无 `axiom`, 无 `admit` [测试]. 未构建.

**注意方向.** 它的良基性走的是语义路线: 在 mathlib `Ordinal` 上定义 ψ, 证 `val` 严格单调, 沿之拉回. 这依赖 ZFC 式基数算术 (`ℵ_v`), 不是构造性的, 不能直接搬到 Agda `--safe`. 但 3.3 的证明是句法的, 对我方层 3 的义务 4 可以逐条参照.

### 12.2 koteitan/googology-lean 的 InaccPsi 与 koteitan/bms-rathjen 的 T(M)

**`Googology/Notation/InaccPsi/`** [原文, 读 README; grep 见上]. Buchholz 1992 Def 4.2 (Pohlers §3.4.4) 的单不可达 ψ, 由 koteitan 与 Claude 推广到 ω 个弱不可达 $I_n$ 与 $I_\omega$. φ 为原语, $\Omega_0=0$, 不与 EBO 逐项对应. 已证: 正规形 `Term.NF` 的比较是严格良序 (`Term.isWellOrder_cmp`), 值保序, 且 `⋃_a Cl(a,0)` 每个元素恰有一个 NF (`Term.existsUnique_NF`). **无基本列**: 目录索引的 `Rewrite` 一栏写 "none". 语义路线, 依赖假设 `InaccSeq`, 所以不提供构造性良基性. 对我方: 这是 I 层第一个我见到的有 NF 完备性的机检系统, 也是 OT_I 之外的一个对照. 另一点要记: README 引 Wilken 称 ω 个弱不可达的 Skolem 壳记号覆盖 $R_2^+$ 的核, 这只是 Wilken 的声称, README 明说未证.

**[koteitan/bms-rathjen](https://github.com/koteitan/bms-rathjen)** [原文, 读 README、`lean/TM/FS.lean`、`lean/Evidence/WF.lean` 开头; 未构建]. Lean 4 无 mathlib, 形式化 Rathjen 1991 §2 的 $\mathfrak T(M)$: 项、序、标准形; `lean/TM/FS.lean` 给基本列, 明写 Rathjen 1991 没有基本列, 这是该仓库的设计选择. 规则形状: φ̄ 走标准 Veblen 列; ψ 的基底走 Γ-闭包; cof α = κ 或 M 时走 γ-链 ($t[n{+}1]=\psi_\kappa(\alpha[t[n]])$), cof α 是 κ 之上的正则 p 时经 ψ_p 下降. **注意: Rathjen 1991 把 χ 收成一元 $\alpha\mapsto\chi_\alpha(0)$, 所以 Ω₂ 没有项**, 与 *Rathjen-type* 和 Maksudov 的二元 χ 不同. 良基性: README 写该项目不要求整体良基, Γ₀ 以下已证; `WF.lean` (746 KB) 只服务证书递归, 处理向量计数. 表中 ✅ 是"行 = 该值"的证书, 整体假设良基. `plan/` 仍列未完成项 (`PsiIdxOKStd172`、`HiMono89`), 不是封闭结果. 对 M 层的结论: 有机检的项与序, 但基本列的递减与封闭在 M 处尚未证 (见其工作树).

### 12.3 Maksudov Mahlo 系统的博客文本: P1、P2a、P2b 的字面确认

[博客版](https://googology.fandom.com/wiki/User_blog:Denis_Maksudov/OCF_and_ordinal_notation_based_on_a_weakly_Mahlo_cardinal) 是 LaTeX 文本, 开头写明原文在作者站点. 由此核对 §3.4 的读图 [原文]: 序第 10.5 条第 3 款确是严格的 $\tilde\chi(a,b)\lhd c^\star$, 所以 **P1 不是读图错误, 是文本上的缺口**; 规则 20 确实不检查 $G$; 规则 18 的条件是 $M\lhd b$, 输出 $\omega^{b[x]}$ 未处理 $b[x]\unlhd M$; 第 11 节末尾注确实声称 $a[x]\in\mathcal T$. §9 末条 "P1 需要对照原图复核" 可以关闭一半: 字面已核, 正确性仍只来自语义判断. 博客版同样无证明, 附 FGH 与 $F(n)$、扩展箭头的定义.

### 12.4 评论区记录的已知缺陷 (经 Fandom 评论接口只读) [原文][社区]

**Maksudov 博客的评论.** p進大好きbot 指出两类问题: 用 ◃ 定义 T 而 ◃ 又限制在 T² 上, 造成循环 ($b\lhd\chi(a,b)$ 在已知 $\chi(a,b)\in T$ 之前就要算), Maksudov 回复已修; 其次是序规则是"部分指定", 情形不完备, 例如 $\chi(a,b)\lhd M$、$\chi(a,b)\lhd\psi_p(d)$ 没有完整规则, 他说"若 X 则 a◃b"不蕴含反面. Maksudov 加了 $a\lhd b\Rightarrow\neg(b\lhd a)$ 并自认未必够. 这与 §3.4 的 P1 同属一类 (我方测试独立发现的三歧缺口有社区先例). TrialPurpleCube 对 θ 的基本列提过意见, 与本系统无关.

**EBO 博客的评论.** C7X 问同构的证明梗概, p進大好きbot 给了五步语义梗概: $C_0(\text{OFP})$ 闭包、规范形唯一、$o$ 给规范形、$o$ 双射、$o$ 保序. 所以 "by the construction" 背后是这个梗概, 现在已由 koteitan 机检 (§12.1).

### 12.5 *Rathjen-type* 与 Naruyoko 的实现

**实现** [原文, 读 [`padicBotRathjen/implementation.js`](https://github.com/Naruyoko/googology/tree/main/padicBotRathjen) 的结构, 没有运行]. 2022-01 发布, 约 1800 行 JS. 完整实现了博客的项集 (`inT` 等)、`lessThan`、三角序 `triangleLessThan`、`inOT`、`dom`、`fund`、`gamma`、`linePhi`、`psiMinus` 和 FGH (`limitOrd`), 附一个回归测试函数 (对 `testTerms` 表逐对检验 `lessThan` 与 `inOT`). 没有证明, 也不是穷举. 页面的缩写表包括 $K_0=\varphi^3_0(0)$, 所以系统过 M 还到弱紧的类比符号.

**它解决了什么** [原文, 评论区约 47000 字符, 我只读了与缺陷相关的部分]. Naruyoko 在实现过程中向作者报告了 **24 个带编号的缺陷** (如 `031293` 展开出错并造成死循环, `79CBAE` 规则 2.4 恒假, `7F118A` φ 上 γ 数后继的展开非标准, `4559B6` 标准形判定与展开不相容, `C5BE66` 涉及 K 的序错误). 作者逐条修正, 有的是定义缺陷而不止笔误, 其中一次修正又引入新错 (作者自认). 结尾 Naruyoko 称暂未发现新问题, 作者将此记法命名为 "Naruyoko is the great" 以致谢, 实现页也写明记法大部分由他修正. **这回答了 §11 的问题: 博客的现行版本是实现驱动调试后的版本, 比 Maksudov 文本严肃得多, 但调试只是有限实验, 不是封闭性证明.** 这也说明这类规则集在未执行前缺陷密度很高, §3.4 对 Maksudov 的三处发现属于同样的现象, 仍可能未穷尽.

**实现与博客之间仍有不一致** [原文, 经 [koteitan/bms-rathjen](https://github.com/koteitan/bms-rathjen) 的 `lean/TM/FS.lean` 注记与 `table/findings.md`, 我未独立复现]. koteitan 的记录: 在 Γ-闭包的种子上实现与博客不同, `fund(Γ₀,·)` 为 $2,\zeta_0,\varphi_{\zeta_0}(0),\dots$, 博客表为 $\Gamma^0(0,1+1+\cdots)$ 且与其 Lean `fsN` 一致 (偏移一位); 51 个 ψ 区项上实现与其 `fsN` 只在 21 个上相同, 差异都在种子. Ω 层级上两者用 $\varphi^1$ 对 χ 的不同参数化, Rathjen 1991 的一元 χ 写不出 Ω₂. 反过来, koteitan 把这份实现当独立裁判, 证伪了自己翻译 `oR` 的一处值 (见 `findings.md` §134), 并发现其 `inOT` 在 62664 个项中通过 13181 个 [转述 koteitan]. 所以实现确实可用作反例搜索的工具, 也已被这样使用.

**Strength 段落的自述.** 作者说不知道序型, 只说若正确则超过 $\lim\psi_{\Omega_1}(\alpha)$, $\alpha\in M^\Gamma$. 分析表自 $\psi_{\Omega_1}(\chi_1(0))$ 起写 WIP, 并承认可能有错. "最强可计算记法" 见 §12.6.

### 12.6 p進大好きbot 的其余帖子

- ***Relation between an OCF and an Ordinal Notation*** ([链接](https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Relation_between_an_OCF_and_an_Ordinal_Notation)), 日文版 *OCFと順序数表記の関係*. 区分五个常被混淆的概念: OCF、序数记号、带序数对应的记号、带基本列的记号、序数的基本列系统. 我只读了前面与目录. 对我们的用处是术语: 我方 Agda 记号是"带基本列的记号", 要到"序数记号"还差良基性.
- ***New Issue on Traditional Analyses*** ([链接](https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/New_Issue_on_Traditional_Analyses)). 主张: 超过 $\psi_0(\Lambda)$ 就没有公认的递归基本列, 分析必须声明所用系统; 同一 OCF 没有典范基本列; 简化 OCF 通常失去比较算法. 他转述 Hyp cos 自认没有弱紧简化 OCF 的显式基本列算法. 这条与我方的立场一致: EBO 以上不存在"标准答案".
- ***New Googological Ruler*** ([链接](https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/New_Googological_Ruler)). 约定: 层 13–14 用 Buchholz, 15–16 用扩展 Buchholz, 17–20 用 Rathjen 弱 Mahlo 标准 OCF, 21 用 Rathjen 弱紧 OCF, 22–23 用 Stegert 的 $T(\Xi)$、$T(\Upsilon)$. 他说的计算性在 OCF 上指: 函数本身不可定义于 ZFC, 但所得 FGH 在 ZFC 里有意义.
- **"最强可计算记法"** 指 [*Ordinal Notation for a "Proof-Theoretic Analogue" of the PTO of ZFC*](https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Ordinal_Notation_for_a_%22Proof-Theoretic_Analogue%22_of_the_PTO_of_ZFC) 及其后继 [*Ordinal Notation with the PTO of ZFC*](https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Ordinal_Notation_with_the_PTO_of_ZFC) [我的判断, 由目录和开头; 帖子里的 "here" 链接目标未核]. 手法不是 ψ: 枚举形式理论内可证良序, 得到递归记号和典范基本列 (前一篇) 或可计算函数 (后一篇). 是对角化, 不提供 EBO 到 M 的规则. 与我方无关.
- ***Analysis of 非想非非想 notation*** ([链接](https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Analysis_of_%E9%9D%9E%E6%83%B3%E9%9D%9E%E9%9D%9E%E6%83%B3_notation)). *Rathjen-type* 的前身, 汉字拼写的项, 作者自己的 *List of My Googological Works* 说终止性是开放的, 分析无证明. 他另有桜花閃々记法 (弱 1-Mahlo 上的 Rathjen 式 OCF, 带记号), 同样不知精确强度 [社区].
- ***List of common misconceptions about Rathjen's psi*** ([链接](https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/List_of_common_misconceptions_about_Rathjen%27s_psi)). 澄清 χ 的定义域、χ 不等于二元 I、$\chi_\alpha$ 不是 α-弱不可达的枚举等. 我方写 χ 层时应当先过一遍 [未精读].
- ***Full References of Arguments on Ordinal Notations with Large Cardinals*** ([链接](https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Full_References_of_Arguments_on_Ordinal_Notations_with_Large_Cardinals)): 目的是列出 ZFC 下记号良定义所依赖的文献. 分析者的公理调查答复多为无特定公理; 末节说 UNOCF 只由有限例的展开规则确定, 其 Mahlo、弱紧层是否对应标准 OCF 未知. 中段文献我只翻了结构, 没有新规则. ***ペア数列の停止性*** 的机检版见 §12.9.
- 他引用的 ***How to Create a Recursive Notation*** 有一节专讲 "partial specialisation" 造成的情形不完备. 这是 §12.4 批评的出处, 是写规则时的好清单. 我没有读.

### 12.7 Maksudov 系统的日文重写: 独立印证 P1

KawamoYurase [*Denisの弱マーロψについて*](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:KawamoYurase/Denis%E3%81%AE%E5%BC%B1%E3%83%9E%E3%83%BC%E3%83%AD%CF%88%E3%81%AB%E3%81%A4%E3%81%84%E3%81%A6) (2023-11-16) [原文][社区] 按 p進大好きbot 的写法重写了 Maksudov 的系统: 符号 $N$ (M)、$X$ (χ)、$W$ (M 上的 $\omega^\cdot$)、$D$ (ψ), 记 $\partial_T$ 为 $r^\ominus$, $a\lhd_r c$ 为 $K_r$ 的三元版本, 带形成集 $T$ 与 OT, 规则逐条对应 Rathjen 1990 的 Lem 5.14、Def 7.1 等.

**与 §3.4 的比较** (作者称期望兼容, 无证明, 也未提 Maksudov 的笔误):
- **P1 在此已是 $\le$:** χ-χ 比较的第三支写作 "$c<a$ 且 ($X(a,b)<d$ 或 $X(a,b)\le c^\star$)". 这是对我方补丁 P1 的独立印证, 虽然作者没有声明这是修正. 第二支也用 $\le$ ($b\le X(c,d)$), 比 Maksudov 文本的 ◁ 更宽, 我没有测试.
- **P2b 部分处理:** $W$ 分支显式判断 $[b,n]=M$ 时不再包 $W$, 与补丁同向.
- **P2a 未处理:** $[X(b,c),n]:=X(b,[c,n])$ 不查 $G$.
- 序比 Maksudov 的完整: 所有组合都给了子句, 回应了 §12.4 的批评. dom 的值域是 $\{0,1,\omega,N\}\cup(T\cap RS)$, 处理规则 22 处作者写着大意是"应该避开了 bug"的注记, 也就是说他没有证明. $f$、$F$ 的定义也一并给出.

**对我方的作用**: 若继续用 Maksudov 系统作参照, 这个版本比原文更好. 我建议把 `mnot.py` 换到它上面再测一次, 这次没有做.

### 12.8 日文 Wiki 上的重要发现: みずどら 的 I 层系统带人工证明

みずどら [*到達不能基数を数え上げる崩壊関数*](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:%E3%81%BF%E3%81%9A%E3%81%A9%E3%82%89/%E5%88%B0%E9%81%94%E4%B8%8D%E8%83%BD%E5%9F%BA%E6%95%B0%E3%82%92%E6%95%B0%E3%81%88%E4%B8%8A%E3%81%92%E3%82%8B%E5%B4%A9%E5%A3%8A%E9%96%A2%E6%95%B0) (首版 2024-09-05, 正文约 13 万字符) [原文][社区; 未经同行评审; 我读了结构、定义和关键结论, 证明没有逐行检查]. 作者明确说目标是带"能工作的证明". 在 ZFC 加"存在基数 κ, 其下有 κ 个弱不可达"下工作, 取最小者 Λ:

- **函数.** Ω 枚举不可数基数, $I$ 枚举弱不可达或其极限, ψ_κ 按 κ 正则定义, $C_\kappa(\alpha)$ 闭于 $+,\Omega,I,\psi$. **没有 φ.** $\psi_{\Omega_0}(0)=1$, 所以 Ω₀ 是第一个不可数基数, 下标比 EBO 少 1. 强度与 $T_W$ 的极限 $\lambda$ 同级 [推断], 即 $\psi_{\Omega_0}(\Lambda)$ (命名 ekbo).
- **记号.** 项集 $T$, 递归序 ≺ (约 2.8 万字符, 按情形全写), 递归的 $\hat G_k(b)\lhd a$ 对应语义的 $G_\kappa(\beta)\lhd\alpha$, $OT$ 由它筛选. **所以这是 §3.1 "$T_W$ 的正规形只是语义条件" 这个局限的正面解决.** 形状就是 EBO 的 `G(X,Y)◃Z` 的直接推广.
- **文中证明了的:** $o$ 保序, 进而 $(OT,\prec)$ 良序; 为第 3 章的需要, 同型定理 $(OT,\prec)\cong(C_{\Omega_0}(\Lambda),<)$ (定理 2.3 及之后).
- **基本列.** `dom`、`a[b]` 结构性定义 (dom 分派 $\Omega_a$、$I_a$、$\psi_a(b)$; $\psi$ 分支与 EBO 同型). **引理 3.3: $b\prec\mathrm{dom}(a)$ 时 $a[b]\prec a$. 第 3 章最后证了封闭性: $a,b\in OT$, $b\prec\mathrm{dom}(a)$ ⇒ $a[b]\in OT$**, 并带 $\hat G_k$ 的不变量 ($\hat G_k(a)\lhd c\wedge\hat G_k(b)\lhd c\Rightarrow\hat G_k(a[b])\lhd c$). 作者明说 dom 与序数共尾度的一致性不证, 目标只是 OT 上的基本列系.
- **Bachmann 型性质、Hardy 正则性: 没有.** 另外 $F$ 走的是有界搜索 `expand(a,n)`$=\max\{s\in OT\cap U^n: s\prec a\}$, 不是用 $a[n]$ 跑的, 作者只把 $a[b]$ 用于封闭性那一章. 作者自注 ∂ 在 OT 外可能出问题.

这是我找到的**第一个到 I 层、带递归标准形、结构性基本列、并写出了封闭性证明**的系统, 又没有 φ, 比 Maksudov 和 *Rathjen-type* 都贴近 EBO. 它只有人工证明, 且未见第二人核查. 没有到 M.

**同一社区的其它系统** [原文, 只读概要][社区]:
- Kanrokoti *到達不能ψ関数* ([英文版](https://googology.fandom.com/wiki/User_blog:Kanrokoti/Inaccessible_%CF%88_function)): 直接扩展 p進大好きbot 的 EBO 记号, 项 $\psi_a(b)$, $I_a(b)$, $\psi_0(0)$ 从 Ω₀ = 1 起, **规则与 EBO 同构的程度最高**, 目标极限 $\psi_{\chi_0(0)}(\psi_{\chi_M(0)}(0))$ (TEBO) 只是"期望", 有 Naruyoko 计算器 (`kanrokotiInaccessiblePsi`). 目录有标准形一节 (被工具过滤, 未读), 未见封闭性证明; 解析表对照くまくま3変数ψ, 作者称"期望". "与 EBO 同构程度最高" 是我的判断 [推断].
- くまくまψ関数: 基于 EBO 但略去标准形定义, 所以 Wiki 明说它不是序数记号. Naruyoko 补过标准形判定程序.
- mrna 段階配列表記 与 降下段階配列表記 (Wiki 有定义): 前者 $\psi_0(\Omega_\omega)$, 用 k 置换, 不用 dom. 只见定义.
- Freighter-number: *弱コンパクトΨ関数* 与 [博客汇总](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC:Freighter-number/%E3%83%96%E3%83%AD%E3%82%B0%E8%A8%98%E4%BA%8B%E3%81%BE%E3%81%A8%E3%82%81), 自标 "◯ 定义了但终止性未证", 包括弱 Mahlo 到弱不可达的混合、弱紧崩塌, 汇总表用这样的符号评级, 是好的索引. 大部分没读.
- みずどら *Mahloメモ帳*: 记号直觉的笔记, 有用的 FNOCF ω-Mahlo 片段, 不是定型系统.

**みずどら 基本列的形状** [原文]. 记 $\partial(\kappa)$ 为前一位置. 主项 $\psi_{a_0}(a_1)$:

| $\mathrm{dom}(a_1)$ | $a_0$ | $a[b]$ |
|---|---|---|
| 0 | $\Omega$ 后继 | $\partial(a_0)\hat+a[\mathrm{pred}\,b]$, 基底 $\partial(a_0)$ |
| 0 | $I$ 后继 | $\Omega_{a[\mathrm{pred}\,b]}$, 基底 $\partial(b)\hat+1$ (原文如此, 可能指 $\partial(a_0)$) |
| 0 | $I_0$ | $\Omega_{a[\mathrm{pred}\,b]}$, 基底 0 |
| 1 | $\Omega$ 型 | $\psi_{a_0}(\mathrm{pred}\,a_1)\hat+a[\mathrm{pred}\,b]$ |
| 1 | $I$ 型 | $\Omega_{a[\mathrm{pred}\,b]}$, 基底 $\psi_{a_0}(\mathrm{pred}\,a_1)\hat+1$ |
| 极限 | $\mathrm{dom}<a_0$ | $\psi_{a_0}(a_1[b])$ |
| 极限 | $a_0\preccurlyeq\mathrm{dom}$ | γ-链: $\psi_{a_0}(a_1[\psi_{\mathrm{dom}(a_1)}(\Gamma)])$, 其中 $a[\mathrm{pred}\,b]=\psi_{a_0}(\Gamma)$ |

γ-链是 Γ 回取的形式, **这正是 EBO 第 6 条, 只是起点是 $\psi_{\mathrm{dom}}(0)$ 型而不是 $\Omega_\mu$**, 与 §4 的差异 A 相同. $I$ 型的 Ω-塔与 §3.1 $T_W$ 的 $[\eta+1]=\Omega_{\alpha[\eta]}$ 相同, 所以这本质上就是带标准形的 $T_W$. $\Omega_a$、$I_a$ 的下标极限走 $\Omega_{a_0[b]}$、$I_{a_0[b]}$.

### 12.9 机器检查一览 (补 §7)

§7 的表需要大改. 下表都是 [原文, 读 README 或源码; 未构建]; sorry/axiom 是我对浅克隆的文本 grep, 另外注明 [测试].

| 工作 | 系统 | 强度 | 结构性基本列 | 良基性 | sorry / axiom |
|---|---|---|---|---|---|
| **[koteitan/googology-lean](https://github.com/koteitan/googology-lean) `ExBuchholz`** | Lean 4 + mathlib | **$\psi_0(\Lambda)$, 正是 EBO** | **有, 且封闭 (`OTFS_thm`)、递减、单调、共尾** | **定理 (`OTLt_wf`), 语义路线** | 该目录无 [测试]; 全库 3000 个 lean 文件 (`Googology/` 下 2992 个) |
| 同上 `InaccPsi` | Lean 4 + mathlib | $\omega$ 个弱不可达, 带 φ | 无 | 序良序 (`isWellOrder_cmp`), 语义, 假设 `InaccSeq` | 该目录无 [测试] |
| 同上 `Trans/PoR/InaccPsi` | Lean + 纸面 | 探 Wilken 的 $R_2^+$ 声称 | 否 | 分层 | 该子树有 114 处 `axiom` 字样, 其余状态见其 README, 未细读 |
| [koteitan/bms-rathjen](https://github.com/koteitan/bms-rathjen) | Lean 4 无 mathlib | $\mathfrak T(M)$ 的项与序, 一元 χ | 有定义, M 处递减与封闭未证 | 仅 Γ₀ 以下 | 只有 `axioms_of.lean` 的自测 sorry [测试] |
| [koteitan/pss-proof](https://github.com/koteitan/pss-proof) | Isabelle、Lean | Buchholz 段 | 有 | Buc 2.2 自证; PSS 良基 | 少数未进依赖的 Isabelle 文件有 `sorry`, 编译期审计保证主定理不依赖; README 称主结果 sorry 零 |
| [zball-bz/btbms-formalization](https://github.com/zball-bz/btbms-formalization) | Lean 4 + mathlib | BTBMS, 与 ψ 无定量比较 | 自带展开 | **假设对每个 n 存在弱 n-Mahlo, 良序为定理** | README 称无 sorry, 4027 声明 |
| EgoFakeFantasy BMS、Phyrion 1-Y、koteitan 的 1y/wy-wo-por、bms-elem-pattern、dh-bms-wf-formal | Lean 4 | BMS / Y 系列 | 自带展开 | 良序定理 | Ego README 公理审计 `propext, Classical.choice, Quot.sound`; 代码检索未命中 Lean 内 sorry, 不是穷举 |
| [coquand/agda-ordinal-analysis-id1](https://github.com/coquand/agda-ordinal-analysis-id1) | Agda `--safe --without-K` | Veblen 到 Γ₀; ID₁ 的记号到 Bachmann–Howard (笔记) | README 未提 | 用于序数分析, 带比较 | README 称无公设 |
| [SteveWmoc/lean-ordinal-analysis](https://github.com/SteveWmoc/lean-ordinal-analysis) v0.3 | Lean 4 | ε₀ (到此), 通用 API | 有, 证共尾 | 嵌入 `Ordinal` | — |
| hydra-battles | Coq | ε₀ 完整; `Gamma0/*.v` 明标 draft | ε₀ 的 canonical 序列 + KS 机制 | ε₀ | 未 grep |
| Mathlib `ONote`, `cj-xu/OrdinalNotations` | Lean, Cubical Agda | ε₀ | §7 已列 | ε₀ | 主线库 |
| [choukh/agda-veblen](https://github.com/choukh/agda-veblen) | Agda | Veblen 树侧 | 不是记号 | — | 本用户旧仓库, 不算外部 |

**修正 §7 的结论.** "机检的 ψ 型记号带结构性基本列, 最高是 koteitan 的 Buchholz 段" 已过时: 最高是 **googology-lean 的 EBO**. 其基本列是定理级的, 到 EBO 为止. 我方 `EBO.lagda.md` 只是平级, 不高于它, 差别是我方 `--safe`、构造性, 他方经典、用 mathlib 序数. I 和 M 层仍没有带基本列封闭的机检工作. 我方 OT_I 良序 (构造性) 在强度上仍是最接近的机检对照, 这一点不变.

**规则 6 的来源问题** (§2.1). koteitan 的 [`lean/Buchholz-rel-ord/`](https://github.com/koteitan/pss-proof/tree/main/lean/Buchholz-rel-ord) 写明他们也没有原稿, 只按引文记录采用: 取 $x_0=D_u0$, $x_{i+1}=D_u(b[x_i])$, $(D_vb)[n]=D_v(b[x_n])$, 替换 Buchholz 1986 的 ([ ].4)(ii). 这确认 ([ ].4)(ii) 就是要被替换的那条, §2.1 猜 "([ ].5)(ii)" 是编号问题. 所以这条规则至今只有二手转录, 但有机检的 Lemma 3.3 为它背书.

### 12.10 David Exmachina: Rathjen 系统本身的基本列, 一路到弱紧和 Stegert

这是 §11 没提到的第三条 M 层线索, 我之前的清单只列了他的 UNOCF 帖 [原文][社区].

- [*How I Actually Came Up With The Fundamental Sequence Of Rathjen's Little ψ Function*](https://googology.fandom.com/wiki/User_blog:David_Exmachina/How_I_Actually_Came_Up_With_The_Fundamental_Sequence_Of_Rathjen%27s_Little_%CF%88_Function) (2024 起, 2026-04 改名 *Small ψ*). 对 **Rathjen 1990 的原系统**写出记号、序、规范形、共尾度、基本列, 符号是 $\varphi,\Phi,\chi,\psi,M$, 比较和规范形按论文定理逐条转写 ($a^*$, $C$-成员), **未做任何简化**. 基本列是作者设计的; 他明说基本列是经过测试的 JS 程序的副产品, 还可能有 bug, 最难的两行在 $\psi_{\chi_M(0)}(0)$ 与 $\psi_{\chi_{\psi_{\chi_M(0)}(0)}(0)}(0)$ 处 (M 共尾的 χ 下标). 他把 $\varphi$ 的受限看作避免 $M$ 被当作小序数的必要条件.
- [*I Finally Figured The FS Of Rathjen's CAPITAL Ψ*](https://googology.fandom.com/wiki/User_blog:David_Exmachina/I_Finally_Figured_The_Fundamental_Sequence_Of_Rathjen%27s_CAPITAL_%CE%A8_Function_Out!) 与 [*How My FS … Was BROKEN (And Then I Fixed It)*](https://googology.fandom.com/wiki/User_blog:David_Exmachina/How_My_Fundamental_Sequence_Of_Rathjen%27s_Capital_%CE%A8_Was_BROKEN_(And_Then_I_Fixed_It)): 弱紧的 $T(K)$ (Rathjen 1994). 作者说他没有找到前人的这种基本列. 版本一发布后用更好的检查法发现是错的: 验证手段是约 600 个测试序数加一个"能否从上方经 FS 搜到它"的搜索 (即共尾性的有限测试), 打破了原以为的正确. 序的部分他说严格按论文定理, 没有动.
- [*Stegert's OCF Part IV、V*](https://googology.fandom.com/wiki/User_blog:David_Exmachina/My_Recent_Progress_on_Stegert%27s_OCF_Part.IV_-_The_Fundamental_Sequence_of_Stegert%27s_First_%CE%A8_is_out!) (2026): Stegert 2010 的 Ψ 的基本列, 已到 $\Pi^2_0$-不可描述. 他声明严格照论文定义有不良行为, 所以给了"修正", 这是对 Stegert 的一处社区异议 [未核实].
- 实现: 网上程序 *Garden of Ordinals*, 可算共尾度、基本列、FGH, 还带比较 (`comp`) 与搜索. 我没有找到其源代码是否公开, 没有运行.

**这对 Q1 的影响.** 他的系统与 Rathjen 原文最贴近, 正确性判据是搜索测试, 不是证明. 以 φ、Φ 为原语, 所以与 EBO 不逐项对应, 与 *Rathjen-type* 同一路数, 只是不扩展.

### 12.11 对第 3 层路线 (§8) 的具体含义

读了 `ExBuchholz/{Std,FS,Closure,System}.lean` 的导入和定义 [原文; 未构建]:

- **3.3 的证明不碰序数.** `FS.lean` (1204 行) 与 `Closure.lean` (1833 行) 只依赖项、序、`G` 和 `Googology.Core`; `import Mathlib` 只在 `Ord`、`Ladder` 等语义文件里, `Core` 无 mathlib [测试, grep]. 所以 §8 义务 4 有一份约 3000 行的句法证明可照搬, 不必经 $\tau$. 是否用了经典逻辑要看 `#print axioms`, 我没跑. 移植到 `--safe` 时, 它的 `if` 依赖 `Term` 上可判定的序, 我方 `cmpᵀ` 同样可判定, 我预计问题不大 [推断].
- **规则相同** [推断, 逐支读 `dom`、`fs` 与 `EBO.lagda.md` 的 `cof`、γ-链比对, 未机器验证]: $\psi_{\text{后继}}(0)[Y]=Y$; 参数后继取 $\psi_{X_1}(X_2[0])\cdot n$; γ-链起点 $\psi_{Z[0]}(0)$, 即 $\Omega_\mu$; 回取 $\Gamma$ 后 $X_2[\psi_{Z[0]}(\Gamma)]$. 差别是他的 `fs` 对任意项是全函数, 非数下标给默认值, 我方用哑值分支. **这值得用翻译测试落实.** **[已落实 → 指南 §5.3]** 全部项大小 $\le 8$ 的转写测试, 无不一致; 差异只在定义域外.
- **两个已知陷阱** (其 README 记录, `test/ExBuchholzCheck.lean` 有见证项):
  1. Buchholz 的绝对不变量 $G_u(W_i)<X_2[W_i]$ 在下标是项时为假, 必须换成**相对于 $c$** 的界: $X[\psi_{Z[0]}(0)]\le c\le X\Rightarrow G_u(Z)\preceq G_u(c)\cup\{0\}$. 下标是序数项的 EBO 不能直接抄 Buchholz 1986.
  2. Bachmann 性质 $\forall x\in G_A(B),\ x<B[\psi_{Z[0]}(0)]$ 要带前缀做归纳 (`bach_pre`), 否则对 $\psi_\Omega(0)+\psi_1(\psi_\Omega(0))$ 型的项不成立. 证明靠大小论证 `no_small_between`, 形式上很轻.
- **$G$ 的定义**: `G a (cons c d t) = (if a ≤ c then d :: (G a c ++ G a d) else []) ++ G a t`. 它原来把下标 $c$ 一并收进, 比 p進大好きbot 的强; 校正后所有定理无改动通过. 我方若写谓词, 取校正后的版本.
- **良基性不能抄**: `OTLt_wf` 走 `Ordinal` 上的 ψ, 需要 ZFC 式的 $\aleph_v$. 我方 `--safe` 仍要 §8 的 $\tau$ 嵌入 OT_I (义务 2、3、5). 但其语义版本让 $\tau$ 不再是唯一证据: EBO 良基性本身已无悬念, 所以 §8 只剩 "能否构造地得到" 这一问.
- **对 FGH 与层 4**: `rank_exbOT_eq_val` 与共尾定理说明基本列确实走满 $\psi_0(\Lambda)$, 这正是我方层 3 之外缺的语义校准, 可当验收依据.

### 12.12 类型论方面的先例

[原文 = 我读了 README 或 PDF 相关小节; 转述 = 只见摘要.]

- **Kovács, *Generalized Universe Hierarchies and First-Class Universe Levels*** (CSL 2022, [arXiv:2103.00223](https://arxiv.org/abs/2103.00223)) [原文, 读 §4–§5 片段]. 层级来自任意带传递良基关系的集合. Def 13 的 `UIR/ElIR` 以 `i : Lvl` 与 `f : (j : Lvl) → j < i → Set` 为参数, 用 IR 定义代码, 本质上是 McBride 的无冗余层级 (层号从 ℕ 推广). 他特别提到超宇宙、Mahlo 宇宙足以建模超限层级, 但不易支持严格的 Lift 保持. 脚注称三歧且外延的层级结构就是类型论序数. **但这里 `Lvl` 是外部给定的**; 一等层级只是把外部结构内化 (例子是 ℕ). **我方树侧 `Lv` (裸的 IR 宇宙, `limᴼ k g` 不带证据, `toLv` 总函数, `Ordᴸ` 与 Level 同形) 的方向相反**: 层号由树族自身生成, 良基性证书 (`WF`) 甚至不成立 (`¬WF-L₁`), 所以判决 `D` 是外部的. 这是我找到的**最相近**的先例, 但不是同一件事. 本仓库 `archive/probes/OCF/Kovacs/` 已沿这条线试过多互递 IR, 所以它已是项目语境的一部分.
- **Takahashi, *Interpretation of Inaccessible Sets in MLTT with One Mahlo Universe*** ([arXiv:2402.15074](https://arxiv.org/abs/2402.15074); [Agda](https://github.com/takahashi-yt/czf-in-mahlo)) [原文, README]. CZF 加各超限阶不可达集, 解释进带 Mahlo 宇宙和 `Acc` 的 MLTT. `ExternalMahlo.agda` 用 IR 定义外部 Mahlo 宇宙, `TypeHierarchy.agda` 沿 `Acc` 迭代高阶宇宙算子. **层级沿可及性而非沿记号走**, 与我方 Mahlo 归档的思路同类.
- **[coquand/agda-mahlo-universe](https://github.com/coquand/agda-mahlo-universe)** (2026-10, 199 模块约 47000 行, `--safe --without-K`) [原文, README 摘要]: Setzer Mahlo 宇宙的元理论 (Russell 式; 主语化简; 依赖不动点的规范化与可判定类型检查). README 未提序数. 这是一个强有力的类型论方基础, 但与记号无接触. [coquand/agda-ordinal-analysis-id1](https://github.com/coquand/agda-ordinal-analysis-id1): ID₁ 的序数分析, Veblen 记号与 Bachmann–Howard 笔记, 同一作者同时活跃于这两条线.
- **Dybjer–Setzer, *The extended predicative Mahlo universe in MLTT*** (JLC 34(6), 2024) [转述]: 模型在 Agda 里类型检查, 用超出 IIRD 的索引 IR. SOURCES.md 已有相关材料.
- **Rathjen–Griffor–Palmgren 1998 (APAL 94)** [转述, 经 Takahashi]: CZFπ 上界由二阶宇宙算子的 MLQ 给出. Setzer、Palmgren 的 Mahlo/超宇宙文章见 SOURCES.md, 本次未重读.
- **[BedrockInstitute/QIITOrd](https://github.com/BedrockInstitute/QIITOrd)** (2026): Kraus–Nordvall Forsberg–Xu 的 Brouwer 树 QIIT 的重构, 用计算的序定义解决原先的 TERMINATING 问题, Cubical Agda, literate. 未超过 Brouwer 树本身的表达, 不到 I. 可看它的序定义如何过终止检查 [推断].

**小结.** 我没找到把"层号类型本身作为裸 IR 宇宙、在其上建树族并与序数记号比对"的先前工作. 这是"我没找到", 检索范围见本节, Setzer 的原文只有 SOURCES.md 已读部分. 另一方面, Kovács 与 Takahashi 都**外给**良基结构, 这与我方 `Barrier` 与 `¬WF-L₁` 指出的代价一致 [推断].

### 12.13 其余已读与未取得

**读过, 对规则无用** [原文]: Deedlit11 *Ordinal Notations IV*、*VI* (全文无 "fundamental", 只讲定义与多 Mahlo、弱紧的直观); C7X *OCFs* 与 *OCFs/Non Hyp cos-style* (反射编码的 OCF, 作者自注实验性, 无基本列); C7X *Drafts* (目录含 I、M 的 OCF 小节, 基本列只在 Ω 层出现; 未全读); C7X *OCFs/Ordinal notations* 只确认存在 (读取被工具过滤); Scorcher007 (作者自述不是良序, 只是强度记号, 无基本列); Hyp cos *Attempt of OCF up to Stability*、*Degrees of Recursive Inaccessibility* (只看了长度, 未读); Nayuta Ito *An attempt to well-define OCF as a number notation* (作者明说不是 OCF, 是数记号, 未深入); Syst3ms *A formal definition for UNOCF* (未读); Rgetar 的 Ordinal Explorer 系列 (字符串展开, 非 ψ 记号, 其解释帖列有已知问题); Fandom 词条 *Fundamental sequence*、*Extended Buchholz's function*、*Buchholz's function*、*Rathjen's psi function*: 与 §1、§5 所述一致; EBO 词条的 "EBO in Japanese Googology" 回答了 §2.2 的命名问题.

**未取得或未读全** (见 §10 表的更新):
- Miraheze 的页面: 显示等待/校验页, 未试图通过, 跳过.
- Cantor's Attic 的 *Ordinal collapsing function*: 404. Fandom 上 Hyp cos *OCF vs Array Notation*、Rgetar *Ordinal Explorer* 的这两个标题不存在 (Rgetar 有其它标题的同系列帖). PsiCubed2 的 "OCF for PSS" 未能定位.
- 部分切片被浏览器工具的 "Cookie/query string" 过滤拦下 (Kanrokoti 标准形节、みずどら 一处、C7X notations、KawamoYurase 由 `get_page_text` 读全), 所以 Kanrokoti 的标准形节未读.
- ペア数列の停止性 可读 (约 34 万字符), 只取结构; 其机检版见 §12.9.

### 12.14 五个问题的回答

**Q1. 除 Maksudov 与 *Rathjen-type* 外, 还有别的 EBO 到 M 的结构性基本列系统吗?** 有. 按严格程度 (都没有覆盖整段的证明):

| 系统 | 到达 | 严格程度 | 与 EBO 的贴合度 |
|---|---|---|---|
| *Rathjen-type* + Naruyoko 实现 | 过 M, 有 K 符号 | 实现驱动, 24 个缺陷已修; 无证明; 作者不担保 | 低, φ 原语 |
| David Exmachina *Rathjen Small ψ* + Garden of Ordinals (§12.10) | M, 另有 $T(K)$、Stegert | 序照原论文定理; 基本列是设计的, 经测试与搜索; 曾自曝错误后修复 | 低, φ、Φ 原语, 原系统 |
| koteitan `bms-rathjen` $\mathfrak T(M)$ (§12.2) | M 内 | 项、序、标准形在 Lean; 基本列定义在 Lean, M 处性质未证; 一元 χ | 低, 且缺 Ω₂ |
| Maksudov + KawamoYurase 重写 (§12.7) | 过 M | 无实现测试 (除 §3.4 我方的); P1 等已知; 序经重写后更完整 | **高**, 无 φ, 主项 ψ、χ |
| p進大好きbot 桜花閃々 (弱 1-Mahlo) | M₁ | 无证明, 作者不知强度 | 低 |

M 以下但走到 I 层的另两个更好: **みずどら** 带人工证明 (§12.8), Kanrokoti 的 EBO 直系 (期望值 TEBO, 低于 M). 所以最严格的是 *Rathjen-type*/Exmachina, 最贴合的是 Maksudov/KawamoYurase, 两者仍不重合.

**Q2. 有人证过或机检过 EBO 及以上的良基性或标准形封闭吗?** **有, 这是本次最大的发现.** EBO 段: koteitan/googology-lean **机检了良基性 (语义) 与基本列封闭 (句法), 含 $G$ 封闭的 ⊲ 关系 (Buchholz 3.4–3.6) 与 Bachmann 性质, 外加共尾、秩等于序数值、满射到 $C_0(\Lambda)$** (§12.1, §12.11). 这正是 `G(X,Y)◃Z` 封闭, 无条件. I 层: みずどら 有**人工证明** (2024, 未核查) 的 $\hat G$ 封闭与序同构; `InaccPsi` 有 Lean 的良序但无基本列. M 层: 没有. BTBMS 在假设 n-Mahlo 下有 Lean 良序, 但那是 BMS 类, 与 ψ 不对接. **§9、§11 结论里 "没有人证过" 须按此修正** (仅到 EBO, I 层部分).

**Q3. Naruyoko 的代码解决了什么?** 没解决证明问题, 解决了实证问题: 它驱动作者修掉 24 个缺陷 (§12.5), 后来又成为 koteitan 验证 $\mathfrak T(M)$ 的外部裁判. 与博客仍有不一致 (Γ₀ 种子处, 51 项仅 21 项相同). 其它已报缺陷: Maksudov 的序不完备 (p進大好きbot 评论) 与 P1、P2 (§3.4, §12.3); Exmachina 的 $\Psi$ 基本列; 他声称的 Stegert 定义瑕疵; p進大好きbot 的 EBO $G$ 无错, 只是 koteitan 自己一度写强了; pss-proof 的 `corrections/` 里有机检的路线反例 (Red²、Mark/NextAdm), 那是关于 PSS 证明路线的.

**Q4. ψ_I、χ、M 的规则形状最佳来源, 标尺要不要改?** ψ_I: **みずどら 的表 (§12.8)**, 带递归标准形, 比 $T_W$ 好; Kanrokoti 作 EBO 式写法的对照. χ 与 M: **KawamoYurase 重写 (§12.7) 优先于 Maksudov 原文**, 规则 13–15 的形状不变; Exmachina 的第 07.04.04 节与 *Rathjen-type* 作交叉检验. **建议改标尺**: EBO 段以 `ExBuchholz` 为校准 (已机检); §9 第 1 阶段从 "$T_W$ 取 $I_1$" 改成 "みずどら 取 $I_0$ 段, 加 §4 的 A、B、C", 但 A、B、C 能否照搬未测试 [推断]; 第 2、3 阶段用 KawamoYurase 版并重跑 `mnot.py`. 这是建议, 没有做测试.

**Q5. 类型论方面有无类似我方树侧 I 层的先例?** 最近的是 Kovács 2022 的 IR 层级 (§12.12), 但层级结构是外给的, 良基证据在外; Takahashi 沿 `Acc` 迭代. 没有找到"层号就是裸 IR 宇宙"的工作. Coquand 的 Mahlo 宇宙元理论 (2026-10) 是强力的新基础, 但不涉及序数.

**结论的修正.** 文首 "存在, 但只在社区层面, 没有证明" 对 M 仍然成立. 对 EBO 段不成立: 已有机检. §7 的 "最高" 一行、§9 的标尺与缺口表都已在本节更新. 我方相对优势在 `--safe` 与树侧, 而不是在 EBO 记号本身.
