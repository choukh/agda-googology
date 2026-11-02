# 从 EBO 经 I 到 M 的序数记号与基本列: 文献调研

> 调研日期 2026-11-02. 对象: 能从 EBO 一路走到 Mahlo 的序数记号, 以及定义在其上的基本列.
> 来源标记: **[原文]** 我读了一手来源 (论文、作者页、代码仓库); **[本项目已核]** `archive/src/Mahlo/SOURCES.md` 已读过, 此处不重复; **[推断]** 我自己的推理; **[测试]** 我的脚本在有限样本上的结果, 不是证明; **[转述]** 只见二手来源或搜索摘要; **[社区]** 未经同行评审.
> 读图转写的地方单独说明. 图中公式我是逐条读的, 但没有第二人复核.

## 结论

**存在, 但只在社区层面, 没有证明.** Denis Maksudov 的页面 *OCF and ordinal notation based on a weakly Mahlo cardinal* 给出了递归项集、递归序、以及逐条的结构性基本列, 从 0 开始, 经 EBO、不可达层级, 过 M, 到 $\psi_{\chi(0,0)}(\chi(\varepsilon_{M+1},0))$ 为止. M 处的分派写得很明确 (见 §3.3). 这正是用户要找的形状. 页面没有任何证明, 也没有人核查过的记录 [原文].

**正式文献到不了.** 有证明的结构性基本列, 我找到的最高点是 Wilken 在 $\Pi^1_1\text{-CA}_0$ 强度上的系统, 带 Bachmann 性质 [转述, 读了摘要与章节结构]. 它低于 EBO. 在 M 处, 正式文献里只有 Buchholz–Cichon–Weiermann 1994 的范数定义 $\alpha[x]=\max\{\beta<\alpha: N\beta\le\dots\}$ [本项目已核], 那是有界搜索, 不是结构规则. Rathjen 1990、1991 与 Setzer 的 OT_I、OT_M 都没有基本列. Takaki 2005 明说 $\mathcal T(M)$ 上的典范基本列还在建立之中 [原文]. 这是"我没找到", 不是"不存在": 德语文献 (Pfeiffer 1992、Wemheuer 1994、Buchholz 1990 草稿) 没有取得.

**本次的三个新事实.**

1. **Maksudov 的 Mahlo 系统字面上有缺陷, 小补丁可修.** 我把它独立转写成脚本测试. 字面版在三处出错: 序的第 10.5.3 条有等号缺口, 造成三歧失败; 规则 20、规则 18 的输出可以落在项集之外. 打三个小补丁后, 6000 个主项、35931 步展开全部通过 (输出在项集内、严格递减、ω 型单调), 所有分支都走到 [测试]. 这不是良基性证明.
2. **它不是 EBO 基本列的保守扩张.** EBO 的项可以保序地嵌进去 (3000 项, 40000 对比较无一例不一致 [测试]), 但基本列只有 64% 逐项相同. 差异集中在小下标, 共三类 (§4). 我认为可以修补, 但修补后的系统没人写过.
3. **"EBO 到 OT_I 的序嵌入"这条第 3 层路线看起来是通的.** 映射只有三行, 像是纯字典序的. 3000 项、8978 步展开无一例离开 OT, 60000 对比较无一例不一致 [测试]. 见 §8.

**首要缺口.** `googology.fandom.com` 对抓取一律返回 HTTP 402. 我没有绕过它, 因此 Hyp cos、p進大好きbot、Deedlit、C7X 的博客全文都没有读到, 只有搜索摘要. 其中可能有比 Maksudov 更好的东西, 尤其是 p進大好きbot 的 *Rathjen-type Ordinal Notation*. 清单见 §10.

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

---

## 1. 正确性判据

**Bachmann 性质与正则性.** BCW 1994 的 (B1)–(B6)、Lemma 1、Theorem 4 已由 SOURCES.md §82 核过, 我方 `Bachmann.lagda.md` 还机检了其中一段, 这里不重复. 要点是: Cichon 式的范数基本列在相对界下自动给出 Bachmann 系统, 绝对界则不行. Rathjen 在 *The Realm of Ordinal Analysis* 里说得很直接: 只有考虑序数代数性质的"自然"指派, 得到的层级才可用于组合独立性结果 [原文].

**没有"唯一正确"的基本列.** 我读到的文献都把正确性当作一组可验证的性质, 而不是一个唯一答案 [推断]. 对结构性规则, 实际要证的是四件事: 输出仍是规范项; $a[x]<a$; 递增且共尾; Bachmann 性质或正则性. Buchholz 1986 的 Lemma 3.2、3.3 证了前两件的原型 [原文]. Wilken 证了第四件 [转述]. 到 EBO 以上, 这四件都没有人证过.

**对 M 的特殊要求.** 这一点放在 §3.3 结合规则讲.

## 2. EBO 这一段

### 2.1 Buchholz 1986

§3 的 $\mathrm{dom}(a)$ 与 $a[z]$ 就是我方规则的祖先 [原文, 读图, 印刷页 203–204]: $\mathrm{dom}(D_{u+1}0)=T_u$ 且 $(D_{u+1}0)[z]=z$; $(D_\omega 0)[n]=D_{n+1}0$; 参数后继给 $(D_v b[0])\cdot(n+1)$; 参数共尾度低于或等于当前层时 $a[z]=D_v b[z]$; 否则走 $D_u$ 迭代. Lemma 3.2 给 $a[z]<a$ 与单调性, Lemma 3.3 给 $a[z]\in OT$. 这一节的目的是证 $\mathrm{PRWO}(\psi_0\varepsilon_{\Omega_v+1})$ 的不可证性, 用到 Buchholz 的另一篇文章.

**存疑.** ([ ].4)(ii) 我放大读到的是 $a[n]:=D_v b[D_u b[1]]$. 如此读法右边不依赖 $n$, 不可能是对的基本列, 所以要么是扫描问题, 要么印刷有误 [推断]. 社区页面说扩展版把这条规则改成了 Buchholz 另一篇 *Relating ordinals to proofs in a perspicuous way* 第 6 页的规则 6, 但编号写作 ([ ].5)(ii), 与我读到的不合 [社区]. 我没能打开那篇原文 (链接 404).

**与我方的差异**: 下标只到 $\omega$; $\omega[n]=n+1$ 而我方 $\omega[n]=n$; 后继参数乘 $n+1$ 而我方乘 $n$; 不可数共尾的迭代写法不同. $\Omega_0=1$ 与我方相同.

### 2.2 谁造了 EBO

函数与基本列是 Maksudov 的, 页面写明基本列定义于 2017 年 4 月, 记号定义于 2020 年 7 月, 并引用 Deedlit 的帖子和 p進大好きbot 的记号 [原文]. Wiki 说递归比较与基本列的显式算法出自 p進大好きbot, 并有 koteitan 的计算器 [社区]. "EBO" 这个词的出处我没查到: Maksudov 页面不用这个名字, 我见到的最早用法是 kanrokoti 的博客标题里的 "EBOCF" [社区]. 另有未证的期望: Extended Weak Buchholz (不取加法闭包) 与它极限相同, 尚未证明 [社区].

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

**局限.** 正规形写作语义条件 (如 $\gamma\in C(\gamma,\psi_\pi(\gamma))$), 不是递归判定 [原文]. Wiki 的 WNF 第 1 条写的是 $P_B$, 疑为 $P_W$ 笔误. 这些段落都没有证明.

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

页面第 11 节末尾的注记声称 $a[x]\in\mathcal T$, 字面上因此不成立. P2a、P2b 都不改序数值, 只是规范化. P1 是序的修正, 我由语义判断 $\chi(c,d)>c^\star$, 所以应取等号 [推断]. P1 也可能是作者笔误而非我的误读, 请对照原图.

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

我的搜索范围内, 机检的 ψ 型记号带结构性基本列, 最高是 koteitan 的 Buchholz 段 (若其 README 属实). 我方 EBO 的定义已高于它, OT_I 的良序也高于它. Isabelle AFP 与 Kovács 的工作本次没有重新检索.

## 8. 对第 3 层路线的影响: EBO 嵌入 OT_I

**映射** [推断 + 测试]:

$$\tau(\mathbf 1)=\varphi'_0 0,\qquad \tau(\psi_u(0))=\Omega'_{\tau u}\ (u\ne 0),\qquad \tau(\psi_u(a))=\psi_{\Omega'_{\tau u+1}}(\tau a)\ (a\ne 0),$$

和逐项映射. 这不保值, 只保序. 第 3 层只需要序.

**为什么它是字典序的** [推断]. 像集里没有 $\psi_I$、$I$, φ 只有 $\varphi'_0 0$. 按 `Order.lagda.md` 的子句, 比较只会用到 (≺′1)(≺′2) 的和的字典序、(≺′5) 的 $\psi$ 对 $\psi$ 先比层再比参数、(≺′6) 的 $\psi_\pi b\prec\kappa\iff\pi\preceq\kappa$、(≺′9) 的 $\Omega'$ 对 $\Omega'$, 以及 φ′₀0 落到最底的 (≺′11). 这与 EBO 的 `_<ᵀ_` (§2) 完全同构. (OT5) 只要求参数非 0、不在 Fi′, 像集自动满足. (OT4) 的 $G_\pi$ 在像集上就是 Buchholz 的 $G_u$ 加上层的部分.

**测试** [测试]. 我把 `Order`、`Closure` 里相关子句转写成 Python.

- 22 个 EBO 种子中 6 个的像不在 OT, 全是 $\psi_0(\psi_1(\Omega_2))$ 这种非 Buchholz 标准形 (此处 $\Omega_2\not<\psi_1(\Omega_2)$), OT 拒绝它们是对的.
- 从其余 16 个种子对 EBO 规则取闭包: 3000 项、8978 步, **无一步离开 OT**, 也即"标准形对展开封闭"在样本上成立.
- 60000 对比较, EBO 字典序与 $\prec'$ **无一例不一致**. 所有 $t[n]$ 的像都在 $t$ 的像之下.

缺陷: 这里"标准形"正是用 OT 条件筛的, 不是独立写的 EBO 标准形谓词; 也没有在 Agda 里跑.

**要做的义务.**

1. 在 EBO 上写标准形谓词 (Buchholz 的 $G_u(a)<a$, 带层).
2. $\tau$ 严格保序 (对项大小归纳, 预计是几十行的字典序论证).
3. $\tau$ 保标准形, 核心是 $G_{\Omega'_{\tau u+1}}(\tau a)$ 与 $\tau(G_u(a))$ 的对应. 注意 (G5) 无条件地把 $\Omega'_c$ 降到 $c$, 而 (G4) 多了层上的 $G_\pi(c)$, 这里要小心比较.
4. 标准形对 `fsn↓` 封闭 (Buchholz Lemma 3.3 的 EBO 版). 这条不依赖 $\tau$, 也是最费力的一条, 它决定 FGH 能否只在标准形上跑.
5. $\tau t\prec\psi_{\Omega'_1}(\Omega'_{I+n})$, 由 (≺′5)(≺′6)(≺′10) 得到.

然后 `archive/src/Mahlo/Inacc/Theorem.lagda.md` 的 `wellfounded : ∀ n {y} → OT y → y ≺ endpt n → Acc y` 沿 $\tau$ 拉回, 给出 EBO 标准形的 Acc, FGH 就不再依赖燃料或假设.

**边界.** 对 I 层 (不只是 EBO) 的嵌入要处理 $\psi_I$: Setzer 的 $\psi_I 0$ 已是 Ω-不动点, 而 $T_W$ 的 $\psi_I(0)=1$、$\psi_I(1)=\Lambda$, 下标差一 [推断], 也未测试. Setzer 只有一个 $I$, 而 $T_W$ 有 $I_\nu$, 只有 $I$ 的片段才可能嵌入. 这条路不提供基本列: OT_I 自身仍只有范数搜索.

## 9. 建议的标尺与开放缺口

**标尺建议** [判断]: 以 **Maksudov Mahlo 系统 (带 P1、P2a、P2b)** 作为规则形状的参照, 不作为正确性的依据. 底层保留 `EBO.lagda.md` 不动, 按 §4 的三类差异改写其下层. 分阶段:

1. **I 片段.** $T_W$ 只取 $I_1$, 加 A、B、C 修正, 成为 EBO 的保守扩张. 这一段新增的规则很少 (§3.1), 与 EBO 的对应已由测试支持, 良基性可以走嵌入 OT_I.
2. **χ 层.** 引入 $\chi(b,c)$ 与 $\mathrm{tp}(b)\in\{1,\omega\text{ 型}\}$ 的分派.
3. **M 层.** 加规则 13–15 与 $\tilde\omega$. 良基性只能指向 OT_M 或 $T(M)$, 这些只有纸面证明, 我方未机检.

Wilken 的结构可作为 Bachmann 性质证明的模板. BCW 的范数基本列留作 M 层的对照, 可用来测试结构规则是否被其支配.

**开放缺口.**

- 没有人证过 Maksudov 系统的任何一条: 项封闭、递减、$(\mathcal T,\lhd)\cong(T,<)$、$K_r$ 的等价. 我的测试只覆盖小样本.
- Maksudov 对 Rathjen 函数的简化是否与原系统序同构, 未知. 即便规则自洽, $\mathcal T$ 的序型也未被核实.
- 修补后的"逐项扩张 EBO"的版本尚不存在 (§4 末).
- 结构性 M 规则与 BCW 范数基本列的关系, 没有任何比较结果.
- P1 需要对照原图复核, 也可与 Rathjen 的序或 Setzer Def 3.3 比较后确认.

## 10. 没能取得或未读

| 材料 | 情况 |
|---|---|
| Fandom 上的 Hyp cos *General fundamental sequences for OCFs*、*OCF vs Array Notation*, p進大好きbot *Cheatsheet on Properties of OCFs*、*New Googological Ruler*、*Rathjen-type Ordinal Notation*、*Ordinal Notation Associated to Extended Buchholz's OCF*、*ペア数列の停止性*, Deedlit11 *Ordinal Notations V/VI*, C7X *OCFs*, Maksudov 博客版 | HTTP 402, 未绕过. 只有搜索摘要, 其中两句有用: Cheatsheet 称 Rathjen 弱 Mahlo ψ 某处以上的"分析"并非基于真实算法因而不可复现; *Rathjen-type* 的作者注称其强度未知. 如用户手动保存这些页面, 可以补读. Miraheze 上这些博客 404 |
| Buchholz 1990 草稿 | 只有书目 |
| Buchholz 2003 *Ordinal notations and fundamental sequences*、*Relating ordinals to proofs*、2015 综述 | 主页链接 404, 未在别处取得. koteitan 的 `lean/Buchholz-rel-ord` 有规则 6 的转写, 未细读 |
| Buchholz 1986 ([ ].4)(ii) | 已读, 但一处读法存疑 (§2.1) |
| Rathjen 1994 (AML 33, KPM 良序证明) | 未读 |
| Pfeiffer 1992 (MLQ 38, DOI 10.1002/malq.19920380142)、Wemheuer 1994 (Hannover) | 只见书目与摘要片段. Pfeiffer 明确建在 Mahlo 数之上, 是否带基本列不明 |
| Jäger 1984、Schütte 的 Klammersymbole、Duchhardt、Stegert、Weiermann、Carlson、Arai O(μ)、Grimm | 未读 |
| 日文 Wiki 上 mrna 的「降下段階配列表記」「多変数段階配列表記」、kanrokoti 的 KumaKuma ψ | 只见英文 Wiki 转述; 强度声称未核 |

**测试脚本** 已存入 `probes/Survey/scripts/`: `cmp.py` (EBO 对 $T_W$), `mnot.py` (Maksudov Mahlo 系统, 含补丁开关), `emb.py` (EBO 对 OT_I 与 Mahlo 系统的序嵌入, 须在该目录下运行). 这些是有限样本测试, 不是证明.
