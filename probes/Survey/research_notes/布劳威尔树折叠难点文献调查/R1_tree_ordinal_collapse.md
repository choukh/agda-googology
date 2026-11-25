# R1 树序数上的折叠与子递归层级: 针对难点 1–3 的文献调查

档位说明: "原文已读" = 本轮看过原文页面 (给页码); "只见摘要/目录" = 只读了摘要、目录或出版页; "二手" = 只见检索摘要或他人转述; "未核" = 没有取得. 推断一律放在各节 Inferences, 是判断, 不是定理. 难点编号沿用简报: 1 = 不可判定的分派, 2 = 值语义与非规范树, 3 = 阶段无关的下界证明.

与本地手册的重合 (查过 `OrdinalNotationsGuide.md`, `CodeGuide.md`): BCW 的 (B2) Bachmann 性质与范数基本列 (手册 §2), Buchholz 1987 的 $W_u$ (手册 §6.1 末, CodeGuide §1(g)), Buchholz 的 `([ ].4)(ii)` 规则 (手册 §4.4 与 §7, 记作 "Buchholz 1986"), Wilken 2024 (手册 §2), Weiermann (手册 §7 "未读") 都已出现. **不在两份手册里的**: Buchholz 1987 §1 的树类 $\mathcal T_v$ 与树上折叠 $\mathcal D_v$; Schwichtenberg 1993 的树上折叠 $D_\sigma$ 与 $<_k$; Fairtlough 1992 (Wainer 的学生) 的 structured 树, 多层下标向量与范畴语义; Buchholz 的 $\ll_k$ (Schmidt step-down 关系的推广); Kraus–Nordvall Forsberg–Xu 的可判定性表; Freund 的带 support 的折叠. Eremondi 的 SMB 树不在 Survey, 但仓库 `archive/probes/OCF/Ord1D/` 下有 SMB 的旧探针记录.

## 问题一: 树序数上的折叠怎样定义, 按层分派怎样做, 是否比较无穷分支

### Takeaway
本轮读到原文的三处树上折叠 (Buchholz 1987, Schwichtenberg 1993, Fairtlough 1992 的树类) 都按**结点自带的字面分支类标签** (分支域 $I=\mathcal T_u$, $u\in\mathbb N$) 分派, 比较的是自然数 $u$ 与目标 $v$, **从不比较分支**. "同层" 与 "高于目标" 在 Schwichtenberg 的写法里是同一条规则: 用**结点自身层**的折叠 $D_\mu$ 从 $\Omega_\mu$ 起走链. 层号是树时, 这个分派落在不可判定处, 文献没有处理这种情形.

### Cited Findings
- **Buchholz 1987, §1 (原文已读, pp. 133–134).** 树类 $\mathcal T_v$ ($v\le\omega$): $\mathcal T_v$ 是含 $0$ 且封闭于下述规则的最小集: 若 $\alpha: I\to\mathcal T_v$, $I\in\{\{0\},\mathbb N\}\cup\{\mathcal T_u:u<v\}$, 则 $\alpha\in\mathcal T_v$. 分支域 $I$ 是结点数据的一部分 (函数连同定义域). 折叠 $\mathcal D_v:\mathcal T_\omega\to\mathcal T_v$ 对 $\alpha\in\mathcal T_\omega$ 超限归纳, **对一切 $v\le\omega$ 同时定义**:
  - $(\mathcal D1)$ $\mathcal D_0(0):=0^+$, $\mathcal D_{n+1}(0):=(z)_{z\in\mathcal T_n}$, $\mathcal D_\omega(0):=(\mathcal D_{n+1}(0))_{n\in\mathbb N}$.
  - $(\mathcal D2)$ $\mathcal D_v((\alpha_x)_{x\in I})$ 等于: $(\mathcal D_v(\alpha_0)\cdot(n+1))_{n}$ 若 $I=\{0\}$; $(\mathcal D_v(\alpha_x))_{x\in I}$ 若 $I\in\{\mathbb N\}\cup\{\mathcal T_u:u<v\}$ (低于目标, 保留); $(\mathcal D_v(\alpha_z))_{n\in\mathbb N}$, 其中 $z:=\mathcal D_u(\alpha_{0^+})$, 若 $I=\mathcal T_u$ 且 $v\le u<\omega$ (同层或更高).
  - 原文 Remark: 后一情形下 $\mathcal D_v(\alpha)$ 是定义域为 $\mathbb N$ 的**常值函数**. 也就是说, 树里故意产生常值 ℕ-极限; 这棵树只用于终止性 (Theorem I 由 $\mathcal T_0$ 上的超限归纳得到), 链的迭代分摊到九头蛇的逐步移动上.
  — [Buchholz, *An independence result for (Π¹₁-CA)+BI*, APAL 33 (1987)](https://epub.ub.uni-muenchen.de/3842/1/buchholz_wilfried_3842.pdf)
- **Buchholz 1987, §2 (原文已读, pp. 135–136).** 项结构 $(T,\cdot[\cdot])$ 是上面树的记号: $\overline{D_v a}:=\mathcal D_v(\bar a)$, 并要求 $\overline{a[z]}=\bar a(\bar z)$. 规则 `([ ].4)(ii)`: $\mathrm{dom}(b)=T_u$, $v\le u<\omega$ 时 $\mathrm{dom}(D_vb)=\mathbb N$, $(D_vb)[n]:=D_v\,b[D_u\,b[1]]$ (右边不依赖 $n$, 与 $(\mathcal D2)$ 第三支逐字对应). 原文说树的解释只作动机, 证明不用它. — [同上](https://epub.ub.uni-muenchen.de/3842/1/buchholz_wilfried_3842.pdf)
- **Schwichtenberg 1993, §1–2 (原文已读, pp. 82–86).** 树类 $\mathcal T_\sigma$ ($\sigma\le\nu<\omega$): $\alpha:I\to\mathcal T_\sigma$, $I=\emptyset,\{0\}$ 或 $\mathcal T_\rho$ ($\rho<\sigma$); $\Omega_\sigma:=(\zeta)_{\zeta\in\mathcal T_\sigma}\in\mathcal T_{\sigma+1}$, $\omega=\Omega_0$. 折叠 $D_\sigma:\mathcal T_\nu\to\mathcal T_{\sigma+1}$ ($\sigma<\nu$) 对 $\mathcal T_\nu$ 归纳:
  - i. $D_\sigma0:=\Omega_\sigma$; ii. $D_\sigma(\alpha+1):=(D_\sigma(\alpha)\cdot(n+1))_{n\in\mathbb N}$;
  - iii. 若 $\rho\le\sigma$: $D_\sigma((\alpha_\zeta)_{\zeta\in\mathcal T_\rho}):=(D_\sigma\alpha_\zeta)_{\zeta\in\mathcal T_\rho}$ (保留);
  - iv. 若 $\sigma<\mu+1$: $D_\sigma((\alpha_\zeta)_{\zeta\in\mathcal T_{\mu+1}}):=(D_\sigma\alpha_{\zeta_n})_{n\in\mathbb N}$, $\zeta_0:=\Omega_\mu$, $\zeta_{n+1}:=D_\mu\alpha_{\zeta_n}$.
  - 作者称 iv 是关键条款, 它让 $D_\sigma$ 对 $\mathcal T_{\sigma+1}$ 以上的树也有定义. 例: $D_0\Omega_1$ 的链 $\zeta_0=\omega,\ \zeta_{n+1}=D_0\zeta_n$, 与 $\varepsilon_0$ 相似. 作者说第 1–3 节关于树、树记号、慢增长层级的材料取自 Buchholz (1987).
  — [Schwichtenberg, *Proofs as programs*, in Aczel–Simmons–Wainer (eds.), *Proof Theory* (Leeds 1990 programme), CUP, 重印页标 ©1993](https://epub.ub.uni-muenchen.de/4489/1/4489.pdf)
- **Schwichtenberg 1993 的记号侧 (原文已读, pp. 84–86).** 树记号 $a$ 带 "类型" $\tau(a)\in\{0,1\}\cup\{\Omega_\sigma\}$; 规则 iv 的记号版: $\tau(a)=\Omega_{\mu+1}$, $\sigma<\mu+1$ 时 $\tau(D_\sigma a):=\omega$, $(D_\sigma a)[n]:=D_\sigma a[z_n]$, $z_0:=\Omega_\mu$, $z_{n+1}:=D_\mu a[z_n]$. Lemma 2.1: $\mathrm{val}(a[z])=\mathrm{val}(a)(\mathrm{val}(z))$. — [同上](https://epub.ub.uni-muenchen.de/4489/1/4489.pdf)
- **Fairtlough 1992, Ch. 1 (原文已读, pp. 12–15).** 树类 $\Omega_n$ ($n<\omega$): $\alpha:I\to\Omega_n$, $I=\emptyset,\{0\}$ 或 $\Omega_k$ ($k<n$); 记 $\mathrm{dom}(\alpha)$. Def 1.3 另设 $\mathrm{lev}(\alpha)$ = 使 $\alpha\in\Omega_k$ 的最小 $k$; 作者说 lev 大致量基数, dom 量共尾度. 这里 $\Omega_k\subset\Omega_n$ 靠 "把函数等同于其图像" 实现, lev 由此可算. 第 1 章没有出现折叠函数. — [Fairtlough, *Ordinal Complexity of Recursive Programs and their Termination Proofs*, PhD thesis, Leeds; LFCS report ECS-LFCS-92-196](https://www.lfcs.inf.ed.ac.uk/reports/92/ECS-LFCS-92-196/) ([PDF, 扫描件](http://www.lfcs.inf.ed.ac.uk/reports/92/ECS-LFCS-92-196/ECS-LFCS-92-196.pdf))
- **Freund 2019 (原文已读 Def 1.1–1.2 与 §1 构造).** 不在树上, 在 dilator 上: prae-dilator 带自然变换 $\mathrm{supp}_T:T\Rightarrow[\cdot]^{<\omega}$ (有限 support); Bachmann–Howard collapse $\vartheta:T_X\to X$ 要求 (i) 若 $\sigma<_{T_X}\tau$ 且 $\mathrm{supp}(\sigma)<^{\mathrm{fin}}_X\vartheta(\tau)$, 则 $\vartheta(\sigma)<_X\vartheta(\tau)$; (ii) $\mathrm{supp}(\sigma)<^{\mathrm{fin}}_X\vartheta(\sigma)$. 构造时用 $C(\tau,\alpha)=\mathrm{supp}(\tau)\cup\{\vartheta(\sigma)\mid\sigma<\tau,\ \mathrm{supp}(\sigma)\subseteq\alpha\}$ 迭代取闭包. 比较义务只在有**有限字面证据** (support 落在界下) 时出现. — [Freund, *Π¹₁-comprehension as a well-ordering principle*, arXiv:1809.06759](https://arxiv.org/abs/1809.06759)

### Inferences
- [判断] 文献里 "低于目标保留 / 否则走链" 的分派之所以可判定, 全靠层标签取自 ℕ (或 $\le\omega$): 分派看的是**字面分支域** $\mathrm{dom}$, 不是算出来的 $\mathrm{lev}$, 也不看分支内容. 我方层号是树, 同一个分派落到壁垒上; 文献没有可直接搬的解法, 但支持 "让比较只发生在字面标签上" 这一方向, 即候选的 framed keep (目标与槽位带字面公共上界证据).
- [判断, 可借的装置 1] Schwichtenberg 的 iv 把我方的 "同层对角" 与 "高于目标走链" 合成一条: 链总用**结点自身层**的折叠 $D_\mu$, 从字面地板 $\Omega_\mu$ 起步; $\mu=\sigma$ 时 $\zeta_{n+1}=D_\sigma\alpha_{\zeta_n}$ 恰是 "以输出作下标". 于是需要的判定从三分降为二分: "结点层 $\le$ 目标" 与 "结点层 $>$ 目标". 代价是折叠必须对一切目标层同时定义 (Buchholz 明写 "对一切 $v\le\omega$ 同时定义"), 且链里调用的是 $D_\mu$ 作用于子树, 结构递归仍成立. 这只减少分派的种类, 不消除 "保留与走链之间" 的那一次比较.
- [判断] 若把保留误判成走链, iv 给出的是 $\mathcal T_{\mu+1}$-分支的一个可数共尾子列, 值严格下降; 这与简报所述 "总走链, 值严格下降" 是同一现象, 文献没有给出不判定就恢复的办法.
- [判断, 可借的装置 2] Freund 的条件 (i) 是 "带字面证据的比较" 的现成范式: 序关系的义务以有限 support 落在界下为前提, 与我方 "律里每一对下标都带字面公共上界" 同构. 可以试着把 framed keep 的证据写成 support 形状 (有限的下层树列表 + 它们在目标下方的见证), 而不是任意证据.
- [判断] Buchholz 1987 树里有意出现常值 ℕ-极限, 说明在只需终止性的场合, 退化结点是无害的; 值的论证完全交给记号侧. 这对 "折叠树里的退化结点是否必须消除" 给出一个先例: 不必消除, 但值语义要另找载体 (见问题二).

### Gaps
- Fairtlough–Wainer 的 Handbook 章 (1998, pp. 149–207) 与 Schwichtenberg–Wainer *Proofs and Computations* (2012) 第 5–6 章本轮未取得 (付费); 两处是否有 Wainer 式二元折叠 $\varphi^{k+1}_k$ 以及其条款形状, **未核**. 只确认了章的书目与 Arai 2000 在 BSL 6(4) 有书评 ([Cambridge 书评页](https://cambridge.org/core/journals/bulletin-of-symbolic-logic/article/matt-fairtlough-and-stanley-s-wainer-hierarchies-of-provably-recursive-functions-handbook-of-proof-theory-edited-by-samuel-r-buss-studies-in-logic-and-the-foundations-of-mathematics-vol-137-elsevier-amsterdam-etc-1998-pp-149207/85169502CC25D8966AA5B4C03D34CA0B), 正文不可见).
- Buchholz–Wainer 1987 (Contemp. Math. 65, 179–198) 本轮未读; 书目来自 Fairtlough 论文参考文献页.
- 手册把 `([ ].4)(ii)` 记作 "Buchholz 1986"; 本轮读到的是 Buchholz 1987 p. 136 的同号条款, 内容与手册转述一致. 是同一处还是 1986 文另有同号条款, 待核. 若是同一处, 手册 §7 "一手文本" 一项可用上面的 LMU 开放链接.

## 问题二: 对树的结构条件怎样避开非规范树 (难点 2)

### Takeaway
已发表的 "只对良好树陈述" 理论有两种: (a) Dennis-Jones–Wainer/Fairtlough 的 **structured** 树 (遗传的逐点闭包条件, Bachmann 性质的弱形式), 在 $\Omega_1$ 上给出 "路径集穷尽子树集" 与线性支配, 但作者给出**在第 2 层以上不成立**的反例; (b) Buchholz/Schwichtenberg 的做法: 树只作动机, 一切值与单调性定理都陈述在**记号项**上, 项通过 $\mathrm{val}(a[z])=\mathrm{val}(a)(\mathrm{val}(z))$ 对应到树. 后者就是 "读回域" 的先例; 前者说明在高层上单靠遗传结构谓词拿不到完整的值语义.

### Cited Findings
- **Fairtlough Def 1.4 (原文已读, pp. 13–14): 每层一个下标的路径.** 记 $\overline\Omega_n:=\prod_{k<n}\Omega_k$; 对下标向量 $\bar\zeta$, $\prec_{\bar\zeta}$ 是 $\alpha(\bar\zeta)\prec_{\bar\zeta}\alpha$ 的传递闭包, 其中 $\alpha(\bar\zeta)$ 在零/后继/分支域 $\Omega_k$ 时分别取 $0$, $\alpha'$, $\alpha(\zeta_k)$; $\alpha[\bar\zeta]:=\{\beta:\beta+1\preceq_{\bar\zeta}\alpha\}$, $G_\alpha(\bar\zeta):=|\alpha[\bar\zeta]|$. 即在 $\Omega_k$-结点上下降时**一律取向量的第 $k$ 个分量**. 作者注明 $\Omega_1,\Omega_2$ 的版本见 Cichon 1985. — [Fairtlough 1992](https://www.lfcs.inf.ed.ac.uk/reports/92/ECS-LFCS-92-196/)
- **Fairtlough Def 2.1–2.2 (原文已读, p. 15).** $\bar\eta\ \pi_n\ \bar\zeta$ iff 对一切 $i<n$, $\eta_i\in\zeta_i[\bar\zeta\restriction i]$. $\alpha$ **structured** iff 对每个分支域为 $\Omega_k$ 的极限子树 $\gamma\preceq\alpha$ 与每个 $\bar\zeta$, $\eta\in\omega_k[\bar\zeta]$ 蕴含 $\gamma(\eta)\in\gamma[\bar\zeta]$. 作者称它是 Bachmann 性质的弱形式, 最早由 Dennis-Jones 与 Wainer [De84] 引入. 作者并指出: 不加条件时极限的分支序列不必递增, $\alpha\prec\beta$ 也不保证 $G_\beta$ 支配 $G_\alpha$. — 同上
- **Fairtlough Lemma 2.3, 3.3, Cor 3.4, Thm 3.5 (原文已读, pp. 15–18).** 2.3: $\alpha$ structured 且 $\bar\zeta\ \pi\ \bar\eta$ 则 $\alpha(\prec_{\bar\zeta})\subseteq\alpha[\bar\eta]$. 3.3: $\alpha\in\Omega^s_1$ 时 $\alpha(\prec)=\bigcup_x\alpha[x]$ 且被 $\prec$ 良序. 3.4: $\gamma\preceq\beta\prec\alpha$ 则 $G_\gamma$ 最终 $\le G_\beta$. 3.5: $(g_\alpha,\alpha)=\varinjlim G_\alpha$ (作者说本质上是 [De84] Theorem 2, 另给出经 Girard 1981 的证明). — 同上
- **Fairtlough 的否定 (原文已读, pp. 18, 27).** 对更高的树类, 3.3 不成立: 存在 $\mathrm{lev}\ge2$ 的 $\alpha\in\Omega_{n+2}$ 使 $\alpha(\prec)\ne\bigcup_{\bar\zeta}\alpha[\bar\zeta]$. 例: $\omega_k^2$, 取 $\Omega_k$ 中不可比的 $\gamma'_1,\gamma'_2$ (如 $\omega_0$ 与 $1+\omega_0$), 则 $\omega_k\cdot\gamma'_1+\gamma'_2\prec\omega_k^2$, 但不在任何 $\omega_k^2[\bar\zeta]$ 中. 作者还指出这些 "树" 的子树集 $\{\gamma:\beta\preceq\gamma\prec\alpha\}$ 一般不是线性序. — 同上
- **Fairtlough §3–§4 (原文已读, pp. 16–23): 范畴语义与 "滞后" 的记账.** 态射 $\Omega_n(\alpha,\beta)$ = 保 $\prec$ 的 $h:\alpha(\prec)\to\beta(\prec)$. $g$ 称 $\varphi$-decomposable ($\varphi$ 严格递增) 若 $g(\alpha[x])\subseteq\beta[\varphi(x)]$; Lemma 4.3: $\Omega^s$ 中每个态射对某个 $\varphi$ 是 $\varphi$-decomposable. Def 4.9 重新编址 $\alpha\uparrow\psi$ (极限处取 $(\alpha(\psi(x))\uparrow\psi)_x$), 保 structured, 保秩, 且 $(\alpha\uparrow\psi)[x]=\{\beta\uparrow\psi:\beta\in\alpha[\psi x]\}$. Thm 4.5 (归于 Aoyama, Kadota): $\aleph_1$ 上存在 diagonal-built-up 的基本列系统; Cor 4.7: $\Omega^s$ 与 $\mathrm{ON}<\aleph_1$ 范畴等价 (经典证明). — 同上
- **Fairtlough §5 (原文已读, pp. 23–27).** $+,\cdot,\exp$ 在 $\Omega_n$ 上对右参数递归, 在 $\Omega_k$-分支上逐点; Lemma 5.4: $(\alpha+\beta)[\bar\zeta]=\alpha[\bar\zeta]\cup(\{\alpha\}+\beta[\bar\zeta])$; 加法保 structured, 乘法与幂在附加条件 ($1\preceq_{\bar\zeta}\alpha$ 或 $2\preceq_{\bar\zeta}\alpha$ 对一切使 $\omega_k[\bar\zeta]\neq\emptyset$ 的 $\bar\zeta$) 下保 structured. — 同上
- **Buchholz 1987 §2, Schwichtenberg 1993 Lemma 2.1 (原文已读).** 值与序的定理全在项上陈述; 项到树的对应满足 $\overline{a[z]}=\bar a(\bar z)$. Buchholz 明说树的解释不用于证明. — [Buchholz 1987](https://epub.ub.uni-muenchen.de/3842/1/buchholz_wilfried_3842.pdf); [Schwichtenberg 1993](https://epub.ub.uni-muenchen.de/4489/1/4489.pdf)
- **Buchholz 1987 $W_v$ (原文已读, p. 137; 手册已有).** (W2) $a\in T_v$, $\mathrm{dom}(a)\in\{\{0\},\mathbb N\}$, $\forall n\,(a[n]\in W_v)\Rightarrow a\in W_v$; (W3) $\mathrm{dom}(a)=T_u$, $u<v$, $\forall z\in W_u\,(a[z]\in W_v)\Rightarrow a\in W_v$. Ω-分支只对**下层已良基的下标**量化. — [Buchholz 1987](https://epub.ub.uni-muenchen.de/3842/1/buchholz_wilfried_3842.pdf)
- **Kraus–Nordvall Forsberg–Xu 2023 (原文已读摘要与 §4 小结).** Brouwer 树做成商归纳-归纳类型 (极限取严格递增序列并商掉); 许多性质等价于 LPO, 包括关系的可判定性、$\le$ 的分裂、三歧性; 但 "是否有限" 可判定, 在有限树上等式可判定; "在 $\omega$ 处的局部等式" 可判定当且仅当 WLPO, 在 $\omega\cdot2$ 处已等价于 LPO. 具体定理: Thm 46, 48–51, 53. 有 classification 与 classifiability induction. 结果在 cubical Agda 中形式化. — [Kraus, Nordvall Forsberg, Xu, *Type-theoretic approaches to ordinals*, TCS 957 (2023), arXiv:2208.03844](https://arxiv.org/abs/2208.03844)

### Inferences
- [判断] Fairtlough 的 structured 是对我方 "合法性" 谓词最接近的已发表物: 遗传, 逐点, 只要求 "$\eta$ 在 $\omega_k$ 的路径集里则 $\gamma(\eta)$ 在 $\gamma$ 的路径集里". 但他的否定 (第 2 层以上路径集不穷尽子树) 提示: 在高层, 用 "一切子树" 定义预期值与用 "路径" 定义预期值会分开. 预期值若要沿每条折叠规则单调, 宜按**下标向量/路径**定义 (Fairtlough 的 $\alpha[\bar\zeta]$), 不按全体子树.
- [判断, 可借的装置 3] "每层一个共享下标" ($\bar\zeta\in\prod_{k<n}\Omega_k$, 在 $\Omega_k$-结点一律取 $\zeta_k$): 沿一条路径, 同层的所有 Ω-结点用**同一个**下标. 简报难点 1 的 "槽位与目标经同一个孩子到达, 需要知道两个孩子相同" 在这种写法里由构造保证 (同一分量), 不需比较. 若层号是树, 向量变成 "对层号树的前驱的依赖函数", 是否良类型、是否仍不判定, 需要编译验证.
- [判断] Buchholz/Schwichtenberg 的整体组织 (树只作动机; 值定理放在一个封闭于各运算、带 $\overline{a[z]}=\bar a(\bar z)$ 的语法域上) 正是 AGENTS "量化域先取带证据的读回域" 的先例. 按纲领第 4 条, 我方的读回域不能是记号项; 可替换为 "由折叠从规范种子生成的树, 连同生成它的构造证据" 的归纳类型, 保持 $\overline{a[z]}=\bar a(\bar z)$ 这一条作为接口律.
- [判断] Fairtlough 的 $\varphi$-decomposable 态射与 $\alpha\uparrow\psi$ 给出一套记 "滞后" 的语言: 两棵树之间的比较允许下标被一个严格递增函数 $\varphi$ 平移, 且 $\varphi$ 在复合下成幺半群. 简报所说 "损失在外层极限里才补回, 滞后随嵌套增长" 可以试着写成: 存在随嵌套深度复合的 $\varphi$, 使参照树到折叠树有 $\varphi$-decomposable 态射. 这只用于序数值 (保 $\prec$ 的嵌入), 不涉及 FGH 值.
- [判断] Kraus 等的表与壁垒定理同向: 商掉非规范性的代价是要立方类型论的商, 且比较仍是 LPO. 在 `--without-K` 而不开 cubical 的约束下, 这一路只提供 "classifiability induction" 作为 View 的形状参考, 不提供可判定性.

### Gaps
- Dennis-Jones–Wainer 1984 ([De84], LNM 1104, 117–128) 与 Cichon 1985 (Leeds 博士论文) 本轮未取得; structured 的原始定义与 [De84] Theorem 2 只经 Fairtlough 转述 (**二手**).
- Schmidt 1976/77 的 built-up 系统 (Arch. math. Logik 18, 47–53, 145–146; 书目据 Fairtlough 参考文献页) 未读.
- 没有找到在 $\Omega_k$ ($k\ge2$) 树上陈述 "预期值单调于每条折叠规则" 的已发表定理. Fairtlough 的否定只说路径集不穷尽, 没说路径语义上的单调性如何.

## 问题三: 下界与支配怎样证 (单调性引理, 逐点关系, 滞后) (难点 3)

### Takeaway
最可借的是 Buchholz 1987 §3 的 $\ll_k$: 在 Ω-分支结点上**对全部主项分支 $D_ue$ 全称量化** (不挑孩子), 然后一次超限归纳证 "折叠对 $\ll_k$ 单调" ($c\ll_ka\Rightarrow D_vc\ll_kD_va$, 对一切层 $v$ 一致). 这是与阶段无关的单条定理, 支配层级的单调性由它直接得到. Schwichtenberg 的 $<_k$ 则改为在 Ω-结点取字面地板分支 $a[\Omega_\mu]$ 作 "前驱".

### Cited Findings
- **Buchholz 1987 §3 定义 (原文 §3, 在 p. 138 与 p. 144 之间, 逐页页码未核; 据 PDF 的 OCR 文字层).** $c\ll_ka:\Leftrightarrow a\ne0$ 且 $\forall z\in d_k(a)\,(c\ \underline{\ll}_k\ a[z])$, 其中 $d_k(a):=\{k\}$ 若 $\mathrm{dom}(a)\in\{\{0\},\mathbb N\}$; $d_k(a):=\{D_ue:0\ne e\in T\}$ 若 $\mathrm{dom}(a)=T_u$. 作者说 $\ll_0$ 限制在 $T_0$ 上正是 Schmidt 的 step-down 关系, 并参照 Ketonen–Solovay. — [Buchholz 1987](https://epub.ub.uni-muenchen.de/3842/1/buchholz_wilfried_3842.pdf)
- **Buchholz 1987 Lemma 3.1–3.5 (原文已读, OCR 层).** 3.1: 传递; $c\ll_kb\Rightarrow a+c\ll_ka+b$; $b\ne0\Rightarrow a\ll_ka+b$. 3.2: (a) $n\le k+1\Rightarrow(D_va)\cdot n\ll_kD_v(a+1)$; (b) $c\ll_ka\Rightarrow D_vc\ll_kD_va$, 证明对 $a$ 超限归纳, 按 $\mathrm{dom}$ 分支, Ω-分支情形取 $z:=D_u\,a[1]\in d_k(a)$. 3.3: $\mathrm{dom}(a)=\mathbb N\Rightarrow a[n]\ll_ka[n+1]$. 3.4: $a\ll_kb$, $k\le m\Rightarrow a\ll_mb$; $\mathrm{dom}(a)=\mathbb N$, $n\le k\Rightarrow a[n]\ll_ka$. 然后定义与 Hardy 层级相近的 $H_a$, §4 (Theorem 4.0) 用形如 $H_{D_0D_v^{m}0}$ 的函数界住 $\mathrm{ID}_v$ 可证的 $\forall x\exists y$ 句子的见证 (OCR 文字有缺损, 上标的确切写法未核). — 同上
- **Schwichtenberg 1993 §3 (原文已读, pp. 86–89).** $a^-:=a[0]$ 若 $\tau(a)\in\{1,\omega\}$; $a^-:=a[\Omega_\mu]$ 若 $\tau(a)=\Omega_{\mu+1}$. $a<_kb$ iff 有有限链 $a=a_0,\dots,a_n=b$, 每步 $a_i=a_{i+1}^-$ 或 ($\tau(a_{i+1})=\omega$ 且 $a_i=a_{i+1}[j]$, $1\le j\le k$). 目的: $a<_kb\Rightarrow G_an\le G_bn$ ($n\ge k$); 作者说明为何不能直接用值的序 ($G_k(n)=k$, $G_\omega(n)=n$). Lemma 3.1: $(D_\sigma a)^-=D_\sigma a^-$; 3.2: $b<_ka\Rightarrow D_\sigma b<_kD_\sigma a$, $(D^m_\sigma a)+1\le_1D^m_\sigma(a+1)$; 3.3: $\tau(c)=\Omega_{\mu+1}$, $x<_ky\Rightarrow c[x]<_kc[y]$; $c[x]+1\le_1c[x+1]$; $\tau(c)=\omega\Rightarrow c[n]+1\le_1c[n+1]$. 证明对项长度归纳. — [Schwichtenberg 1993](https://epub.ub.uni-muenchen.de/4489/1/4489.pdf)
- **Fairtlough Lemma 2.3 与 Cor 3.4** (见问题二): structured 树上下标向量的 $\pi$-单调性推出路径集包含, 再推出支配. — [Fairtlough 1992](https://www.lfcs.inf.ed.ac.uk/reports/92/ECS-LFCS-92-196/)
- **Fernández-Duque–Weiermann (只见摘要).** Buchholz 为 $\vartheta$ 给的基本列系统满足若干正则性, 包括 Bachmann 性质; 由此 Hardy 函数以自然方式单调, 并支配沿 $\vartheta(\varepsilon_{\Omega+1})$ 原始递归定义的一切函数. 方法本轮未读. — [Fernández-Duque, Weiermann, *Fundamental sequences and fast-growing hierarchies for the Bachmann-Howard ordinal*, arXiv:2203.07758 (v5, 2024)](https://arxiv.org/abs/2203.07758)
- **慢增长对基本列极敏感 (二手).** Wainer 1989 的首页摘录: 他更正了早先 "慢增长层级在 $\Gamma_0$ 追上快增长" 的说法, 并说要在 $|\mathrm{ID}_n|$ 处抓住 $F$, $G$ 须生成到 $|\mathrm{ID}_{n+1}|$; Girard 证明首个追上点是 $\mathrm{ID}_{<\omega}$ 的序数. Weiermann 2001 标题 *Γ0 may be minimal subrecursively inaccessible* 表明追上点随基本列选择而变. — [Wainer, *Slow growing versus fast growing*, JSL 54(2) (1989) 608–614](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/slow-growing-versus-fast-growing/93FA89B675AE184EC1B35A75F0849229); [Slow-growing hierarchy, Wikipedia](https://en.wikipedia.org/wiki/Slow-growing_hierarchy); [Weiermann 2001, MLQ 47(3), PhilArchive](https://dc2.philarchive.org/rec/WEIMB-2)

### Inferences
- [判断, 可借的装置 4] $\ll_k$ 的形状可以直接移到树上: 关系对参数树结构递归, ℕ-结点看第 $k$ 个分支, Ω-结点**对一切 "主形" 分支**全称量化. 这正是 AGENTS 所说的 "一致目标": 关系不要求知道哪个孩子. 然后 "折叠对此关系单调" 是一条对参数树的归纳, 情形只按结点的字面标签分, 对一切目标层一致 (3.2(b) 的证明不依赖 $v$ 的具体值). 这是简报要的 "阶段无关的整体定理" 的一个已发表模板.
- [判断] 3.2(b) 在 Ω-分支情形用的是 $z:=D_u\,a[1]$, 即链的第一项; 它对 $\ll_k$ 够用, 是因为 $\ll_k$ 只要求在 $d_k$ 里的某些下标上成立. 移到我方时, 主形分支集 $d_k$ 的选择 (Buchholz 取一切 $D_ue$, $e\ne0$) 决定了律的量化域; 按 AGENTS "量化域先取带证据的读回域", 应先在规范实例上实填 $d_k$, 再定稿.
- [判断, 可借的装置 5] Schwichtenberg 的 $a^-:=a[\Omega_\mu]$ 是 "字面地板" 的已发表用法: Ω-结点的标准前驱取在字面闭项 $\Omega_\mu$ 处, 永远存在, 无需判定. 3.3(i) "$x<_ky\Rightarrow c[x]<_kc[y]$" 是 Ω-分支上的 Bachmann 型单调性, 对应我方 "槽位下标单调" 一类引理.
- [判断] 慢增长文献的反复更正说明: 同序数值的树, 其 $G$/$F$ 值可以差很远. 这与 AGENTS 只用序数值验收、不比 FGH 的约定一致; 下界证明应写成保 $\prec$ 的嵌入或 $\ll_k$ 一类关系, 不写成函数值比较.

### Gaps
- Buchholz–Cichon–Weiermann 1994 全文本轮取不到 (core.ac.uk 返回 403); (B1)(B2) 与范数的具体陈述以手册 §2 的记录为准. [BCW 在 Wikipedia 的条目](https://en.wikipedia.org/wiki/Fundamental_sequence_(set_theory)) 只给了名称与 "Bachmann 性质推出单调与最终支配" 的转述.
- Weiermann 1995 (AML, *How to majorize slow growing functions nontrivially by fast growing ones*) 与 1997 (APAL 90, 91–99) 未读 (ScienceDirect 403); 其中控制 "非标准基本列" 滞后的技术未核.
- Arai 1991 (APAL 54(2), 101–120, *A slow growing analogue to Buchholz' proof*) 只见书目与摘要转述 ([MaRDI](https://portal.mardi4nfdi.de/wiki/Publication:1182465)); Schwichtenberg 说他的 $\omega^+$-规则来自 Arai 的慢增长版 Ω-规则.

## 问题四: 有限层 Ω_k 之外 (Ω_ω, Ω_Ω, 以树为下标的层)

### Takeaway
树序数传统里本轮能核实的最高层是 Buchholz 1987 的 $v\le\omega$: $\Omega_\omega$ 不是一个分支类, 而是 $\mathcal D_\omega(0):=(\mathcal D_{n+1}(0))_{n\in\mathbb N}$, 即 Ω_{n+1} 树的 **ℕ-极限**, 且 $\mathcal T_\omega$ 从不在 $\mathcal T_\omega$ 上分支. 没有找到在树序数上以树为层号 ($\Omega_\Omega$, $\Omega_\xi$) 定义折叠的工作.

### Cited Findings
- Buchholz 1987: $\mathcal T_v$ 对 $v\le\omega$; 分支域只取 $\mathcal T_u$, $u<v$, 故 $\mathcal T_\omega$ 的结点在一切有限层上分支, 不在 $\mathcal T_\omega$ 上分支; $\mathcal D_\omega(0)$ 是 ℕ-极限; 九头蛇的标签取 $\le\omega$, 项 $D_\omega a$ 允许出现; 标题理论 $(\Pi^1_1\text{-CA})+\mathrm{BI}$. — [Buchholz 1987](https://epub.ub.uni-muenchen.de/3842/1/buchholz_wilfried_3842.pdf)
- Schwichtenberg 1993 与 Fairtlough 1992 只用有限层 ($\nu<\omega$; $\Omega_n$, $n<\omega$). — [Schwichtenberg 1993](https://epub.ub.uni-muenchen.de/4489/1/4489.pdf); [Fairtlough 1992](https://www.lfcs.inf.ed.ac.uk/reports/92/ECS-LFCS-92-196/)
- Wainer 给出 "最小的 subrecursively inaccessible" 序数的记号 (记作 $T$), Kadota 1993 (MLQ 39, 217) 对它给出详细证明 (**二手**: 来自 Kadota 博士论文的检索摘要与 Wainer 1989 的 Crossref 引用列表; 该记号是否用到 $\Omega_\omega$ 层的树, 未核). — [Crossref 引用列表 (Wainer 1989)](https://unpaywall.org/10.2307%2F2274873)
- Girard 的比较定理: 慢增长首次追上快增长于 $\mathrm{ID}_{<\omega}$ 的序数 (**二手**, Wikipedia 转述). — [Slow-growing hierarchy, Wikipedia](https://en.wikipedia.org/wiki/Slow-growing_hierarchy)

### Inferences
- [判断] Buchholz 1987 的 $\Omega_\omega$ 处理与我方 "交替路线" (不可数层在对象层以对角 ℕ-极限表示, 不作可数层构造子) 同形; 它是这一做法在同行评审文献中的早期实例, 可作为 "龙骨上的极限层用 ℕ-极限" 的引用. 但他的层号仍是 $\le\omega$ 的字面数, 极限层只有一个.
- [判断] 从 $\Omega_\omega$ 到 $\Omega_\Omega$ 需要 "层号本身是树" 与 "按层号的比较", 正是壁垒所在. 文献中按 Buchholz $\psi_\nu$ 让层号变成序数的工作 (Buchholz 1986 及其后的 EBO 类系统) 都在记号或集合论序数上做, 层号比较靠记号的可判定序; 树侧没有先例. 这支持把我方的问题看作开放问题, 而不是 "文献已有、我们没找到".

### Gaps
- 集合论的 Bachmann 型层级 (Bachmann 1950, Pfeiffer 1964, Isles 1970, Bridge 1975, Aczel 1972 *Describing ordinals using functionals of transfinite type*) 用长度为 $\Omega_\nu$ 的 distinguished sequences, 层号 $\nu$ 可变. 本轮没有检索, **未核**; 它们是否有 "按 $\nu$ 分派而不比较分支" 的技巧, 值得下一轮专查.
- Kadota 1993 与 Wainer 的 $T$ 记号未取得; Kadota 博士论文的广岛大学链接 (`ir.lib.hiroshima-u.ac.jp/31814`) 本轮返回 404.

## 问题五: 2010–2026 的构造性或证明助手工作, 以及来源总表

### Takeaway
近年的构造性工作集中在 "Brouwer 树本身" (可判定性, 商, 严格单调的 join), 没有找到在证明助手里定义树上折叠或高层树上 FGH 的已发表工作 (检索结论, 非穷举). 与难点直接相关的两条: Eremondi 的 SMB 树给出构造性的 "字面上界" (join), Kraus 等给出 Brouwer 树比较的 LPO/WLPO 精确分界.

### Cited Findings
- **Eremondi, CPP 2024 (只见摘要).** 对 Brouwer 树定义按后继模式匹配的递归 max; SMB 树是该 max 恰为最小上界的子集, 其 join 对后继分配; 任意 Brouwer 树经与自身无穷 join 变成对应的 SMB 树; 全部在 Agda 中实现. — [Eremondi, *Strictly Monotone Brouwer Trees for Well-founded Recursion Over Multiple Arguments*, arXiv:2312.06962](https://arxiv.org/abs/2312.06962)
- **Kraus–Nordvall Forsberg–Xu 2023** (见问题二) 与其前作 MFCS 2021. — [arXiv:2208.03844](https://arxiv.org/abs/2208.03844); [*Connecting constructive notions of ordinals in HoTT*, arXiv:2104.02549](https://arxiv.org/abs/2104.02549)
- **Freund 2019 及后续** (dilator 上的 Bachmann–Howard collapse; Π¹₁-CA₀ 等价于 "每个 dilator 有良基的 Bachmann–Howard 不动点"). — [arXiv:1809.06759](https://arxiv.org/abs/1809.06759)
- **Fernández-Duque–Weiermann 2022–2024; Wilken 2024** (记号侧的 Bachmann 性质; Wilken 已在手册). — [arXiv:2203.07758](https://arxiv.org/abs/2203.07758); [arXiv:2410.15953](https://arxiv.org/abs/2410.15953)
- **Wainer 1999** *Accessible recursive functions*, BSL 5(3) 367–388 (只见摘要): 用简化框架重做 Girard 的 dilator 理论, 生成的函数恰为 $(\Pi^1_1\text{-CA})_0$ 可证递归者. 是否在树序数上定义折叠, 未核. — [Cambridge](https://www.cambridge.org/core/journals/bulletin-of-symbolic-logic/article/accessible-recursive-functions/0971F2F0B2A95CBC99DFB474693E6754)

### 来源总表 (每条: 方法 / 对应难点 / 可借装置 / 构造性 / 档位)

| 来源 | 方法 | 难点 | 可借装置 | 构造性与可判定性 | 档位 |
|---|---|---|---|---|---|
| Buchholz 1987 §1 | 树类 $\mathcal T_v$ ($v\le\omega$), 树上折叠 $\mathcal D_v$, 对一切 $v$ 同时定义 | 1, 4 | 按字面分支域分派; $\Omega_\omega$ 作 ℕ-极限; 容忍常值极限 | 定义是集合论写法, 但递归是结构的, 分派比较自然数, 可判定 | 原文已读 |
| Buchholz 1987 §2–3 | 项结构 $(T,\cdot[\cdot])$; $\ll_k$; $H_a$; $W_v$ | 2, 3 | Ω-结点上对全部主形分支全称量化的逐点关系; 折叠单调 (3.2(b)) 一次归纳; $W_v$ 只对下层良基下标量化 | 关系是归纳定义的命题, 不可判定也不需要判定 | 原文已读 (OCR 层核对) |
| Schwichtenberg 1993 | 树类 $\mathcal T_\sigma$, $D_\sigma$ 带迭代链; 树记号; $<_k$ | 1, 3 | 链用结点自身层的 $D_\mu$, 从 $\Omega_\mu$ 起 (同层是特例); 字面地板前驱 $a[\Omega_\mu]$ | 同上; 层号 $<\omega$ | 原文已读 |
| Fairtlough 1992 (Leeds) | $\Omega_n$ 树类; 每层一个下标的路径; structured; 范畴与 direct limit; decomposable 态射 | 1, 2, 3 | 共享的逐层下标向量; structured 作遗传合法性; $\varphi$-decomposable 记滞后; 高层否定 | 第 1–2 节结构可构造; §4 的 Thm 4.5 与 Cor 4.7 是经典的 | 原文已读 (第 1 章) |
| Dennis-Jones–Wainer 1984 | structured 的来源; $G$ 作 direct limit | 2 | 同上 | 未核 | 二手 |
| Freund 2019 | 带有限 support 的 collapse 条件 | 1, 2 | 比较义务以有限字面证据为前提 | 元理论是二阶算术 (RCA₀ 上的等价); 转换可计算 | 原文已读 (Def 1.1–1.2) |
| Kraus–NF–Xu 2023 | Brouwer 树的可判定性表 | 1, 2 | WLPO/LPO 精确分界; classifiability induction | cubical Agda, 商类型 | 摘要与小结已读 |
| Eremondi 2024 | SMB 树, 递归 max | 1 | 不比较而得的公共上界 (join) | Agda | 只见摘要; 仓库旧探针用过 |
| Fernández-Duque–Weiermann | 记号侧 Bachmann 性质 → Hardy 单调 | 3 | 正则性条件清单 | 未核 | 只见摘要 |
| Wainer 1989; Weiermann 1997/2001; Girard 1981 | 慢增长对快增长 | 3 (反面) | 同值不同 FGH 的文献依据 | 未核 | 二手或只见书目 |
| Fairtlough–Wainer 1998 Handbook 章; Schwichtenberg–Wainer 2012 | 综述 (含树序数) | 1–3 | 未取得 | 未核 | 只见书目 |

### Inferences
- [判断] Eremondi 的 join 是 "字面公共上界" 的现成构造: 两棵树的上界由递归 max 直接写出, 不需比较. 若 framed keep 需要目标与槽位带公共上界证据, join 可作 "证据的默认来源"; 但它只在 SMB 子集上是最小上界, 且在 Ω-分支 (非 ℕ 分支) 上的推广未见. 仓库旧探针用过 SMB, 结论应先查 `archive/probes/OCF/Ord1D/` 下的记录再决定是否重开.
- [判断] 本轮的主要收获按难点归纳: 难点 1, 文献从不比较分支, 靠字面标签; 可借 "链用结点自身层的折叠" (降为二分) 与 "逐层共享下标" (同一孩子由构造保证). 难点 2, 文献的值语义放在读回域 (项, 或 structured 树的路径集) 上, 且有高层路径集不穷尽的否定. 难点 3, $\ll_k$ 式 "Ω-结点对主形分支全称" 的逐点关系加一次归纳的折叠单调性, 是阶段无关定理的模板.

### Gaps
- 没有检索 Lean mathlib、Coq Hydras & Co.、TypeTopology 中是否有高层 Brouwer 树或树上折叠; 本轮一次通用检索没有命中 (手册 CodeGuide 也记 "树折叠: 所读的仓库都没有").
- Hancock 关于类型论中高数类与 Brouwer 序数的工作、Setzer 的 ordinal systems 本轮未查 (Setzer 部分手册已有).
- Wainer 2016 *Pointwise transfinite induction and a miniaturized predicativity* 只见标题 (检索摘要), 未读.
