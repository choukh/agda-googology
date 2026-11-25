# R5 层号可变或由系统生成的折叠与序数层级 (Bachmann 一系, 序数下标的 ψ, 自治迭代), 附 Coquand 的 Agda 无穷演算

标注约定 (沿用 R2): [原文·读] = 本次逐页读了原文页面; [原文·抓取] = 经网页抓取工具读原文 (HTML, PDF 或源码), 措辞未逐字核; [摘要] = 只见出版社摘要、首页节选或书目; [二手] = Wikipedia, nLab, 社区 wiki 的转述; [推断] = 我的推断; [判断] = 未经检验的看法. 引文都短于 15 词.

与 R1–R4 的关系: 不重复 Buchholz 1987 树类, Schwichtenberg 1993, Fairtlough 1992, Freund, Setzer, Kraus–Nordvall Forsberg–Xu, Buchholz 1991. Aczel 1972 的超限型泛函已在 R4 问题 1, 这里只记它在 Bachmann 一系里的位置. 本地 EBO (扩展 Buchholz) 的规则见 `OrdinalNotationsGuide.md`, 不重述.

## 问题 1: 集合论 Bachmann 层级怎样处理可变层号 Ω_ξ; "用第 ξ 条基本列" 怎样不经比较作出

### Takeaway
在 Bachmann 一系里, 层号就是基本列的长度类 (ω, Ω, 推广后为 Ω_n). 它是每个极限下标自带的数据, 分情形时读这个标签, 不做比较. 推广 (Pfeiffer, Isles) 用的是**有限**数类, 标签是数字, 可判定. 本轮没有找到 Bachmann 一系把层号推到超限 (Ω_ξ, ξ ≥ ω) 的原文. Bridge 1975 与 Feferman–Weyhrauch–Aczel 的方向是用闭包或泛函**去掉**基本列, 而不是把基本列推到更高层. 所以这一系能提供两件东西: "种类即数据", 以及 "闭包式定义里没有派发". 它没有提供处理可变层号的技巧.

### Cited Findings
- **Bachmann 1950** [原文·抓取, Dowd 英译]. H. Bachmann, "Die Normalfunktionen und das Problem der ausgezeichneten Folgen von Ordnungszahlen", *Vierteljahrsschrift der Naturforschenden Gesellschaft in Zürich* (1950) 115–147 (MR 0036806). 英译本 *Normal Functions and the Problem of the Distinguished Sequences of Ordinal Numbers*, 译者 Martin Dowd — [arXiv:1903.04609](https://arxiv.org/abs/1903.04609) ([ar5iv](https://ar5iv.labs.arxiv.org/html/1903.04609)).
  - 方法: 正规函数族 φ_η, 下标 η 取到 Ω 之上. 每个极限下标附一条 distinguished sequence, 长度 τ_η 是 ≤ Ω 的极限. "第二种" 极限长度为 ω, "第三种" 极限长度为 Ω.
  - 分情形: 第二种极限取值域之交, 即 V ϕ_η = ⋂_{x<τ_η} V ϕ_{η_x}; 第三种极限取对角, 即 "ϕ_η(x) = ϕ_{η_x}(1)".
  - 层号的表示: 种类是序数表示的一部分. 对 ω^{x₀}·x₁+x₂ 形的下标, 按 x₂ 是第二种极限还是 x₂=0 分情形. 序列是附在每个极限序数上的数据. 分派读种类, 种类由构造给出, 不比较.
  - 抓取工具两次的回答不一致: 一次说 §4 用下标到 ω₂ 的第二类正规函数把序列延伸到 Ω 以上, 另一次说可见文本里没有第三数类的单独构造. **未逐字核**.
  - 否定结果: 在一组约束下, 给第二数类的**一切**极限指定 distinguished sequence 的问题不可解 (§6). 理由是每一步归纳都会改动先前的序列 [原文·抓取].
- **Pfeiffer 1964, Isles 1970, Miller 1976** [摘要 / 书目].
  - Bridge 的首页节选说 Pfeiffer (1964) 与 Isles (1970) 推广了 Bachmann 的方法, 得到更大的层级 — [Bridge 1975, Cambridge](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/simplification-of-the-bachmann-method-for-generating-large-countable-ordinals/4422E482B6FE458ACB23558952D6C179). Pfeiffer 1964 的题名与刊处**未核**.
  - Isles 的出处: D. Isles, "Regular ordinals and normal forms", in Kino, Myhill, Vesley (eds.), *Intuitionism and Proof Theory* (North-Holland 1970) pp. 339–361. Bridge 记作 339–362 — [JSL 书评页](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/david-isles-regular-ordinals-and-normal-forms-intuitionism-and-proof-theory-proceedings-of-the-summer-conference-at-buffalo-n-y-1968-edited-by-a-kino-j-myhill-and-r-e-vesley-studies-in-logic-and-the-foundations-of-mathematics-northholland-publishing-company-amsterdam-and-london1970-pp-339361/3DB3C917FD8BC1135124E641E675AA5A). 正文未读.
  - L. W. Miller, "Normal functions and constructive ordinal notations", *JSL* 41(2) (1976) 439–459, DOI 10.2307/2272243 — [Cambridge](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/normal-functions-and-constructive-ordinal-notations/737928AEF6123F3EBC244026F542F515) [摘要]. r-normal 函数指正则 r>ω 上严格递增且连续的函数. Bachmann 与 Isles 用 "higher finite number classes" 形成更长的 r-正规函数序列. Miller 还把 Bachmann 层级与 Takeuti 的 ordinal diagrams 联系起来. 层号的表示: 有限数类的序号 n, 是数字.
- **Bridge 1975** [摘要, 首页节选]. J. Bridge, "A simplification of the Bachmann method for generating large countable ordinals", *JSL* 40(2) (1975) 171–185, DOI 10.2307/2271898 — [Cambridge](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/simplification-of-the-bachmann-method-for-generating-large-countable-ordinals/4422E482B6FE458ACB23558952D6C179).
  - 动机: 基本列 "are not intrinsically of interest proof-theoretically", 而且 "only serve to obscure the definitions".
  - 文献脉络 (据节选): Feferman 与 Weyhrauch 提出另一种定义, Aczel 加以推广并证明新函数与 Bachmann 层级对应. Weyhrauch 1972 的博士论文独立地对下标 α < ε_{Ω+1} 的初始段得到同样结果.
  - Bridge 自己的简化是什么, 能到哪里, **未读到**.
- **Feferman 的 θ 函数** [二手]. 闭包 C(α,β) 由 0, ω₁, ω₂, …, ω_ω 与 <β 的序数生成, 对加法与 θ_ξ (ξ<α) 封闭. Buchholz 1986 给出 θ_{ε_{Ω_ν+1}}0 = ψ₀(ε_{Ω_ν+1}) (ν ≤ ω) — [Wikipedia, Ordinal notation](https://en.wikipedia.org/wiki/Ordinal_notation).
  - 层号的表示: Ω₁, …, Ω_ω 作为闭包的生成元 (常量) 出现, 不是 θ 的参数.
  - 分情形: 定义里没有按层派发, 派发只在基本列与比较算法里出现. 同页说 θ 系统本身不直接给出记号, Buchholz 造过一套但很复杂 [二手].

### Inferences
- [推断] **种类即数据.** Bachmann 的下标在类型上就是 "带种类标签的极限树": 第三数类的布劳威尔树, 有 ℕ-极限与 Ω-极限两种构造子. 分派读构造子, 可判定. 本项目在目标层固定为 Ω 时 (BTBO 一级) 与此同形. 层号可变时, 标签本身是树, 读标签不够, 还要读 "标签与目标的关系". Bachmann 一系没有提供这一步.
- [推断] **候选: 把相对位置编进类型.** 在 Bachmann–Isles 里, 下标总比函数高一类, 两者的关系由类型固定 (第 k 类函数的下标在第 k+1 类). 若折叠的签名把 "子树层号相对目标层的位置" 编进类型 (例如以目标为原点, 沿龙骨的路径), 分派就只是读构造子. 风险: 同一棵子树对不同目标需要不同的表示, 就要沿龙骨重新标记, 重新标记本身可能需要比较. 派发前先对照 `obs→dec` 一族 (`branch→wdec` 等).
- [推断] **闭包刻画作规格, 不作定义.** Bridge 与 Feferman θ 去掉基本列, 改用闭包刻画, 这在树侧不能直接照搬: "不在闭包里的最小序数" 不可计算. 能借的是分工: 闭包刻画当规格, 写成验收定理 (折叠的值 ≼ 闭包式的值); 怎么算交给树侧规则. 这与 AGENTS "FGH 视角定该是什么, 抽象理论定怎么算" 的分工一致.

### Gaps
- Bridge 1975, Isles 1970, Pfeiffer 1964 的正文都没有读到. Bridge 页只有节选. Isles 只有书目与 Miller 的摘要. Pfeiffer 1964 只见 Bridge 的引用.
- Weyhrauch 1972 的博士论文 (Stanford) 本轮没有定位到.
- Aczel 1972 的主定理仍未读 (付费, R4 已记).
- 没有找到 Bachmann 一系里层号超限 (Ω_ξ, ξ ≥ ω) 的原文. 按 Miller 的摘要, Isles 用的是有限数类. "未找到" 不等于 "不存在".
- 抓取 Rathjen 的 ICM 2006 综述 "The art of ordinal analysis" (Leeds 主机) 时 DNS 失败, 他对 Bachmann 方法的转述没有读到. 书目页: [EMS Press](https://ems.press/books/standalone/21/387).

## 问题 2: 层号是序数的折叠函数: 层号怎样进入定义与分情形, 有没有 "对层号一致" 或 "层号是树" 的写法

### Takeaway
序数下标的 ψ 一系都在集合论里把层取为正则基数. 这一系包括 Buchholz ψ_ν (ν ≤ ω), Buchholz–Schütte 1983, Jäger 1984 的 ρ-inaccessible, Pfeiffer 1992 的 Mahlo 层, 以及社区的扩展 Buchholz. 层号是记号项, 分情形比较层号 (cof(β) 与 π 的序), 而这个序在递归记号上可判定. 有三点可借:
1. 只有正则层作 ψ 的下标. 奇异的 Ω_ξ (ξ 是极限) 只作上确界出现.
2. 基本列只需 "低于 / 不低于" 两支. 同层与高层由同一条从 Ω_μ 起的链处理.
3. 层号集可以作外部参数 (Okada 的 OT(I), Takeuti–Kino 的 O(I,A)), 且系统对层号集连续.

没有找到层号是树的写法, 也没有找到派发时不判定层号序的写法.

### Cited Findings
- **Buchholz ψ_ν 的基本列** [二手]. 层号 ν ≤ ω. 规则 5: cof(β) ∈ {ω} ∪ {Ω_{μ+1} : μ < ν}, 即参数在目标层之下, 按点取 β[η]. 规则 6: cof(β) ∈ {Ω_{μ+1} : μ ≥ ν} 时, cof(α)=ω, α[η] = ψ_ν(β[γ[η]]), 其中 γ[0]=Ω_μ, γ[η+1]=ψ_μ(β[γ[η]]). **同层 (μ=ν) 与高层 (μ>ν) 是同一条规则** — [Wikipedia, Buchholz psi functions](https://en.wikipedia.org/wiki/Buchholz_psi_functions). 分派要判定 μ<ν; 层号是 ≤ ω 的数字, 可判定.
- **扩展 Buchholz (Maksudov)** [二手, 无出处]. Ω₀=1, ν>0 时 Ω_ν=ℵ_ν. 极限是 "first omega fixed point" 的 ψ₀ — [同页 Extension 一节](https://en.wikipedia.org/wiki/Buchholz_psi_functions). 本地 EBO 已覆盖, 不重述. 同页说这一做法后来由 Jäger 与 Schütte 推广, 引用 Buchholz–Schütte 1983 (*Sitzungsberichte der Bayerischen Akademie der Wissenschaften*, 讨论 Π¹₂-分离与 Bar 归纳; 页上题名有 OCR 错字, 卷页未给) 与 Buchholz 1986 (*APAL* 32, 195–207, DOI 10.1016/0168-0072(86)90052-7) [书目].
- **Jäger 1984** [书目已核; 内容为二手]. G. Jäger, "ρ-inaccessible ordinals, collapsing functions and a recursive notation system", *Archiv für mathematische Logik und Grundlagenforschung* 24 (1984) 49–62, DOI 10.1007/BF02007140, Zbl 0545.03031 — [Mathdoc 书目](https://geodesic.mathdoc.fr/item/AMLG_1984__24_138022). 正文在 Springer 付费墙后, zbMATH 页返回 403. 下面的定义取自社区 wiki 的镜像 — [Cantor's Attic 镜像](https://neugierde.github.io/cantors-attic/J%C3%A4ger%27s_collapsing_functions_and_%CF%81-inaccessible_ordinals) [二手, 社区]:
  - **ρ-inaccessible 的定义**: 正则, 且对一切 α<ρ 是 α-inaccessible 的极限. 0-inaccessible 就是 >ω 的正则基数.
  - **枚举函数**: I_α = Enum({β ∈ R : ∀γ<α, I_γ(β)=β}), 其中 R 是 (ω, M₀) 中的正则序数.
  - **ψ_κ 的下标**: 只取 κ ∈ R, 即正则序数. 页上没有定义 Ω_ξ.
  - **闭包 C_κ(α) 的规则**: (1) {κ⁻} ∪ κ⁻ ⊆ C⁰; (3) 对 I_β(γ) 封闭; (4) 若 γ<π<κ 且 π ∈ C, 则 γ ∈ C; (5) 若 γ<α, γ, π ∈ C 且 γ ∈ C_π(γ), 则 ψ_π(γ) ∈ C. 定义 ψ_κ(α) = min{ξ : ξ ∉ C_κ(α)}.
  - **基本列**: ψ_π(β) 按 "ω ≤ cof(β) < π" 与 "cof(β)=ρ ≥ π" 分两支. 极限 λ 的基本列为 λ[η+1] = I(λ[η], 0).
  - 同页自己列了疏漏: φ(0,0) 一条有笔误; 基本列的分情形没有声明穷尽.
- **Pfeiffer 1992** [摘要]. H. Pfeiffer, "A Notation System for Ordinal Using Ψ-Functions on Inaccessible Mahlo Numbers", *Mathematical Logic Quarterly* 38(1) (1992) 431–456, DOI 10.1002/malq.19920380142 — [Crossref](https://api.crossref.org/works/10.1002/malq.19920380142). 摘要说:
  - Jäger 的系统建在 inaccessible 正则序数的层级 I_αβ 上, 遇到满足 I_α0 = α 的 α 就停.
  - Pfeiffer 加上一层 weakly inaccessible Mahlo 数, 并对成对的序数沿一个良序递归.
- **Okada 1987** [摘要]. M. Okada, "A simple relationship between Buchholz's new system of ordinal notations and Takeuti's system of ordinal diagrams", *JSL* 52(3) (1987) 577–581, DOI 10.2307/2274350 — [Cambridge](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/simple-relationship-between-buchholzs-new-system-of-ordinal-notations-and-takeutis-system-of-ordinal-diagrams/F2CD0CB342380A4C93661B5EC9690E0A).
  - 定义两套系统 OT(I) 与 OT(I,A), 其中 I, A 是良序集.
  - "The original system OT of Buchholz [4] is OT(ω + 1, {0}) in our sense."
  - OT(I) ⊆ Kino 的 Od(I); OT(I,A) ⊆ Takeuti 的 O(I,A).
  - 层号的表示: 外给良序集 I 的元素. 正文付费, "关系" 是嵌入还是同构**未核**.
- **Takeuti–Kino 的 ordinal diagrams** [检索摘要].
  - Kino 1961, "On ordinal diagrams" (*J. Math. Soc. Japan*), 从带首元的良序集 I 构造 O(I,A) — [Project Euclid](https://projecteuclid.org/download/pdfview_1/euclid.jmsj/1261062619).
  - 另一篇 "Some properties of ordinal diagrams" (DOI 10.1017/S0027763000021838, 作者未核): 对递增的良序集 I_n, O(I_n, A_n) 嵌入 O(I_m, A_m) (n<m), 并集是 O(I,A). 链接主机 DNS 失败, **未打开**.

### Inferences
- [推断] **奇异层不作分支层.** 本项目龙骨 Ω, Ω_Ω, Ω_{Ω_Ω}, … 上, 层号为极限树的 Ω_ℓ 对应集合论的奇异基数.
  - 在 Jäger 系统里, ψ_κ 只对正则 κ 定义, 奇异层只作上确界出现. 它的基本列取下标 ℓ 的共尾: Ω_Ω = sup_{ξ<Ω} Ω_ξ 的共尾是 Ω₁, 所以 Ω_Ω 是 Ω-极限, 按低层树分支 (这是集合论常识, 不是从 Jäger 原文读出的).
  - R1 记过 Buchholz 1987 把 Ω_ω 写成 ℕ-极限. Jäger 的规则把同一做法推广到一切奇异层.
  - 对本项目: "龙骨上的极限层用下标的极限表示, 不作分支层" 有文献对应, 而且不涉及比较层号.
- [推断] **两支派发.** Buchholz 规则 5/6 只问 "μ < ν 还是 μ ≥ ν". 同层与高层是同一条链: 链从 Ω_μ 起, 每步把 ψ_μ 的输出回灌给 β. 对本项目的含义:
  - "同层对角" 与 "高层走链" 或许能合成一条, 只要 "不低于" 与链的起点 Ω_μ 由字面证据给出 (例如 μ 在目标龙骨位置之上的路径).
  - 这样派发少一支需要证据的分支. [判断, 未在树上检验]
- [推断] **下行闭包代替 "保留" 派发.** 在集合论版本里, "低于目标: 保留" 不是一条派发规则, 而是闭包的性质: Jäger 规则 4 与 Buchholz 的 Ω_ν ⊆ C_ν(α) 保证低层序数都在闭包里. 树侧的对应写法是: 目标层的读回域在类型上就包含一切低层合法树, 由构造给出. 那样就不必在每个结点判定 "是否低于". 这与 "按存在性保留" (AGENTS 先验检查第三条) 同向.
- [推断] **层号集作参数.** OT(I) 的规则对 I 一致, 比较 I 的元素用 I 自带的序. 把 I 取为前一阶段的系统 (I := OT(I′)), 就是 "层号由系统生成" 的一步.
  - 迭代到不动点的序型大概是 ψ₀(Ω_Ω) 量级, 因为 ψ₀(Ω_Ω) 是 ν ↦ ψ₀(Ω_ν) 的最小不动点 [推断, 未核文献].
  - 在记号侧, I 上的序可判定. 在树侧, I 上的序就是前一阶段的树序, 正好落在壁垒上.
  - Kino/Takeuti 的 "对 I 连续" (O(I_n) 嵌入 O(I_m), 并集为 O(I)) 对应跨层嵌入. 但 `stage-current` 记有 "跨层单调接口被否定", 借之前要先对照那条否定定理的前提.

### Gaps
- Jäger 1984 原文未读. 定义来自社区 wiki, 基本列规则的穷尽性与 κ⁻ 在极限处的定义都未核.
- Buchholz–Schütte 1983 未读. Rathjen 一系的折叠 (KPM, Π¹₂ 等) 本轮未查.
- Weiermann 与 Wilken 的初等子结构方法本轮未查 (R4 已记 patterns 一支).
- "Some properties of ordinal diagrams" 未打开 (DNS 失败). Okada 1987 正文付费.
- 没有找到 "对层号一致, 且不判定层号序" 的折叠. 也没有找到层号是树 (而不是记号项或基数) 的折叠.

## 问题 3: 自治迭代归纳定义与到 ψ₀(Ω_Ω), ψ₀(Ω_{Ω_Ω}) 的理论: 系统内部生成的层号在序数分析里怎样处理

### Takeaway
找到的自治迭代原文是**不动点版** Aut(ÎD) (Strahm 2000), 序数 φ200, 即使 |ÎD_{<α}| = α 的最小 α. **归纳定义版** Aut(ID) 的序数 ψ₀(Ω_Ω) 只在 Wikipedia 表里见到, 没有出处. 内部层号的处理方式有三条:
1. 层号只能带证据进入: 先有一个 WO(◁) 的证明, 才能沿 ◁ 迭代.
2. 上界论证不依赖层号的表示.
3. 下界的基本列逐步把上一步的序数回灌作迭代长度.

没有找到用 Ω_ξ-规则 (ξ 由推导生成) 的分析, 也没有找到到 ψ₀(Ω_{Ω_Ω}) 的理论.

### Cited Findings
- **Strahm 2000** [原文·读 pp.1–3, 5–7]. T. Strahm, "Autonomous fixed point progressions and fixed point transfinite recursion" (Bern 主页 PDF, 2000; 刊处**未核**, PDF 首页没有刊名) — [PDF](https://home.inf.unibe.ch/ltg/publications/2000/str00a.pdf).
  - **规则**: Aut(ÎD) 在 PA 上加两条推理规则. "自治不动点层级生成规则": 由 TI(◁,U) 推出 (∀a∈field(◁))(∀x)[P_a^{𝒜,◁}(x) ↔ 𝒜(P_a^{𝒜,◁}, P_{◁a}^{𝒜,◁}, x, a)]. bar 规则: 由 TI(◁,U) 推出 TI(◁,A). 这里 ◁ 是原始递归线序, 语言对每对 (𝒜, ◁) 有一个关系符号 P^{𝒜,◁} (p.5).
  - **序数**: Theorem 2, |Aut(ÎD)| = φ200, 即使 |ÎD_{<α}| = α 的最小 α. 下界的基本列取 α₀ = ε₀, α_{n+1} = φ1α_n0, 再用 ÎD_α 的结果 (Theorem 1).
  - **上界对层号表示一致**: 上界论证 "do not depend on the specific representation of the ordering" (p.5).
  - **嵌入的做法**: Theorem 3 证 Aut(ÎD) ⊆ FTR₀ 时, 对每个证明归纳翻译. 关键一步是解释证明里引入的 P^{𝒜,◁}: 由归纳假设, WO(◁) 在 FTR₀ 中可证, 于是由 (FTR) 得到这个层级 (p.7).
  - **外部自治与内部自治**: Aut(ÎD) 要先有一个已认可的良基证明 ("external"); FTR 对任意良序 ("internal"), 不要求证明. 只要自然数归纳限于集合, 两者强度相同: FTR₀ 也是 φ200. 带完全公式归纳的 FTR 是 φ20ε₀ (pp.2, 6–7).
  - **上界方法**: 在 KPh⁰ (无基础公理, 递归 hyperinaccessible 宇宙) 里建模 (pp.2–3).
- **Aut(ID) = ψ₀(Ω_Ω)** [二手, 无出处]. Wikipedia 的序数分析表把 Aut(ID) 列在 ψ₀(Ω_Ω), 脚注 g 不带引用. 同表的相邻行:
  - ψ₀(Ω_{ε₀}) 对应 ID_{<ε₀} 等;
  - ϑ(Ω_Ω) 对应 TID 等;
  - 没有 Ω_{Ω_Ω}, ψ(Λ) 或 "α ↦ Ω_α 的第一个不动点" 的行.

  来源: [Wikipedia, Ordinal analysis](https://en.wikipedia.org/wiki/Ordinal_analysis). nLab 的表只有 Aut(ÎD) (在 φ(2,0,0), 同列 KPh⁰), 没有 Aut(ID) — [nLab, ordinal analysis](https://ncatlab.org/nlab/show/ordinal+analysis) [二手].
- **Buchholtz 2013** [摘要]. U. Buchholtz 的 Stanford 博士论文 *Unfolding of systems of inductive definitions* 用 operator-controlled 推导分析 ID₁ 的展开, 摘要里没有 Aut(ID) 或 ψ(Ω_Ω) — [Stanford](https://purl.stanford.edu/kg627pm6592).
- **超限迭代的层号取自外给良序** (R2 已记, 这里只引结论): SEP 说 ID_ν 的 ν 是原始递归良序; Buchholz 的 Ω_{μ+1}-规则以 μ 为记号 — [SEP, Proof Theory](https://plato.stanford.edu/entries/proof-theory/).

### Inferences
- [推断] **自治就是输出回灌作层号.**
  - Aut(ÎD) 的序数是 α ↦ |ÎD_{<α}| 的最小不动点. 下界基本列 α_{n+1} = φ1α_n0 每步用上一步得到的序数作迭代长度.
  - 记号侧 ψ₀(Ω_Ω) 的基本列同形: 第 n+1 项是 ψ₀(Ω_{第 n 项}). 列在这里只作对照, 不进定义.
  - 对本项目: 折叠在高层 "走链, 输出回灌作下标", 对应证明论里的自治规则. 序数分析处理它的方式是 "层号必须带一个已认可的良基证明", 而不是比较层号.
- [判断] **证据影响能否算, 不影响到哪里.** 外部自治 (要证明) 与内部自治 (任意良序) 在自然数归纳只对集合时强度相同 (Strahm Thm 2, 3 与 Cor 1: Aut(ÎD) 与 FTR₀ 都是 φ200). 对本项目: 带证据的层号 (framed) 与理想化的裸层号可能到达同一个序数, 证据只决定定义能不能写出来. 这支持 "带证据的读回域" 不损失强度, 但只是类比, 未在树上检验.
- [推断] **对表示一致的上界.** Strahm 的上界不依赖 ◁ 的具体表示, 只依赖序型. 这是 "与阶段无关的整体定理" 在证明论里的形状: 定理以任意 (带证据的) 层号为参数. 对本项目, 对应的是 "以任意带框层号为参数的一步定理", 而不是逐层定制.
- [判断] **ψ₀(Ω_{Ω_Ω}) 的证明论对应物**, 大概是 "迭代长度可以取自已建立的不可数层对象" 的二阶自治, 而不只是可数良序. 本轮没有文献.

### Gaps
- Aut(ID) (归纳定义版) 的定义与 ψ₀(Ω_Ω) 的原始出处: 未找到. Wikipedia 脚注无引用, nLab 无此行.
- 到 ψ₀(Ω_{Ω_Ω}) 的任何理论或分析: 未找到.
- 层号由推导内部生成的 Ω_ξ-规则分析: 未找到. Towsner 2009 说 Buchholz 的 Ω_μ-规则推广有限 (R2 已记).
- Strahm 2000 的刊处未核. 它引用的 Jäger–Kahle–Setzer–Strahm (ÎD_α 的分析) 未读.

## 问题 4: coquand/agda-ordinal-analysis-id1: Ω 分支前提的类型, operator control 的编码, collapse 的定义与停机

### Takeaway
这个演算是 Freund 讲义的 local predicativity 式演算, 没有 Buchholz 式的 Ω-规则. 所有无穷分支都由一个构造子 `dCnj` 表达: 前提按记号项 g 编号, g 满足 `nfT g ≡ true` 与 `lt g (arity X) ≡ true`. 阶段谓词 ¬I^{<a}t 的 arity 就是 a, 所以 a = Ω 时对一切 g<Ω 分支. operator control 是 Bool 递归 `memO`. `collapse` 对推导结构递归, 在无穷分支处逐点变换前提, 不判定 g. 它唯一的分派按调用者给的**覆盖证据**做. 无 LICENSE, 只能借思路.

### Cited Findings
- **版本与许可** [原文·抓取].
  - 仓库只有两次提交: `5db10ba` (2026-09-30) 与 `1f977e0` (2026-11-02, 消息称 83 模块在 Agda 2.8.0 下检查通过) — [GitHub API](https://api.github.com/repos/coquand/agda-ordinal-analysis-id1/commits?per_page=3).
  - 根目录没有 LICENSE 文件 — [仓库首页](https://github.com/coquand/agda-ordinal-analysis-id1). 与 `CodeGuide.md` 的记录一致: 无 LICENSE, 只借思路.
  - 模块都在 `IDHAT/` 下.
- **演算的形状** [原文·抓取] — [`IDHAT/Inf/BHCalc.agda`](https://github.com/coquand/agda-ordinal-analysis-id1/blob/main/IDHAT/Inf/BHCalc.agda).
  - 选项 `--safe --without-K`. 模块以公式 `oA` 与 `noI oA ≡ true` 为参数.
  - `Der : Oper -> T -> T -> Seq -> Set`, 四个参数依次是算子, 高度, 切秩, 序列.
  - 构造子: `dCnj` (合取型, 兼作 ω-规则与阶段分支), `dDsj`, `dCut`, `dFix`.
  - `dCnj` 的前提类型 (原文):
    ```
    ((g : T) -> Eq (nfT g) true -> Eq (lt g (arity X)) true ->
       Sigma T (\ b -> And (Eq (lt b a) true)
                           (Der (adjO H g) b r (cons (sbF X g) G))))
    ```
    分支域是 "满足 Bool 条件的记号项", 不是低层树. 每个前提自带高度 b<a, 并在扩张后的算子 `adjO H g` 下.
- **arity 统一三种分支** [原文·抓取] — [`IDHAT/BHFml.agda`](https://github.com/coquand/agda-ordinal-analysis-id1/blob/main/IDHAT/BHFml.agda).
  - `arity (fall X) = omegaT`: 数量词, 按 ω 分支.
  - `arity (fI a t) = a`: 阶段谓词按其阶段分支.
  - `arity (fand X Y) = twoBH`: 合取, 两个分支.
  - 原子公式的 arity 是 `zeroT`, 没有前提.
  - 对应的实例化: `sbF (fnI a t) g = fnf (opAt g t)`, `sbF (fall X) g = inst0 (toNat g) X`.
  - 所以 ¬I^{<Ω}t 的前提族就是 "对一切 g<Ω 的记号项", 起 Ω-分支的作用.
  - Σ(Ω) 判定: `sigOm (fnI a t) = notB (eqT a omg)`.
- **operator control** [原文·抓取] — [`IDHAT/BHOp.agda`](https://github.com/coquand/agda-ordinal-analysis-id1/blob/main/IDHAT/BHOp.agda).
  - 算子是 `record Oper` (构造子 `mkOp`), 字段为基序数 `opIx : T` 与有限参数表 `opZ : List T`.
  - `memO (mkOp a Z) x = inH a Z x` 是对 θ-子项的 Bool 结构递归. `adjO (mkOp a Z) g = mkOp a (cons g Z)`.
  - 文首说 Def 3.10 那个对集合类的交 "is NOT formalised here". 作者不声称这个递归算的就是那个交, 只验证分析需要的律.
  - 每个构造子带 `Eq (ctrl H a G) true`, 其中 `ctrl H a G = andB (nfT a) (andB (memO H a) (kSeq H G))`.
  - `dFix` 要求 `le omg a`. 文首注释说正是 Ω ≤ a 这个条件, 使高度低于 Ω 的折叠推导里不出现该规则.
- **collapse 与停机** [原文·抓取] — [`IDHAT/Inf/BHCut.agda`](https://github.com/coquand/agda-ordinal-analysis-id1/blob/main/IDHAT/Inf/BHCut.agda).
  - `collapse` 的结论是 `Der (mkOp (etaOf zeroT b) nil) (th (etaOf zeroT b)) …` (Corollary 7.2), 它只是 `collD` 的薄包装.
  - `collD` 的签名把两个下标分开: `(a0 a : T) (X : List T) -> Eq (le a0 a) true -> … -> Der (mkOp a0 X) b (sucT omg) G -> Der (mkOp (etaOf a b) X) (th (etaOf a b)) (th (etaOf a b)) D`. 注释说 "Separating the two indices removes the weakening", 因此递归保持结构.
  - `dCnj` 子句先做 `orL (cov p i) plain lowered`, 再定义 `prem m nm q = go (f m nm q)`. `go` 把高度换成 `th (etaOf a b')`, 并对子推导递归调用 `collD` (参数表加上 m).
  - **对 g 不作任何判定**: m 只往下传, `lt m (arity p)` 只作假设喂给 f.
  - 分派依据是覆盖证据 `CovC G D = (X : Fml) -> In X G -> Or (In X D) (NegLow X D)`. 注释说 NegLow attaches the stage d "to the FORMULA, not computed from the height".
  - `dFix` 与 Ω-切 (`cutOmg`) 在别的子句处理, 经 `bndOne` (boundedness, Thm 5.9) 把 `fI omg t` 降到阶段 `th (etaOf a b')`.
  - 记号的良基性只在 `Inf/BHSound` 作前提 (CodeGuide 已记).

### Inferences
- [推断] **R2 的猜测已证实.** Ω 分支按记号项 g ≺ Ω 编号, 不按低层树. 折叠中凡比较的地方 (`lt`, `le`, `eqT`) 都比较记号项, Bool, 可判定. 所以它的 collapse 不能作为本项目的定义 (纲领 4), 但其中三处组织方式与项目约束相容.
- [推断] **证据派发.** `collD` 在无穷分支处不判定分支下标. 它只按调用者给的覆盖证据分两支, 降低后的阶段作为数据附在公式上, 不由高度算出. 这是 "派发读证据, 不读比较" 的现成写法. 证据在 collapse 的入口一次给出 (`CovC G D` 管整个序列), 沿推导传下去. 与 framed keep 同向: 证据的类型是 "在 D 里, 或有一个带阶段的降低副本", 是一个二选一的字面见证.
- [推断] **两个下标, 一个不等式证据.** 把 "推导所在算子的下标 a0" 与 "折叠下标 a" 分开, 只带 a0 ≤ a 的证据, 去掉了 weakening, 使 Agda 看到结构递归. 对本项目: 子树建成时的层 (或框架) 与目标层分成两个参数, 用证据连接, 不为换框架而重建子树. 重建子树正是终止检查失败的常见来源.
- [推断] **只验律, 不证同一.** `memO` 是可计算的 Bool 近似, 作者只验证分析需要的律, 不声称它就是集合论的定义. 这与 AGENTS "律由抽象接口检验" 一致, 是一个已检查通过的先例.
- [推断] **arity 统一构造子.** 用一个以序数项为 arity 的构造子统一 ℕ-分支, 有限分支与 Ω-分支. 在树侧对应 "一个极限构造子, 定义域类型由层号计算". 本项目现在分开写 ℕ-极限与 Ω-极限, 这一写法是否更好未评估. [判断]

### Gaps
- `notes/` 目录下的两篇说明本轮没有读.
- `collD` 的 `lowered` 分支与 `cutOmg` 的细节只读了摘要式转述.
- `etaOf`, `kStg` 的定义没有读到 (不在 `BHOp`).

## 问题 5 (综合): 逐来源对照与可迁移装置

### Takeaway
文献里层号可变的系统全都比较层号, 比较是在记号项或集合论基数上做的, 可判定. 与 R1–R4 一致, 没有找到层号是树、或由系统生成而折叠不判定层号序的先例. 可借的是让比较不必发生的组织方式, 下表与推断列出八条, 每条都要先对照壁垒与 `obs→dec` 一族再派.

### Cited Findings
| 来源 | 方法 | 层号的表示 | 低 / 同 / 高的分派与可判定性 | 可借装置 | 档位 |
|---|---|---|---|---|---|
| Bachmann 1950 ([arXiv:1903.04609](https://arxiv.org/abs/1903.04609)) | 正规函数族, 极限下标带 distinguished sequence | 种类 (长度 ω 或 Ω) 附在下标上 | 读种类: ω-极限取交, Ω-极限 φ_{η_x}(1) 对角; 可判定 | 种类即数据 | 原文·抓取 (英译) |
| Pfeiffer 1964, Isles 1970, Miller 1976 ([Miller](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/normal-functions-and-constructive-ordinal-notations/737928AEF6123F3EBC244026F542F515)) | 用更高的有限数类加长 Bachmann 序列 | 有限数 n (Ω_n) | 比较数字; 可判定 | 下标总比函数高一类 (关系由类型固定) | 摘要 |
| Bridge 1975; Feferman–Weyhrauch; Aczel 1972 ([Bridge](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/simplification-of-the-bachmann-method-for-generating-large-countable-ordinals/4422E482B6FE458ACB23558952D6C179)) | 去掉基本列 | (未读到) | (未读到) | 规格与计算分开 | 摘要 |
| Feferman θ ([Wikipedia](https://en.wikipedia.org/wiki/Ordinal_notation)) | 闭包 C(α,β) | Ω₁…Ω_ω 作生成元 | 定义里无派发 | 闭包刻画作验收规格 | 二手 |
| Buchholz ψ_ν, ν≤ω ([Wikipedia](https://en.wikipedia.org/wiki/Buchholz_psi_functions)) | 闭包式折叠加结构基本列 | 数字 ν ≤ ω | 两支: μ<ν 按点, μ≥ν 走链 (同层与高层合一); 可判定 | 两支派发, 链起点 Ω_μ | 二手 |
| Jäger 1984 ([书目](https://geodesic.mathdoc.fr/item/AMLG_1984__24_138022)) | ρ-inaccessible 层级 I_α(β) 加 ψ_κ | 正则基数, 记号项 | cof(β)<π 或 cof(β)=ρ≥π; 递归记号上可判定 | 只有正则层作下标; 下行闭包 (规则 4) | 书目已核, 内容二手 |
| Pfeiffer 1992 ([Crossref](https://api.crossref.org/works/10.1002/malq.19920380142)) | 加 Mahlo 层; 对序对的良序递归 | 记号项 | 未读 | (无新装置) | 摘要 |
| Okada 1987 OT(I) ([Cambridge](https://www.cambridge.org/core/journals/journal-of-symbolic-logic/article/abs/simple-relationship-between-buchholzs-new-system-of-ordinal-notations-and-takeutis-system-of-ordinal-diagrams/F2CD0CB342380A4C93661B5EC9690E0A)) | Buchholz 系统以任意良序 I 为层号集 | 外给良序集 I | 用 I 的序; 可判定 | 层号集作参数; I := 前一阶段 | 摘要 |
| Kino 1961, Takeuti O(I,A) ([Kino](https://projecteuclid.org/download/pdfview_1/euclid.jmsj/1261062619)) | ordinal diagrams | 外给良序集 I | 用 I 的序 | 对 I 连续 (直接极限) | 检索摘要 |
| Strahm 2000 Aut(ÎD), FTR ([PDF](https://home.inf.unibe.ch/ltg/publications/2000/str00a.pdf)) | 自治不动点迭代 | 原始递归良序 ◁, 需 WO(◁) 的证明 | 不比较层号; 层号带证据 | 层号带良基证据; 上界对表示一致; 回灌 | 原文·读 |
| Aut(ID) ([Wikipedia](https://en.wikipedia.org/wiki/Ordinal_analysis)) | 归纳定义版自治 | 未知 | 未知 | 序数 ψ₀(Ω_Ω) 的定位 | 二手, 无出处 |
| coquand id1 ([GitHub](https://github.com/coquand/agda-ordinal-analysis-id1)) | Agda 无穷演算加 collapse | 记号项 (Bool 序) | 无穷分支处不判定; 按覆盖证据分支 | 证据派发; 两下标加不等式证据; 只验律 | 原文·抓取 |

### Inferences
可迁移装置, 按与本项目约束的距离排序. 都是 [推断], 未在树上检验:
1. **证据派发** (coquand `CovC`/`NegLow`). 折叠入口一次性接受 "每个子项在哪一侧" 的二选一见证, 沿结构传下去, 无穷分支处不判定分支下标. 与 framed keep 最近.
2. **两个下标加不等式证据** (coquand `collD`). 子树所在层与目标层分开, 只带 ≤ 的证据. 用来保持结构递归, 避免重建子树.
3. **奇异层不作分支层** (Jäger; R1 的 Buchholz 1987). 龙骨上的极限层 Ω_ℓ 以 ℓ 的极限表示, 只有 "后继型" 层号才有折叠规则. 这一条不需要比较.
4. **下行闭包代替 "保留" 派发** (Jäger 规则 4, Buchholz Ω_ν ⊆ C_ν). "低于目标就保留" 写成读回域在类型上的包含, 不写成结点处的判定.
5. **两支派发** (Buchholz 规则 5/6). 同层与高层合成一条从 Ω_μ 起的链, 只剩 "低于 / 不低于" 两支. 前提是 "不低于" 要有字面证据.
6. **层号带良基证据, 上界对表示一致** (Strahm). 层号以 "已认可的证明" 进入, 整体定理以任意带证据的层号为参数. 归纳只对集合时, 外部自治与内部自治同强度, 提示证据不损失强度.
7. **层号集作参数, 对层号集连续** (Okada OT(I), Kino/Takeuti O(I,A)). 层号集取前一阶段即自治. 但跨层嵌入的接口要先对照 `stage-current` 里的否定.
8. **种类即数据, 相对位置编进类型** (Bachmann–Isles). 风险最大: 换目标要重新标记.

### Gaps
- 本轮所有 "层号可变" 的原文 (Isles, Pfeiffer 1964, Bridge, Jäger, Buchholz–Schütte) 都没有读到正文, 只有书目、摘要或二手转述. 下一步若要核实, 优先级: Jäger 1984 (定义与基本列), Bridge 1975 (简化的机制), Okada 1987 (OT(I) 的定义).
- "没有先例" 是在本轮检索范围内的判断, 只用了通用术语检索. 未找到不等于不存在.
