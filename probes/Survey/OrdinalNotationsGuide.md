# 从 EBO 经 I、χ 到 M 的序数记号: 查阅手册

> 证据记录在 [OrdinalNotationsFS.md](OrdinalNotationsFS.md) (下文写作 "调研 §n"), 本文只放结论, 不讲经过. **外部代码按用途查、项目卡片、已否定的问题、待试清单与许可边界在 [CodeGuide.md](CodeGuide.md).** 状态日 2026-11-02; 除另注明外, 所有链接与仓库头的访问日期都是这一天, 链接集中在文末 [§9](#9-链接表).

**来源层级** (每条事实带一个):

| 标记 | 含义 |
|---|---|
| **机检·我方** | 本项目 Agda 代码; 本手册编写时没有重新编译 |
| **机检·已构建** | 他人的 Lean 代码, 我们在写明的提交和工具链上构建过, 公理来自 `#print axioms`. 目前只有 `ExBuchholz` (§5.2, 复现见 §8) |
| **机检·只读** | 他人的 Lean/Isabelle/Agda 代码; 我们读过源码或 README, **从未构建**. "无 sorry" 都是文本检索, 不是 `#print axioms` |
| **同行评审** | 正式发表的论文 |
| **人工证明(社区)** | 社区博客写出了证明, 未经第二人核查 |
| **测试** | 我方脚本的有限样本, 不是证明 (§8 可重跑) |
| **社区无证明** | 社区定义或声称, 没有证明 |
| **推断** | 我方的推理 |

## 1. 一页结论

| 层 | 最好的定义 | 最好的证明状态 | 我们用什么 |
|---|---|---|---|
| **EBO** ($\psi_0(\Lambda)$) | p進大好きbot 记号; koteitan `ExBuchholz` 与我方 `EBO.lagda.md` 的项、序、基本列看来逐项相同 (**测试**与逐分支阅读, 未形式证明, §5.3) | **机检·已构建** (Lean 4.30.0, `6da2de5`, 公理见 §5.2): 标准形封闭 `OTFS_thm`, 递减 `fs_lt`, 单调 `fs_mono`, 共尾 `exists_lt_fs_numeral`, 秩等于值 `rank_exbOT_eq_val`, 同构 `valEquiv`, 良基 `OTLt_wf`. 良基走语义路线, 依赖 mathlib 序数, `Classical.choice` 是实质依赖; 封闭性里的 `Classical.choice` 是两处偶然用法, 可去 | 定义用我方 `EBO`; 校准与封闭性证明的蓝本用 `ExBuchholz`. **构造性良基性仍无**: 要走 EBO → OT_I 嵌入 (§6.1); 第二条路是 $W_u$, 现成证明只到 $\psi_0(\Omega_\omega)$ (§6.1 末) |
| **I** | 递归标准形 + 结构列 + 无 φ: みずどら; 单个 $I$ 的保守扩张: 我方 `EBOI`; 最简规则: $T_W$; 带 φ 的序: Setzer OT_I | **人工证明(社区)**: みずどら 的封闭、递减、序同构. **机检·只读**: `InaccPsi` 的 NF 良序与完备性 (假设 `InaccSeq`, **无基本列**). **机检·我方**: OT_I 的 `wellfounded` (构造性, 无基本列); `EBOI` 的保守性. **测试**: `EBOI` 新规则 | 标尺用 `EBOI`; 交叉核对用 みずどら; 良基性指向 OT_I, 但 OT_I 只到 $\psi_{\Omega_1}\Omega_{I+\omega}$ |
| **χ** | 规则形状: KawamoYurase 重写的 Maksudov 系统 (无 φ, 序情形完备); 严肃程度: *Rathjen-type* (Naruyoko 实现驱动), Exmachina *Rathjen Small ψ* | **同行评审**: Rathjen 1990/1991 的 $T(M)$ (序与项, **无基本列**), BCW 1994 的范数式基本列. 结构列: **无证明**, 只有 **测试** 与实现调试 | 形状抄 KawamoYurase, 用 *Rathjen-type* 与 Exmachina 交叉检验 (这两家闭包含 $\Phi$, 值不同, 只能比序嵌入, 不能比展开, 见 §3 末). 没有可信赖的单一来源 |
| **M** | 同上; 分派见 §4.3 | 同上. **机检·只读**: `bms-rathjen` 有 $\mathfrak T(M)$ 的项、序、标准形与 `fsN` 定义, **M 处递减与封闭未证**, 且一元 χ 写不出 $\Omega_2$. 良基: Rathjen 1994 **同行评审, 未读全文** | 同 χ 层; BCW 范数列作支配性对照. **M 层没有带证明的结构基本列** |

三条总判断:

1. EBO 以下问题已解决, 但只在 Lean + mathlib 的语义路线上解决 (封闭性一半是句法的). 我方相对优势是 `--safe` 与树侧, 不是 EBO 记号本身 [推断].
2. 从 EBO 到 M 没有一套系统同时满足"贴合 EBO"与"严格": 最贴合的是 Maksudov/KawamoYurase (无 φ), 最严格的是 *Rathjen-type*/Exmachina (φ 原语), 两者不重合 [推断].
3. BMS 类与 ψ 的比较本身未证, 不作标尺 [推断]. 依 p進大好きbot 引 Rathjen 1990 Thm 6.3, $T(M)\cap M$ 只到 $\psi_{\chi_{\varphi_1(M+1)}(0)}(0)$ 量级, 此上的社区"分析"没有算法支撑 [社区无证明, 该定理本人未核].

## 2. 术语

- **标准形** (normal form, OT/NF). 项集里真正代表序数的子集. 递归版是可判定谓词 (EBO 的 `G(X,Y)◃Z`); 语义版写成"$\alpha$ 可写成…" ($T_W$), 不能直接判定. 序只在标准形上是良序; 在全部项上 $\Omega>\psi_0(\Omega)>\psi_0(\psi_0(\Omega))>\cdots$ 无穷下降 (`not_wellFounded_lt`, 机检·只读).
- **结构规则 / 结构化基本列.** 按项的形状逐条定义 $t[n]$. 要证的是四件事: 输出在标准形内 (封闭), $t[n]<t$, 递增共尾, Bachmann 性质或正则性.
- **范数式基本列.** $\alpha[n]=\max\{\beta<\alpha:N\beta\le f(N\alpha+n)\}$, 有界搜索. 定义便宜, 证明现成 (BCW, 同行评审), 但不是结构规则, 也不与 EBO 规则逐项一致. 绝对界一般不满足 Bachmann 性质, 相对界才满足 (`archive/src/Mahlo/SOURCES.md` §82).
- **Bachmann 性质.** 经典义: BCW (B2), 控制 $\alpha[n]$ 与其间序数的基本列的关系, 是层级可用于支配论证的条件. **注意同名**: `ExBuchholz` 的 `Bachmann` 是另一件事, 指 $\forall x\in G_A(B),\ x<B[\psi_{Z[0]}(0)]$, 一个为封闭性服务的 $G$ 界 (Closure.lean:1134). 经典义的 Bachmann 性质在 `ExBuchholz` 里未见陈述 (文本检索) [推断], Wilken 2024 才证了它, 但只到 $\Pi^1_1\text{-CA}_0$ 且起点是 ϑ.
- **良基性.** 标准形上序的良基. 与规则无关: 规则封闭 + 递减 + 良基 才给出终止. 语义路线沿 $o:\mathrm{OT}\to\mathrm{Ord}$ 拉回, 经典; 构造路线要 `Acc` (OT_I 的做法); 另有不用序数值的 distinguished sets 路线 (pss-proof `OT_B_wellFounded`, §6.1 末).
- **保守扩张.** 新系统把旧系统的项嵌入, 序与基本列逐项不变 (连哑值也不变). `EBOI` 对 `EBO` 是保守的 (机检·我方). $T_W$、Maksudov 对 EBO 都不是.
- **序嵌入.** 只保序的映射 (τ). 足以拉回良基性, 不给基本列也不保值. 比保守扩张弱得多: Maksudov 系统有序嵌入 [测试] 但基本列只有 64% 相同.
- **共尾度分派.** 把项分到 0、后继、ω、不可数正则 ρ 四类再选规则的路由函数. 我方叫 `cof`, p進大好きbot 与 koteitan 叫 `dom`, みずどら 叫 dom, Maksudov 叫 `tp`. 同一个东西, 前者返回标记, 后者返回项 (§5.3 的 `h`).
- **$\psi_\nu$ 约定 (Buchholz 式).** 下标是序数位置 $\nu$, $\psi_\nu(\alpha)<\Omega_{\nu+1}$, $\psi_\nu(0)=\Omega_\nu$. EBO 用它. 优点: 与 $\Omega_0=1$ 配合, 规则最短. φ 由 ψ 表达.
- **$\psi_\kappa$ 约定 (Rathjen 式).** 下标是正则基数 κ, $\psi_\kappa(\alpha)<\kappa$, $\psi_\kappa(0)$ 取闭包缺口. 换算: $\psi_{\Omega_{\nu+1}}(c)\approx\psi_\nu(1+c)$ (Maksudov 系统, 推断), 这是"$-1+$"偏移与 §3 各种错位的来源.

## 3. 约定对照表

"γ₀" 指规则 6 型折叠链的起点. "转换" 指到我方 EBO 的换算. 比较都是在转写上跑的, 不是在对方代码上跑的.

| 系统 | $\Omega_0$ | $\psi$ 在 0 | γ₀ | 闭包 | φ | 标准形 | 基本列 | 到我方 EBO 的转换 |
|---|---|---|---|---|---|---|---|---|
| **我方 EBO** | $1$ | $\psi_u(0)=\Omega_u$, $\psi_0(0)=1$ | $\Omega_\mu$ | $+,\psi$ | 无 | 本文件无谓词; `EBOI` 的 `isOTᵉ` 递归 | 结构, `--safe` | 恒等 |
| **我方 EBOI** | $1$ | $+$ $\psi_I(0)=\Lambda$ | $\rho=I$ 时 $\Lambda$ | $+,\psi,\psi_I$, $I$ | 无 | 递归 `isNF` | 结构 | 保守扩张, 全部项上 (机检·我方) |
| **Buchholz 1986** | $1$ | $D_v0=\Omega_v$ | $D_u0$ (规则 6, 二手转录) | $+,D_v$ | 无 | 递归 $G_u(a)<a$ | 结构; 下标 $\le\omega$ | 祖先, 不逐项: $\omega[n]=n+1$ (我方 $n$), 后继乘 $n+1$ (我方 $n$) |
| **p進大好きbot EBO** | $1$ | 同我方 | $\langle Z[0],0\rangle=\Omega_\mu$ | $+,\psi$ | 无 | 递归 `G(X,Y)◃Z` | 结构 | 恒等, 只差写法 (调研 §11; 我方未对博客逐字重查, 经 koteitan 校准表间接) |
| **koteitan ExBuchholz** | $1$ | 同我方 | `psi (Z[0]) nil` | $+,\psi$ | 无 | 递归 `isOT`, `G` 校正后 | 结构, 全函数 | **逐项相同**, 见 §5.3 |
| **$T_W$** (Maksudov/Hyp cos) | $0$ | $\psi_\pi(0)=1$ 对所有 π | $1$ | $+,\Omega,I,\psi$ | 无 | **语义** | 结构 | $\tau$: $\psi_u(0)\mapsto\Omega_{\tau u}$, $\psi_u(a)\mapsto\psi_{\Omega_{\tau u+1}}(\tau a)$, 加修正 **A** ($\gamma_0:=\Omega_\mu$)、**B** ($\Omega_0:=1$)、**C** ($\psi_{\Omega_{\nu+1}}(0):=\Omega_\nu$) 后 EBO 段 9000/0 [测试]. I 层再差 $\psi_I$ 的 $1+a$ 偏移 |
| **みずどら** | 第一不可数 ($\psi_{\Omega_0}(0)=1$) | $\psi_\kappa$ 式 | $\psi_{\mathrm{dom}}(0)$ 型 | $+,\Omega,I,\psi$ | 无 | **递归** $\hat G_k(b)\lhd a$ | 结构 | 下标比 EBO 少 1, 差异 A 同型; 转换未测试 [推断] |
| **Kanrokoti** | $1$ | 同 EBO | 未核 | $+,\psi,I_a(b)$ | 无 | 按搜索定义, 非递归谓词 (CodeGuide §2) | 结构 | 直接扩展 EBO, 但没有 ψ_I (CodeGuide §2) [推断]; 未测试 |
| **Maksudov Mahlo** / KawamoYurase 重写 | $\chi(0,\alpha)=\aleph_{1+\alpha}$ | $\psi_{\Omega_1}(0)=1$; $\psi_{\Omega_{\nu+1}}(0)=\Omega_\nu\cdot\omega$ | $\psi_r(0)$ | $+,\chi,\psi$, M 上 $\omega^\delta$ | 无 | 递归 ($K_r,G,\star,\ominus$); Maksudov 序情形不完备, KawamoYurase 完备 | 结构 | $\psi_u(0)\mapsto\chi(0,-1+\tau u)$, $\psi_0(a)\mapsto\psi_{\chi(0,0)}(\tau a)$, $\psi_u(a)\mapsto\psi_{\chi(0,-1+(\tau u+1))}(-1+\tau a)$. 序嵌入 3000 项 40000 对无反例, **基本列 5726/8967 相同** [测试, 打 P1/P2 补丁后的 Maksudov; KawamoYurase 未测] |
| ***Rathjen-type*** (p進大好きbot, Naruyoko) | 未单列 | $\psi_{\Omega_1}$ 从 Γ 数起 | 见 `gamma` | $\varphi^i_a(b),\chi^\kappa_a(b),\psi_\kappa(a)$ | **原语** | 递归 `inOT`; 依赖作者未发表的 OCF | 结构 | 无值对应; 序嵌入未测 |
| **Rathjen $T(M)$** (1990/1991) | 同类 | φ-闭包 | 无基本列 | 含 $\varphi$ (1990 还有 $\Phi$) | **原语** | 递归 | **无** (koteitan 的 `fsN` 是其设计, 非原文) | 无值对应. 1991 版把 χ 收成一元, **$\Omega_2$ 无项** |
| **Setzer OT_I / OT_M** | $0$, 且 Fi 上 $\Omega_a=a$ | $\psi_{\Omega_1}0$ 很大 | 无基本列 | $+,\varphi,\Omega,\psi,I$ (或 $M$) | **原语** | 递归 (G, OT4, OT5) | 无 (OT_I 上我方只有范数搜索) | $\tau(\mathbf 1)=\varphi'_00$, $\tau(\psi_u0)=\Omega'_{\tau u}$, $\tau(\psi_ua)=\psi_{\Omega'_{\tau u+1}}(\tau a)$; `EBOI` 再加 $\tau(\psi_Ia)=\psi_I(\tau a)$, $\tau I=I$. 不保值只保序, 样本无反例 [测试] |

**下标错位速记** [推断, 除注明外]. $\psi_I(1)$ ($T_W$) $=\psi_I(0)$ (EBOI, Setzer) $=\Lambda$. $\psi_I(\omega)[n]$: EBOI 是 $\psi_I(n)$, $T_W$ 是 $\psi^{T_W}_I(n)$ 即 EBOI 的 $\psi_I(n-1)$, 每处都是 EBOI 的项更大 [测试]. 差 A、B、C 不是单纯改名: $\psi_\pi(\omega)[0]=\psi_\pi(0)$ 在 $T_W$ 是 1, 在 EBO 是 $\Omega_\nu$.

**同一写法 $\psi_I(0)$ 跨族不是同一个序数** [推断, 手算, 未证]. φ-free 的 Maksudov 与 `EBOI` 是 $\Lambda=\Phi_1(0)$; Exmachina 与 Naruyoko 的闭包含 $\Phi$ ($=\varphi^1$), 是 $\Phi$ 的 Γ-不动点, 大得多. 所以这些族之间只能比序嵌入 (过 τ), 不能比展开. 分水岭看来是**含不含 $\Phi$**, 不是含不含普通 φ: `InaccPsi` 与 OT_I 有 φ 无 $\Phi$, 按上行与 `InaccPsi` F10 仍落在 $\Lambda$ (F10 只证了 Ω-不动点, 同值是推断). 详见 CodeGuide §6.

## 4. 规则形状速查

只给形状. 完整规则: EBO 见 `probes/OCF/Align/EBO.lagda.md` §5; I 见 `EBOI.lagda.md` §5; χ、M 见调研 §3.3 的表与 §12.7.

### 4.1 EBO

`cof`/`dom` 四类: 0, 后继, ω, $\Omega_{\mu+1}$.

| # | 形状 | 展开 |
|---|---|---|
| 1 | $x+a$ | $x+a[\cdot]$ |
| 2 | $1$ | $0$ |
| 正规叶 | $\Omega_{\mu+1}$ | $[\eta]=\eta$, $\eta<\Omega_{\mu+1}$ |
| 3 | $\Omega_u$, $u$ 极限 | $\Omega_{u[\cdot]}$ |
| 4 | $\psi_u(b+1)$ | $\psi_u(b)\cdot n$ |
| 5 | $\psi_u(b)$, $\mathrm{cof}\,b=\omega$, 或 $\Omega_{\nu+1}$ 且 $\nu+1\le u$ | $\psi_u(b[\cdot])$; 共尾度穿透 |
| 6 | $\psi_u(b)$, $\mathrm{cof}\,b=\Omega_{\nu+1}$, $\nu+1>u$ | $\psi_u(b[\gamma_n])$; $\gamma_0=\Omega_\nu$, $\gamma_{k+1}=\psi_\nu(b[\gamma_k])$; 共尾度 ω |

非标准输入有哑值 (我方 `EBO` §9 清单); 这些哑值与 Lean 的取值只在定义域外不同 (§5.3).

**G (标准形).** $\psi_a(b)$ 标准当且仅当 $a,b$ 标准且 $G_a(b)$ 中每个元素 $<b$; 和要求主项弱降. $G_a(\psi_c(d)+t)$: 若 $a\le c$ 取 $\{d\}\cup G_a(c)\cup G_a(d)$, 否则空, 再并 $G_a(t)$. 下标 $c$ 本身不收集, 只递归进去.

### 4.2 ψ_I (单个 I, EBOI 的读法)

$\mathrm{cof}\,I=I$. 新规则:

- $\Lambda=\psi_I(0)$: $\Lambda[n]=1,\Omega_1,\Omega_{\Omega_1},\dots$, 与 EBO 的 Ω-塔逐项相同 (`ψ₀Λ-tower` 机检·我方).
- $\psi_I(b+1)[n]$: $\psi_I(b)+1,\ \Omega_{\psi_I(b)+1},\dots$; Ω-塔.
- $\mathrm{cof}\,b=\omega$ 或 $\rho<I$: 穿透, $\psi_I(b[\cdot])$. **严格** $<I$; 这是与 $\psi_u$ 唯一的不对称.
- $\mathrm{cof}\,b=\rho\ge I$: 折叠, γ-链, $\gamma_0=\psi_\rho(0)$ 型 ($\rho=I$ 时 $\Lambda$), 进 $\psi_I$.
- 别名: $\Omega_f$ ($f$ 不动点) 不标准, 规范化到 $f$. 这是 $\Omega_a=a$ on Fi.

**其它读法.** $T_W$ 同型, 基底是 $I_\nu+1$、$\psi_{I_{\nu+1}}(\beta)+1$, $\gamma_0=1$. みずどら 的 dom 表最完整 (调研 §12.8, 7 行), 带递归标准形. 其一行基底写作 $\partial(b)\hat+1$, 疑为 $\partial(a_0)$. γ₀ 取 $\Lambda$ 还是 $1$ 是开放选择, 只动 `γT` 一行, 极限相同 (`EBOI` §11).

### 4.3 χ 与 M (Maksudov 编号)

$\chi(0,\alpha)=\aleph_{1+\alpha}$, $\chi(\alpha,0)$ 与 $\chi(\alpha,\beta+1)$ 正则; 正则基数的基本列都是 $[x]=x$ (规则 19). $\psi_{\chi(b,c)}(d)$ 的基底由 $(c,d)$ 定, 按 $\mathrm{tp}(b)$ 三分:

| 规则 | $\mathrm{tp}(b)$ | 共尾 | 展开 |
|---|---|---|---|
| 7–9 | 1 | ω | $a[0]$=基底$+1$ 或 0; $a[n]=\chi(b[0],a[n{-}1])$ |
| 10–12 | ω 型, $<M$ | $\mathrm{tp}(b)$ | $\chi(b[x],\text{基底})$ |
| **13–15** | $M$ | ω | $a[0]$=基底$+1$ 或 0; $a[n]=\chi(b[a[n{-}1]],0)$ |

其余: 20: $\chi(b,c[x])$; 21: $\psi_p(b[x])$, $\mathrm{tp}\,b<p$; 22: γ-链 $\psi_p(b[c_n])$, $c_{m+1}=\psi_r(b[c_m])$, $p\le\mathrm{tp}\,b=r$.

**M 的要点.** **在 Maksudov 与 $\mathfrak T(M)$ 中** ψ 的参数都 $<M$, 所以 $\psi_M$ 不存在, 规则 22 的 $r$ 总是 $\mathcal R$ 的元素, $\mathrm{cof}\,M=M$ 只在 χ 的**第一参数**起作用, 规则 13–15 把 γ-链搬到那里, 是 Π-反射式的对角回去 [推断]. **Exmachina 与 Naruyoko 不是这样**: ψ 的参数无 $<M$ 上界, $\mathrm{cof}\,\gamma=M$ 可以落在 ψ 上, 走 $\psi_{\chi_{A[n]}(0)}(0)$ (`ordinal.js:961-985, 1290`, Exmachina 无 $\psi_M$) 或 $\psi^M$ (`implementation.js:1455-1458`, Naruyoko 的 $M$ 是合法下标) [社区无证明, 静态读码]. 切掉这部分是否丢强度未知. 代价不在基本列, 在序与形成条件 $r^\ominus,K_r,a^\star,G$. 它们**不与一般基本列同时递归**, 依赖是单向的: $r^\ominus$ 只对后继 $b$ 取 $b[0]$, 即 `pred` (`mnot.py:112-113`, `ordinal.js:944`; Naruyoko 与 koteitan 的序层根本不碰基本列); 基本列层依赖序层, 不反过来 [静态读码 + 手算; KawamoYurase 的序未查]. 所以 `EBOI` 的分层可沿用, 真正的同时递归只在 $\{<,\star,K,\ominus,G\}$ 内部 (CodeGuide §1(b), §3). $\mathfrak T(M)$ 的 `fsN`: $\alpha$ 极限且 $\mathrm{cof}\,\alpha\ge\kappa$ 时 $t[n{+}1]=\psi_\kappa(\alpha[t[n]])$, 同型.

### 4.4 已知缺陷

| 位置 | 缺陷 | 状态 | 层级 |
|---|---|---|---|
| Maksudov 10.5.3 | **P1**: 严格 $\lhd c^\star$, 等号处三歧失败; 补丁 $\unlhd$ | 博客文本字面确认; KawamoYurase 已写成 $\le$; 正确性只来自语义判断 | 测试 + 推断 |
| Maksudov 规则 20 | **P2a**: 不查 $G$, 如 $\chi(0,I+I)[0]=\chi(0,I)$ 而 $\chi(0,I)=I$; 补丁 $G=0$ 时取 $c[x]$ | KawamoYurase 仍未处理 | 测试 |
| Maksudov 规则 18 | **P2b**: $b[x]\unlhd M$ 时 $\omega^{b[x]}$ 不合形成条件; 补丁取 $M$ | KawamoYurase 部分处理 | 测试 |
| Maksudov 序 | 用 ◃ 定义 T 而 ◃ 限于 T², 循环; 情形不完备 (部分指定) | 作者自认未必修全; KawamoYurase 全情形 | 社区无证明 |
| *Rathjen-type* | 24 个带编号缺陷 (如 `031293` 死循环, `79CBAE` 规则恒假, `4559B6` 标准形与展开不相容, `C5BE66` K 的序), 作者逐条修正, 一次修正又引入新错 | 现行版是调试后的; 只凭评论区记录, 我们未复现 | 社区无证明 |
| *Rathjen-type* 实现 vs 博客 | Γ-闭包种子偏移一位: `fund(Γ₀,·)` 与博客表不同 (另有 51 项中 21 项相同的记录) | 单一来源 (koteitan `findings`), 未复现 | 社区 |
| Exmachina | $\Psi$ ($T(K)$) 基本列第一版错, 靠约 600 个序数 + 从上方搜索发现后修复; 声称 Stegert 定义有不良行为需修正 | 未核实 | 社区无证明 |
| Buchholz 1986 | ([ ].4)(ii) 读出来右边不依赖 $n$, 由 *Relating ordinals* 规则 6 替换 | 替换规则只有二手转录, 但 pss-proof 的 Lemma 3.3 机检 (只读) 背书 | 推断 |
| p進大好きbot EBO | $G$ 无错; koteitan 曾写强了 (把 $c$ 也收集), 校正后定理无改动通过. 其 README "Standard forms" 一段仍是旧说法, **以 `Std.lean` 为准** | 代码与 README 不符, 见 §5.3 | 机检·只读 |
| `EBOI` | $\psi_f(0)$ 别名上 Setzer 给 $\Lambda\prec\Omega'_\Lambda$, `cmpᵀ` 给 `eq`; 该项不在 NF, 不算冲突. `cmpᵀ` 的 `lt` 不蕴含 `_<ᵀ_` (反例是别名) | 已记录 | 测试 / 机检·我方 |

## 5. 机检索引

**计数口径.** "文本计数" = 我的脚本去掉注释与字符串后数 `sorry` 词和 `axiom` 声明, 在 2026-11-02 的克隆上跑. 不是 `#print axioms`, 不能排除 `Classical.choice`、`propext`. "README 称" = 只读了作者声明. **以下外部工作, 除 `ExBuchholz` (已构建, 公理见 §5.2) 外, 我们都没有构建** (其余是否依赖经典逻辑一律以 `#print axioms` 为准, 我们没跑).

### 5.1 ψ 型记号

| 工作 | 提交 (日期) | 定理 / 文件 | 一句话 | 依赖 | sorry/axiom | 构建 | 许可 |
|---|---|---|---|---|---|---|---|
| **koteitan/googology-lean `ExBuchholz`** | `6da2de5` (2026-11-02) | `OTLt_wf` Mono:139; `OTFS_thm` Closure:1827; `valEquiv` Onto:314 | EBO 标准形良基、基本列封闭、到 $C_0(\Lambda)$ 的同构 (§5.2) | Lean 4.30.0; `FS`/`Closure` 句法无 mathlib, `Ord` 起用 mathlib v4.30.0 | 目录 0/0 (文本计数, 20 个 `.lean`); `Core` 0/0. 公理见 §5.2 | **是**, 到 `RankVal` 为止, 0 警告 0 错误 (2026-11-02, 自建 Lake 项目, 源文件未改; §5.2). `Eps`、`Ladder`、`LadderV` 与 `test/` 未构建 | MIT (`NOTICE` 列的 Apache 例外在 `Y/WellOrder` 等处, 不含此目录) |
| 同仓库 `InaccPsi` | 同上 | `Term.isWellOrder_cmp` Correct:1166; `Term.existsUnique_NF` Onto:562 | ω 个弱不可达上的 ψ, φ 原语; NF 良序且完备. **无基本列** | mathlib; 假设结构 `InaccSeq` (Hyp) | 0/0 (文本计数, 9 文件 4288 行) | 未 | MIT |
| 同仓库全库 | 同上 | `Googology/**` 2992 个 `.lean` | — | — | 0 sorry; **156 个 `axiom` 声明在 27 个文件** (绝大多数在 `Trans/` 下引用外部结果的 `Cited*` 文件, 另有 `OmegaY/WellOrder/OmegaY/Reflection.lean`; 都不在 `ExBuchholz`、`InaccPsi`、`Core`) (文本计数) | 未 | MIT + Apache |
| **koteitan/bms-rathjen** | `7bde9d7` (2026-08-22) | `lean/TM/{Terms,Order,NF,FS}.lean` 共 942 行 | Rathjen 1991 $\mathfrak T(M)$ 的项、序、标准形; `fsT`/`fsN` 是**作者设计**, M 处递减封闭未证; 良基只到 Γ₀; 一元 χ 缺 $\Omega_2$ | Lean 4.30.0, 无外部依赖 | 1 sorry (`scripts/axioms_of.lean` 自测), 0 axiom (文本计数) | 未 | **CC BY-SA 3.0** (仓库 LICENSE; GitHub 判 NOASSERTION) |
| **koteitan/pss-proof** | `d1be91f` (2026-09-06) | Isabelle `y5_PSS_wf` `isabelle/8/Support_8_C.thy:13087`; `lean/Buchholz-1986/`, `lean/Buchholz-rel-ord/` | PSS 停机, 含 Buchholz 1986 Lemma 2.1、2.2、3.2a、3.3 的自证; **不用序数值的良基** `OT_B_wellFounded` (`lean/OTB-well-founded-syntactic/…-main.lean:235`, $D_\omega$-free, §6.1 末) | Isabelle/HOL; Lean 4 | Lean 0/0 (文本计数); Isabelle 按词 114 处在 20 文件 (未去注释). **131 与 5 已解开**: 131 是 `isabelle/8/audit.thy:41-42` 的历史清单, 陈述已迁到单命题文件, README 的 "`pss_paper.thy` 131 处" 是过时说法; 5 = 3 条真 `sorry` (`pss_paper.thy:233,239,250`, 都是 [Buc1] 引用) + 2 处注释. 全 `isabelle/` 独占一行的 `sorry` 8 处; 审计按名字, 不按证明项 (`Support_8_C.thy:12651`) | 未 | **未找到 LICENSE** (仓库无文件, GitHub 无判定) → 默认无授权 |
| **我方 OT_I** `archive/src/Mahlo/Inacc/` | 工作树 | `Theorem.lagda.md`: `wellfounded : ∀ n {y} → OT y → y ≺ endpt n → Acc y` | Setzer OT_I 到 $\psi_{\Omega_1}\Omega_{I+n}$ 的构造性良基 | `--safe --cubical-compatible`, stdlib | 文件头 `--safe` | 我方, 本次未重编 | 本仓库 |
| **我方 EBO** `probes/OCF/Align/EBO.lagda.md` | `c56b781` | `fsn↓`, `fsT↓`, `γ↓`; `FGH` 沿 `Acc` | 规则式基本列 + 递减证书; **无** NF 封闭, **无** 标准形良基 | `--safe --without-K --lossy-unification` | 文件头 `--safe` | 我方, 本次未重编 | 本仓库 |
| **我方 EBOI** `probes/OCF/Align/EBOI.lagda.md` | 未提交 | `fsn (ιT t) n ≡ ιT (E.fsn t n)` 等; `NF-ι`; `ψ₀Λ-tower` | 对 EBO 保守; 片段封闭 (§9.1); 全系统封闭、良基未做 | 同上 | 文件头 `--safe` | 我方, 本次未重编 | 本仓库 |

### 5.2 `ExBuchholz` 文件地图 (行号于 `6da2de5`, 路径 `Googology/Notation/ExBuchholz/`)

| 文件 (行) | 内容 | 关键行 | mathlib | 移植到 Agda |
|---|---|---|---|---|
| `Basic` (118) | `Term`, `cmp`, `lt`, `le` | 29, 45 | 否 | 我方 `T`/`cmpᵀ` 已有 |
| `Order` (159) | 严格全序 | `lt_trans` 76, `lt_trichotomy` 80 | 否 | 要写 |
| `Std` (66) | `G`, `isOT`, `OT` | 22, 39, 46 | 否 | `EBOI` 的 `isOTᵉ` 已有, Bool 形 |
| `WF` (130) | `not_wellFounded_lt` | 50 | 否 | 可选 |
| `Sum` (304) | `HeadLe`, `leadCount`, `size`; `acc_of_OT` 把良基归约到主项 | 20, 180, 203 | 否 | 要写; 与证明路线无关的部分可跳 |
| `FS` (1204) | `dom`, `fs`, `fs_lt`, `fs_mono`, `tower`, `fs_numeral` | 36, 270, 451, 745, 805, 811 | 否 | `fs_lt` 我方已由证书得到 |
| `Closure` (1833) | Buchholz 3.3–3.6 与 $G$ 界 | 见下 | 否 | **主要工作量** |
| `Ord`, `Eval`, `Opow`, `Level`, `Eps`, `Ladder`, `LadderV` | 语义: $\Omega$, $C$, ψ, `val`, 闭式值 | — | **是** | 不移植 |
| `Mono` (170) | `val_lt_val`, `OTLt_wf` | 121, 139 | **是** | 不能移植 (经典), 走 §6.1 |
| `System` (75) | `exbOT`, `exbOT_wf`, `exbOT_terminates` | 40, 61, 66 | 经 `Mono` | 只看形状 |
| `Cofinal` (414) | `exists_lt_fs_numeral` | 294 | 文件经 `System` 导入, 定理本身不用序数 | **纯句法**: 依赖闭包不含 `val`、不含 `OTFS_thm`, 只触及 `Basic`、`Order`、`Std`、`WF`、`Sum`、`FS`、`Cofinal`; mathlib 只用到 `le_max_left/right`、`Nat.strong_induction_on`、`Nat.instLinearOrder`. `tower_val_mono` 的 val 是"塔的取值", 不是序数 `val` (本手册早先把这里写成"不是纯句法", 是读错了) |
| `NF`, `Onto` (642, 391) | 满射: `Vals_eq`, `valEquiv`, `existsUnique_OT_of_lt_psi_Lam` | 274, 314, 289 | **是** | 不移植 |
| `RankVal` (53) | `rank_exbOT_eq_val` | 26 | **是** | 验收依据, 不移植 |

`test/ExBuchholzCheck.lean` (176 行) 带两个陷阱的见证项; 未构建.

**构建结果** (**机检·已构建**, 2026-11-02; 提交 `6da2de5`, `leanprover/lean4:v4.30.0`, arm64-apple-darwin, 复现见 §8).

- *构建方式.* 仓库的 `lakefile.toml` 无条件要 mathlib、`bmselempattern`、`pss`, 所以没有用它. 句法部分是自建的无依赖 Lake 项目, 只含 `Basic`、`Order`、`Std`、`WF`、`Sum`、`FS`、`Closure`、`Googology.Core` 及 `Core/*` 共 13 个文件, 模块名不变, 与提交逐字节相同. 语义部分是另一个自建项目, 要 mathlib `c5ea003` (v4.30.0, 与仓库 manifest 同) 和官方缓存, 再加 `Rank`、`Cofinal` 与 `ExBuchholz/*`. 所以这**不是**仓库默认目标的 `lake build`.
- *结果.* 句法部分 14 个作业, 干净重建约 4 秒; 语义部分 963 个作业, 约 9 秒 (mathlib 全来自缓存, 只编译本项目 24 个模块). 都是 0 警告 0 错误. `Closure` 上跑 `leanchecker` 重放通过 (退出码 0). 反向对照: 改坏 `Trian_fs_aux` 一个实参, 构建失败; 把 `fs` 的 `numVal Y` 改成 `numVal Y + 1`, `FS.lean` 的 `#guard` 失败. 定义按本节和 §5.3 的描述编译: `G : Term → Term → List Term`, `isOT : Term → Bool`, `dom : Term → Term`, `fs : Term → Term → Term`; `#check` 只核了类型, 逐支对照仍是 §5.3 的读码与转写测试.
- *构建期执行.* 这些文件没有 `initialize`、`run_cmd`、`#eval`、`IO.Process`、`elab`、`macro`、`@[extern]`、`unsafe`、`implemented_by`. 只有 45 条 `#guard` (`Order` 7, `Std` 8, `WF` 2, `FS` 28), 由 Lean 求值纯项. `deriving DecidableEq, Repr` 走内置处理器.

`#print axioms` 原样结果 (名字省去前缀 `Googology.Notation.ExBuchholz.Term.`):

| 声明 | 公理 | 声明 | 公理 |
|---|---|---|---|
| `size` | 无 | `OT_psi_fs` | `propext, Quot.sound` |
| `cmp`, `G`, `isOT`, `dom` | `propext` | `bachmann` | `propext, Quot.sound` |
| `lt_trans`, `lt_trichotomy`, `lt_irrefl`, `cmp_eq_iff` | `propext` | `OTFS_of_Bachmann`, `OTFS_thm` | `propext, Classical.choice, Quot.sound` |
| `fs` | `propext, Quot.sound` | `Trian_fs`, `Trian_fs_thm` | `propext, Classical.choice, Quot.sound` |
| `fs_lt`, `fs_mono` | `propext, Quot.sound` | `exists_lt_fs_numeral`, `tower_val_mono` | `propext, Quot.sound` |
| `acc_of_OT`, `wellFounded_OTLt` | `propext, Quot.sound` | `OTLt_wf`, `val_lt_val`, `val`, `valEquiv`, `Vals_eq`, `existsUnique_OT_of_lt_psi_Lam`, `rank_exbOT_eq_val`, `exbOT_wf`, `exbOT_terminates` | `propext, Classical.choice, Quot.sound` |

**公理从哪里进来** (对 `OTFS_thm` 的依赖闭包 326 个常量逐个查).

- `Classical.choice`: **偶然, 已机检可去.** 闭包内只有 `Trian_fs_aux` (`Closure:1027`) 和 `OTFS_aux` (`Closure:1645`) 直接用 `Classical.byContradiction`, 都来自同一个写法: 归纳的 `zero` 分支里 `simp only [size_cons] at hsz; omega`. 假设本身矛盾, 但目标不可判定, `omega` 的反证开场就退回经典版. 在暂存副本里把这两行改成 `...; exfalso; omega`, 重建和 `leanchecker` 都通过, 得到 `OTFS_thm`、`Trian_fs_thm`: `[propext, Quot.sound]`. 这同时说明 `fs` 的 `if` 和 `Closure` 的 59 处、`FS` 的 34 处、`Sum` 的 4 处 `by_cases` 都没有走经典判定, 全部用的是可判定实例. `Core` 里三处显式 `Classical.byContradiction` (`Rewrite:51`, `Morphism:93`, `Goals:54`) 不在闭包内.
- `Quot.sound`: 工具带来的. 闭包内 65 个入口里 61 个是 `omega` 产生的 `_proof_` 引理 (`Lean.Omega.*`), 含 `fs` 的终止性证明; 其余是库引理 `List.all_eq_true` 与 `simp` 用的 `funext` (`dom_shape`). 另有 `forall_congr` 在 `OT_G_lt`、`OT_psi_of_le`, 及生成的 `fs._unary.eq_def` 用 `funext`. 没有看到把函数相等当数学内容用的地方 [推断, 只看了名字和位置].
- `propext`: 三个来源. (1) 定义层的编译副产物: `cmp._f` 经 `Ordering.then`, `dom`、`numPred` 的 `_sparseCasesOn` 经 `Nat.land`、`Nat.hasNotBit`. (2) `omega` 的 `Lean.Omega.*`, 闭包 57 个入口里 51 个. (3) `simp`: `eq_self`、`and_true`、`ite_cond_eq_true`、`List.mem_append` 等, 以及闭包内 8 个声明里直接的 `propext` (如 `Order` 的私有引理、`cons_lt_psi_iff`、`lt_one_iff`、`bach_succ`). 在 Lean 内去不掉, 因为 `cmp` 自身就带它, 所以"证明不实质依赖 propext"**没有机检**, 是推断.
- 语义部分的 `Classical.choice` 是实质的: `val` 取值在 mathlib `Ordinal`, `Onto` 的 `valEquiv` 还显式用 `Classical.choose` (15 行). `OTLt_wf` 这条路线不能原样搬; 这是这条证明路线的限制, 不是对陈述本身的判断.

**对移植到 `--safe --without-K` 的含义.** `OTFS_thm`、`bachmann`、`fs_lt`、`fs_mono`、`exists_lt_fs_numeral`、条件式的 `acc_of_OT` 都没有经典内容阻碍移植; `Classical.choice` 已机检可去, 其余两个公理看来只是 Lean 工具的痕迹 [推断, 真正写出来才算数]. 剩下的是工程量: 没有 `omega`、`simp_all`, 这些自动化要换成显式推理 (`omega` 行数: `Sum` 6, `FS` 27, `Closure` 59); `fs` 的良基递归要换形式 (见下面注记 (a)).

**`OTFS_thm` 的证明顺序** (全在 `Closure.lean`):

1. 工具: `addT` 148, `G0` 168, `listLe` 171, `Trian` 193 ($b\lhd_z a$: $b<a$ 且 $\forall c\in(b,a]$, $G_u(b)\preceq G_u(c)\cup G^0_u(z)$).
2. Buchholz 3.5: `Trian.addT_left` 238, `Trian.psi_left` 302, `Trian.psi_sub` 550.
3. Buchholz 3.4: `G_lt_of_Trian` 359, `Trian.G_lt` 382; 由它得 `OT_psi_fs` 617.
4. 假设 `OTFS` (645) 下, `SubBound` (651): `subBound_lt` 671, `subBound_of_OTFS` 887, `sub_G_le` 891, `tower_G_le` 912, `Trian_case4` 968.
5. Buchholz 3.6: `Trian_fs_aux` 1016, `Trian_fs` 1127. 只以 `OTFS` 为前提.
6. `Bachmann` (1134) 与大小论证: `W0` 1192, `size_fs_W0` 1205, `G_size_succ_lt` 1286, `no_small_between` 1323, `bach_pre` 1796, `bachmann` 1820. 这一支**不依赖** `OTFS`.
7. `towerOT_of_Bachmann` 1554; `OTFS_aux` 1635 (对 `size` 归纳, 同时带 3.6); `OTFS_of_Bachmann` 1787; `OTFS_thm` 1827; `Trian_fs_thm` 1830.

**两个陷阱.**

1. *界必须相对于 $c$.* Buchholz 的绝对不变量 $G_u(W_i)<X_2[W_i]$ 在下标是项时为假. 要写成 $X[\psi_{Z[0]}(0)]\le c\le X\Rightarrow G_u(Z)\preceq G_u(c)\cup\{0\}$ (`SubBound` 651), 且索引必须是 $\psi_{Z[0]}(0)$ 而不是任意 $W<\mathrm{dom}\,X$. 下标是序数项的 EBO 不能照抄 1986 的证明.
2. *`bach_pre` 要带前缀 $p$.* 对 `caseV` (`ExBuchholzCheck` 143): $V=\psi_\Omega(0)+\psi_1(\psi_\Omega(0))$, $G_1$ 看得到 $V$ 自己的头, 所以"低于头"、"低于尾"都不成立, 只有带前缀的结论成立.

**移植注记** [推断, 未试]. (a) Lean 的 `fs` 走良基递归, 度量 (size X, size Y), γ-链靠从 `fs X (numPred Y)` 的值拆出 Γ; 我方是结构递归的 `γT`, 证明应该对 `tower` 版 (`fs_numeral`) 而不是 `fs` 的定义. (b) `dom` 返回项, 我方 `cof` 返回标记, 用 §5.3 的 $h$ 过桥. (c) `G` 是列表, `listLe` 与 `Trian` 都读列表; `isOTᵉ` 是 Bool 形 (`Gᵉ`), 要证二者等价, 或者在 Agda 里也用列表. (d) 这些文件不 `import Mathlib`, 其中有 59 处 `by_cases` (Closure), 都走可判定实例, 已由上面的 `exfalso` 对照机检; 对应到 Agda 是 `cmpᵀ` 与 `Term` 的判等. `propext` 改写要换成 `⇔` 或显式转换, 涉及的命题都是 Bool 或 `Ordering` 上的等式, 预计不难, 这部分未试.

### 5.3 `ExBuchholz` 与我方 EBO 是否逐项相同

**结论: 是同一个 EBO. 项、序、共尾度分派、标准形谓词在全部项上相同; 基本列在全部项上相同 (数字下标的 `fsn` 对全部项, Ω-下标的 `fsT` 对 `cof = cΩ` 的项), 差异只在定义域外的哑值.** 依据: 逐支读码 [推断] + 转写测试 [测试]. 没有运行 Lean 或 Agda, 也没有形式证明.

**字典** (`EBO.lagda.md` ↔ `Basic`/`FS`/`Std`):

| 我方 | Lean | 关系 |
|---|---|---|
| `T`, `PT`, `ψ u a ∷ t`, `[]` | `Term`, `cons u a t`, `nil` | 互逆双射. 单归纳 vs 互递归 + `List`, 无内容差异 |
| `_<ᵀ_`, `cmpᵀ` | `lt`, `cmp` | 同一字典序: (下标, 参数, 尾), 前缀更小 |
| `cof : T → Cof` | `dom : Term → Term` | **`dom = h ∘ cof`**, 其中 $h(c0)=$ `nil`, $h(c1)=$ `t1`, $h(c\omega)=$ `tw`, $h(c\Omega\,\mu)=\psi_{\mu+1}(0)$. $h$ 单射. `dom X₂ < cons X₁ X₂ nil` 对 $b\ne0$ 等价于我方 `cmpᵀ (sucT μ) u ∈ {lt, eq}`: $(\mu+1,0)$ 对 $(u,b)$ 字典序比较 |
| `pred`, `natT n` | `fs X nil`, `numeral n` | 后继项上相同 |
| `rep↓` | `repeatPrin` | 相同: $\psi_u(b')\cdot n$ |
| `γT β μ k` | `tower (fs (subOf (dom β)) nil) β k` | 相同: 起点 $\psi_\mu(0)$, 步 $\psi_\mu(\beta[\cdot])$ |
| `fsn t n`, `fsT a η` | `fs t (numeral n)`, `fs a η` | 见下 |
| `isOTᵉ` (`EBOI`) | `isOT` | 同一合取, Bool 形 vs 列表形 |

**规则逐支** (调研 §12.11 的未落实项现已落实): 和、$1[\cdot]=0$、正规叶 $[\eta]=\eta$、奇异叶 $\Omega_{u[\cdot]}$、规则 4、规则 5ω、规则 5Ω、规则 6 (γ-链) 全部同形. 其中我方 `fsn↓0` 的正规叶给 `natT n`, 正是 Lean `Y` 在 `numeral n` 处的值; 规则 5Ω 的 ℕ-截断 `fsT b (natT n)` 也正是 Lean `fs X₂ (numeral n)`. 这两条我方标作哑值, Lean 把它们当普通分支, **值相同**.

**唯一的差异, 都在定义域外.**

- `fsT₊ u b c η` 在 `c` 不是 `cΩ` 时我方返回 `ψ u b` 自身; Lean 在 `dom b = 1` 返回 `repeatPrin`/`nil`, 在 `dom b = ω` 继续下降, γ-链分支在非数字 $Y$ 时取基底. 这些都不是合法调用: 我方前提 `cof a ≡ cΩ μ` 排除, Lean 前提 $Y<\mathrm{dom}\,X$ 排除.
- `fsT 𝟏 η` 两边都是 `[]`/`nil`, 相同.
- 另一处差异不是规则: FGH. 我方 `FGH` 沿 `Acc`; Lean 没有对应的函数, 用 `exbOT` 与 `rank`.

**转写测试** [测试]. 脚本把 `EBO.lagda.md` 与 `FS.lean`/`Std.lean` 分别转写成 Python, 在双射下比较; 枚举**全部**项 (含非标准形), 大小 $\le 8$ (`cons` 结点数):

| 比较 | 样本 | 不一致 |
|---|---|---|
| `dom t = h (cof t)` | 52788 项 | 0 |
| `fsn t n = fs t (numeral n)`, $n\le4$ | 263935 对 | 0 |
| `fsT a η = fs a η`, `cof a = cΩ`, $\eta$ 大小 $\le 3$ | 155941 对 | 0 |
| `cmpᵀ = cmp` | 20 万随机对 | 0 |
| `isOTᵉ = isOT` (大小 $\le 7$, 其中 3599 个标准) | 9525 项 | 0 |

敏感性: 把 γ₀ 改成 1, `fsn` 报 345 处不一致 (大小 $\le 6$); 把规则 4 改成乘 $n+1$, 报 4305 处. 限制: 转写未与真实 Lean/Agda 执行比对, 大小以外未覆盖. 脚本未入库 (本任务只准动两个文件), 见 §7.

**剩下的.** (a) 真正的形式证明: 把 Lean 项翻译进 Agda 或反过来, 目前只有读码 + 测试. (b) p進大好きbot 原文与两边的逐字核对: Lean README 的校准表自称逐条比过, 我方只比过调研 §11 的转述. (c) `Std.lean` 的 `G` 不收集 `c`, 与 README "Standard forms" 段的旧说法相反; 同 README "The correction" 段明说这是校正后的结果, 我方转写用的是代码.

### 5.4 其它机检工作

未细读, 只记状态. 提交是 2026-11-02 的默认分支头. 表中 "未判定"、"未查" 的许可与状态, 以及读过代码后的判断, 见 CodeGuide §2、§5.

| 工作 | 提交 (日期) | 内容 | 依赖 | sorry/axiom | 构建 | 许可 |
|---|---|---|---|---|---|---|
| [EgoFakeFantasy/BMS-Well-Ordering-Lean](https://github.com/EgoFakeFantasy/BMS-Well-Ordering-Lean) | `3a4a945` (10-28) | BM4 良序 `bm4_strictWellOrder_l`; 每个固定高度的 Z₂ 推导 | Lean | README 称公理只含 `propext`, `Classical.choice`, `Quot.sound` | 未 | Apache-2.0 |
| [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) | `03d794f` (09-20) | 0-Y ≅ BMS 序, 1-Y 良序 | Lean | 同上, README 称 | 未 | Apache-2.0 |
| [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) | `d555ade` (09-25) | 上者的改编, 已并入 googology-lean | Lean | — | 未 | Apache-2.0 |
| [zball-bz/btbms-formalization](https://github.com/zball-bz/btbms-formalization) | `4f31c78` (10-27) | 假设每个 $n$ 有弱 $n$-Mahlo, BTBMS 良序 | Lean + mathlib | README 称无 sorry | 未 | 未判定 |
| [coquand/agda-ordinal-analysis-id1](https://github.com/coquand/agda-ordinal-analysis-id1) | `1f977e0` (11-02) | README 称 Veblen 到 Γ₀, 读过的模块里未见 Γ₀ 的定义 (CodeGuide §2); ID₁ 的记号笔记到 BH | Agda `--safe --without-K` | README 称无公设 | 未 | 未判定 |
| [coquand/agda-mahlo-universe](https://github.com/coquand/agda-mahlo-universe) | `199a725` (10-12) | Mahlo 宇宙元理论, 不涉及序数 | 同上 | — | 未 | 未判定 |
| [SteveWmoc/lean-ordinal-analysis](https://github.com/SteveWmoc/lean-ordinal-analysis) | `0aa3551` (10-31) | ε₀, 通用 API, 基本列共尾 | Lean 4 | 未查 | 未 | MIT |
| [cj-xu/OrdinalNotations](https://github.com/cj-xu/OrdinalNotations) | `4690b68` (2021-02-21) | Cantor 范式到 ε₀ | Cubical Agda | 未查 | 未 | GPL-3.0 |
| [coq-community/hydra-battles](https://github.com/coq-community/hydra-battles) | `ed8e604` (2025-01-22) | ε₀ 完整; `Gamma0` 标 draft (标记在 `README.md:145` 与 `meta.yml`, `Gamma0/*.v` 文件内没有此字样; 那边也无基本列) | Coq | 未查 | 未 | MIT |
| [takahashi-yt/czf-in-mahlo](https://github.com/takahashi-yt/czf-in-mahlo) | `b8aa846` (2025-08-19) | CZF 解释进 Mahlo 宇宙 + `Acc` | Agda | 未查 | 未 | MIT |
| [BedrockInstitute/QIITOrd](https://github.com/BedrockInstitute/QIITOrd) | `7def431` (2026-06-22) | Brouwer 树 QIIT 的可计算序 | Cubical Agda | 未查 | 未 | AGPL-3.0 |
| [Naruyoko/googology](https://github.com/Naruyoko/googology) `padicBotRathjen` | `958ac91` (10-01) | *Rathjen-type* 的 JS 实现 (不是证明) | JS | — | 未跑 | 页面声明 CC BY-SA 3.0; 仓库未判定 |
| [DavidExmachina/garden-of-ordinals](https://github.com/DavidExmachina/garden-of-ordinals) `RathjenM` | `618e814` (10-23) | 二元 χ 的实现 (不是证明), `ASSETS/ordinal.js:858-1388` | JS | — | 未跑 | **源码公开, 无 LICENSE**, 默认无授权 |
| [hzyhhzy/column-ordinal-notations-hzy](https://github.com/hzyhhzy/column-ordinal-notations-hzy) | `2da3765` (10-22) | 列式记号与良序证明, 非 ψ | Lean/纸面 | 未查 | 未 | 未判定 |
| [hyperpolymath/echo-types](https://github.com/hyperpolymath/echo-types) | `b0982c4` (10-31) | Buchholz 语法脚手架 | Agda | 未查 | 未 | GitHub 判 NOASSERTION, 未读 |
| Mathlib `SetTheory/Ordinal/Notation` | 未钉 | ε₀ `ONote` + `fundamentalSequence` | Lean | 主线库 | 未 | Apache-2.0 [未核] |

## 6. 与本项目的接口

### 6.1 EBO → OT_I 嵌入 (第 3 层)

目的: 把 `archive/src/Mahlo/Inacc/Theorem.lagda.md` 的 `wellfounded` 沿 τ 拉回, 得到 EBO 标准形的 `Acc`, 让 FGH 不靠燃料或假设. 映射见 §3. 义务清单 (调研 §8) 现状:

| # | 义务 | 现状 | 文献省下什么 | 省不下什么 |
|---|---|---|---|---|
| 1 | EBO 标准形谓词 | **有**: `EBOI` 的 `isOTᵉ`. 与 Lean `isOT` 同一 [§5.3 测试] | 全部 | — |
| 2 | τ 严格保序 | 未做. 样本 60000 对无反例 [测试]. 预计几十行字典序论证 [推断] | 无 (Lean 的 `val_lt_val` 是语义的) | 全部 |
| 3 | τ 保标准形 | 未做. 核心: $G_{\Omega'_{\tau u+1}}(\tau a)$ 对 $\tau(G_u a)$; (G5) 无条件把 $\Omega'_c$ 降到 $c$, (G4) 多了层上的 $G_\pi(c)$ | 无 | 全部 |
| 4 | 标准形对 `fsn` 封闭 | 未做, **有机检蓝本**: `FS` + `Closure` 约 3000 行, 不依赖 τ (§5.2) | 证明结构, 引理顺序, 两个陷阱, 也免去了猜测其真假 | Agda 重写本身; `--safe` 下要改写自动化; 经典公理不是障碍 (`Classical.choice` 已机检可去, `propext`、`Quot.sound` 推断可去, §5.2) |
| 5 | $\tau t\prec\psi_{\Omega'_1}(\Omega'_{I+n})$ | 未做, 由 (≺′5)(≺′6)(≺′10) [推断] | 无 | 全部 |

**它改变了什么.** EBO 良基性的真假已无悬念 (`OTLt_wf`), §8 只剩"能否构造地得到". `rank_exbOT_eq_val` 与 `exists_lt_fs_numeral` 说明基本列确实走满 $\psi_0(\Lambda)$, 可作我方的验收依据 (已构建, 公理见 §5.2; 其中 `exists_lt_fs_numeral` 无 `Classical.choice`, 也是纯句法, 将来可以移植而不只是引用). 由于 §5.3 的测试与阅读, 这些结果看来可直接用于我方 `EBO`, 不需要换系统; 严格的转移定理没写, 这一步目前不是定理.

**它不给什么.** 构造性 `Acc`; `--safe`; FGH 的等式. 语义路线依赖 $\aleph_v$, 不能搬. OT_I 自身仍只有范数搜索, 这条路不提供 I 层以上的基本列.

**第二条路: distinguished sets.** `koteitan/pss-proof` `d1be91f` 的 `OT_B_wellFounded` (`lean/OTB-well-founded-syntactic/OTB-well-founded-syntactic-main.lean:235`) 不用序数值: 对基本列的迭代归纳集 $W_u$ (Buchholz 1987) 加共尾 `y4_bachmann` (`…-cofinality.lean:1438`) 得 Lean `Acc` [**机检·只读**, 未构建]. 分支是基本列, 形状与树相同 [推断]. 限制: 只到 $D_\omega$-free ($\psi_0(\Omega_\omega)$), 下标是 ℕ; EBO 的下标是项, 对 $\mathrm{Acc}\,u$ 递归定义 $W_u$ 的版本无人写过 [推断]; 证明里的经典写法能否消去未核; 仓库无 LICENSE, 只取数学. 所以现在它不是 EBO 良基性的证明, 只是与 τ 并列的备选. 见 CodeGuide §1(g).

### 6.2 I 片段标尺 `EBOI`

| 项目 | `EBOI` | $T_W$ | みずどら | Kanrokoti |
|---|---|---|---|---|
| 基数 | 单个 $I$ | $I_\nu$ | $I_\nu$, 到 κ 个 | $I_a(b)$ |
| EBO 段 | 保守 (机检·我方) | A+B+C 后逐项同 (9000/0; `EBOI` 样本 309 个纯 EBO 项 0 不一致) [测试] | 下标差 1 + 差异 A; **未测** | 声称直接扩展; **未测** |
| 第一 Ω-不动点 | $\psi_I(0)=\Lambda$ | $\psi_I(1)=\Lambda$, $\psi_I(0)=1$ | 按其表 $\psi_{I_0}(0)$ 走 Ω-塔, 基底 0, 所以与 `EBOI` 同列 [推断, 未测] | 未核 |
| γ₀ ($\rho=I$) | $\Lambda$ | $1$ | $\psi_{\mathrm{dom}}(0)$ 型 | 未核 |
| I 层规则 | 见 §4.2 | 同型, **不逐项**: 13404/2463 ($\gamma_0=1$), 14295/1572 ($\gamma_0=\Lambda$); 去掉 $1+$ 偏移后 15867/0 [测试; 后者一半是同构造] | 同型 [推断] | 未核 |
| 标准形 | 递归; 等于 Setzer `isOT ∘ τ` [测试] | 语义 | 递归 $\hat G$ | 未读 |
| 封闭性 | 片段 (机检·我方); 全系统测试 | 无 | **人工证明(社区)** | 未见 |
| 良基 | 无 | 无 | **人工证明(社区)**, 经序同构 | 无 |

**省下什么.** 全 `EBOI` 封闭性的路线: Lean 的 `Trian` 蓝本加 みずどら 的不变量 $\hat G_k(a)\lhd c\wedge\hat G_k(b)\lhd c\Rightarrow\hat G_k(a[b])\lhd c$. 新规则的第二意见: みずどら 的表可与 `EBOI` §5 逐行比, 这个翻译测试没人做过.

**省不下什么.** みずどら 没有 Bachmann 型性质, 不证 dom 与共尾度一致, 其 $F$ 走有界搜索不走 $a[n]$. 良基性对 OT_I 只覆盖 $\psi_0(\Omega_{I+n})$ 以下, 不覆盖全部 Tᴵ (`EBOI` §11). 下标偏移是 `EBOI` 的约定代价, 不打算修.

### 6.3 树侧 I 层

文献没有直接可用的东西. 外部给的是验收样例和形状, 不是实现:

- `EBOI` §11 列了树要匹配的规则 (易: Ω-塔; 难: 折叠输出层号, $\rho>I$ 折叠穿过 $I$). `InaccTree` §结论 1–5 是现状.
- `InaccTree` 文首第 5 点说"全 EBO 的 NF 谓词尚不存在"已过时: 谓词有了 (`isOTᵉ`), 封闭性在 Lean 有, Agda 无. `OrderEmb` 的那半要的序同构在 Lean 是 `valEquiv` (语义).
- Lean 的 `dom` 与我方 `cof` 同一 (§5.3), 所以判决问题 `D : Lv → Lv → Verdict` 不会因换用 Lean 记号变简单: 比较是语法的, 树上没有对应物 [推断].

### 6.4 类型论先例

| 先例 | 相近之处 | 差别 |
|---|---|---|
| Kovács CSL 2022 | 层号来自任意传递良基关系, IR 定义 `UIR/ElIR` | 我方树侧方向相反: 层号由树族生成, `WF` 不成立 (`¬WF-L₁`). 良基性他外给 |
| Takahashi 2024, `czf-in-mahlo` | Mahlo 宇宙 + 沿 `Acc` 迭代高阶宇宙算子 | 沿可及性走, 不沿记号走 |
| Coquand `agda-mahlo-universe` (2026-10) | Setzer Mahlo 宇宙元理论, `--safe` | README 未提序数 |
| Dybjer–Setzer JLC 2024 | 扩展谓词 Mahlo 宇宙, 模型在 Agda 通过 | 只见摘要 |
| QIITOrd | Brouwer 树 QIIT 的计算序过停机检查 | 不到 I |

**小结.** 没找到"层号就是裸 IR 宇宙"的前人工作 (检索范围有限). 这些只提供参照, 不提供可搬的代码 [推断]. 读过代码后的判断见 CodeGuide §1(e)(f), §2.

### 6.5 χ 与 M 层

若开工: 形状用 KawamoYurase 版; 把 `mnot.py` 换到它上面重测 (未做); 下一个测试是 Naruyoko 实现作序的对照 (koteitan 已这样用过, 我方没有). 良基性只能指向 Rathjen 1994 或 OT_M, 都只有纸面, 我方未机检. BCW 范数列可测结构规则是否被其支配 (未做). `bms-rathjen` 的 `fsN` 只在 Γ₀ 以下有外部见证 (12 行 `#guard`, 对博客表), 不能当 M 层规则的依据, 其一元 χ 也写不出 Ω₂. 动手前先过一遍 p進大好きbot *List of common misconceptions about Rathjen's psi* (未精读). 所有这些都**不提供**证明.

## 7. 未取得与待核

**未取得.**

| 材料 | 现状 | 需要什么 | 用户可做 |
|---|---|---|---|
| Buchholz 1990 *Wellordering proofs for systems of fundamental sequences* (草稿) | 只有书目; Setzer 1998 称其良序证明的主要基础 | 全文, 可能最对口 | 向作者或 LMU 索取 |
| Buchholz 2003 *Ordinal notations and fundamental sequences*, *Relating ordinals to proofs* (LNL 15, 2002), 2015 综述 | 主页链接 404; 搜索片段打不开 | 规则 6 的一手文本 | 从机构库下载存入 `archive/src/Mahlo/Sources/` |
| Rathjen 1994 (AML 33(1), DOI 10.1007/BF01275469) | 付费 | KPM 良序证明 | 机构访问存档 |
| Pfeiffer 1992 (MLQ 38), Wemheuer 1994 | 只有书目 | 有无基本列不明 | 馆际 |
| Jäger 1984, Schütte Klammersymbole, Duchhardt, Stegert 2010, Weiermann, Carlson, Arai O(μ), Grimm | 未读 | 背景 | Stegert 可能在 Münster 馆藏 |
| Kanrokoti 标准形节, みずどら 一处切片, C7X *Ordinal notations* | Chrome 工具过滤了部分文本 | Kanrokoti 是否自证封闭 | 打开页面, 把正文另存给我们 |
| Miraheze 页面 | 校验页, 没试图通过; Wiki 表的 wikitext 早先读到过 | 再核 `T_W` | 同上 |
| *How to Create a Recursive Notation*, Syst3ms *UNOCF*, Hyp cos 其它 OCF 帖 | 未读 | 写规则时的清单 | — |
| Garden of Ordinals (Exmachina) | **源码公开** (`DavidExmachina/garden-of-ordinals` `618e814`), 静态读过 `RathjenM`, 没运行; 无 LICENSE, 代码与数据都不能并入 | 使用许可 | 问作者 |

**未核实, 或只有单一来源.**

| 声称 | 来源 | 缺什么 |
|---|---|---|
| `ExBuchholz` 主要定理 | **已构建**: `6da2de5`, Lean 4.30.0, mathlib `c5ea003`; `#print axioms` 见 §5.2, 复现见 §8 | 用的是自建 Lake 项目和 mathlib 官方缓存, 不是仓库默认目标; `Eps`、`Ladder`、`LadderV`、`test/` 未构建. `Classical.choice` 可去已机检; `propext`、`Quot.sound` 可去是推断, 要写出 Agda 证明才算 |
| `ExBuchholz` 与我方 EBO 逐项相同 | §5.3 读码 + Python 转写; 脚本 `probes/Survey/scripts/ebo_vs_exbuchholz.py` | 未形式证明; 如需定理要写转移定理 |
| みずどら 的证明 | 只读了结构、定义和结论 | 第二人核查 |
| Maksudov 简化与 Rathjen 原系统序同构 | 无人证明; *Rathjen-type* 作者警告简化丢失可计算性 | 比较测试 |
| P1 的正确性 | 语义判断 + KawamoYurase 独立同向 | 对 Rathjen 或 Setzer Def 3.3 的序比较 |
| 24 个缺陷 | 博客评论区, 只读相关部分 | — |
| 实现与博客 51 项中 21 项相同; `inOT` 通过 13181/62664 | koteitan (`lean/TM/FS.lean:338`, `table/findings.md:2152`) | 未独立复现, 没运行实现 |
| Rathjen 1990 Thm 6.3 的上界 | 经 p進大好きbot *Cheatsheet* | 对原文 |
| Stegert 定义有瑕疵 | Exmachina | 对 Stegert 2010 |
| Buchholz 1986 ([ ].4)(ii) 的读法, 规则 6 | 读图; koteitan 二手转录 | 一手文本 |
| Lean/Agda 外部工作的 README 声明 (§5.4) | README | 构建 |
| Wilken 对 $R_2^+$ 的声称 | 经 InaccPsi README | 明说未证 |

**可以直接做的测试** (都没做): `mnot.py` 换 KawamoYurase 版; `EBOI` 对 みずどら 表; $A,B,C$ 对 みずどら; `mnot` 对 BCW 范数列.

## 8. 复现

都是我方脚本, 只用标准库, 不读外部数据. 下列数字 2026-11-02 重跑过, 全部复现. `eboi/` 下的脚本互相 `import`, 而 `python3 -I` 不把脚本目录放进 `sys.path`, 所以那边不用 `-I`, 用 `python3 -B` 免写 `__pycache__`.

| 脚本 | 目录 | 命令 | 测什么 | 结果 |
|---|---|---|---|---|
| `cmp.py` | `probes/Survey/scripts` | `python3 -I cmp.py` | EBO 规则对 $T_W$, 经 τ 与 A/B/C 六种组合 | A+B+C: 3000 项 9000/0 (约 15 秒). 调研 §4 的 2400 步表要把第 167 行 `3000` 改 `800`, 得 1714/686 … 2400/0 |
| `mnot.py` | 同上 | `python3 -I mnot.py 6000 300` | Maksudov 字面版 | 6000 项 32437 步; notMono 239, notT 237, notLess 183 等 |
| `mnot.py` (补丁) | 同上 | `PATCH=1 PATCH2=1 python3 -I mnot.py 6000 300` | P1 (`PATCH`), P2a/P2b (`PATCH2`) | 6000 项 35931 步无失败; 分支计数同调研 §3.4 |
| `emb.py` | 同上 (**必须**, 它读 `cmp.py`, `mnot.py`) | `python3 -I emb.py` | EBO → OT_I 与 → Mahlo 序嵌入 | OT 种子 16/22; 3000 项 8978 步 0 离开; 60000 对 0; Mahlo 40000 对 0, FS 5726/3241 |
| `eboi/test1.py` | `probes/Survey/scripts/eboi` | `python3 -B test1.py` | 样例项的 cof、NF、OT | 目测 |
| `eboi/test2.py` | 同上 | `python3 -B test2.py 6000` | 闭包留 NF/OT, 递减, 单调; `isNF` 对 `isOT∘τ` | 6000 项 25750 步 0; 14665 原始项 3688 NF 0 不一致 |
| `eboi/test3.py` | 同上 | `python3 -B test3.py 6` | 基于 bot 的 $G$ 的 NF 对 OT, 对 Setzer 形 NF; 序公理 | 14665/3688, 0 不一致 |
| `eboi/test4.py` | 同上 | `python3 -B test4.py 20000 900` | 大闭包 | 20000 项 66650 步 0; 18437 ω 项单调; 30 万对/三元组 0 |
| `eboi/cover.py` | 同上 | `python3 -B cover.py` | 分支走到次数 | $\psi_I$: $\rho<I$ 5986, $=I$ 789, $>I$ 46; $\psi_u$: 穿透 1228, 折叠 1059; $\Omega_u$ $\mathrm{cof}=I$ 10 |
| `eboi/tw.py` | 同上 | `python3 -B tw.py 6000` | `EBOI` 对 $T_W$ | 13404/2463, 14295/1572, 纯 EBO 项 0 不一致 |
| `eboi/tw2.py` | 同上 | `python3 -B tw2.py 6000` | 去掉 $1+$ 偏移 | 15867/0 |

`eboi/` 里的 `closure.py`、`test2data.py` 是库. 如须用 `-I`, 把目录拷到暂存处, 用 `sys.path.insert` 的薄包装跑.

**`gen.py`、`gen2.py`** 生成 `SetzerTest.agda`, 写到 `../setzer/SetzerTest.agda`. `gen2.py` 要读 `hdr.txt`, 仓库里**没有**这个文件, 所以 `gen2` 不能原样重跑. 没有重跑.

**`eboi/SetzerTest.agda`** 用 Agda 跑归档的 Setzer `lt`、`isOT` 本身 (`refl` 断言: `isNF ≡ isOT ∘ τ` 在 `raw` 1489 项上, `<?` 对 `lt` 在 1000 项 $10^6$ 对上, $t[n]$ 的性质). 本次**没有重编**, 只描述设置. 不要在 `archive/` 或 `probes/` 里原地编译, 免得留下接口文件:

```sh
S=<暂存目录>; R=<仓库根>
mkdir -p $S/Mahlo/Inacc $S/OCF/Align
cp $R/archive/src/Mahlo/Inacc/{Syntax,Order,Closure}.lagda.md $S/Mahlo/Inacc/
cp $R/probes/OCF/Align/{EBO,EBOI}.lagda.md $S/OCF/Align/
cp $R/probes/Survey/scripts/eboi/SetzerTest.agda $S/
cd $S && agda --library-file=<含 stdlib 的库文件> -l standard-library-2.4 -i . SetzerTest.agda
```

`Mahlo.Inacc` 三个文件的 Mahlo 导入只到彼此, `SetzerTest` 不导入 `Arith`; `EBOI` §10 说还拷了 `Arith`, 按导入看不必要. 归档文件若要 `--hidden-argument-puns` 就加上. 这套命令没有跑过, 预期要几分钟或更久 [推断].

**§5.3 的转写测试** 在 `check.py` (路径见 §7), 用法 `python3 -I check.py '' 8`, 第一个参数给 `gamma0` 或 `rep` 是敏感性变异. 未入库.

**`ExBuchholz` 的构建与 `#print axioms`** (2026-11-02 跑过, 结果见 §5.2). 全部放在一个暂存目录里, 不动家目录和 shell 配置; 下载内容: elan 安装脚本与 elan 4.2.4 发行包, Lean v4.30.0, 语义部分再加 mathlib 及其 8 个依赖的 git 克隆和 8459 个官方缓存文件. 占用: 工具链 2.5G, 句法项目 7M, 语义项目 7.4G, 缓存 437M.

```sh
B=<暂存目录>; mkdir -p $B/{home,tmp,src,mini,sem}
export ELAN_HOME=$B/elan HOME=$B/home XDG_CACHE_HOME=$B/home/.cache TMPDIR=$B/tmp PATH=$B/elan/bin:$PATH
curl -fsSL -o $B/elan-init.sh https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh   # 先读
sh $B/elan-init.sh -y --no-modify-path --default-toolchain none
git clone https://github.com/koteitan/googology-lean $B/src/repo && git -C $B/src/repo checkout 6da2de5

# 句法部分: 无依赖, 不取 mathlib
cd $B/src/repo
for f in Googology/Core.lean Googology/Core/{WF,Rewrite,Std,Morphism,Goals}.lean \
         Googology/Notation/ExBuchholz/{Basic,Order,Std,WF,Sum,FS,Closure}.lean; do
  mkdir -p $B/mini/$(dirname $f); cp $f $B/mini/$f; done
cp lean-toolchain $B/mini/
printf 'name = "glmini"\n\n[leanOptions]\npp.unicode.fun = true\n\n[[lean_lib]]\nname = "Googology"\n' > $B/mini/lakefile.toml
cd $B/mini && lake build Googology.Notation.ExBuchholz.Closure
lake env leanchecker Googology.Notation.ExBuchholz.Closure
cat > $B/ax.lean <<'E'
import Googology.Notation.ExBuchholz.Closure
namespace Googology.Notation.ExBuchholz.Term
#print axioms OTFS_thm
#print axioms bachmann
#print axioms Trian_fs_thm
#print axioms fs_lt
#print axioms fs_mono
#print axioms OT_psi_fs
#print axioms acc_of_OT
#print axioms lt_trans
#print axioms lt_trichotomy
end Googology.Notation.ExBuchholz.Term
E
lake env lean $B/ax.lean

# 去 Classical.choice 的对照: 在 mini 的副本里, Closure.lean 第 1027 和 1645 行
#   simp only [size_cons] at hsz; omega  改成  simp only [size_cons] at hsz; exfalso; omega
# 重建后 OTFS_thm 只剩 [propext, Quot.sound]

# 语义部分: lakefile.toml 只要 mathlib (rev = "v4.30.0"), lake-manifest.json 取仓库的并删去 pss、bmselempattern,
# name 用 glsem (manifest 里不能带连字符); 拷入 Googology/{Core.lean,Core/,Rank.lean,Cofinal.lean} 与 ExBuchholz/*.lean
cd $B/sem && lake exe cache get && lake build Googology.Notation.ExBuchholz.RankVal
# 然后对 Term.OTLt_wf, Term.valEquiv, Term.exists_lt_fs_numeral, Term.rank_exbOT_eq_val 跑 #print axioms
```

`lake exe cache get` 会编译并运行 mathlib 的缓存工具, 这是全过程唯一运行的非工具链程序; `ExBuchholz` 自身除 §5.2 的 `#guard` 外不在构建期执行代码. 我们实际用的项目名是 `gl-mini`, 这里写 `glmini` 只是统一写法, 没有影响. 上面的 `git clone` 那行我们没有照跑: 实际是拷贝先前已有的同提交克隆. 这段命令没有作为一个整体重跑过.

**EBO 与 `ExBuchholz` 的逐项比较**: `probes/Survey/scripts/ebo_vs_exbuchholz.py`, 在该目录运行 `python3 -I ebo_vs_exbuchholz.py`; 两边都是我方的 Python 转写, 不是 Lean 或 Agda 代码本身. 大小不超过 8 的全部项 (52788 个, 含非标准形) 上 `fsn`、`fsT`、`cmp`、`dom` 与标准形无不一致. 参数可做变异测试 (见脚本开头 `MUT`).

## 9. 链接表

全部访问于 2026-11-02. Fandom 页面经用户授权用其 Chrome 只读, 抓取工具直连返回 402. 博客内容 CC-BY-SA.

| 键 | 链接 |
|---|---|
| Buchholz 1986 | <https://epub.ub.uni-muenchen.de/3841/1/3841.pdf> |
| BCW 1994 | <https://epub.ub.uni-muenchen.de/3849/1/16.pdf> |
| Rathjen 1990 | <https://web.archive.org/web/20231208185422/http://www1.maths.leeds.ac.uk/~rathjen/Ord_Notation_Weakly_Mahlo.pdf> |
| Rathjen 1991 | <https://web.archive.org/web/20231207051454/http://www1.maths.leeds.ac.uk/~rathjen/KPM-Ordinal-Analysis.pdf> |
| Takaki 2005 | <https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1437-11.pdf> |
| Wilken 2024 | <https://arxiv.org/abs/2410.15953> |
| Kovács 2022 | <https://arxiv.org/abs/2103.00223> |
| Takahashi 2024 | <https://arxiv.org/abs/2402.15074> |
| Hunter (BMS) | <https://arxiv.org/abs/2307.04606> |
| Maksudov EBO | <https://sites.google.com/site/travelingtotheinfinity/the-extension-of-buchholz-s-function> |
| Maksudov $T_W$ | <https://sites.google.com/site/travelingtotheinfinity/hypcos-s-notation-with-weakly-inaccessibles>; 博客 <https://googology.fandom.com/wiki/User_blog:Denis_Maksudov/FS_for_Hypcos%27s_notation_(with_weakly_inaccessibles_cardinals)_up_to_%CE%A8(M%5E2)> |
| Maksudov Mahlo | <https://sites.google.com/site/travelingtotheinfinity/ocf-and-ordinal-notation-based-on-a-weakly-mahlo-cardinal>; 博客 <https://googology.fandom.com/wiki/User_blog:Denis_Maksudov/OCF_and_ordinal_notation_based_on_a_weakly_Mahlo_cardinal> |
| Wiki 基本列表 | <https://googology.miraheze.org/wiki/List_of_systems_of_fundamental_sequences> |
| p進大好きbot EBO | <https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Ordinal_Notation_Associated_to_Extended_Buchholz%27s_OCF> |
| *Rathjen-type* | <https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Rathjen-type_Ordinal_Notation> |
| Naruyoko 实现 | <https://github.com/Naruyoko/googology/tree/main/padicBotRathjen>, <https://naruyoko.github.io/googology/padicBotRathjen> |
| *Cheatsheet* | <https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/Cheatsheet_on_Properties_of_OCFs> |
| *Misconceptions* | <https://googology.fandom.com/wiki/User_blog:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/List_of_common_misconceptions_about_Rathjen%27s_psi> |
| KawamoYurase | <https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:KawamoYurase/Denis%E3%81%AE%E5%BC%B1%E3%83%9E%E3%83%BC%E3%83%AD%CF%88%E3%81%AB%E3%81%A4%E3%81%84%E3%81%A6> |
| みずどら | <https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:%E3%81%BF%E3%81%9A%E3%81%A9%E3%82%89/%E5%88%B0%E9%81%94%E4%B8%8D%E8%83%BD%E5%9F%BA%E6%95%B0%E3%82%92%E6%95%B0%E3%81%88%E4%B8%8A%E3%81%92%E3%82%8B%E5%B4%A9%E5%A3%8A%E9%96%A2%E6%95%B0> |
| Kanrokoti | <https://googology.fandom.com/wiki/User_blog:Kanrokoti/Inaccessible_%CF%88_function> |
| Exmachina Small ψ | <https://googology.fandom.com/wiki/User_blog:David_Exmachina/How_I_Actually_Came_Up_With_The_Fundamental_Sequence_Of_Rathjen%27s_Little_%CF%88_Function> |
| Exmachina $\Psi$ 修复 | <https://googology.fandom.com/wiki/User_blog:David_Exmachina/How_My_Fundamental_Sequence_Of_Rathjen%27s_Capital_%CE%A8_Was_BROKEN_(And_Then_I_Fixed_It)> |
| koteitan 仓库 | <https://github.com/koteitan/googology-lean>, <https://github.com/koteitan/bms-rathjen>, <https://github.com/koteitan/pss-proof> (提交见 §5.1) |

其它页面的链接在调研 §11–§12 的对应小节, 也都是这一天访问的.
