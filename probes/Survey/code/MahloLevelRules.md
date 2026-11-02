# M 层实现的规则: 静态代码分析

> **证据记录, 手册见 [CodeGuide](../CodeGuide.md).** 查结论看手册; 本文是阅读当时的记录, 已知更正记在手册 §3、§6, 原文未改.

> 状态日 2026-11-02. **纯静态**: 只读源码, 没有构建, 没有运行任何代码 (包括 JS). 手算处都标 [手算]. 读到的写 [读], 推出来的写 [推断]. 规则一律转述.

**最重要的七条** (细节见各节):

1. **Exmachina 的 Rathjen 系统源码是公开的** (`DavidExmachina/garden-of-ordinals`, 无许可证), 调研 §12.10 记成未找到. `RathjenM` 模块 530 行, 是最短的二元 χ 实现 (§3).
2. **序与标准形都不依赖一般基本列** (§6). $r^\ominus$ 用的 $b[0]$ 只作用于后继, 即 `pred`. 手册 §4.3 与调研 §3.3 的"同时递归"说过头了; 依赖是单向的, `EBOI` 的分层可以原样沿用.
3. **Maksudov 形状的序层, 两项大小之和下降** (§6, 手算). 所以可定义, 但不是结构递归: $r^\ominus$ 现场造节点.
4. **同一写法 $\psi_I(0)$ 在两族系统里是不同序数** (§5.2): φ-free 的是 $\Lambda=\Phi_1(0)$, φ 原语的是 $\Phi$ 的 Γ-不动点. 跨族只能比序嵌入, 不能比展开.
5. **规则 13–15 的递归结构在三个二元系统里相同** (上一项喂给 $b[\cdot]$), 差在种子与外包的 $\psi_\cdot(0)$ (§5.2 G). **koteitan `fsN` 没有这条规则**: 字面读 $\psi_{ZM}(0)[n]$ 是常量 $Z\,0$ (§2).
6. **"ψ 的参数都 $<M$" 只对 Maksudov 与 $\mathfrak T(M)$ 成立.** Exmachina 与 Naruyoko 都让 $\mathrm{cof}\,\gamma=M$ 落在 ψ 上, 走 $\psi_{\chi_{A[n]}(0)}(0)$ 或 $\psi^M$ (§3, §5.1). 这修正手册 §4.3 的范围.
7. **蓝本建议**: Maksudov/KawamoYurase 形状 + `EBOI` 架构, 不加 φ (§7). **M 层没有任何系统有证明**, 也没有可搬用的展开语料 (§8).

## 1. Naruyoko `padicBotRathjen` (*Rathjen-type* 的 JS 实现)

**版本与许可.** `Naruyoko/googology` @ `958ac91`; `padicBotRathjen/implementation.js` 1944 行 (与此前存的副本逐字节相同). 仓库根无 LICENSE 文件 (GitHub API 报 none), 但 `implementation.html:47` 声明 `implementation.js` 与页面用 **CC BY-SA 3.0 Unported** [读]. 下文行号都指该文件 (记 `impl`).

**签名与文法** [读]. 项是 `0`、和、`φ^i_a(b)`、`χ^κ_a(b)`、`ψ^κ(a)` (`impl:755–767`). 都是五类纯句法集合: T, PT (主项), ST (后继), RT (正则形状, `impl:794–810`). 常量: $1=\varphi^0_0(0)$, $\omega=\varphi^0_0(1)$, $\Omega_1=\varphi^1_0(0)$, $M_0=\varphi^2_0(0)$ (`impl:747–750`); 解析器把 $\Omega_{n}$ 读成 $\varphi^1_0(n-1)$, 把 `I_t` 读成 $\chi^{M}_0(t)$, 把 `K_t` 读成 $\varphi^3_0(t)$ (`impl:158–195`). 所以**这里没有 $\Omega_0$**, 也没有单独的 $M$ 符号: $M$ 只是 φ 第三层的一项, 上面还有 $M_t$, $\chi^{M_1}$, $K$, $\varphi^{\Omega}$ 等. 这比 Maksudov 的系统宽得多.

**序** `lessThan` (`impl:939–1038`) [读]. 一个大的二元分派, 14 组子句, 按 $(S,T)$ 的构造子走. 依赖 `termAstGeq` ($a^{*\ge T}$), `termMinus` ($S^-$, 即 $r^\ominus$), `termBullet` ($S^T_\bullet$), `triangleLessThan` ($\lhd(L,C)$, 即 $K_L$), 且入口就查 `inT`. χ 对 χ 的子句形如: 上标相同时 $a=c\wedge b<d$; $a<c$ 时要 $a^{*\ge l}<T$ 且 $b<T$; $c<a$ 时 $S\le c^{*\ge k}$ 或 $S\le d$. 上标不同时比 $k\le T$、$S\le T^-$ 等 (`impl:1009–1020`). 这与 Maksudov 的 10.x 同形, 只多了上标这一层, 且 $c^{*}$ 处已是 $\le$ (对应 `P1` 的补丁方向).

**标准形** `inOT` (`impl:1071–1150`) [读]. 不是"形成条件 + 简单 G": 三个构造子各有一串分情形判据 (φ 12 支, χ 9 支, ψ 1 支). ψ 处最干净, 只要 $a\lhd(\kappa,a)$. χ 处要 κ 是 RT、$\mathrm{pred}(\deg\kappa)\ne0$、$b<\kappa$、$a<\psi^{\kappa^+}(0)$, 然后枚举 $b$ 的外形. 和要求尾 $<\varphi^0_0(a+1)$. **这几处都现场拼出更大的项** ($\psi^{k^+}(0)$, $\chi^k_a(0)$, $\varphi^0_0(a+1)$, 见下 §6).

**dom 与 cof=M 的分派** [读]. `dom` (`impl:1251–1311`) 值域是 $\{0,1,\omega\}$ 加项. $M$ 走 3.3: φ 的上标 dom 非 0、$a$ dom 0、$b$ dom 0 或 1, 返回自身; 基本列 3.3 是 $[n]=n$. 所以 $\mathrm{dom}\,M=M$ 不是特例, 与所有 $\varphi^{i\ge1}_0(b)$ 同一条. χ 同型 (4.1). ψ 的 dom 在 $a$ 为 0/后继时查 $\chi^k_0(0)\in$ OT, 否则看 `index k`.

**规则 13–15 的对应物** `fund` 5.5 (`impl:1440–1450`) [读]. 取 $\psi^k(a)$, $a$ 为 0 或后继, `index k` $=(l,c)$ 且 $c\ne0$ (即 $k=\chi^l_c(\cdot)$). 按 $\mathrm{dom}\,c$ 三分:

| 支 | 条件 | $n$ 为后继时 | $n=0$ 时 |
|---|---|---|---|
| 5.5.1 | $\mathrm{dom}\,c=1$ | $\chi^l_{c[0]}(S[n{-}1])$ | $\chi^l_{c[0]}(\psi^-(k,a))$ |
| 5.5.2 | $1<\mathrm{dom}\,c<l$ | 无递归 | $\chi^l_{c[n]}(\psi^-(k,a))$ |
| **5.5.3** | $l\le\mathrm{dom}\,c$ | $\chi^l_{c[S[n{-}1]]}(0)$ | $\chi^l_{c[\psi^-(k,a)]}(0)$ |

这与 Maksudov 7–9 / 10–12 / 13–15 **同形**. 差别: 判据是 $l\le\mathrm{dom}\,c$, 不是 $\mathrm{tp}=M$ (这里 χ 的上标 $l$ 可变, 所以 $l$ 是任一 $\varphi$-层正则); 种子是 `psiMinus` (`impl:1350–1362`), 只在 $a$ 后继或 $k^-\ne0$ 时加 1.

$c=0$ 时走 `index` 下钻 (`impl:881–890`): $\mathrm{index}(\chi^k_0(b))=\mathrm{index}(k)$. 这是 5.3/5.4, 即 φ-层的 Γ-闭包 (`gamma`, `impl:1318–1326`): $\gamma(I,S,0)=S$ (若 $\varphi^I_S(0)\in$ OT, 否则 $S+1$), $\gamma(I,S,n{+}1)=\varphi^I_{\gamma(I,S,n)}(0)$. 另一个独立入口 5.1/5.2: $\chi^k_0(0)\in$ OT 时 $\psi^k(\cdot)[n]=\chi^k_{\gamma(0,k,n)}(\cdot)$, 这是 $\psi_M$ 式的折叠, 但只在 $\deg k\ge2$ 时可达 [推断: 来自 `inOT` 4 对 `pred(deg k)`].

**γ-链** 5.7 (`impl:1455–1458`) [读]. $\mathrm{dom}\,a\ge k$ 时 $\psi^k(a[\psi^{\mathrm{dom}\,a}(\cdot)])$, 链头 $\psi^{\mathrm{dom}\,a}(0)$. 与规则 22 同形.

**不动点与 $a\in B(a,\chi_a(b))$** [读 + 推断]. 没有一条命名的约束. 它拆散在三处:
- `inOT` 4.4–4.9 枚举 $b$: $b$ 是 $\chi^l_c(d)$ 且同度时要 $c\le a$ (排除 $\chi_a$ 的不动点); $b$ 是 $\psi^l(c)$ 时**若 $a\not\lhd(l,c)$ 就直接通过** (4.6). 后一条读法: $a$ 不在 $C_l(c)$ 里, $\psi_l(c)$ 不可能是 $\chi_a$ 不动点.
- 序 10.2/10.3 的 $a^{*\ge l}<T$: 这就是 $a$ 的可构造性条件.
- $\Phi$ 型 (`pred(deg k)=0`) 不许出 χ.

**忠实度** [读 + 手算]. 规则编号与博客一一对应, 注释写着子句号 (`//5.5.3.1`). Γ₀ 种子差异在代码里可手算确认: $\Gamma_0=\psi^{\Omega_1}(0)$, $\Omega_1=\varphi^1_0(0)$, `termMinus` 1.1 返回 $i=1$, `psiMinus` 1 给 $1+1=2$, `gamma(0,2,0)` 因 $\varphi^0_2(0)\in$ OT 返回 $2$, 再 $\varphi^0_2(0)=\zeta_0$, $\varphi^0_{\zeta_0}(0)$. 这正是 koteitan 记录的 $2,\zeta_0,\varphi_{\zeta_0}(0),\dots$ [手算, 只查到这三项]. 与博客的偏移是否就在这一 "+1" 上, 要对博客表, 见 §2 的 koteitan 记录. **M 层规则本身的忠实度我没有逐条对博客**: 只有文本编号对齐这一证据.

**$\Omega$ 的基本列要经 φ^1.** $\psi_{\chi_a(b)}$ 的结果用 $\varphi^1$ 与 $\chi$ 表达, 所以 $I[n]$ 型的塔不是 $\chi(0,\cdot)$ 而是 $\varphi^1_{\gamma}(0)$ (5.3 + `gamma`). 这是 φ 原语带来的结构差异, 影响 §5 的比较.

## 2. koteitan `bms-rathjen`: `lean/TM/`

**版本与许可.** @ `7bde9d7`; Lean 4, 无外部依赖; 根 LICENSE: CC BY-SA 3.0 [读]. 下文文件都在 `lean/TM/`, 没构建.

**签名** (`Terms.lean`) [读]. 七个构造子: `zero, M, add, omg, phi, psi, Z`. `Z a` 是 $\chi_a(0)$, 只有一元. `phi` 是 Rathjen 的 $\bar\varphi$, **跳过不动点地计数** (文件头专门警告: $\bar\varphi(0,\varepsilon_0)=\omega^{\varepsilon_0+1}$). 这是"原语"的另一种写法, 使标准形唯一, 代价是 `phiNF`/`phiShifted` (`FS.lean:92–111` 的长注释记了一个"未修的缺口").

**序** (`Order.lean`) [读]. `starF`/`ltF` 互递归, **用燃料, 燃料是两项大小之和**. 文件头说每次递归严格降低大小之和 (未见证明, 只是注释). $\kappa^-=\delta^*$ 只需 $*$. **`Kset` 不进序**: 16 条子句只用 $*$. 这与二元 χ 不同 (§6).

**标准形** (`NF.lean`) [读]. `inT` 递归, 只有 $\psi$ 处看 `Kset k a` 都小于 $a$. `Z a` 只要 `inT a`. **没有 $a\in B(a,\chi_a(b))$ 约束, 也没有 $G$**: 一元 χ 没有第二参数, 不存在 $\chi_a$ 不动点的问题. 这正是 Rathjen 1991 的简化点.

**基本列** (`FS.lean`) [读]. 三层: `kindT` (零/后继/极限, 句法), `cofT` (共尾度标记), `fsT` (项索引), `fsN` (ℕ 索引). 作者写明这是自己的设计. $\mathfrak T(M)$ 没有规则 13–15 的完整对应物:

| $\psi_{Z d}(a)$ | `fsN` 取值 [读] |
|---|---|
| $a=0$, $d$ 后继或 0 | Γ-闭包 `iterGamma (psiSeed k)` |
| $a=0$, $d$ 极限 | $Z(d[n])$, `fsN d n` |
| $a$ 后继 | Γ-闭包, 种子 $\psi+1$ (**不看 $d$**) |
| $a$ 极限, cof ω | 穿透 |
| $a$ 极限, cof $p\ne\kappa$ 正则 | `diagIdx`: 经 $\psi_p$ 的塔, 2026-08-21 才修 (`:239, :245`) |
| $a$ 极限, cof $=\kappa$ | $\psi_\kappa(a[t_{n-1}])$ |

**三个具体缺口** [手算, 按字面读函数, 未运行]:

1. **$\psi_{Z M}(0)[n]$ 是常量.** $d=M$ 走 `isLim` 支得 $Z(\mathrm{fsN}\,M\,n)$, 而 `fsN M _` 落到通配 `zero`, 所以每项都是 $Z\,0=\Omega$. 文件头也说 "`Z δ, M`: `fsN` is undefined (junk 0)". 所以**规则 13–15 的 $a[n]=\chi(b[a[n-1]],0)$ 在这里不存在**. 这是 $\mathrm{dom}\,c\ge l$ 的恰当情形.
2. **`fsT` 的自环.** $\mathrm{cof}\,\psi_{Z\Omega}(0)=\Omega$ (`cofT`), 但 `fsT (psi k zero) s = psi k (fsT zero s) = psi k zero`, 项索引基本列恒等于自身. 这是 Naruyoko 5.5.2 的区域.
3. **$a$ 后继时不按 $d$ 分派.** 表里第三行与 Naruyoko 5.5.x 不同. 一元 χ 没有第二参数放基底, $\chi_{c[n]}(\psi^-)$ 写不出来, 只能退回 Γ-闭包 [推断]. 这是下面"一元的局限"的实质.

**一元 χ 的局限** [读 + 推断]. 第二参数做两件事: 枚举 $\Omega$ 层级 ($\chi_0(\alpha)=\Omega_{1+\alpha}$), 以及**携带基底**. `Terms.lean` 文件头、`plan/chi-2ary.md` 记了第一件: $\Omega_2=\chi_0(1)$ 无项, `Z 1` 是 $I$. 该文也记录一条教训: 值都写得出 (可数值全有项), 写不出的是**作为折叠目标的正则基数** $\Omega_2$, 所以 $\psi_{\Omega_2}$ 型中间对象没有名字. 仓库作者评估过改成二元, 算出要动约 1200 处, 决定不改 [读, 据该文]. 对本项目: **EBO 的 $\psi_u$ 恰恰全靠这些中间基数, 所以 $\mathfrak T(M)$ 不能作 EBO 的超集** [推断]. 第二件我没在该文里见到, 是我从 `fsN` 读出的.

**外部见证** [读]. $\Gamma_0$ 以下 12 行 `#guard` 对博客表; `cofT` 对 $\mathrm{dom}$ 19 例 (169 项库内 169/169). 这些都在 $\Omega$ 量级, 不涉 M 处规则. `Lemmas.lean` 未见 `fsN` 相关引理 (grep 为空).

**Γ₀ 差异** [读]. `FS.lean:323–342` 记: 博客的 $\Gamma^0(0,1+1+\cdots)$ 与 `fsN` 差一位 (`ours[n]=Γ⁰(0,n+1)`, 种子 1); 实现的种子是 2, 51 项中 21 项与 `fsN` 相同; 作者判定以博客为定义. 我的手算 (§1) 确认实现确实从 2 起; 博客本身未在本次重读.

## 3. David Exmachina *Garden of Ordinals*: `ASSETS/ordinal.js`, 模块 `RathjenM`

**版本与许可.** `DavidExmachina/garden-of-ordinals` @ `618e814` (2026-10-23), 公开. **无 LICENSE, `index.html`/`main.js` 无版权声明** [读, grep]: 默认保留一切权利. 模块在 `ordinal.js:858–1388`; 下文行号指此文件. 同文件还有 `RathjenK` (`:1389`), `Stegert1`, `Stegert2`. 调研 §12.10 说"没找到源码", 现在找到了.

**签名与文法** [读]. 项是字符串, 和是拼接. 单项: `(v a,b)` $=\varphi_a(b)$, `(V a,b)` $=\Phi_a(b)$, `(x a,b)` $=\chi_a(b)$, `(r κ,γ)` $=\psi_\kappa(\gamma)$; 常量 `M` 与顶 `A`. `(v,)` 是 1. **二元 χ, 且 φ、Φ 都是原语.** 这是 Rathjen 1990 原系统的未简化写法.

**序** `lt` (`:1018–1100`) [读]. 同构造子比: χ 对 χ 按 `(a,b)` 三分, 第一支恰是 $\chi_a(b)$ 对 $\chi_c(\chi_a(b))$; 第二支 $b<T$ 且 $a^*<T$; ψ 对 ψ 比 κ. 异构造子: χ 对 ψ 要 $S<\kappa$ 且 $S\in C_\kappa(\gamma)$. 依赖 `st` ($a^*$, `:898`), `isreg`, `least`, `inc`.

**$C$-成员的写法** [读]. **不用 $K$ 列表, 用 `least`:** `least(c, κ)` (`:923`) 返回使 $c\in C_\kappa(\gamma)$ 的最小 $\gamma$, `inc(c,κ,γ)` 就是 $\gamma\ge$ `least(c,κ)` (`:954`). 这与 $K_\kappa(c)\lhd\gamma$ 等价但是**单值函数**, 表述更短; 代价是要在子项之间取 max, §6 的大小度量不再直接成立 [推断]. 它用 $\kappa^-$ 的显式写法: `(x α,β+1)` 的前驱写作 `(x α,fs β)`, `(x α,)` 的前驱是 $\alpha^*$ (`:943–944`).

**标准形** `isnormal` (`:961–990`) [读]. 极简: $\varphi$ 要两参数都小于自身; $\chi$ **只要 $b<\chi_a(b)$**; $\psi$ 要 κ 正则且 $\gamma\in C_\kappa(\gamma)$. 所以"不动点"和 $a\in B(a,\chi_a(b))$ **都推给序**: `lt` 的 χ-χ 第一支判 $\chi_c(d)<\chi_a(\chi_c(d))$ 为 "$c\le a$ 或 $a^*\ge\chi_c(d)$" [手算, `:1048`]. 也就是说: 不动点 ⟺ $a<c$ 且 $a^*<$ 该值. 这是我见到的**最短的写法**. 对应地 `norm` (`:1125`) 把非标准的 χ 映回 $b$ (别名规范化), 这与我方 `Ω̂` 同一思路.

**cof** (`:1150–1184`) [读]. 值: `""`, 1, ω (`(v,(v,))`), 或项. 正则返回自身. ψ 处: $\mathrm{cof}\,\gamma\ge\kappa$ 得 ω; $\gamma$ 极限且 $\mathrm{cof}\,\gamma<\kappa$ 得其 cof; 其余看 $\kappa=\chi_\alpha(\beta)$ 的 $\alpha$: $\mathrm{cof}\,\alpha$ 是 $\le 1$ 或 $M$ 时得 ω, 否则得 $\mathrm{cof}\,\alpha$. **这解释了 M 的分派:** $\mathrm{cof}\,\alpha=M$ 时 ψ 的共尾度落回 ω, 其它不可数 cof 则继承.

**基本列** `fs` (`:1195–1353`). ψ 分支 (`:1286` 起) 的顺序 [读]:

| 分支 | 条件 | 规则形状 ($\psi_{\chi_\alpha(\beta)}(\gamma)$) |
|---|---|---|
| `GAMMA COF IS MAHLO` | $\mathrm{cof}\,\gamma=M$ | $\psi_\kappa(\gamma[\psi_{\chi_{A[n]}(0)}(0)])$ |
| `AT LEAST CARD` | $\mathrm{cof}\,\gamma\ge\kappa$ | γ-链: `re`, $c_{n}=\gamma[\psi_{\mathrm{cof}\gamma}(c_{n-1})]$, 链头 0 |
| `GAMMA IS LIMIT` | 其它 | 穿透 |
| `ALPHA IS ZERO` | $\gamma$ 与 $\alpha$ 无极限 | $\varphi$-塔; 基底经 $\psi+1$ |
| `ALPHA IS ONE` | $\alpha=1$ | $\Phi$-塔: $(V\ \text{prev},\cdot)$; 起 `(x,)` |
| `ALPHA IS SUC` | $\alpha$ 后继 | $\chi_{\alpha-1}(\text{prev})$ (规则 7–9) |
| `ALPHA IS LIMIT` | $\mathrm{cof}\,\alpha<M$ | $\psi_{\chi_{\alpha[x]}(\text{基底}+1)}(0)$ (规则 10–12) |
| **`ALPHA COF IS MAHLO`** | $\mathrm{cof}\,\alpha=M$ | $a[0]$=基底; $a[n]=\psi_{\chi_{\alpha[a[n-1]]}(0)}(0)$ (规则 13–15) |

**三处与 Maksudov/Naruyoko 不同** [读 + 推断]:

1. **ψ 的参数可以 $\ge M$, 所以 $\mathrm{cof}\,\gamma=M$ 能出现在 ψ 上.** 第一支专门处理它, 走 $A[n]$ (`:1205–1210`: $A[0]=0$, $A[1]=M$, $A[2]=\varphi_M(1)$, 再 $\varphi_{A[n-1]}(0)$), 落到 $\psi_{\chi_{A[n]}(0)}(0)$. **手册 §4.3 "ψ 的参数都 $<M$" 只对 Maksudov 与 $\mathfrak T(M)$ 成立, 对 Exmachina 转写的 Rathjen 1990 不成立** [读 `isnormal`: ψ 不限 $\gamma<M$; 论文原文未核]. 这是最大的结构差异.
2. **规则 13–15 外面多包一层 $\psi_{\cdot}(0)$.** $a[n]=\psi_{\chi(\alpha[a_{n-1}],0)}(0)$, 而不是 $\chi(\alpha[a_{n-1}],0)$. 规则 10–12 也一样. 两者应互为共尾 [推断, 未证]. 所以**逐项比较时这里必不相同**.
3. **规则 10–12 的基底不总加 1.** `ALPHA IS LIMIT` 无基底时用 `tail`、比较决定是否取 $\mathrm{tail}+1$ (`:1338–1342`). `tail` 取 $\alpha$ 中 $<M$ 的尾巴, 目的应该是让 $\chi_{\alpha[x]}(\cdot)$ 超过 $\alpha$ 自带的小部分 [推断]. Maksudov 没有这个机关.

**`strong` 参数.** `fs(a,n,strong)` 中 `strong` 为真时 `M[n]=ψ_{χ_{A[n]}(0)}(0)`, `χ_a(b)[n]=ψ_{χ_a(b)}(A[n])`, 即用 ω-序列代替恒等 (`:1214–1216, :1280–1282`). 只在 `ALPHA IS LIMIT` 这几支传下去. 用途未读.

## 4. 其余实现

**Kanrokoti 的 I 层 (`Naruyoko/googology/kanrokotiInaccessiblePsi/implementation.js`, CC BY-SA 3.0, `implementation.html:36`).** 不到 χ、M, 但它是**唯一直接在 EBO 记号上加 I 的实现**, 所以列在这里. 文法: `I(a,b)`, `ψ(u,a)`, 和; ψ 的参数只能由 ψ 项组成 (`inTPsi`, `:600–622`).
- **序是纯字典序** (`:688–720`): I 项大于一切 ψ 项, 内部比 (sub,inner). 没有 $\star$, 没有 $K$, 没有 $G$ [读].
- **标准形是搜索定义**: `isStandard` 从 `limitOrd(n)` 沿 `fund` 往下走, 走到就算 (`findOTPath`, `:913–941`) [读]. 不是递归谓词, 依赖 `fund` 单调.
- **没有 $\psi_I$ 这个折叠**. $\psi_0(\Omega_I)$ 的规则是直接往第 0 层塌 (`fund` 4.3.2.2.1, `:860`): 手算 $\psi(I,0)[T]=\psi(I[T],0)=\Omega_T$ (`:819` 的 4.1.2.2.1), 再用链 $\psi(0,\Omega_{\psi(0,\cdot)})$. 所以这里 $\psi_0(I)$ 是 EBO 量级, 而 $\Lambda$ 不是一个项 [手算 + 推断]. $I_0(b)$ 的 $b$ 像 $\omega^b$ 式乘法, 不是枚举 (3.2: $I_0(b+1)[n]=I_0(b)\cdot n$ 型) [读 + 推断].
- 顶是 $\psi_0(\Omega_{I_{\psi(I_{\cdots})}})$, 比 $\chi(2,0)$ 低 [推断]. 测试表 76 项 (`:947` 起).
- **与 EBOI 的差别是根本的**: EBOI 带 $\psi_I$ 并且用 `isNF` 递归, 这边不带. 所以它不是"EBOI 的前身"; 手册 §3 "贴合度最高" 只对项的外形成立.

**不含 I、χ、M 规则, 无须比较:**

| 仓库 | 版本 | 内容 [读] | 许可 |
|---|---|---|---|
| `hypcos/notation-explorer` | `30c43bd` | Taranovsky (`TON-*`)、扽西 (`DEN*`)、BMS 类山脉、`cOCF` (solarzone 写的一元 `p`/`P`), grep 无 mahlo/inaccess/χ. 没有序数函数式的 M 规则 | 无 |
| `AzertyWasTaken/Ordinals` | `a921bf9` | 序列、九头蛇、BMS 类, `Metadata/` 与 `TODO` grep 无 mahlo/inaccess/rathjen/psi | MIT |
| `vihdzp/ordinal-notation` | `46a81b1` | Lean, Cantor、Veblen、Buchholz, grep 无 mahlo; README "under construction", 仓库已归档 | 无 |
| `koteitan/bms-paper-formalization` | `4a83c05` | Isabelle BMS; ψ 只在 README 里出现 (`git grep`), 无 ψ 侧规则 | MIT |

`Naruyoko/googology` 另有 `IPsi`, `inaccessiblePsiExperimental`, `strongInaccessiblePsiExperimental`, `weakKPsi`, `strongKPsi` 等, 各约 900–1200 行, **本次没读** (grep "mahlo|χ" 没命中它们); `NotCollapsing/II.html` 命中但只看了文件存在.

## 5. 跨实现对照 (问题 1、2)

### 5.1 结构表

| | Maksudov (`mnot.py` 转写) | Naruyoko / *Rathjen-type* | Exmachina `RathjenM` | koteitan $\mathfrak T(M)$ | 我方 `EBOI` |
|---|---|---|---|---|---|
| χ 元数 | 二元 | 二元 + 上标 κ | 二元 | **一元** | 无 χ |
| φ | 无 | 原语, 三层 $\varphi^i$ | $\varphi$, $\Phi$ 原语 | $\bar\varphi$ 原语 | 无 |
| ψ 的下标 | $\mathcal R$ | RT, **含 $M$** | χ 正则 (`isreg`), 无 $\psi_M$ | `Z a` | $\psi_u$ 全 $T$, 加 $\psi_I$ |
| ψ 的参数 | $<M$ | **无上界** | **无上界**, 顶 `A` | $<M$ | 全 $T$ |
| $M$ 之上 | $\omega^\delta$ | φ 继续 | $\varphi$ 继续到 $A=\Gamma_{M+1}$ | $\bar\omega^\delta$ | 无 |
| $\mathrm{cof}\,M$ | 第一参数 | 第一参数 **和** ψ 参数 | 第一参数 **和** ψ 参数 | 无规则 (常量) | 无 $M$ |
| ψ 参数 cof $=M$ 时 | 不发生 | 5.7: 经 $\psi^M(\cdot)$ | 专门分支, 经 $\psi_{\chi_{A[n]}(0)}(0)$ | 不发生 | 无 |
| $C$-成员 | `K` 列表 | `triangleLessThan` | `least` 单值 | `Kset` 列表 | 无 $C$; `isNF` 用 $G$ |
| 不动点 | `G(a,b)` | `inOT` 枚举 $b$ 的外形 | 只查 $b<\chi_a(b)$, 推给序 | 无 | `Fi`, 灵巧构造子 |
| 序依赖 OT | 否 | **是** (`termMinus`、`termAstGeq` 查 `inOT`) | 否 | 否 | 否 |
| 标准形 | `inT` 递归 | `inOT` 递归 | `isnormal` 递归 | `inT` 递归 | `isNF` 递归 |
| 基本列的索引 | 项 $x$ (ω 处 `unnat`) | 项 | 项 (ω 处经 $n[0]$ 递归) | `fsT` 与 `fsN` 分开 | `fsT` 与 `fsn` 分开 |

**$\psi^M$ 的来历** [读 + 手算]. Naruyoko 里 $M$ 是 RT, 所以 $\psi^M(0)$ 是合法项: `inOT` 第 5 支只查 RT 与 $\lhd$. 它的基本列走 5.1, $\chi^M_{\gamma(0,M,n)}(0)$, 而 `gamma` 的种子因 $\varphi^0_M(0)\notin$ OT (3.2 要 $\deg$ 关系) 而取 $M+1$. 这与 Exmachina 的 $A[n]$ 是同一个想法: **用 $M$ 之上的一条 ω-序列把 M 压回来** [推断]. Maksudov 与 $\mathfrak T(M)$ 只是把这部分切掉了.

### 5.2 测试项 [全部手算, 从规则读出, 未运行, 未证]

记 $\chi(b,c)$ 按 Maksudov 写法, 其它系统已翻译. $\Phi_a(b)=\varphi^1_a(b)$.

| # | 项 | Maksudov | `EBOI` | Naruyoko | Exmachina | koteitan |
|---|---|---|---|---|---|---|
| A | $M[x]$, $\chi(M,0)[x]$, $\chi(b,c{+}1)[x]$ | $x$ | $I[x]=x$ | $x$ (3.3, 4.1) | $x$ | $x$ (`fsT`) |
| B | $\psi_I(0)=\psi_{\chi(1,0)}(0)$ | $0,\Omega_1,\Omega_{\Omega_1},\dots$ (7) | $1,\Omega_1,\Omega_{\Omega_1},\dots$ | $3,\Phi_3(0),\Phi_{\Phi_3(0)}(0),\dots$ (5.3) | $0,\Omega_1,\Phi_{\Omega_1}(0),\dots$ | 不可比 |
| C | $\psi_I(1)$ | $\psi_I(0){+}1$, 再 $\chi(0,\cdot)$ (9) | $\psi_I(0){+}1$, 再 $\Omega$ | $\psi^I(0){+}1$ 为种子的 $\Phi_\cdot(0)$ 塔 | $0,\psi_I(0),\Phi_{\psi_I(0)}(1),\Phi_\cdot(0),\dots$ | 不可比 |
| D | $\psi_I(I)$ | $\psi_I(I[c_n])$, $c_0=\psi_I(0)$ (22) | 同, $\gamma_0=\Lambda$ | $\psi^I(\psi^I(0))$ 起, 5.7 | $0,\psi_I(0),\psi_I(\psi_I(0)),\dots$ | 无 $I$ 下折叠 |
| E | $\psi_{\chi(2,0)}(0)$ | $0,I,\chi(1,I),\dots$ (7) | 无 | $\chi_0^M(3),\chi_0^M(\cdot)$ 塔 (5.5.1) | $0,I,\chi_1(I),\dots$ | Γ-闭包, **形状不同** |
| F | $\psi_{\chi(\omega,0)}(0)$ | $\chi(\omega[n],0)$ (10) | 无 | $\chi^M_{\omega[n]}(3)$ (5.5.2) | $\psi_{\chi_{n}(\cdot)}(0)$ 型 | $Z(n)$ |
| G | $\psi_{\chi(M,0)}(0)$ | $0,\Omega_1,\chi(\Omega_1,0),\chi(\chi(\Omega_1,0),0),\dots$ (13) | 无 | $\chi^M_3(0),\chi^M_{\chi^M_3(0)}(0),\dots$ (5.5.3) | $0,\psi_{\Omega_1}(0),\psi_{\chi(\psi_{\Omega_1}(0),0)}(0),\dots$ | **常量 $Z\,0$** |
| H | $\psi_{\chi(M,0)}(1)$ | $\psi{+}1$ 起, $\chi(\text{前项},0)$ (15) | 无 | $\chi^M_{\psi+1}(0)$ 起 | $\psi,\psi_{\chi(\psi,0)}(0),\dots$ (无 $+1$) | Γ-闭包 |
| I | $\psi_{\chi(M{+}1,0)}(0)$ | $0,\chi(M,0),\chi(M,\chi(M,0)),\dots$ (7) | 无 | $\chi^M_M(3)$ 起, 第二参数塔 | $0,\chi_M(0),\chi_M(\chi_M(0)),\dots$ | 未手算 |
| J | $\psi_{\Omega_1}(M)$ | 非项 | 无 | $\psi^{\Omega}(\psi^M(0))$ 起 | $\psi_{\Omega_1}(\psi_{\chi_{A[n]}(0)}(0))$ | 非项 |

**这张表说明什么** [推断]:

1. **形状相同:** 规则 19 (A) 全部相同; 规则 22 (D) 只差种子; 规则 7–9 的第二参数塔 (E, I) 在三个二元系统上相同. **13–15 (G) 的递归结构相同: 上一项喂给 $b[\cdot]$.** 这是全部二元系统共有的 M 层规则.
2. **形状不同:** Exmachina 的 G、H 在外面多一层 $\psi_\cdot(0)$; Naruyoko 的 $0$ 被 $\psi^-$ 换成常量; 这些应该互为共尾, 但没有人证过.
3. **值不同, 所以不能跨系统比项:** B 行不是差一个种子. Maksudov 与 `EBOI` 的 $\psi_I(0)$ 是 $\Lambda=\Phi_1(0)$, φ 原语系统是 $\Phi$ 的 Γ-不动点, 大得多. 因为后者的 $C$-闭包含 $\Phi$. 所以**同一个写法 $\psi_I(0)$ 在两族系统里是不同序数**, 只能各族内比, 跨族比要过 τ, 序列不可能相同. 反过来, 手册 §1 的 "用 *Rathjen-type* 交叉检验" 只能是序嵌入意义上的.
4. Maksudov 与 `EBOI` 在 B 行除首项外相同: $\chi(0,\alpha)=\Omega_{1+\alpha}$ 吸收了差异 [手算]. 这是我方能直接用的那族.

**可写成回归测试的只有族内这几条:** A; D 的递归形状; B、C、E、I 对 Maksudov 的**前 4 项** (给定 τ); G 的前 3 项. 其余都只能是"族间序嵌入"断言.

## 6. 隐藏的基础问题: 什么必须与基本列同时算 (问题 4)

**结论: 三个二元系统里, 序与标准形都不依赖一般的基本列. 依赖是单向的.** 这修正手册 §4.3 与调研 §3.3 的"$r^\ominus,K_r,a^\star,G$ 与基本列同时递归" [读].

| 系统 | 序层用到基本列吗 | 证据 |
|---|---|---|
| Maksudov | 只在 $r^\ominus$ 取 $b[0]$, 且只对后继 $b$ | `mnot.py:113` 前有断言 `tp(b)==ONE`; `tp` 为 1 只发生在 1 或末项为 1 的和上 [手算], 所以这就是 `pred` |
| Naruyoko | 完全不用 | `impl:1251` 之前的序、`inOT`、`termMinus`、`termAstGeq` 里 grep 不到 `dom(`、`fund(`. $r^-$ 直接用句法的 `pred` |
| Exmachina | 只有 `:944` 一处 `this.fs(b1[1])`, `isreg` 保证它是后继 | `:867–1100` 里 `fs`/`cof`/`type` 只此一处 (awk 查的) |
| koteitan | 不用 | `Order.lean`, `NF.lean` 不 import `FS` |

**实际的分层** [读 + 推断]:

```
层 0  句法: 形状, 是否后继, pred
层 1  {lt, star, K, ⊖, G}  互递归 (真正的同时递归在这里)
层 2  inT / isNF           依赖层 1
层 3  tp / dom / cof       依赖层 1 (只在 ψ 处比 tb 与 p)
层 4  a[x]                 依赖层 1、3; 灵巧构造子回调层 1 或 2
层 5  a[n]                 依赖层 3、4
```

`EBOI` 已经是这个架构 (`cmpᵀ` → `cof` → `fsT` → `fsn`; `isNF` 独立). **所以架构不用改, 只是层 1 变厚** [推断].

**层 1 的终止性, 这才是可行性的关键.**

- **Maksudov 形状: 两项大小之和下降** [手算: 逐子句过了 `mnot.py` 的 `lt`、`star`、`K`、`om`、`G`]. 唯一不严格的是 `p` 对 `x` 的翻转 (`not lt(b,a)`), 同大小但下一步必降. `om(r)` 现场造的 $\chi(a,b_0)$ 比 $r$ 小, 所以不破坏度量. `inT` 不在层 1 内.
- **这不是结构递归**: $\chi(a,b_0)$ 是新造的节点, $b_0$ 是表的前缀. 三条可行的做法 [推断, 都没写]: (1) 燃料, 如 koteitan 的 `starF`/`ltF` (一元版, 燃料 $2(|s|+|t|)+8$), 代价是证明时要带燃料充足引理; (2) ℕ 上的大小界 + `Acc`, `refl` 测试可能变慢; (3) 把 $r$ 拆成部件传参, 写 `cmpΘ`, 这正是 `EBOI` 的 `cmpᵀ¹`/`cmp¹ᵀ` 的手法 (§2 那段说明), 但 `⊖` 分情形 (G 真或假) 会使它分裂.
- **Exmachina 形状: 和的度量不直接成立.** `least` 里的 `lt(s0,s1)` 比的是 $\gamma'+1$ 这种派生值, 两个都来自同一个 $a$, 大小和可能超过原调用. 应该可以换度量 (如只看 $a$ 的子项), 我没细查.
- **Naruyoko 形状: 不是大小递减, 最不适合 Agda.** `inOT` 的 χ 分支调 `lessThan(a, ψ^{k^+}(0))` (`impl:1121`), 和的分支造 $\varphi^0_0(a+1)$, 这些比输入大; `termMinus` 与 `termAstGeq` 回调 `inOT`, 序因而依赖标准形. 博客评论区的 `031293` 死循环记录 (调研 §12.5) 与此相容 [推断].
- 博客文本的 KawamoYurase 版序情形更全, 第二支用 $\le$. **我没有对它做同样的度量检查**, 它不在代码里.

**基本列层 (层 4、5) 没有新难点** [推断]. 13–15 是 $a[n+1]=\chi(b[a[n]],0)$: 外层递归 $n$, 内层 `fsT b x` 结构递归 $b$, 与 `γT` 同形. 规则 22 是同一模式. `fsT`/`fsn` 分开的 `EBOI` 写法比 Naruyoko、Exmachina 的"用项当索引"好: 后者在 ω 处要对项做 $n[0]$ 递归. koteitan 的 `fsN` 用 `termination_by (sizeOf t, n)` 通过 (只读).

**真正昂贵的是证明, 不是定义** [推断]. `EBOI` 的 `fsn-dec` 建立在句法的 `_<ᵀ_` 上. 层 1 一旦含 $\star,K,\ominus$, $<$ 不再是字典序, 递减证书要对层 1 做全部情形分析; 这正是 Rathjen 没给、社区也没做的部分. 灵巧构造子同样昂贵: P2a 的 $G$ 回调 (`mnot.py:171`)、Exmachina 的 `norm`、Naruyoko 的 `linePhi` 都让 `fsT` 的输出依赖序.

## 7. `EBOI` 到 χ、M 的蓝本 (问题 3)

**建议** [推断, 我的判断]: **规则形状取 Maksudov/KawamoYurase (φ 无、参数 $<M$, 带 P1、P2 补丁), 工程架构沿用 `EBOI`. Naruyoko 只作外部序对照, Exmachina 只作规则形状的第二意见, koteitan 只作工程先例.**

| 候选 | 为何(不)作蓝本 |
|---|---|
| Maksudov/KawamoYurase | **唯一 φ-free**, 所以 $\psi_I(0)=\Lambda$, 与 `EBOI` 同族; `EBOI` 的规则就是它的特例 (§5.2 B、C、D); 层 1 大小下降. 缺点: 无证明; 序在 `mnot.py` 转写上才测过 |
| Naruyoko | **φ 原语改变值** (§5.2 第 3 点), 保不住 EBO; 序依赖 OT, 还造大项 |
| Exmachina | 同样 φ 原语; 不过 `isnormal` 把不动点推给序的写法值得借鉴; 但无许可证 |
| koteitan $\mathfrak T(M)$ | 一元, $\Omega_2$ 无项, EBO 根本进不来 |
| Kanrokoti | 无 $\psi_I$, 标准形靠搜索, 与 `EBOI` 不相容 |

**要改什么 (EBO 不动).**

| 问题 | 决定 | 理由 |
|---|---|---|
| φ 原语? | **不加** | 加了 $C$-闭包就变, `ψ₀Λ-tower` 与保守性 (`EBOI` §7) 立即失败 |
| $\Omega_0=1$? | **保留** | EBO 的约定. $\psi_{\chi(0,\cdot)}$ 不进项, EBO 的 `ψ u a` 就是它 |
| χ(0,·) | **不作构造子**; `χ̂ [] c = Ω̂(1+c)` 灵巧构造子 | 规则 7 的 $\chi(b[0],\cdot)$ 在 $b=1$ 时落到 Ω-塔, 与 `EBOI` 的 `ψ₀Λ-tower` 同一行 |
| 偏移 | 取 `EBOI` 的 | $\Lambda[0]=1$ 而非 $0$, $\gamma_0=\psi_\rho(0)$; Maksudov 的差异 C ($\psi_{\Omega_{\nu+1}}(0)=\Omega_\nu\cdot\omega$) **不引入** |
| 项 | `ψ u a`, `χ b c` ($b\ne0$), `ψχ b c a`, `M`, 之后 `ωᴹ a` | $I$ 是 `χ 𝟏 []`, $\psi_I a$ 是 `ψχ 𝟏 [] a` |
| `Rg` | 增 `χr b c` | `idx (χr b c)` 取自身, 因为 χ 正则都是 Ω-不动点, `EBOI` 的"比较 `idx r` 与 $u$"继续成立 [推断] |
| `Fi` | 扩到所有 $\chi(b\ge1,\cdot)$ 与 `ψχ` | 这是 $G$ 的最低层影子; `Ω̂` 不变 |
| 序 | 层 1 | $\psi$ 对 $f$ 的字典序在 `EBOI` 还是对的, $f$ 对 $f'$ 换成 KawamoYurase 的情形 |
| `isNF` | 新增 $G(a,b)$、$K_r$ | EBO 段 $G_u$ 应与 $K_{\Omega_{u+1}}$ 一致 (手算: $c<u$ 时 $\psi_c(d)\le r^\ominus$, $K$ 给空, 与 EBO 的"否则空"相同; **未证**) |
| 共尾度 | `cR r` 不变, 增 `cM` | 按 $\mathrm{tp}(b)$ 三分: 后继、ω 型或 $<M$ 正则、$M$ |

**建议次序** [推断]: 先做**无 M 的 χ 片段** (`χ b c`, $b$ 只取 $M$ 以下的项, 上界是 χ 的第一不动点): 这已经包含层 1 全部难点, 而不必碰 13–15 与 $\omega^\delta$. 保守性命题照 `EBOI` §7 写成 `ιT : EBOI.T → T`. 成功后加 `M` 与 13–15, 然后才是 `ωᴹ` 与规则 16–18 (P2b 在这里).

**未知的事** [不要被上面的表掩盖]:

1. **M 层没有任何系统有证明**: 无封闭性, 无递减, 无良基, 无值语义. Rathjen 1990/1991 只给序与项, 且不含基本列 (调研 §3, 我未读 1994).
2. Maksudov 序的完备性: `mnot.py` 只是测试; KawamoYurase 的全情形版未被任何代码实现 (我们也没有), 未做度量检查.
3. φ-free 的 $\psi_0(\chi(\cdot,\cdot))$ 到底比 φ 原语的同名项小多少, 上限是否仍达 $T(M)\cap M$: 不知道, 也没人证过. **所以 φ-free 系统的强度未必等于 $\mathsf{KPM}$ 量级** [推断].
4. 规则 13–15 的三个版本 (§5.2 G) 是否互为共尾: 只能手算几项, 未证.
5. $\mathrm{cof}\,\gamma=M$ 落在 ψ 参数上的那部分 (J 行) 我们建议切掉. 切掉是否丢强度: 未知 (Exmachina 与 Naruyoko 都保留).
6. $\chi(b,c)$ 的 $a\in B(a,\chi_a(b))$ 在 φ-free 下的形式: 我方只有 `mnot.py` 的 `G` 这一种转写; Exmachina 的短写法未移植, 不知道它在 φ-free 下是否等价.
7. 我没写任何 Agda, 所以"可行"都只是读代码的判断.

## 8. 测试语料 (问题 5)

**没有 M 层的"期望展开"语料.** 下面只有序的表, 展开只到 Ω 量级.

| 语料 | 内容 [读] | 层 | 许可 | 能搬吗 |
|---|---|---|---|---|
| Naruyoko `testTerms` (`impl:1517`) | 158 项升序表; `testFunction` 查 $i<j\iff$ `lessThan`, 且全部 `inOT`. 第 38 项起到 $\psi(\psi^I(0))$, 第 62 项起到 $\chi_M$. **无期望展开** | 过 M | CC BY-SA 3.0 | 见下 |
| Kanrokoti `testTermsPre` (`:947`) | 76 项升序, 带 `findOTPath` 极限 | 到 $I_a$ | CC BY-SA 3.0 | 见下 |
| Exmachina `ASSETS/DATA/SHEET/Ordinal{00..49}.json` | 5000 行; 列 `#, Veblen, Buchholz, RathjenM, RathjenK, Stegert1, Stegert2, Notes` (`resources.json`). `RathjenM` 列 911 行 (`0100`–`1010`), 210 行含 `M`. 按编号**应**是升序, 我没验证. **无展开** | 过 M | **无许可证** | **不能** |
| koteitan `FS.lean` `fsRow` (`:452` 起) | 12 行展开, 对博客表; 另有 `domCorpus` 169 项 `cofT` 比较 | $\Gamma_0$ 量级 | CC BY-SA 3.0 | 见下 |
| koteitan `table/` | BMS ↔ $\mathfrak T(M)$ 行, 以及 `refimpl-audit`、`order-sweep` | $\Omega$ 量级, 与 M 无关 | CC BY-SA 3.0 | 见下 |
| 博客表 | *Rathjen-type* "Up to Γ₀" 等 | $\Gamma_0$ 以上少量 | Fandom CC BY-SA 3.0 (koteitan 如此引) | 见下 |
| 我方 `mnot.py` 自产 | 本项目 | 全部 | 我方 | 能, 但只是自证 |

**许可兼容** [推断, 非法律意见]. 本仓库根 `LICENSE` 是 **CC BY-NC-SA 4.0**. BY-SA 3.0 的材料不能并入 BY-NC-SA (加 NC 不合 ShareAlike), 反过来也不能. 所以 **Naruyoko、koteitan、博客的表都不宜逐字收进本仓库**. koteitan 自己的做法可抄: `scripts/padicbot-ref.js` 的注释写明不收录该资料, 只按路径从外部读. 单条序关系算不算受保护我不敢说; 稳妥的路线是手工从规则推出少量向量 (§5.2), 其余放仓库外比对. 那个比对的执行是另一个任务, 也不在本文范围内; 本次没有运行任何一方的代码. Exmachina 的数据要用得先问作者. MIT 的两个仓库 (`AzertyWasTaken/Ordinals`, `bms-paper-formalization`) 没有相关语料.

**对 Naruyoko 表的额外提醒.** φ 原语, 所以要过 τ 才能对上 φ-free 的项, 而且只有 φ-free 能表达的那一部分能对上. 能对上多少没算.

## 9. 读了什么, 没读什么

**逐行读过:** `padicBotRathjen/implementation.js` 的 `inT`–`fund` 与测试表头尾 (`Term` 类与 UI 只扫了); `lean/TM/{Terms,Order,NF}.lean` 全部, `FS.lean` 到 `:345` 与之后的 `domSpec`; `ordinal.js` 的 `RathjenM` 全部, `RathjenK` 的 `least`、`lt` (未引用); Kanrokoti 的 `lessThan`、`dom`、`fund`、`findOTPath`; `plan/chi-2ary.md` 开头; `mnot.py` 到 `:240`; `EBOI` §1–§3; 手册 §1、§3、§4、§6.5; 调研 §3.3、§12.2、§12.5、§12.7、§12.10.

**只 grep 或只看结构:** `hypcos/notation-explorer`, `AzertyWasTaken/Ordinals`, `vihdzp/ordinal-notation`, `koteitan/bms-paper-formalization`; koteitan 的 `table/findings.md`; Exmachina `05_RathjenM_en.html` 只读开头与末尾; SHEET 只统计列.

**没读:** `IPsi`, `inaccessiblePsiExperimental`, `strongInaccessiblePsiExperimental`, `weakKPsi`, `strongKPsi`; `RathjenK`、`Stegert1/2` 的 `fs`; koteitan `Evidence/`; `EBOI` §4 后半 (基础引理, 只浏览了前半). 博客原文这次没重读, 用的是调研里的转述; 所以 §1 "忠实度" 只到注释编号, §5、§7 涉及 KawamoYurase 处只来自调研的文字. `.claude/`、`CLAUDE.md`、`AGENTS.md` 按要求未读.

**本次未执行任何东西**: 只有 `gh api` 元数据、`git clone --depth 1`, 以及本地用 `python3 -I` 读 JSON 做行数统计. 克隆在 `/private/tmp/claude-501/-Users-alsg-Agentic-agda-googology/047974d5-11ad-4b0c-a01d-76eb45cfb49f/scratchpad/codescan/mahlo/`.
