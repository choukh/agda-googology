# Lean 记号代码静态阅读: `InaccPsi`, `ExBuchholz`, `Trans`, `pss-proof`

> **证据记录, 手册见 [CodeGuide](../CodeGuide.md).** 查结论看手册; 本文是阅读当时的记录, 已知更正记在手册 §3、§6, 原文未改.

> 2026-11-02, 静态阅读, 未构建未运行任何外部代码. 克隆: `koteitan/googology-lean` `6da2de5` (下称 gl), `koteitan/pss-proof` `d1be91f` (下称 pss), `koteitan/bms-rathjen` `7bde9d7` (下称 br). 行号均对应这些提交.
>
> **标记.** [读] = 读了证明或定义. [推断] = 我从读到的代码推出, 仓库里没有这条陈述, 也没有机检. [文档] = 只读了作者的文档或注释. sorry/axiom 数都是文本检索, 不是 `#print axioms`.

## 1. 范数与模: 能否由 s 界定 m

路径前缀 `gl:E/` = `Googology/Notation/ExBuchholz/`. 这一节是给 `InaccModulus*` 的.

### 1.1 结论

**有, 而且是线性的, 与 t 无关.** 对 `OT X`, `dom X = ω`, `OT Y`, `Y < X`, `exists_lt_fs_numeral` (`gl:E/Cofinal.lean:294`) 的证明给出的见证满足

$$n\le\mathrm{size}\,Y+1\qquad[\text{推断: 逐支读证明得到, Lean 里没有这条陈述}]$$

其中 `size (cons a b t) = size a + size b + size t + 1`, `size nil = 0` (`gl:E/Sum.lean:203`). 配上 $n\mapsto X[n]$ 单调 (见 1.4 的缺口), 就是范数形式的 Bachmann: $X[m]\le s<X\Rightarrow\mathrm{size}\,s\ge m$.

逐支核算 (读 `Cofinal.lean:294-395`, 对 `size Y` 强归纳):

| `X` 的情形 | 见证 | 界 |
|---|---|---|
| 和 $\psi+(\ldots)$; `Y` 首项相同时对尾递归 | $n(r)$, 否则 0 | $\mathrm{size}\,r+1\le\mathrm{size}\,Y$ |
| $\psi_a(0)$, `dom a` 极限 | $n(p)$, $p$ 是 `Y` 的首项下标 | 同上 |
| $\psi_a(b)$, `dom b = 1`, 规则 4 | `exists_lt_repeatPrin` (278): $k\le$ 顶层项数 $+1$ | $\mathrm{size}\,Y+1$ |
| $\psi_a(b)$, `dom b = ω` | $n(q)$, $q$ 是首项参数 | 同第一行 |
| 规则 6 (`dom b` 是项, 不小于 $X$) | `exists_lt_fs_tower q` (257): $n(d)=1+\max_{x\in G_{Z_0}(d)}n(x)$, 空表取 $0$ (`exists_bound_list` 242) | `size_lt_of_mem_G` (`Sum.lean:274`) 给 $n(d)\le\mathrm{size}\,d+1$, 所以 $\le\mathrm{size}\,Y$ |

**界是紧的**: $X=\omega=\psi_0(1)$, $Y=$ 数字 $m$, $\mathrm{size}\,Y=m$, 而 $\omega[m]=m$ 不大于 $Y$, 必须 $n=m+1$ (`fs_psi_of_one_numeral` `Cofinal.lean:123`; `repeatPrin` `FS.lean:258`, $k=0$ 给 `nil`).

**对 `size` 的依赖只有一处实质内容**: 规则 6 的递归沿 $G_{Z_0}(d)$ 走, 每步严格减小 `size`. 其余都是字典序的结构下降.

### 1.2 项下标的模 (`dom X` 是项)

`lt_fs_psi_of_G` (`Cofinal.lean:135`) [读]:

```
OT V, dom V ∉ {nil, 1, ω}, OT d, d < V, (∀ x ∈ G Z₀ d, x < β)  ⟹  d < V[ψ_{Z₀}(β)]
```

其中 $Z_0=(\mathrm{subOf}(\mathrm{dom}\,V))[0]$. **这是 Ω-共尾度的显式模**: 见证是 $\psi_{Z_0}(\beta)$, $\beta$ 只需压住 $G_{Z_0}(d)$. 对 `V` 归纳, 不用闭包, 不用语义, 文件注释说每支都短 [文档]; 我读了前两支和结构 [读]. 取 $\beta=V[W_k]$ 就是规则 6 的上一级. 这条对应我方 `Ωcof`/`ΩC` (`StandardOmega.lagda.md:211`), 但 Lean 的版本对全部 EBO 成立, 我方只到 `NF₁`.

### 1.3 已陈述的范数定理

| 定理 | 位置 | 陈述 | 假设 | 是否要 `Y` 标准 |
|---|---|---|---|---|
| `size_fs_W0` | `Closure.lean:1205` | $\mathrm{size}(V[W_0])+1=\mathrm{size}\,V$ | `OT V`, `dom V` 是项 | — |
| `G_size_succ_lt` | `Closure.lean:1286` | $x\in G_u(V)\Rightarrow\mathrm{size}\,x+1<\mathrm{size}\,V$ | `dom V` 是项, 不要 `OT` | — |
| `no_small_between` | `Closure.lean:1323` | $\mathrm{size}\,y+1<\mathrm{size}\,V$, $V[W_0]<y$ $\Rightarrow$ $\neg(y<V)$ | `OT V`, `dom V` 是项 | **不要**, `y` 是任意项 |
| `bach_pre` | `Closure.lean:1796` | $G_u(V)<p+V\Rightarrow G_u(V)<p+V[W_0]$ | `OT V`, `dom V` 是项 | — |
| `bachmann` | `Closure.lean:1820` | $x\in G_A(B)\Rightarrow x<B[W_0]$ (配置: `OT ψ_A(B)`, 规则 6) | 同上, 且 `¬ dom B < ψ_A(B)` 这条未用 | — |
| `Trian_fs_thm` | `Closure.lean:1830` | $X[Y]\lhd_Y X$, 见 2 | `OT X`, $Y<\mathrm{dom}\,X$ | **不要**, 中间项 `c` 任意 |

`no_small_between` 只在塔的第 0 级, 只在项下标. 它不给 $m$ 的界, 给的是一条缝: $V[W_0]$ 与 $V$ 之间没有比 $V$ 小两个结点以上的项.

### 1.4 用到树侧之前要补的

1. **`dom = ω` 时 $n\mapsto X[n]$ 单调, gl 没有陈述** [读: 检索 `Notation/ExBuchholz` 与 `Trans/BMS/ExBuchholz`, 只有项下标的 `fs_mono` (`FS.lean:745`)]. `tower_val_lt` (`FS.lean:847`) 给规则 6 的部分; 其余分支是结构的 [推断]. pss 的 `y4_N_mono` (`OTB-…-cofinality.lean:1022`) 在 Buchholz 系统上陈述了它, 用 `OT` 与 $D_\omega$-free. 我方 `fs-mono₁` (`GoodLBase`) 在 `NF₁` 上已有.
2. **$s$ 的标准性不可省.** 我方 `vX≮` (`StandardOmega`) 是反例形状; `y4_inner` 注释也给了 Buchholz 情形的反例 $D_0(D_50)<D_10$ [文档]. 证明里用标准性的唯一地方是 `OT_G_lt` (`Sum.lean:292`), 把 `G` 压在参数之下.
3. **`size` 是记号的, 树上没有对应物.** 这里 $m$ 的界读 $s$ 的语法; 树侧 `ω` 与 `ω⁺` 互不可比 (`InaccStrike` §3) 正说明同值的树范数不唯一. 所以这一节给记号侧的上界与归纳形状 (沿 `G` 走), 不给树上的 `nrm` [推断].
4. **我方已有同形的证明.** `Cof6` (`StandardOmega.lagda.md:244`) 对 `sz c ≤ m` 归纳, 见证 `suc k` 每步消耗一个 `sz`, 所以 $n\le$ `sz c`, 这个界在 Agda 里已是隐含的, 把 `Σ ℕ` 换成带上界的 Σ 即可显式化 [推断, 未试]. `Cof6` 只沿首项下标的首项参数走一条链, Lean 对 `G` 全部成员取最大; 这是 `NF₁` 下的简化还是普遍可行, 未判定.

**勘误 (指南 §5.2).** `Cofinal` 一行写着 "用到 `val` (`tower_val_mono` 234), 不是纯句法", 这是错的. `tower_val_mono` 的 `val` 指 "塔在 `fs` 下产出的值", 它只调 `tower_val_lt` (`FS.lean:847`). `Cofinal.lean` 文本检索没有 `val`/`Ordinal`/`OTFS`/`Trian` 这些词 (`\bval\b` 无命中), 也不用 `OTFS_thm`. 它依赖的 `G_subset_of_le`, `OT_of_mem_G`, `OT_G_lt`, `le_pred_of_lt`, `OT_subOf_dom`, `dom_sub_dom_eq_one` 都在 `Sum`/`FS`/`Closure`, 这几个文件不导入 Mathlib [读]. `import System` (带入 Mathlib) 只为文件末尾 `exbOT_exists_le_step` (410) 的状态类型 [读]. **所以 `exists_lt_fs_numeral` 是纯句法的, 且不依赖基本列封闭性, 可移植.** 是否用到经典公理未核: 证明里有 `by_cases`, `cmp` 可判定, 预计可消.

## 2. 经典 Bachmann 性质在哪里

**字面的 "$s<t[n+1]\Rightarrow s\le t[n]$" 是假的**, 不用找: $t=\omega^\omega=\psi_0(\omega)$, $t[n]=\psi_0(n)=\omega^n$, 取 $s=\omega^n+1$ [推断, 手算]. 能成立的只有带范数或带 `G` 的形式. 五个候选:

| 形式 | 陈述 | 位置 | 系统 | 状态 |
|---|---|---|---|---|
| 三角形 (Buchholz 3.6) | `Trian Y X[Y] X`: $X[Y]<X$, 且对任意 $u$ 与任意项 $c\in(X[Y],X]$, $G_u(X[Y])\preceq G_u(c)\cup G^0_u(Y)$ | `gl:E/Closure.lean:1830` `Trian_fs_thm`, 定义 193 | **全 EBO**, `OT X`, $Y<\mathrm{dom}\,X$ | **定理, 无假设** [读] |
| 共尾 + 无界 | $Y<X\Rightarrow\exists n, Y<X[n]$ | `Cofinal.lean:294`; 一步版 `exists_le_fs_idx` 401 | 全 EBO, 可数 | 定理 |
| 范数形式 | $X[m]\le s<X\Rightarrow\mathrm{size}\,s\ge m$ | 无 | 全 EBO | **没有陈述**, 1.1 推出, 需补单调 [推断] |
| 第 0 级缝 | $V[W_0]<y<V\Rightarrow\mathrm{size}\,y+1\ge\mathrm{size}\,V$ | `Closure.lean:1323` | 全 EBO, 项下标 | 定理 |
| 项下标共尾 | $b<a\Rightarrow\exists z\in\mathrm{dom}\,a, b\le a[z]$, 且 $z$ 标准 | `pss: lean/OTB-…-cofinality.lean:1438` `y4_bachmann` | Buchholz 1986 ($D_\omega$-free) | 定理, 那边叫 "Bachmann (共尾性)" |

gl 的 `bachmann` (`Closure.lean:1820`) 确实只是 `G` 界, 指南说得对: 它说 $G_A(B)<B[W_0]$, 是规则 6 塔的起点条件, 不说任何项不在中间. 真正的经典内容在 `Trian_fs_thm`. 它在 gl 里是 `OTFS` 的副产品 (`Trian_fs_aux` 1016, `Trian_fs` 1127), 不依赖语义. **指南 §5.2 的路线图里已列出它, 但未标出它就是 Bachmann 性质的 `G` 形式.**

**`OrderEmb` 需要的到底是哪一个.** `OrderEmb` (`InaccTreeAccept.lagda.md:274`) 要 $u<v\Rightarrow L(u)\prec L(v)$, 而 `≺` 是树内的**路径**见证 (`via`). 所以它要的是 "$u$ 可由 $v$ 沿基本列下行到达", 不是单步. 由 1.1 可得更强的确定性版本 [推断, 未试]:

> 设 $N=\mathrm{size}\,s+1$, $s<t$, 都标准. 从 $t$ 反复取 $t\mapsto t[N]$ (后继处取前驱): 只要当前项是极限, 下一项仍严格大于 $s$; 只要当前项是后继, 下一项 $\ge s$ (`le_pred_of_lt`). 由良基, 走路必终止, 所以恰好经过 $s$.

这是 Cichon 式的 "固定范数的 Hardy 走路". 它把 `OrderEmb` 的分支搜索变成**一条确定的路**, 路径上每个数字下标都是 $N$. 只对可数项; 不可数项还要 1.2 的 $\psi_{Z_0}(\beta)$. 它需要单调性 (1.4 第 1 点) 和良基 (gl 用 `OTLt_wf`, 语义的). 路径**长度**没有界, 所以这不是判决算法, 只省了分支.

`gl: Trans/BMS/ExBuchholz/Reach.lean` 的注释描述的是同一走法的非确定版: 共尾 + `fs_lt` + `OTLt_wf` 走到相等 [文档]; 只在 $\psi_0(\Omega)$ 下.

**对 `InaccStrike` 的结论.** "证 `GV` 还需要项侧的封闭性与 Bachmann 性质" 这句里, 项侧部分现在都有 Lean 证明且是句法的: 封闭 `OTFS_thm`, 共尾 `exists_lt_fs_numeral`, 三角形 `Trian_fs_thm`, 项下标模 `lt_fs_psi_of_G`. 缺的只有良基 (`OTLt_wf` 是语义的) 和单调的陈述. `GV` 的树侧 (判决本身) 这些都不碰.

## 3. `InaccPsi`

路径前缀 `gl:P/` = `Googology/Notation/InaccPsi/`. 9 个 `.lean`, 4288 行 (指南数字, 我的 `wc` 一致). 0 sorry/0 axiom (文本). 许可 MIT.

### 3.1 结构

| 文件 (行) | 内容 |
|---|---|
| `Hyp` (246) | `InaccSeq` (169): $I:\mathbb N\to$ Ord 严格增, 每个 $I_n$ 正则不可数且 $\Omega_{I_n}=I_n$. **这是唯一假设**, 作为结构字段传入, 不是 `axiom`. 不要求是最前面的 ω 个 |
| `Facts` (330), `Ord` (354) | $\mathrm{Cl}(\alpha,\beta)$, $\psi_\kappa$, F1–F12 (Buchholz 1992 Def 4.2, Pohlers §3.4.4 的 (155)–(179)) |
| `Term` (217) | 8 个构造子: `zero`, `inacc n`, `inaccW`, `add`, `phi`, `om`, `psiS s a`, `psiI n a` (29); `val` (57) 经 `S`; `cmp` (112) 句法, 不看 `S`; `KLt` (194); `NF` (205) |
| `CNF` (307), `Struct` (372) | Cantor 范式、结构引理; `Lam` (`Struct:88`) 是 $I_\omega$ 之上第一个 Ω-不动点, **不是** EBO 的 $\Lambda$ |
| `Correct` (1179) | `cmp_lt_iff` (1105): NF 上 `cmp` 与 `val` 一致; `eq_of_val_eq` (1102); `isWellOrder_cmp` (1166) 把良序沿 `val` 拉回 |
| `NFM` (714) | 算子 $M$ (43), 把序数规范化到范式参数 |
| `Onto` (569) | `vals_eq`: NF 的值恰是 $\bigcup_a\mathrm{Cl}(a,0)$; `existsUnique_NF` (562) |

### 3.2 离基本列多远

**没有任何一步.** 全目录没有 `dom`, `fs`, `cof`, 没有 Bachmann 字样 (文本检索). 要做就是从头写, 还要处理 EBO 没有的东西 [推断]:

- `phi`: 二元 Veblen 的基本列, 含 $\varphi(a,b)$ 而 $a$ 不可数共尾的情形;
- `om` 与 `psiS` 分离: `Ω_a` 与 $\psi_{\Omega_{s+1}}(a)$ 是两个构造子, 标准形要排除 $a\in F$, 基本列要按 `om` 的下标后继/极限/不动点分派;
- `inaccW` 共尾度 ω, 新; `psiI n` 的折叠表.

`ExBuchholz` 无 φ, `FS` + `Closure` + `Cofinal` 共 3451 行 (`wc`). 带 φ 且有 $I_n$ 的版本不会更小 [推断]. `NF` 是 Prop 值的, `KLt` 里 `cmp _ μ = .lt ∨ ...`; 句法, 可判定, 但判定性未打包成 Bool [读].

而且证明路线不可移植: `Correct`, `Onto` 全靠 `val` 与基数算术 (Hyp 导入 `Mathlib.SetTheory.Cardinal.*`). `cmp` 的正确性没有不经 `val` 的证明.

### 3.3 与 `EBOI` 的关系

**不能逐项翻译** [推断, 未试; 仓库里没有这种翻译].

| | `EBOI` | `InaccPsi` |
|---|---|---|
| 基数 | 单个 `I` | $I_n$, $I_\omega$ |
| 原语 | `ψ u a`, `ψI a`, `I`, 列表和 | 另有 `phi`, `om`, `inacc`, `inaccW` |
| 塌缩 | $\psi_u$ 不闭 φ, $\psi_u(0)=\Omega_u$ | $\mathrm{Cl}$ 闭 φ, 所以 $\psi_{\Omega_{s+1}}(0)$ 是 $\Omega_s$ 之上第一个强临界数 (F6, F9) |
| 下标 | 任意项 | `psiS s a` 的 $s$ 任意项 |
| $\psi_I(0)$ | $\Lambda$ | $\psi^I_0(0)$; F10 说它是 Ω-不动点, 与 $\Lambda$ 同值 [推断] |
| 标准形 | `isOTᵉ`, `G` | `KLt`; 都是 Pohlers/Buchholz 型, `KLt` 多走 `om` |
| 基本列 | 有 (测试) | 无 |

低端的值不重合 (φ 把 $\psi_{\Omega_{s+1}}(a)$ 的小参数吸收掉), 大参数上才对齐, 所以映射至少要像 Setzer τ 那样改写参数. 指南 §6.1 的 $\Omega'$ 映射是这个问题在 OT_I 上的版本, 同样未证.

**作标尺的用法.** (1) `cmp` 是全句法的, 可以转写成脚本, 当 `EBOI` 序的第三意见: 两边翻译到同一里程碑序列 (如 $\psi_0(I)$, $\psi_0(I\cdot2)$, $\psi_0(\Omega_{I+1})$) 后比较. (2) `Onto` 证明这些是全部值, 可作 "没有漏项" 的外部依据. 它给不了 `EBOI` 新规则的正确性, 因为新规则是基本列, 这边没有.

## 4. `Trans`: 翻译、假设、保序

### 4.1 假设

全部 `axiom` 在 `Trans/BMS/PoR/PSS/{Main,TR}` 和 `Trans/PoR/InaccPsi/R2/` (**我的行首检索 31 个文件 160 行, 未去注释; 指南的脚本是 27 个文件 156 个声明, 差额未核**, 如 `Main.lean`, `UhTerm`, `LcBlk` 的命中是注释里写了 `axiom`). 另有一个 `Notation/OmegaY/WellOrder/OmegaY/Reflection.lean`.

**`Trans/ExBuchholz`, `Trans/BMS/ExBuchholz`, `Trans/DBMS/ExBuchholz` 没有任何 `axiom`** (文本). 所以本项目关心的记号翻译都是无假设的, 引用公理全部是 patterns of resemblance 一侧:

- `Trans/BMS/PoR/PSS/Main/Cited.lean` (16), `Cited2` (7), `Cited3` (10): Carlson 2001, Wilken 2007a/b, Carlson–Wilken 2012 关于 $\le_1$ 的事实. `le1` 自身是无定义常量 (72) [读].
- `TR/Cited.lean` (12): Wilken 的 $\vartheta$, `vartheta` 是无定义常量 (63), 其它是 `val_level`, `vartheta_inj` 之类 [读].
- `Trans/PoR/InaccPsi/R2/Cited.lean` (28 = 7 常量 + 21 事实, 文件头自述) 及 20 余个 `Cited*`: Wilken 的 $T^\tau$, `Tset`, `Par`, `pi`, `ht` 都是常量 [读头部]. 该目录 1975 个文件, 目标是 Wilken 关于 $\mathrm{Core}(R_2^+)$ 的主张, 头部明说两半都开放, 只推进到 $\psi_{\Omega_1}(\Omega_\omega+\cdots)$ 的片段, 还带前提 FRAG [文档]. **它对我们无用**, 只有 `Trans/PoR/InaccPsi/LowTerms.lean` 等可能含 `InaccPsi` 项的具体计算, 我没读; `LowerT.lean` 头部说 Wilken 的 υ 未形式化, LOW-0 与 LOW-STEP 是假设.

**`InaccPsi` 不依赖这些**: 引用只在翻译层.

### 4.2 证明形状

`Core/Morphism.lean` 提供 `OrdHom` (27), `Sim` (65), `StepHom` (106), `Equiv` (124). `StepHom` 字段: `map`, `reindex`, `map_step : map (R.step s k) = Q.step (map s) (reindex k)`, `map_halted`. `Sim` 只要求 "一步映到一步"; `OrdHom` 只保序.

| 翻译 | 文件 | 形状 | 何以保序 | 与我方的对应 |
|---|---|---|---|---|
| 一行 BMS → EBO | `BMS/ExBuchholz/Commute.lean:514` `read_expandL`; `Prim.lean` `primHom` | **`StepHom`, 逐项交换**: $\mathrm{read}(\mathrm{expand}_N)=(\mathrm{read})[\mathrm{idx}(N+1)]$, reindex 就是 $N\mapsto N+1$ | 不直接证; 标准性由 `OTFS_thm` 传过来 ("交换把问题变成 `OTFS_thm`") [文档]. `Equiv.lean` 在 $\psi_0(\Omega)$ 下得 `primEquivE0` | **`Lab`/`Commute` 的同形物**: 一个映射, 与基本列交换, 带 reindex. 关键差别: 这里只有 `dom` 三种 (`dom_read`), 规则 6 永不触发 |
| Buchholz → EBO | `BMS/ExBuchholz/PSS/Terms.lean` | `toTerm`: 下标映到数字或 `tw`. `toTerm_injective`, `lessBT_iff_lt`, `isOT_toTerm`, `toTerm_bijOn_OT` | **对项归纳的句法保序**, 不走值 | **τ 的同形物, 最直接的参考**. `lessBT_iff_lt` 的证明可作 §6.1 义务 2 的模板 |
| 二行 PSS → EBO | `PSS/Expand`, `Steps`, `StepBound`, `Rank` | `Eval`, 不是 `StepHom` | 经 pss 的 `trans_bijOn`, `trans_order_iso` 与 `belowEquiv` | 见下 |
| 二行 DBMS → EBO | `DBMS/ExBuchholz/{TwoRow,TwoRowBlock}` (`OneRow` 是 `StepHom`) | `Eval` | 同上 [文档] | |
| EBO → 三行 BMS | `ExBuchholz/BMS/Trio/` | 校准表, 大文件 (单文件到 3902 行) | 未读 | 与本项目无关 |

**有一条负结果值得记: `pairToExbOT_steps_unbounded`** (`PSS/StepBound.lean:492`) [读陈述, 未读证明]. 一步 pair 展开对应多步 $X\mapsto X[\mathrm{idx}\,X\,k]$, 步数没有常数界 (反例族 `famA`, `famB`). 所以 PSS → EBO 根本不是 `StepHom`, 只有 `Sim` 的传递闭包. 这对我们的提示是: 逐项标签 (`Lab`) 对单步翻译是强条件, 换到别的基本列就立刻失效; 我们的标签只在树与 EBO 自己的基本列一致时才成立, 这是 `InaccStrike` 第 3 点 (`ver-dev`) 的同一现象 [推断].

**`Trans/BMS/ExBuchholz/Cofinal.lean`** (338 行): 只在 `AllNil` 项上证 `exists_le_fs` (206), `fs_lub` (327); 已被 `Notation/ExBuchholz/Cofinal` 取代, 但证明更短, 可先看.

**通用形式**: `Googology/Cofinal.lean` 的 `Eval.Cofinal` 与 `Eval.Cofinal.rank_eq`: 带求值的重写系统, 共尾 ⟹ 秩等于值. 语义的, 不能搬, 但它把 "验收" 的陈述抽象得干净: **秩 = 值**. 我方层 4 没有对应陈述.

## 5. `pss-proof`: Buchholz 1986 的自证与**语义无关的良基**

路径前缀 `pss:` = `lean/`, 提交 `d1be91f`. **没有 LICENSE 文件**, 只读, 不可抄. gl 把它作 Lake 依赖 (`lake-manifest.json`, 同一提交), 用而不抄. 文本检索: 下面这些目录 0 个 `axiom`; `sorry` 的 6 处命中都是注释里的 "sorry 0" 或指向 Isabelle 的说明.

| 文件 (行) | 内容 | 状态 |
|---|---|---|
| `Buchholz-1986/…-2.1`, `…-2.1-order` (118, 123) | `BT`, `lessBT`, 线性序 | 下标在 `ℕ∞`, $D_\omega$ 用 `dfree_BT` 排除 |
| `…-2.2` (73) | `GBT`, `T_B`, `descP`, `OT`, `OT_B` | 只是定义 |
| `…-3.2`, `…-3.2-descent` (92, 462) | `addBT`, `domB`, 3.2(a) | |
| `…-3.3` (1372) | `G_control_bc` (254, 即 3.4), `buchholz_fseq_closed_general` (1354) 对 `z ∈ dom a` 或数字, `buchholz_fseq_closed` (1362) | **同时归纳** `OT` 与 3.6 的 `G` 控制 (`triGBC`), 文件头明说 A23 分支需要这个加强 [读] |
| `Buchholz-rel-ord/…-6` (97) | `operB`, `xseq`: $x_0=D_u0$, $x_{i+1}=D_u(b[x_i])$, $(D_vb)[n]=D_v(b[x_n])$ | **规则 6 是二手转录**: 文件头说 Buchholz 未刊稿不可得, 依 PSS 文章 §7.1 脚注 30 实现 [文档]. 与指南一致 |
| `Buchholz-1987/…-2.3-W` (382), `…-2.4-2.8` (979) | **$W_v$ 层级**: 见下 | 指南未提 |
| `OTB-well-founded-syntactic/…-cofinality` (1791), `…-main` (241) | **`OT_B_wellFounded`** (`main:235`): 不用序数值 | 指南未提 |

**是否陈述经典 Bachmann.** 不是 BCW (B2) 形式. `y4_bachmann` (`cofinality:1438`) 是 $b<a\Rightarrow\exists$ 下标 $b\le a[\cdot]$, 共尾形式. 3.3 里的 `triGBC` 与 gl 的 `Trian` 同义 (3.4/3.6) [读陈述; 两者的逐字对照未做].

**(B2) 字面本身在 EBO 上不成立.** 指南 §1 说经典义是 BCW (B2) (控制 $\alpha[n]$ 与其间项的基本列). 按常见写法 $\alpha[n]<\beta<\alpha\Rightarrow\alpha[n]\le\beta[0]$, EBO 的编号下它为假: $\alpha=\psi_0(\omega)$, $\beta=\psi_0(n+1)$, 规则 4 给 $\beta[0]=$ `repeatPrin _ _ 0` $=0$ [推断, 手算; (B2) 的精确文本我没读 BCW 原文, 只读了指南的转述]. 改成 $\beta[1]$ 能否救, 未判定, 这里只说要先定编号. gl 的一步系统也为此用 `idx X (n+1)`.

### 5.1 语义无关的良基路线 (重要, 指南没有)

`OT_B_wellFounded` 走 Buchholz 1987 的 distinguished sets [读 `main` 全文, `2.3-W` 头部]:

1. `bwl_Aop` (`2.3-W:62`): $a\in A_v(X)$ 当 $a=0$, 或 `dom a` 是 $\{0\}$/ℕ 且全部 $a[n]\in X$, 或 `dom a` $=T_u$ ($u<v$) 且 $\forall z\in W_u, a[z]\in X$. **这就是 Acc 的形状, 分支是基本列.**
2. `bwl_W u` (115-121): 对 $u$ 递归, 每层取最小不动点. 头部说明: $W_u$ 在生成中的集合上不单调, 所以不能一次 lfp, 要分层.
3. `bwl_DC` (`2.4-2.8:652`), `bwl_2_8_principal` (921): 每个 $D_\omega$-free 项进某个 $W$.
4. `acc_of_W_wfe` (`main`): 由共尾 (`bwl_cof_wfe`) 与闭包 (`buchholz_fseq_closed_general`), $W_u\subseteq$ Acc. 这里只用 **Lean 的 `Acc` 和句法**.

**对我们的含义.**

- 这是 EBO 良基性的第二条路, 与 §6.1 的 τ 嵌入并列, 而且形状和树一样 [推断]. gl 的 `WF.lean:105` 与 README:278 也提到了这条路, 只因当时基本列未校准而没走.
- Agda 形式化看起来可行: `W` 是对 `ℕ` 递归的归纳族, `∀ z ∈ W u` 里的 `W u` 是已定义的上一层, 严格正 [推断, 未试]. 证明有 39 处 `by_contra`/`by_cases`/`Classical` (文本), `cmp` 可判定, 能否消去未核. `Set` 用的是 Mathlib, 但没有序数.
- **卡点是下标.** `bwl_W : ℕ → Set BT` 只对数字下标递归. EBO 的 $u$ 是项, 递归要沿 $<$ 走, 也就是要先有下标的良基, 这是循环. 可能的解法是对 $\mathrm{Acc}\,u$ 递归定义 $W_u$, 同时归纳证明遇到的下标都 Acc; 这没人写过, 我也没试. 所以它直接给的是 $\psi_0(\Omega_\omega)$ 以下, 比 §6.1 的 OT_I 终点小得多, 但不带 φ, 与 EBO 同形.
- 与 `InaccStrike` 的关系: `W` 把 "树" 换成 "基本列上的归纳谓词", 等于把 Ω 分支限制到 $W_u$. 这正是 `InaccStrike` §2 说的好输入类 `G` 必须知道标准形. 可以读作: `W_u` 是 `G` 的一个现成解, 而且在 Buchholz 段**已证非空且足够大** [推断]. `InaccStrike` §3(ii) 说 `Gen`/`Run` 互递归不严格正; 这里靠分层解决, 分层就是 §3(iii) 的 `Gs`, 只不过层号是基数层而不是折叠步数. 这一条值得单独验证.

## 6. gl 的其它部分

- **`Core`**: `Rewrite` (20), `Rel`, `WF`, `Terminates`; `Morphism` (§4.2); `Std`, `Goals` 是验收表. 文本检索不导入 Mathlib, 没有序数内容. 可以抄 `StepHom` 的形状, 没有定理值得移植.
- **`Rank.lean`** (导入语义): `StepHom.rank_map` (83), `rank_eq_iSup_nat` (127). 只作陈述参考.
- **Veblen**: 只用 Mathlib 的 `veblen`, 在 `InaccPsi` 和 `ExBuchholz/Ladder.lean`.
- **Bachmann–Howard**: 只作校准表上的名字. `Ladder.lean`: $\psi_0(\Omega\cdot(1+\gamma))=\varepsilon_\gamma$ 对任意 $\gamma$; `Eps.lean:777` `psi_Omega_omega`. 可作 `EBO` 低端里程碑的语义依据.
- **I**: 只有 `InaccPsi`. **没有带基本列的 I 层记号**, `Trans/PoR/InaccPsi` 也只消费值.
- **Mahlo**: `Notation` 下 `.lean` 文本检索 0 处. 指南 §5.4 的 `btbms-formalization` 不在此仓库.
- **br `lean/TM/FS.lean`**: 文件头自认 $\mathfrak T(M)$ 的基本列是该仓库的设计选择, 只与 *Rathjen-type* 对过 12 行, Γ₀ 以下 [文档]. 与指南一致, 对 EBOI 无直接用处.

## 7. 复用清单

记法: 省什么 = 相对于从头写. 都是**只读后在 Agda 重写**, 不是移植代码. gl 目录是 MIT, 可参考并注明出处; pss 无许可, 只读思路, 不抄文本.

### (a) 标签路线上关闭一般下标的 `NF`

| # | 位置 | 省什么 |
|---|---|---|
| 1 | `gl:E/Closure.lean:193-1127` (`Trian`, `Trian.psi_sub` 550, `G_lt_of_Trian` 359, `SubBound` 651, `Trian_case4` 968, `Trian_fs` 1127) | 一般下标的不变量. **相对于 $c$ 的界** 正是 `StandardOmega` `regSb`/`swapΩ`/`SELFΩ` 的 `NoSb ⊎ HdIs` 前提想表达的东西; 一次替换掉按下标形状分类的 `Sb`, 不必逐类打补丁 [推断] |
| 2 | `gl:E/Closure.lean:1192-1820` (`size_fs_W0`, `no_small_between`, `bach_pre`, `bachmann`) | 规则 6 起点的 `G` 界, 只要大小论证, **不依赖 `OTFS`**, 可先做. `bach_pre` 的前缀 $p$ 不可省 (指南陷阱 2) |
| 3 | `gl:E/Closure.lean:1554-1827` (`towerOT_of_Bachmann`, `OTFS_aux`, `OTFS_thm`) | 证明顺序; 对 `size` 归纳同时带 3.6 |
| 4 | `gl:E/Cofinal.lean:135, 257, 294` | `cofin₁` 推广到全 EBO 的直接蓝本, 句法, 不依赖 1–3. 我方 `Cof6` 已同形 |
| 5 | `gl:E/Cofinal.lean:40-58`, `Sum.lean:256,274,292` | `G` 的小工具; 对应 `Vis₁`, 含 `vs` (`G_mem_cons_sub` 47) |
| 6 | `pss: Buchholz-1986-3.3.lean:1354` | 同一定理的 ℕ-下标版, 作对照: 同时归纳的组织方式不同, 1 选不动时看 |

注意: 1 里的 `Trian` 读 `G` 的列表, 与 `Vis₁` 的归纳形式要有桥; 我方 `fsn` 结构递归, Lean 走 `tower`, 指南 §5.2 注记已说.

### (b) `EBOI` 标尺

| # | 位置 | 省什么 |
|---|---|---|
| 1 | `gl:P/Term.lean:112,194,205` (`cmp`, `KLt`, `NF`) | 第三意见的序与标准形, 全句法, 可转写成脚本与 `EBOI` 比里程碑. 翻译要自己写, 非逐项 (§3.3) |
| 2 | `gl:P/Onto.lean:562`, `Correct.lean:1105` | "NF 恰好枚举值" 的机检依据, 假设 `InaccSeq`. 用作 "这张表没漏项" 的外部引用 |
| 3 | `gl:P/Ord`, `Facts` (F1–F12) | F9, F10 明确 $\psi_{I}$ 与 $\psi_{\Omega_{s+1}}$ 的值域, 核 `EBOI` 约定 ($\psi_I(0)=\Lambda$) 用 |
| 4 | `gl:E/` 整个 | EBO 段的校准; 对 `EBOI` 只经保守性 |
| — | I 层基本列 | **这些仓库都没有**, 仍靠 みずどら 与 $T_W$ (指南 §6.2) |

### (c) `InaccStrike` 的 `GV` 与模, 记号侧输入

| # | 位置 | 省什么 |
|---|---|---|
| 1 | `gl:E/Cofinal.lean:294` + 1.1 的逐支核算 | 数字下标的**线性模** $n\le\mathrm{size}\,Y+1$, 与 $t$ 无关, 紧. 回答 "`lim` 目标上的范数模能否证出" 的记号侧 [推断] |
| 2 | `gl:E/Cofinal.lean:135` `lt_fs_psi_of_G` | Ω-分支的显式见证 $\psi_{Z_0}(\beta)$; 这大概是 `pen` 分支搬运 `b` 对应的项 [推断] |
| 3 | `gl:E/Closure.lean:1830` `Trian_fs_thm` | 全 EBO 的 `G` 形式 Bachmann; 中间项 `c` 不要求标准 |
| 4 | `gl:E/Closure.lean:1323` `no_small_between` | 第 0 级的范数缝, 中间项 `y` 不要求标准 |
| 5 | `gl:E/Closure.lean:1827` `OTFS_thm` | `P-fs` (`InaccStrikeCommute`) 对 `isOTᵉ` 成立的记号证据. `P-pr` 同 (后继时 `OT` 的前驱) |
| 6 | §2 的固定范数走路 | 把 `OrderEmb` 的路径搜索变成一条确定的路 (只在可数段). 需要良基, 所以只作设计依据 [推断] |
| 7 | `pss: OTB-…-main`, `2.3-W` | `W_u` 作为好输入类 `G` 的现成模型 (§5.1) |

**不给的.** `GV` 的 `pen`/`rise` 由树判决, 这些全在项上. `InaccStrike` 的第一个具体障碍 (奇异 Ω 下标, 树上判 `j ≺ g x`) 这里没有任何对应物: Lean 比较项不比较树. `size` 没有树上的读法 (1.4 第 3 点).

## 8. 限制

**读了:** `Closure.lean` 的 Bachmann 段 (1130–1215, 1280–1345, 1790–1833) 与 `Trian` 定义; `Cofinal.lean` 除 `lt_fs_psi_of_G` 后几支之外全部; `InaccPsi` 的 `Term.lean` 大半, `README` §1–§4 开头与 §5, 其余文件只读头部和定理名; pss `…-main` 全文, `…-cofinality` 头部与定理陈述, `2.3-W` 头部; `Morphism.lean` 结构定义; `Commute`, `Equiv`, `Prim`, `Terms` 的头部; `Cited*` 只读头部与前几条 axiom.

**没读:** `Closure.lean` 中 `Trian` 情形的证明体; `OTLt_wf`/`Mono`/`Onto` 的证明体; `Trans/ExBuchholz/BMS/Trio/`; `Trans/PoR/InaccPsi/R2/` 除 `Cited.lean` 头部以外的 1970 余个文件; `Trans/BMS/PoR`; `lessBT_iff_lt` 的证明体 (表 §4.2 "对项归纳的句法保序" 是**由它的第一行 `lt_of_lessBT` + 三歧** 与文件头推断的, 不是读完证明); pss 的 Isabelle; BCW 与 Buchholz 1987 原文.

**未验证:** 全部 [推断] 项. 其中最值得先机检的是 1.1 的线性界: Agda 里把 `cofin₁`/`Cof6` 的 `Σ ℕ` 加一个上界, 或用指南 §5.3 的 Python 转写枚举 $(X,Y)$ 对. 这次按要求没有运行.

**许可.** gl: MIT (`LICENSE`), Apache 例外只在 `Notation/Y/WellOrder/{ZeroY,OneY,Por}` 等 (`NOTICE`), 不含本文涉及的目录. pss: 无 LICENSE, 默认无授权. br: CC BY-SA 3.0 (指南记录, 本次未重查).
