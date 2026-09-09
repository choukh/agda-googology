# Mahlo 宇宙与目标序数基本列：定义 v1

> **主线修正（2026-09-09）**：当前任务是[从类型宇宙规则统一提取基本列](EXTRACTION-PLAN.md)。下文保留此前“手写记号／基本列，再由宇宙证明良基”的方案作为历史与校准探针，不再规定主线执行顺序。高度搜索列和手填端点不是自动提取成果。

日期：2026-09-09。先给具体定义，再补正确性与量级依据。宇宙定义采用已有外部构造；内部极限列选用本项目的有限高度搜索候选。两者的地位不同。

## 1. 实际使用的宇宙

外部大宇宙为 `V = Set : Set₁`，解码 `T(A)=A`。定义

\[
\mathrm{Fam}=\Sigma(X:\mathrm{Set}).(X\to\mathrm{Set}).
\]

对每个 `F : Fam → Fam`，同时归纳递归定义小代码宇宙 U_F 与解码 El_F。省略下标 F 后，构造子是：

\[
\begin{aligned}
&\mathrm{nat}:U,\quad \mathrm{fin}(n):U,\quad
 \mathrm{sum}(a,b):U,\\
&\mathrm{pi}(a,b),\mathrm{sigma}(a,b),\mathrm{w}(a,b):U
 &&(a:U,\ b:\mathrm{El}(a)\to U),\\
&\mathrm{eq}(a,x,y):U &&(x,y:\mathrm{El}(a)),\\
&\mathrm{res}_0(a,b):U,\quad
 \mathrm{res}_1(a,b,z):U &&(z:\mathrm{El}(\mathrm{res}_0(a,b))).
\end{aligned}
\]

自然数、有限类型、和、Π、Σ、W、等式代码解码为对应宿主类型。最后两项的解码是本构造的关键：令

\[
(X',Y')=F\bigl(\mathrm{El}(a),\lambda x.\mathrm{El}(b(x))\bigr),
\]

则

\[
\mathrm{El}(\mathrm{res}_0(a,b))=X',\qquad
\mathrm{El}(\mathrm{res}_1(a,b,z))=Y'(z).
\]

把 `U_F : Set` 本身作为 V 的元素 `u(F)`，取 `s(F)=El_F`。因此每个族算子 F 都有一个在 V 内、对 F 封闭的代码宇宙，并且

\[
\mathrm{decode}(\mathrm{restrict}(c))=F(\mathrm{decode}(c)).
\]

以上不是新添的公理接口；构造及解码等式已在 [External.agda](Universe/External.agda) 实现并安全检查。这采用 [Dybjer–Setzer 的外部 Mahlo 方法](https://csetzer.github.io/articles/dybjerSetzerWeylVolume2025/dybjerSetzerWeylVolume2025Final.pdf)。它不等于本项目已构造内部 `M : Set`，也不等于完整 MLM 解释已经完成。

## 2. 基本列属于哪个对象

基本列不作用于任意类型 `A : V`。我们为参考序数记号中的可数极限定义它，以便最终沿该记号递归。

取 [Setzer 原系统](https://csetzer.github.io/articles/mahlo.pdf)的合法记号 OT 和次序 ≺，记 `OT_c = {a ∈ OT | a ≺ Ω₁}`。再单独添目标端点 Top，预期表示

\[
\alpha_M=\psi_{\Omega_1}(\Omega_{M+\omega}).
\]

OT 判定及次序已有带递归预算的候选实现 [Reference.agda](Notation/Reference.agda)，与参考系统的等价性仍待证明。以下数学定义引用该指定的参考系统，不能用任意布尔函数替代其语义。

## 3. 固定语法高度与有限候选集

使用 [Syntax.agda](Notation/Syntax.agda) 的主项序列表示。空序列 nil 表示零；cons 将一个主项接到序列前。

固定高度如下，**没有待选的控制函数**：

\[
\begin{aligned}
h(\mathrm{nil})&=0, &h_P(M)&=0,\\
h(\mathrm{cons}(p,t))&=1+\max(h_P(p),h(t)),\\
h_P(\varphi(a,b))&=1+\max(h(a),h(b)),\\
h_P(\psi(a,b))&=1+\max(h(a),h(b)),\\
h_P(\Omega(a))&=1+h(a).
\end{aligned}
\]

由于只有这些有限元构造且没有任意数值原子，高度有界的底层语法集合有限。可直接递归枚举：

```
T₀ = {nil}                         P₀ = {M}
Tₙ₊₁ = {nil} ∪ {cons(p,t) | p∈Pₙ, t∈Tₙ}
Pₙ₊₁ = {M} ∪ {φ(a,b), ψ(a,b) | a,b∈Tₙ}
            ∪ {Ω(a) | a∈Tₙ}
```

这些是底层语法，随后必须按 **OT** 过滤；`Raw` 的 T′ 检查不够。枚举不是高效算法，复杂度可能极大；这里首先确定定义。

## 4. 完整的候选下降规则

对非零可数极限 λ∈OT_c，定义

\[
\boxed{\lambda[n]=\max_{\prec}
 \bigl(\{0\}\cup\{\beta\in OT_c:\beta\prec\lambda,\ h(\beta)\le n\}\bigr).}
\]

另外规定

\[
0[n]=0,\qquad (\beta+1)[n]=\beta.
\]

零的约定仅用于总化下降操作；FGH 在零处直接返回 n+1，不递归使用 0[n]。

端点使用独立的列：

\[
\boxed{\mathrm{Top}[n]=b_n=\psi_{\Omega_1}(\Omega_{M+n}).}
\]

所有项按参考正规化解释，包含 n=0 的情况。端点列的合法性及共尾性仍须证明，不把原始 Ω 构造视为一般正规化函数。

这是**本项目 v1 的具体选择**，不是宣称文献已经给出并认证了这套逐点相同的列。特别是它不是未经验证就套用 Buchholz–Cichon–Weiermann 定理的实例。

## 5. 哪些性质容易说明，哪些仍决定量级

在正确的参考次序及完备枚举前提下，内部极限规则的有限最大值存在，输出低于 λ，随 n 不减。若 γ≺λ，取一个仍低于 λ 的后继记号 δ，令 n≥h(δ)，就有 γ≺δ≤λ[n]；这给出共尾性的数学论证。它允许重复项，不声称每一步严格递增。

上述说明尚未成为 Agda 中的参考系统证明。更关键的是：下降和共尾**不足以保证** Bachmann 性质、有效层级支配、与独立参考 FGH 的受控双向比较或固定输入的大数下界。v1 必须继续接受 [CALIBRATION](CALIBRATION.md) 的这些验收；若不满足，需要显式换版本，不能暗中更改列。

## 6. 已实现与尚未实现

- 外部宇宙 U_F 及解码：已有实际实现。
- 固定高度、有限枚举、过滤取最大算法：已在 [FiniteSearch.agda](Fundamental/FiniteSearch.agda) 实现，安全检查通过。
- [Reference.agda](Notation/Reference.agda) 已实现比较、SC／sc／G、临界项判定及 OT 检查；不再只有外部参数。返回 `Maybe Bool`，递归预算耗尽时返回 `nothing`。
- [Mahlo.agda](Fundamental/Mahlo.agda) 将这些实际算法接到 `basicSequence : Term → Nat → Result Term` 和 `endpointSequence : Nat → Result Term`；调用者不必提供比较器。结果区分 `ok`、`invalid`、`exhausted`。端点也检查合法性及低于 Ω₁。
- FGH 的 `view` 还需要把合法项分类为零／后继／极限，并接入上述规则；统一下降证书仍待构造。
- [MahloChecks.agda](Fundamental/MahloChecks.agda) 以 `refl` 检查实际归约：`basicSequence ω 2 = ok 1`、`basicSequence ω 3 = ok 2`、后继取前驱、拒绝 Ω₁、端点第 0／1／2 项及前两项递增。这是高度搜索列，所以不预设通常的 `ω[n] = n`。

这里的程序在 Agda 意义下总终止，但结果可能是 `exhausted`；尚未证明预算 `32 × (size a + size b)` 足以让所有合法输入返回判定结果，因此还不是已认证的全域基本列算法。

还有一项明确的转录约定需要核实：原文 Definition 3.5 的 Gκ(ψλb) 最后一支在扫描版中写严格条件 κ≺′ψλb，与前一支一起未覆盖相等情形；而 Definition 3.6 会使用 Gκ(κ)。当前代码把“不低于 κ”的情形（含相等）统一定义为 Gκ(λ) ∪ Gκ(b) ∪ {b}，并用一个归约检查固定这一选择。[前身系统 Definition 2.7](https://csetzer.github.io/articles/2papdiss.pdf) 的相关分支含非严格比较，可作为调查线索，不能替代本系统的等价性证明。这个约定影响嵌套 ψ 的合法性检查，须在语义校准时优先审计。

现在有无需外部判定器的可执行候选；尚不报告已得到参考系统正确性、目标强度或闭合的 FαM。
