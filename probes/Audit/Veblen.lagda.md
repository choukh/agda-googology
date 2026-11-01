# Veblen 系列的定义审计: 每个递归算出的是不是它声称的序数

> 本文回答一个问题: `src/Veblen/` 的五篇文章 (Base, Multinary, Finitary, Infinitary, Transfinitary) 里, 每个声称实现某个标准数学对象 (序数算术, 不动点枚举, ε/ζ/η, 二元/三元/四元/有限元 Veblen 函数, Γ, SVO, ω+1 元到 (ω2)+1 元, 超限元 Veblen 函数, LVO) 的定义, 有没有 [BTBO](../../src/OCF/BTBO.lagda.md) 那一类改变数值的定义错误.
> 方法: 仿 [BTBOSemantics](../OCF/Align/BTBOSemantics.lagda.md). 把 Agda 递归逐条与标准定义 (Wikipedia "Veblen function" 的有限元定义与基本列表; Schütte 的 Klammersymbole 对超限元的定义) 对照, 能 `refl` 的写成 Agda, 其余写成带假设与置信度的论证.
> 范围外顺带: `src/Lower.lagda.md` 只看 Base 用到的部分, 但其中葛立恒数的定义有一处改变数值的错误, 记在 §1.5.
>
> **结论 (详见 §7)**:
> - Veblen 五篇里**没有改变数值的定义错误**. 有限元部分 (二元到 n 元, Γ, SVO) 的递归与 Wikipedia 的定义和基本列规则**逐条相同**, 本文用 `refl` 核对了每一类规则. 极限位置 (ω, ω2, 一般 λ) 处的 `jump⟨ 1 ⟩` 种子是正确的, 而且是必要的: 换成 `jump` 会把 φ(1@ω) 算成 1 (§4.1, Agda). 极限值落在极限位置上时, 基本列沿位置对角走. 这只改基本列, 不改值 (§4.2, 论证).
> - 超限元 Veblen 函数在一切有限元数上与有限元 Veblen 函数**逐点相等** (§5.3 `agree`, Agda, 对全部参数). 由此 `Transfinitary.SVO ≡ Finitary.SVO`. LVO 的基本列以 0, ω, SVO 开头 (Agda). 极限位置被当作新的层级常量, 不会出现 BTBO 那种层级压平 (§5.4).
> - **改变数值的错误只有一处, 而且不在 Veblen 里**: `Lower.Graham.G (suc n) = 3 ↑⟨ n ⟩ 3` 没有迭代. `G 64` 等于 $3\uparrow^{63}3$, 介于 $g_1$ 与 $g_2$ 之间, 远小于葛立恒数 $g_{64}$ (Agda: `G 1 ≡ 9`). 一行修正.
> - 工程问题: `Veblen.Transfinitary` **不能被任何模块导入**. 导入时 Agda 2.8 会重新检查它的 `REWRITE Φ-ż-α`, 这一检查报 `RewriteNonConfluent`, 而该文件单独编译能通过. 本文因此逐字复制了它的定义部分来审计 (§5.1).
> - 文字小错: Base 文末 oom 的说明差一 (§1.3).

```agda
{-# OPTIONS --cubical --lossy-unification --rewriting --local-confluence-check #-}
module Audit.Veblen where
```

**选项.** `Veblen.Infinitary` 用 `--cubical`, 这个选项有传染性 (`InfectiveImport`), 所以本文也用 `--cubical`. `--rewriting` 同理. 被审计的 Finitary, Infinitary, Transfinitary 都不是 `--safe`, 所以本文也不能是 `--safe`. 本文没有 postulate. 函数外延只用 `Cubical.Data.Equality.Conversion.funExt`, Infinitary 也是这样做的.

```agda
open import Veblen.Base
import Lower as L
import Veblen.Multinary as M
import Veblen.Finitary as Fin
import Veblen.Infinitary as Inf
open Fin using (_→ⁿ_) renaming (_0̇ to _0̇ᶠ)
open import Relation.Binary.PropositionalEquality.Core using (cong)
open import Cubical.Data.Equality.Conversion using (funExt)
```

本文的每条结论标注来源:

- **[Agda]**: 本文件中以 `refl` 或短证明机器检验;
- **[标准]**: 序数论的已知事实 (Veblen 1908; Schütte, *Proof Theory* 第 V 章 Klammersymbole; Wikipedia "Veblen function" 的定义与 "Fundamental sequences" 一节);
- **[估计]**: 本文的论证, 给出假设与置信度, 未形式化.

## §0 语义与约定

**模型.** 与 BTBOSemantics §1 相同: `Ord` 的树按 $[\![0]\!]=0$, $[\![a^+]\!]=[\![a]\!]+1$, $[\![\mathsf{lim}\,f]\!]=\sup_n[\![f\,n]\!]$ 解释. 这里只有 ℕ-极限, 没有不可数分支, 所以每棵树的值就是一个可数序数, 不依赖模型.

**基本假设 (A).** 下文的 [估计] 论证都假设: (A1) 出现的树的基本列严格递增 (Base 的前言声明了这一点, 并引用了到 $\Gamma_0$ 的证明); (A2) 标准 Veblen 函数的性质: 在每个参数上单调, 在 "最高非零参数" 处连续, 且 $\varphi(\ldots)\ge$ 它的每个参数. (A1) 是树的事实. (A2) 是 [标准].

**基本列取项.** `a [ n ]` 是树 `a` 的第 `n` 个基本列项. 对后继和零的定义无关紧要.

```agda
_[_] : Ord → ℕ → Ord; infixl 5 _[_]
zero  [ _ ] = zero
suc α [ _ ] = α
lim f [ n ] = f n
```

`F ∘^ finord n` 与有限迭代 `F ∘ⁿ n` 逐点相等. 这条引理让 "基本列第 n 项是 n 次迭代" 能对变量 `n` 陈述.

```agda
∘^-finord : ∀ (F : Ord → Ord) n x → (F ∘^ finord n) x ≡ (F ∘ⁿ n) x
∘^-finord F zero x = refl
∘^-finord F (suc n) x = cong F (∘^-finord F n x)

iterω-fs : ∀ (F : Ord → Ord) x n → iterω F x [ n ] ≡ (F ∘ⁿ n) x
iterω-fs F x n = ∘^-finord F n x
```

## §1 Base 与 Lower

### §1.1 序数算术 `_+_`, `_*_`, `_^_`

**标准.** $\alpha+0=\alpha$, $\alpha+\beta^+=(\alpha+\beta)^+$, $\alpha+\lambda=\sup_{\xi<\lambda}(\alpha+\xi)$. 乘法和幂同理, 起点分别是 $0$ 和 $1$, 极限处连续.

**Agda.** `α + β = (suc ∘^ β) α`, `α * β = ((_+ α) ∘^ β) 0`, `α ^ β = ((_* α) ∘^ β) 1`, 其中 `∘^` 在极限处取 `lim`.

**判定: 正确.** 这三条正是标准递归式. 底数与指数没有颠倒: `α ^ suc β = α ^ β * α`, `α * suc β = α * β + α`. 基本列也是标准的: $\omega^{\beta+1}[n]=\omega^\beta\cdot n$, $\omega^{\lambda}[n]=\omega^{\lambda[n]}$ [Agda]. 树 `ω ^ 1` 与树 `ω` 不是同一个项, 但外延相等 [Agda]. §5.4 要用到这条.

```agda
ω^suc-fs : ω ^ suc α [ n ] ≡ ω ^ α * finord n
ω^suc-fs = refl

ω^lim-fs : ω ^ lim f [ n ] ≡ ω ^ f n
ω^lim-fs = refl

ω^1≡ω : ω ^ 1 ≡ ω
ω^1≡ω = cong lim (funExt lem) where
  lem : ∀ k → ((_+ 1) ∘^ finord k) 0 ≡ finord k
  lem zero = refl
  lem (suc k) = cong suc (lem k)
```

修正: 无.

### §1.2 `iterω`, `jump`, `fixpt`

**标准.** 设 $F$ 是正规函数. 它的不动点的枚举 $F'$ 满足 $F'(0)=\sup_nF^n(0)$, $F'(\alpha+1)=\sup_nF^n(F'(\alpha)+1)$, 并在极限处连续. Wikipedia 的基本列取 $F'(0)[n]=F^n(0)$ 与 $F'(\alpha+1)[n]=F^n(F'(\alpha)+1)$.

**Agda.** `fixpt F = jump (iterω F)`, `jump F α = ((F ∘ suc) ∘^ α) (F 0)`.

**判定: 正确, 基本列与标准逐项相同.** 由 `fixpt-suc` (源文件) 与 `iterω-fs`:

```agda
fixpt-0-fs : ∀ (F : Ord → Ord) n → fixpt F 0 [ n ] ≡ (F ∘ⁿ n) 0
fixpt-0-fs F n = iterω-fs F 0 n

fixpt-suc-fs : ∀ (F : Ord → Ord) n → fixpt F (suc α) [ n ] ≡ (F ∘ⁿ n) (suc (fixpt F α))
fixpt-suc-fs {α} F n = iterω-fs F (suc (fixpt F α)) n
```

种子 `0` 和 `suc` 都对. 如果 $F(0)=0$, `fixpt F 0` 也会正确地给出 $0$. 但下文用到的 $F$ 都满足 $F(0)>0$. 修正: 无.

### §1.3 ε, ζ, η 与 oom

**判定: 正确.** `ε = fixpt (ω ^_)` 给出 $\varepsilon_0[n]=\omega\uparrow\uparrow n$ 式的标准塔, 等等. 源文件的 `ε-0`, `ε-suc`, `ε-lim` 都是 `refl`.

**文字小错 (外观).** Base 文末说 "$\zeta_{\zeta_{\cdot_{\zeta_0}}}$ 是从 $\zeta_0$ 开始迭代了 99 次 $\zeta$". 实际上 `FGH.f (η 0) 99` 取的项是 $\eta_0[99]=\zeta^{99}(0)$. 这一共是 99 个 $\zeta$, 最内层是 $\zeta(0)=\zeta_0$. 所以是 "从 $\zeta_0$ 开始再迭代 98 次". 不影响任何数值.

```agda
η0-fs : η 0 [ 3 ] ≡ ζ (ζ (ζ 0))
η0-fs = refl
```

修正 (Base 第 693 行文字): "从 $0$ 开始迭代了 99 次 $ζ$".

### §1.4 FGH, SGH, MGH, HH

**判定: 正确.** 四个层级都是标准定义: $f_{\alpha+1}(n)=f_\alpha^n(n)$; $g_{\alpha+1}(n)=g_\alpha(n)+1$; $m_{\alpha+1}=m_\alpha\circ m_\alpha$; $H_{\alpha+1}(n)=H_\alpha(n+1)$. 极限处都对角化. 源文件的 `f-3-2 : f 3 2 ≡ 2048` 等数值与标准一致. "$f_{\omega+1}(64)$ 大于葛立恒数" 是已知事实 [标准].

### §1.5 Lower 的葛立恒数: 改变数值 (范围外, 但确定)

**标准.** $g_1=3\uparrow^4 3$, $g_{k+1}=3\uparrow^{g_k}3$, 葛立恒数为 $g_{64}$. Lower 的 `↑⟨ k ⟩` 中 `k` 是箭头个数 (`↑⟨ 0 ⟩` 是乘法, `↑⟨ 1 ⟩` 是乘方). 所以 "从 4 个箭头开始" 应写成 $G_0=4$, $G_{n+1}=3\uparrow^{G_n}3$, 这时 $G_{64}=g_{64}$. Lower 正文的非形式说明 "$G\,n := 3 ↑^{3 ↑^{\cdots ↑^{3 ↑↑↑↑ 3} \cdots} 3} 3$" 也是这个意思.

**Agda (Lower 第 220–222 行).**

```text
G zero = 4
G (suc n) = 3 ↑⟨ n ⟩ 3
```

LaTeX 公式 (第 206 行 $G\,n^+ := 3 ↑^n 3$) 也写成了同样的式子.

**判定: 改变数值 (偏小), 确定.** 箭头数用的是下标 $n$, 不是上一项 $G_n$. 于是 $G_{n+1}=3\uparrow^n3$, 从而 `G64` $=3\uparrow^{63}3$. 它大于 $g_1=3\uparrow^43$, 但远小于 $g_2=3\uparrow^{g_1}3$, 更远小于 $g_{64}$. 最小的反例: `G 1` 应为 $3\uparrow^4 3$, 实为 $3\times3=9$.

```agda
G-bug : L.Graham.G (suc n) ≡ 3 L.↑⟨ n ⟩ 3
G-bug = refl

G-1 : L.Graham.G 1 ≡ 9
G-1 = refl

G-2 : L.Graham.G 2 ≡ 27
G-2 = refl
```

**修正 (一行代码 + 一行公式, 未应用).**

```agda
module GrahamFix where
  G : ℕ → ℕ
  G zero = 4
  G (suc n) = 3 L.↑⟨ G n ⟩ 3

  G-rec : G (suc n) ≡ 3 L.↑⟨ G n ⟩ 3
  G-rec = refl

  -- G 1 = 3 ↑↑↑↑ 3 = g₁, 于是 G 64 = g₆₄
```

公式改为 $G\,n^+ := 3 ↑^{G\,n} 3$.

## §2 Multinary: 二元, 三元, 四元 Veblen 函数与 Γ

```agda
module Bin = M.BinaryVeblen
module Tri = M.TrinaryVeblen
module Qua = M.QuaternaryVeblen
```

### §2.1 二元 `Φ` 与 `φ`

**标准.** $\varphi_0(\beta)=\omega^\beta$. $\varphi_{\alpha+1}$ 枚举 $\varphi_\alpha$ 的不动点. 极限 $\lambda$ 时, $\varphi_\lambda$ 枚举所有 $\varphi_\alpha$ ($\alpha<\lambda$) 的公共不动点. Wikipedia 的基本列:
(i) $\varphi_{\alpha+1}(0)[n]=\varphi_\alpha^n(0)$; (ii) $\varphi_{\alpha+1}(\beta+1)[n]=\varphi_\alpha^n(\varphi_{\alpha+1}(\beta)+1)$; (iii) $\varphi_\lambda(0)[n]=\varphi_{\lambda[n]}(0)$; (iv) $\varphi_\lambda(\beta+1)[n]=\varphi_{\lambda[n]}(\varphi_\lambda(\beta)+1)$; (v) $\varphi_\alpha(\mu)[n]=\varphi_\alpha(\mu[n])$.

**Agda.** `Φ F = rec F fixpt (λ φ[_] → jump λ β → lim λ n → φ[ n ] β)`.

**判定: 正确, 五条基本列与 Wikipedia 逐条相同.** (i)(ii) 来自 §1.2. (iii)(iv)(v) 是 `jump` 的展开 [Agda]. 极限步的 `jump` 不是随意的选择. 下一个公共不动点 $\sup_n\varphi_{\lambda[n]}(\varphi_\lambda(\beta)+1)$ 恰好就是它: 这个序列递增, 因为 $\alpha<\alpha'$ 时 $\varphi_{\alpha'}(x)$ 是 $\varphi_\alpha$ 的不动点且 $\ge x$, 所以 $\varphi_{\alpha'}(x)=\varphi_\alpha(\varphi_{\alpha'}(x))\ge\varphi_\alpha(x)$. 序列的上确界被每个 $\varphi_{\lambda[m]}$ 固定 (连续性加上尾段被固定). 任何大于 $\varphi_\lambda(\beta)$ 的公共不动点都大于等于序列的每一项 [标准].

```agda
bin-ii : Bin.φ (suc α) (suc β) [ suc n ] ≡ Bin.φ α (Bin.φ (suc α) (suc β) [ n ])
bin-ii = refl

bin-iii : Bin.φ (lim f) 0 [ n ] ≡ Bin.φ (f n) 0
bin-iii = refl

bin-iv : Bin.φ (lim f) (suc β) [ n ] ≡ Bin.φ (f n) (suc (Bin.φ (lim f) β))
bin-iv = refl

bin-v : Bin.φ (suc α) (lim g) [ n ] ≡ Bin.φ (suc α) (g n)
bin-v = refl
```

标签样例: $\zeta_0[2]=\varepsilon_{\varepsilon_0}$, 这里没有 "直接退回低一层" 的压平.

```agda
ζ0-fs : Bin.φ 2 0 [ 2 ] ≡ ε (ε 0)
ζ0-fs = refl
```

修正: 无.

### §2.2 `Γ` 与后代函数

**标准.** $\Gamma$ 枚举 $\alpha\mapsto\varphi_\alpha(0)$ 的不动点, $\Gamma_0[n]$ 是 $\alpha\mapsto\varphi_\alpha(0)$ 从 $0$ 起的 $n$ 次迭代.

**判定: 正确.** $\Gamma_0[3]=\varphi_{\varphi_{\varphi_0(0)}(0)}(0)=\varphi_{\varphi_1(0)}(0)=\varphi_{\varepsilon_0}(0)$ [Agda]. `ε̇ = fixpt Γ` 等 "第二代" 函数只是命名. 三元的 `φ-1-1 : φ 1 1 ≡ ε̇` (源文件, `refl`) 说明它们与 $\varphi(1,\beta,\cdot)$ 一致, 这与标准相符: $\varphi(1,1,\cdot)$ 枚举 $\Gamma$ 的不动点.

```agda
Γ0-fs : Bin.Γ 0 [ 3 ] ≡ Bin.φ (ε 0) 0
Γ0-fs = refl
```

### §2.3 三元与四元 `Φ`

**标准 (Wikipedia 有限元定义).** 记 $z$ 为一串零. $\varphi(s,\alpha+1,z,\gamma)$ 枚举 $\xi\mapsto\varphi(s,\alpha,\xi,z)$ 的不动点. 也就是说, 后继只看**紧邻的下一位**, 右侧全部填零. 若 $\alpha$ 为极限, $\varphi(s,\alpha,z,\gamma)$ 枚举 $\xi\mapsto\varphi(s,\beta,\xi,z)$ ($\beta<\alpha$) 的公共不动点. 固定前面各位时, 后面各位按低元数的同一规则递归.

**Agda.** 三元: `rec F (λ φ-α → Bin.Φ (fixpt λ β → φ-α β 0)) (λ φ[_] → Bin.Φ (jump λ β → lim λ n → φ[ n ] β 0))`. 四元在外面再套一层 `Tri.Φ`.

**判定: 正确.** 不动点链经过紧邻的下一位, 这一位上的值是变量 (`λ β → φ-α β 0`), 不会 "经目标层抄近路". 外层的 `Bin.Φ`/`Tri.Φ` 恰好是 "固定前面各位, 后面各位按低元数递归". 基本列 [Agda]:

```agda
tri-s00 : Tri.φ (suc α) 0 0 [ suc n ] ≡ Tri.φ α (Tri.φ (suc α) 0 0 [ n ]) 0
tri-s00 = refl

tri-l0s : Tri.φ (lim f) 0 (suc β) [ n ] ≡ Tri.φ (f n) (suc (Tri.φ (lim f) 0 β)) 0
tri-l0s = refl

qua-s000 : Qua.φ (suc α) 0 0 0 [ suc n ] ≡ Qua.φ α (Qua.φ (suc α) 0 0 0 [ n ]) 0 0
qua-s000 = refl
```

源文件的 `φ-1-0 : φ 1 0 ≡ Γ` 与四元的 `φ-1-0-0` 对应标准的 $\varphi(1,0,\gamma)=\Gamma_\gamma$ 与 $\varphi(1,0,0,\gamma)$ (后者在 $\gamma=0$ 时是 Ackermann 序数). 修正: 无.

## §3 Finitary: 有限元 `Φₙ`, `φ` 与 SVO

**Agda.** `Φₙ {n} F = rec F (λ φ-α → Φ (fixpt λ β → φ-α β 0̇) n) (λ φ[_] → Φ (jump λ β → lim λ m → φ[ m ] β 0̇) n)`, `Φ F (suc n) = Φₙ (Φ F n)`.

**判定: 正确.** 这是 §2.3 的规则对元数的一致推广. 源文件 `φ₁ : φ 1 ≡ Bin.φ`, `φ₂ : φ 2 ≡ Tri.φ`, `φ₃ : φ 3 ≡ Qua.φ` 都是 `refl`. 一般 $n$ 的五条计算模式 (`Φ-s-ż-z` 到 `Φ-α-ż-l`) 正是 Wikipedia 的 $(s,\alpha{+}1,z,0)$, $(s,\alpha{+}1,z,\gamma{+}1)$, $(s,\lambda,z,0)$, $(s,\lambda,z,\gamma{+}1)$, $(s,\alpha,z,\mu)$ 五条基本列. 它们在源文件中已经证明 (经 `Φ-ż-α` 替换).

**SVO.** `SVO = lim λ n → φ n 1 0̇`, 即 $\sup_n\varphi(1@n)$. 这是 SVO 的标准定义 [标准]. 前三项是 $\omega$, $\varepsilon_0$, $\Gamma_0$ [Agda]:

```agda
SVO-fs0 : Fin.SVO [ 0 ] ≡ ω ^ 1
SVO-fs0 = refl

SVO-fs1 : Fin.SVO [ 1 ] ≡ ε 0
SVO-fs1 = refl

SVO-fs2 : Fin.SVO [ 2 ] ≡ Bin.Γ 0
SVO-fs2 = refl
```

修正: 无.

## §4 Infinitary: ω+1 元到 (ω2)+1 元

```agda
module Eqω  = Inf.OmegaUnaryVeblen
module Bω   = Inf.OmegaBinaryVeblen
module Ltω2 = Inf.DoubleOmegaryVeblen
module Eqω2 = Inf.DoubleOmegaUnaryVeblen
```

表示约定: `Eqω.φ α n β₁ … βₙ₊₁` 表示 $\varphi(\alpha@\omega,\beta_1@n,\ldots,\beta_{n+1}@0)$.

### §4.1 极限位置的后继值: `jump⟨ 1 ⟩` 正确且必要

**标准.** $\varphi(\alpha{+}1@\omega,\gamma)$ 枚举一切 $\eta\mapsto\varphi(\alpha@\omega,\eta@k)$ ($k<\omega$) 的公共不动点. 下文称这些函数为 $h_k$. 特别地, $\varphi(1@\omega)=\mathrm{SVO}$ [标准].

**Agda.** `Ltω.Φ (jump⟨ 1 ⟩ λ β → lim λ n → φ-α n β 0̇)`. 记 $G(\beta)=\sup_n\varphi(\alpha@\omega,\beta@n)$. 新的底函数是 $\gamma\mapsto$ `jump⟨ 1 ⟩ G γ`: 在 $0$ 处取 $G(1)$, 在 $\gamma+1$ 处取 $G(x+1)$, 其中 $x$ 为前一个值.

**判定: 正确 [估计, 高 ~95%].** 先看 $G(1)=\sup_n\varphi(\alpha@\omega,1@n)$. 其中 $\varphi(\alpha@\omega,1@n{+}1)$ 是 $h_n$ 的最小不动点, 而且也被一切 $h_k$ ($k\le n$) 固定. 由 (A2) 的连续性, 上确界被每个 $h_k$ 固定. 反过来, 任何公共不动点 $z$ 都满足 $z\ge1$, 从而 $z=h_n(z)\ge h_n(1)$. 所以 $G(1)$ 是最小的公共不动点. 后继步 $G(x+1)$ 同理. 极限步取上确界, 对应公共不动点集的闭性.

**为什么必须是 `jump⟨ 1 ⟩`.** 如果写成通常的 `jump` (种子 $0$), 新底函数在 $0$ 处取 $G(0)=\sup_n\varphi(\alpha@\omega,0\ldots)$. 这个序列是常数 $\varphi(\alpha@\omega,0)$, 不是不动点. $\alpha=0$ 时它就是 $\sup(1,1,1,\ldots)=1$, 也就是会把 SVO 算成 $1$ [Agda]:

```agda
all-zero : ∀ n → Fin.φ n 0 0̇ᶠ ≡ 1
all-zero zero = refl
all-zero (suc n) = all-zero n

jump⟨0⟩-would-give-1 : jump (λ β → lim λ n → Fin.φ n β 0̇ᶠ) 0 ≡ lim (λ _ → 1)
jump⟨0⟩-would-give-1 = cong lim (funExt all-zero)
```

而实际定义给出正确的 SVO 及其基本列 (源文件 `φ-1⋯0 : φ 1 (0) 0 ≡ Fin.SVO`):

```agda
Eqω-SVO-fs : Eqω.φ 1 0 0 [ n ] ≡ Fin.φ n 1 0̇ᶠ
Eqω-SVO-fs = refl
```

同理, $\varphi(2@\omega)$ 的基本列是 $\varphi(1@\omega,1@n)$. 位置 $\omega$ 上的 $1$ 作为常量保留着, 没有被对角掉 [Agda]:

```agda
Eqω-2-fs : Eqω.φ 2 0 0 [ n ] ≡ Eqω.φ 1 n 1 0̇ᶠ
Eqω-2-fs = refl
```

修正: 无.

### §4.2 极限位置的极限值: 对角只改基本列

**Agda.** 极限步 `jump λ β → lim λ n → φ[ n ] n β 0̇`, 即 $G(\beta)=\sup_n\varphi(\lambda[n]@\omega,\beta@n)$. 基本列项是对 $n$ 同时取值序列和位置: 第 $n$ 项把值 $\lambda[n]$ 放在位置 $\omega$, 把参数放在位置 $n$ [Agda]:

```agda
Eqω-l-s-fs : Eqω.φ ω 0 1 [ n ] ≡ Eqω.φ (finord n) n (suc (Eqω.φ ω 0 0)) 0̇ᶠ
Eqω-l-s-fs = refl
```

**标准.** $\varphi(\lambda@\omega,\gamma)$ 枚举 $R=\bigcap_{\alpha<\lambda}\mathrm{ran}\,\varphi(\alpha@\omega,\cdot)$. 这里的值域单调递减且闭. 有限元的对应规则是把 $x+1$ 放到**紧邻的下一位**. 极限位置没有紧邻的下一位, 所以标准文献没有唯一的规定. 常见写法是放在位置 $0$, 即 $\varphi(\lambda[n]@\omega,x+1)$.

**判定: 只改基本列, 值相同 [估计, 高 ~90%].** 设 $x$ 为前一个值. 令 $a_n=\varphi(\lambda[n]@\omega,x+1)$, $b_n=\varphi(\lambda[n]@\omega,(x+1)@n)$. 两个序列都递增, 都落在 $\mathrm{ran}\,\varphi(\lambda[n]@\omega,\cdot)\subseteq\mathrm{ran}\,\varphi(\alpha@\omega,\cdot)$ ($\alpha\le\lambda[n]$) 中. 因为值域闭, 两者的上确界都在 $R$ 中, 且 $>x$. 另一方面, 设 $c$ 是 $R$ 中 $>x$ 的最小元. 那么 $c\in\mathrm{ran}\,\varphi(\lambda[n{+}1]@\omega,\cdot)$, 所以 $c$ 被 $\eta\mapsto\varphi(\lambda[n]@\omega,\eta@n)$ 固定, 从而 $c\ge b_n\ge a_n$. 因此 $\sup a=\sup b=c$. FGH 数值会随这一选择变, 序数标签不变. $\gamma=0$ 时两种写法都给出 $\sup_n\varphi(\lambda[n]@\omega,0)$.

修正: 无. 如果希望与 "放在位置 0" 的常见写法逐项一致, 可以把 `φ[ n ] n β 0̇` 改成 `φ[ n ] 0 β`, 但这没有必要.

### §4.3 ω+2 元, ω+n 元与 (ω2)+1 元

**Agda.** `Bω.Φ` 的后继步是 `Eqω.Φ $ Ltω.Φ $ fixpt λ β → φ-α β (0) 0`, 即枚举 $\beta\mapsto\varphi(\alpha@\omega{+}1,\beta@\omega)$ 的不动点. 这里的不动点链经过紧邻的位置 $\omega$, 然后按 ω+1 元与 ω 元的规则重建下面各位. `Ltω2.Φₙ` 是对 $\omega+n$ 的一致推广. `Eqω2.Φ` 在位置 $\omega2$ 处重复 §4.1 的 `jump⟨ 1 ⟩`, 对 $\omega+n$ 各位取上确界.

**判定: 正确 [估计, 高 ~90%; 结构同 §2.3 与 §4.1].** 标签样例: $\varphi(1@\omega{+}1)$ 的基本列是 $\alpha\mapsto\varphi(\alpha@\omega)$ 的迭代, 第 2 项是 $\varphi(1@\omega)=\mathrm{SVO}$ [Agda]. $\mathrm{SVO}_2=\sup_n\varphi(1@\omega{+}n)=\varphi(1@\omega2)$ (源文件 `φ-1⋯0⋯0`, `refl`).

```agda
Bω-fs : Bω.φ 1 0 0 0 [ 2 ] ≡ Fin.SVO
Bω-fs = refl

SVO₂-fs : Ltω2.SVO₂ [ 0 ] ≡ Eqω.φ 1 0 0
SVO₂-fs = refl
```

修正: 无.

## §5 Transfinitary: 超限元 Veblen 函数与 LVO

### §5.1 工程问题: 该模块不能被导入

**现象.** 在任何模块中写 `import Veblen.Transfinitary`, 都会报

```text
error: [RewriteNonConfluent]
Local confluence check failed:
Veblen.Transfinitary._0̇,_ (Veblen.Transfinitary.Φ (λ z → F z))
reduces to both F and ...
when checking confluence of the rewrite rule
Veblen.Transfinitary.Φ-ż-α with Veblen.Transfinitary.Φ-clause2
```

本文试过 `--rewriting` 单独, 加 `--local-confluence-check`, 加 `--confluence-check`, `--cubical`, `--erased-cubical` 几种组合, 都会失败. 去掉 `--rewriting` 则报 `InfectiveImport`. 而把同一文件改名后单独编译能通过. 所以问题出在导入时对 `{-# REWRITE Φ-ż-α #-}` (第 210 行) 的重新检查. Finitary 与 Infinitary 的说明里提到, Agda 2.8 下它们已经因为同样的原因撤掉了这条重写规则. Transfinitary 没有撤. 目前仓库里没有模块导入它, 所以问题一直潜伏.

**修正 (未应用, 约 40 行).** 删去 `REWRITE` 与 `--rewriting --local-confluence-check`. 十条计算模式改用 Finitary 的写法, 沿 `Φ-ż-α` 作 `subst`. 例如:

```text
Φₛ-s-ż-z : (Φ F {suc α} (suc β) 0̇, 0) ≡ iterω (λ γ → Φ F {suc α} β γ 0̇) 0
Φₛ-s-ż-z {F} {α} {β} = cong (λ h → h 0) (Φ-ż-α {F = fixpt λ γ → Φ F {suc α} β γ 0̇} {α = α})
```

**本文的做法.** 下面逐字复制 Transfinitary 的定义部分 (第 36–39, 63–66, 102–104, 116–118, 130–132, 144–146, 156–157, 499–500, 520–521 行), 不含重写规则与计算模式, 放在模块 `TC` 中审计. 重写规则不参与定义, 只用于证明计算模式, 所以复制件与原文定义相同. 下面的命令已核对两者一致 (输出 `SAME`):

```text
diff <(sed -n '36,39p;63,66p;102,104p;116,118p;130,132p;144,146p;156,157p;499,500p;520,521p' src/Veblen/Transfinitary.lagda.md) \
     <(awk '/^module TC where/{f=1;next} f&&/^```/{exit} f' probes/Audit/Veblen.lagda.md | sed 's/^  //' | grep -v '^$') && echo SAME
```

```agda
module TC where
  _→^_ : Set → Ord → Set
  A →^ zero = A
  A →^ suc α = Ord → A →^ α
  A →^ lim f = ∀ {n} → Ord → A →^ f n

  _0̇ : A →^ α → A
  _0̇ {α = zero} = id
  _0̇ {α = suc _} F = F 0 0̇
  _0̇ {α = lim _} F = F {0} 0 0̇

  Φₛ : Ord →^ suc α → Ord →^ 2+ α
  Φₗ : Ord →^ lim f → Ord →^ suc (lim f)
  Φ : Ord →^ 1 → (∀ {α} → Ord →^ suc α)

  Φₛ F = rec F
    (λ φ → Φ $ fixpt λ γ → φ γ 0̇)
    (λ φ → Φ $ jump λ γ → lim λ n → φ n γ 0̇)

  Φₗ F = rec F
    (λ φ → Φ $ jump⟨ 1 ⟩ λ γ → lim λ n → φ {n} γ 0̇)
    (λ φ → Φ $ jump λ γ → lim λ n → φ n {n} γ 0̇)

  Φ F {α = zero}  = F
  Φ F {α = suc α} = Φₛ (Φ F)
  Φ F {α = lim f} = Φₗ (Φ F)

  φ : ∀ {α} → Ord →^ suc α
  φ = Φ (ω ^_)

  SVO : Ord
  SVO = φ {ω} 1 {0} 0

  LVO : Ord
  LVO = fixpt (λ α → φ {α} 1 0̇) 0
```

### §5.2 定义的语义

**标准 (Schütte 的 Klammersymbole).** 参数是有限支撑的位置到值的映射. 设最高的非零位置 (位置 0 以外) 是 $\pi$, 其值为 $\beta$, 其余位置为零:

- $\pi=\rho+1$ 为后继位置, $\beta$ 为后继值 $\beta'+1$ 时, $\varphi(\beta@\pi,\gamma)$ 枚举 $\xi\mapsto\varphi(\beta'@\pi,\xi@\rho)$ 的不动点;
- $\pi$ 为极限位置, $\beta=\beta'+1$ 时, 枚举一切 $\xi\mapsto\varphi(\beta'@\pi,\xi@\rho)$ ($\rho<\pi$) 的公共不动点;
- $\beta$ 为极限值时, 枚举一切 $\beta''<\beta$ 对应函数的公共不动点.

位置在 $\pi$ 以下的参数按同一规则递归. LVO 是 $\alpha\mapsto\varphi(1@\alpha)$ 的最小不动点.

**Agda 与判定.**

- `Φₛ` 对应后继位置: 不动点链经过紧邻的位置 $\alpha$ (`φ γ 0̇`), 然后用 `Φ {α}` 在新底函数上重建位置 $\le\alpha$ 的各位. **正确**, 与 §2.3 同构.
- `Φₗ` 对应极限位置 $\lambda=\mathsf{lim}\,f$: 后继值用 `jump⟨ 1 ⟩` 对位置 $f(n)$ 取上确界, 极限值沿 $(g(n),f(n))$ 对角. 这两步分别是 §4.1 与 §4.2 的论证, 只是把 $\omega$ 换成 $\lambda$, 把 $n$ 换成 $f(n)$. 公共不动点只取位置 $f(n)$ 处的函数, 这已经足够: 被 $\xi\mapsto\varphi(\beta'@\lambda,\xi@f(n))$ 固定的点, 也被一切位置 $\rho<f(n)$ 的对应函数固定 (A2). **正确 [估计, 高 ~90%]**.
- 类型 `A →^ lim f = ∀ {n} → Ord → A →^ f n` 把 "位置 $<\lambda$ 的有限支撑参数" 表示成 "先选 $n$, 再给位置 $\le f(n)$ 的参数". 不同的 $n$ 之间相容: 全部填零的结果与 $n$ 无关. 这由源文件的 `Φ-ż-α` 给出, 它对一切 $\alpha$ 成立. **正确**.
- `LVO = fixpt (λ α → φ {α} 1 0̇) 0` 是 $\alpha\mapsto\varphi(1@\alpha)$ 从 0 起迭代的上确界. 这个函数递增, 且在极限处连续 (`jump⟨ 1 ⟩ G 0 = G 1`), 所以上确界就是最小不动点. **正确**.

**非外延性.** `φ {α}` 依赖树 `α`, 而不只依赖它的值. 例如 `ω ^ 1` 与 `ω` 是不同的树, 但值相同 (§1.1). 序数标签只对构造中实际出现的规范树有意义. 这与 BTBO 的情形相同, 不算错误.

### §5.3 超限元与有限元逐点相等 [Agda]

本节证明: 对任意底函数与任意 $n$, `TC.Φ F {finord n}` 与 `Fin.Φ F n` 在**全部参数**上取值相同. 这样, 超限元推广在有限元数上不改变任何值. 两者的类型 `Ord →^ finord n` 与 `Ord →ⁿ n` 对变量 `n` 不是定义相等的, 所以先定义逐参数相等 `Agree`.

```agda
Agree : ∀ n → TC._→^_ Ord (finord n) → Ord →ⁿ n → Set
Agree zero x y = x ≡ y
Agree (suc n) x y = ∀ β → Agree n (x β) (y β)

agree-0̇ : ∀ n {x y} → Agree n x y → TC._0̇ {α = finord n} x ≡ y 0̇ᶠ
agree-0̇ zero p = p
agree-0̇ (suc n) p = agree-0̇ n (p 0)

fixpt-cong : {F G : Ord → Ord} → (∀ x → F x ≡ G x) → ∀ x → fixpt F x ≡ fixpt G x
fixpt-cong e x = cong (λ H → fixpt H x) (funExt e)

jump-cong : {F G : Ord → Ord} → (∀ x → F x ≡ G x) → ∀ x → jump F x ≡ jump G x
jump-cong e x = cong (λ H → jump H x) (funExt e)

agree : ∀ n {F G : Ord → Ord} → (∀ x → F x ≡ G x)
  → Agree (suc n) (TC.Φ F {finord n}) (Fin.Φ G n)
agree zero e = e
agree (suc n) {F} {G} e = go where
  go : ∀ α → Agree (suc n) (TC.Φ F {finord (suc n)} α) (Fin.Φ G (suc n) α)
  go zero = agree n e
  go (suc α) = agree n (fixpt-cong λ γ → agree-0̇ n (go α γ))
  go (lim f) = agree n (jump-cong λ γ → cong lim (funExt λ m → agree-0̇ n (go (f m) γ)))
```

推论: 两篇文章各自定义的 SVO 相等.

```agda
SVO-agree : TC.SVO ≡ Fin.SVO
SVO-agree = cong lim (funExt λ n → agree-0̇ n (agree n (λ _ → refl) 1))
```

### §5.4 LVO 的基本列, 以及极限位置不被压平 [Agda]

LVO 的基本列以 $0,\ \omega,\ \mathrm{SVO}$ 开头. 第 2 项是 `φ {ω ^ 1} 1 0̇`, 经过 §1.1 的 `ω^1≡ω` 才等于 SVO.

```agda
LVO-1 : TC.LVO [ 1 ] ≡ ω ^ 1
LVO-1 = refl

LVO-2 : TC.LVO [ 2 ] ≡ TC.SVO
LVO-2 = cong (λ a → TC._0̇ {α = a} (TC.φ {a} 1)) ω^1≡ω
```

**与 BTBO 的对照.** BTBO 的第二个错误是, 极限层 $\Omega_\lambda$ 从未被当作常量, 于是 $\omega$ 以上的层全部塌到 $\psi_0(\Omega_\omega)$. 超限元 Veblen 函数的对应位置是极限位置 $\lambda$. 这里的检验是: $\varphi(2@\omega)$ 的基本列是 $\varphi(1@\omega,1@n)$, 位置 $\omega$ 上的值 $1$ 保留在每一项里. 也就是说, `Φₗ` 在位置 $\lambda$ 上开了新的一层, 没有把它对角成 $\varphi(\cdot@f(n))$.

```agda
TC-ω2-fs : TC.φ {ω} 2 {0} 0 [ n ] ≡ TC._0̇ {α = finord n} (TC.φ {ω} 1 {n} 1)
TC-ω2-fs = refl
```

修正: 定义无需修正. 导入问题见 §5.1.

## §6 汇总表

| 定义 | 文件 | 判定 | 置信度 | 修正规模 |
|---|---|---|---|---|
| `_+_`, `_*_`, `_^_` | Base | 正确, 基本列标准 | [Agda] + [标准] | 无 |
| `iterω`, `jump`, `fixpt` | Base | 正确, 基本列与 Wikipedia 逐项同 | [Agda] | 无 |
| `ε`, `ζ`, `η` | Base | 正确 | [Agda] | 无 |
| oom 的文字说明 | Base | 外观: 差一 (99 个 ζ, 不是 ζ₀ 之上再 99 个) | [Agda] | 1 行文字 |
| FGH/SGH/MGH/HH | Base | 正确 | [标准] | 无 |
| `Graham.G` | Lower | **改变数值, 偏小**: `G 64 = 3↑⁶³3 ≪ g₆₄` | 确定 [Agda] | 1 行代码 + 1 行公式 |
| 二元 `Φ`/`φ` | Multinary | 正确, 五条基本列 = Wikipedia | 高 ~97% [Agda] + [标准] | 无 |
| `Γ` 与后代函数 | Multinary | 正确 | 高 [Agda] | 无 |
| 三元/四元 `Φ` | Multinary | 正确 | 高 ~95% [Agda] | 无 |
| `Φₙ`/`Φ`/`φ`, `SVO` | Finitary | 正确, SVO = sup φ(1@n) | 高 ~95% [Agda] | 无 |
| ω+1 元 `Φ` 后继步 (`jump⟨ 1 ⟩`) | Infinitary | 正确且必要 (换 `jump` 得 1) | 高 ~95% [Agda] + [估计] | 无 |
| ω+1 元 `Φ` 极限步 (对角) | Infinitary | 只改基本列 | 高 ~90% [估计] | 无 (可选 1 行) |
| ω+2, ω+n, (ω2)+1 元, `SVO₂` | Infinitary | 正确 | 高 ~90% [Agda] + [估计] | 无 |
| `Φₛ`/`Φₗ`/`Φ`/`φ` | Transfinitary | 正确; 有限元数上与 Finitary 逐点相等 | 高 ~90% ([Agda] 对有限部分) | 无 |
| `SVO`, `LVO` | Transfinitary | 正确; `SVO ≡ Fin.SVO`, LVO 基本列 0, ω, SVO, … | 高 [Agda] + [标准] | 无 |
| `REWRITE Φ-ż-α` | Transfinitary | 工程: 模块不能被导入 | 确定 (复现) | 约 40 行 |

## §7 结论与边界

**已机器检验 [Agda]:**

- 序数算术与不动点枚举的基本列: $\omega^{\beta+1}[n]=\omega^\beta n$, $\omega^\lambda[n]=\omega^{\lambda[n]}$, $F'(0)[n]=F^n(0)$, $F'(\alpha+1)[n]=F^n(F'(\alpha)+1)$; $\omega^1=\omega$ (外延).
- 二元 Veblen 的 Wikipedia 基本列 (ii)–(v); 三元与四元的后继/极限规则; $\zeta_0[2]=\varepsilon_{\varepsilon_0}$, $\Gamma_0[3]=\varphi_{\varepsilon_0}(0)$, $\mathrm{SVO}[0..2]=\omega,\varepsilon_0,\Gamma_0$.
- ω+1 元: 极限位置若用种子 $0$, φ(1@ω) 会退化成 $\sup(1,1,\ldots)$ (`jump⟨0⟩-would-give-1`). 实际定义给出 $\mathrm{SVO}[n]=\varphi(1@n)$ 与 $\varphi(2@\omega)[n]=\varphi(1@\omega,1@n)$. 极限值步的对角基本列; $\varphi(1@\omega{+}1)[2]=\mathrm{SVO}$.
- 超限元: `agree` (对任意底函数与任意 $n$, 全部参数逐点相等); `SVO-agree`; $\mathrm{LVO}[1]=\omega^1$, $\mathrm{LVO}[2]=\mathrm{SVO}$; $\varphi(2@\omega)[n]=\varphi(1@\omega,1@n)$.
- Lower: `G (suc n) ≡ 3 ↑⟨ n ⟩ 3`, `G 1 ≡ 9`, `G 2 ≡ 27`.

**由论证得到 [估计]:**

| 断言 | 置信度 | 依赖 |
|---|---|---|
| 二元到有限元的每个值等于标准 Veblen 值 | 高 (~97%) | 递归式与 Wikipedia 定义逐条相同; 极限步 `jump` 的公共不动点论证 (§2.1) |
| 极限位置后继值 (`jump⟨ 1 ⟩`) 给出最小/下一个公共不动点 | 高 (~95%) | §4.1, 假设 (A1)(A2) |
| 极限位置极限值的对角选择不改变值 | 高 (~90%) | §4.2 的夹逼论证, 值域闭且递减 |
| ω+2 到 (ω2)+1 元与超限元在一般位置上正确 | 高 (~90%) | 与有限元同构; 有限部分已由 `agree` 机器检验 |
| SVO, SVO₂, LVO 的标签成立 | 高 (~95%) | 上面各条 + 它们的标准定义 |

**边界.**

1. 本文没有在 Agda 中定义序数的序关系, 所以 "值相同" 类的结论 (§4.2, §5.2) 是纸面论证. 要形式化, 需要 Brouwer 树上的 $\le$ 与 Veblen 函数的单调性和不动点性质. 这在 "Agda大序数" 系列中只做到了 $\Gamma_0$.
2. 无法用数值实验区分. 这些序数的 FGH 在 $n\le2$ 时退化, 在 $n\ge3$ 时不可算. 本文因此只比较基本列的项.
3. Infinitary 只做到 (ω2)+1 元. Transfinitary 覆盖一般序数元. 两篇在 ω+1 元以上的逐点一致性没有机器检验, 本文只检验了 SVO 处的一致: 源文件给出 `Eqω.SVO ≡ Fin.SVO`, 本文给出 `TC.SVO ≡ Fin.SVO`. 一般的逐点一致需要 Infinitary 与 `TC` 之间的 `Agree` 类关系, 而两边的类型形状不同.
4. Transfinitary 的审计基于逐字复制件 (§5.1). 若原文件此后改动定义, 复制件需要同步.

**对仓库的含义.** Veblen 五篇的序数标签 (Γ₀, SVO, φ(1@ω), SVO₂, LVO) 可以保留. 需要修正的是 Lower 的葛立恒数定义 (一行) 与 Base 的 oom 说明 (一行文字). Transfinitary 的重写规则在 Agda 2.8 下让该模块无法被导入, 若后续工作要用它, 应先按 §5.1 去掉 `REWRITE`.
