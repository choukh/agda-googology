# 无填充的对角线: $\psi_0(\Omega_\Omega)$ 的规则 6 链

> 接 [Level](Level.lagda.md). 那里有下标类型 `Ordᴵ` (证据模 $\cong$)、树族与忠实折叠、遗传步进 `HS` 与证书 `toLevel`. 本文以安全路径引理
>
>     Uniform : ∀ (a : Ordᴵ) → HS (ψ⁰ (Ω a))
>
> 为**模块参数** (由并行的工作证明, 这里不证), 组装扩展 Buchholz 记号 (EBO) 的 $\psi_0(\Omega_\Omega)$, 不用 `ordᴰ`/`cumsum`.
>
> 结论先说:
>
> 1. **对角线的基本列就是 EBO 规则 6 的链 (`refl`).** $\gamma_0=\Omega_0=1$, $\gamma_{k+1}=\psi_0(\Omega_{\gamma_k})$, `BTBOᴵ = lim (γ ∘ suc)`, 第 $n$ 项定义性地是 $\psi^0(\Omega_{\mathtt{toLevel}\,\gamma_n})$; 层号 $\gamma_n$ 的基本列逐项是 $\gamma_n$ 的基本列 (Level `toLevel-lim`). EBO 那边 `fsn (EBOψ 2) n` 的前三项是 $\psi_0(\Omega_1)$, $\psi_0(\Omega_{\psi_0(\Omega_1)})$, $\psi_0(\Omega_{\psi_0(\Omega_{\psi_0(\Omega_1)})})$ (`refl`), 形状一致.
> 2. **极限本身也带证书, 不需要额外假设.** 相邻两项的步进 $\gamma_n\sqsubseteq^0\gamma_{n+1}$ 由 `Ψ⁰-mono` 与 `toLevel-⊑` 归纳证出 (`diag-step`), 所以 `HS BTBOᴵ` 成立, 对角线本身是一个层号 `BTBOᴸ`, 它的 $\Omega$ 是对角 $\mathbb{N}$-极限 $\lim_n\Omega_{\gamma_{n+1}}$ (`refl`). `Uniform` 只用来给每个 $\gamma_{k+1}$ 发证书.
> 3. **与 src 的 BTBO 的差别 (§3).** $\Omega_0=\omega$ 对 $1$; 链起点 $0$ 对 $\Omega_0$ (对角线与每个规则 6 的链都是); 层号经 `cumsum` 对逐项; 提升 `↑` 遍历并改写证明对 `up` 节点; 下标 `Ordᴰ` (严格单调) 对 `Ordᴵ` (模 $\cong$ 步进). 两条对角线的值交错 ($1<\omega<\varepsilon_0<\mathsf{BO}<\ldots$, 估计), 极限的标签都是估计的 $\psi_0(\Omega_\Omega)$. 小输入的 FGH 测试见 §3; 参数为 2 的测试从 $\gamma_1$ (以及 src 的 $\psi^n\,2$) 起在一分钟内算不完.
> 4. **`FGH BTBOᴵ 1` 在 `Uniform` 抽象时也能算到 2**: 层号对树递归 (Level §9), 证书只提供步进证据, 而这条计算路径从不读它.
>
> 全文 `--safe --without-K`, 无公设、无洞、无停机或正性编译指示; `Uniform` 是模块参数.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.Diagonal where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
module S = Ord-Ord
import OCF.Align.EBO as E
open import OCF.Align.Level
```

## §1 对角线

EBO 的 $\psi_0(\Omega_\Omega)$: $\Omega_\Omega$ 的共尾度是 $\Omega_1$, 规则 6 在 $\mu=0$ 处折叠, $\gamma_0=\Omega_0=1$, $\gamma_{k+1}=\psi_0(\Omega_\Omega[\gamma_k])=\psi_0(\Omega_{\gamma_k})$, $\psi_0(\Omega_\Omega)[n]=\psi_0(\Omega_{\gamma_n})=\gamma_{n+1}$. 树这边: 每一项连同证书一起迭代 (`next`), 层号是 `toLevel`, 没有任何填充.

```agda
module Diagonal (Uniform : ∀ (a : Ordᴵ) → HS (ψ⁰ (Ω a))) where

  next : Σ (Ordᶜ zero) HS → Σ (Ordᶜ zero) HS
  next (x , h) = ψ⁰ (Ω (toLevel x h)) , Uniform (toLevel x h)

  Γ : ℕ → Σ (Ordᶜ zero) HS
  Γ = iter next (Ω zero , hs hz)

  γ : ℕ → Ordᶜ zero
  γ n = proj₁ (Γ n)

  cert : ∀ n → HS (γ n)
  cert n = proj₂ (Γ n)

  L : ℕ → Ordᴵ
  L n = toLevel (γ n) (cert n)

  BTBOᴵ : Ordᶜ zero
  BTBOᴵ = lim (λ n → ψ⁰ (Ω (L n)))
```

**规则 6 的形状, 全部 `refl`.** 起点是 $\Omega_0=1$, 它的层号是 1; 每一项是上一项的层号上的 $\psi_0(\Omega_\cdot)$; 对角线是 $\gamma\circ\mathrm{suc}$ 的极限. 第 1 项 $\psi_0(\Omega_1)$ 内部又是一条规则 6 的链, 在第 0 层上 ($G_0=\Omega_0=1$, $G_{k+1}=\psi_0(G_k)$, 经 `up zero` 嵌入第 1 层), 与 EBO 的 $\psi_0(\Omega)[n]$ 同形 (EBO §8.2). 层号 $L_1$ 的第 $n$ 项就是 $\psi_0(G_n)$ 的层号.

```agda
  _ : γ 0 ≡ Ω zero
  _ = refl

  _ : γ 0 ≡ suc zero
  _ = refl

  _ : L 0 ≡ suc zero
  _ = refl

  _ : ∀ n → γ (suc n) ≡ ψ⁰ (Ω (L n))
  _ = λ n → refl

  _ : BTBOᴵ ≡ lim (γ ∘ suc)
  _ = refl

  G : ℕ → Ordᶜ zero
  G = iter (λ x → ψ zero (λ q → q) (up zero x)) (suc zero)

  _ : γ 1 ≡ lim (λ n → ψ⁰ (G n))
  _ = refl

  _ : ∀ n → L 1 [ n ]ᴵ ≡ toLevel (ψ⁰ (G n)) (hl₁ (cert 1) n)
  _ = λ n → refl
```

EBO 一侧 (参照记号 [EBO](EBO.lagda.md), `EBOψ 2` $=\psi_0(\Omega_{\Omega})$, `Ωt μ` $=\Omega_\mu$, `natT 1` $=1$): 前三项基本列.

```agda
  _ : E.fsn (E.EBOψ 2) 0 ≡ E.ψ [] (E.Ωt (E.natT 1)) ∷ []
  _ = refl

  _ : E.fsn (E.EBOψ 2) 1 ≡ E.ψ [] (E.Ωt (E.ψ [] (E.Ωt (E.natT 1)) ∷ [])) ∷ []
  _ = refl

  _ : E.fsn (E.EBOψ 2) 2 ≡ E.ψ [] (E.Ωt (E.ψ [] (E.Ωt (E.ψ [] (E.Ωt (E.natT 1)) ∷ [])) ∷ [])) ∷ []
  _ = refl
```

即 $\psi_0(\Omega_1)$, $\psi_0(\Omega_{\psi_0(\Omega_1)})$, $\psi_0(\Omega_{\psi_0(\Omega_{\psi_0(\Omega_1)})})$, 与树侧的 $\psi^0(\Omega_{L_0})$, $\psi^0(\Omega_{L_1})$, $\psi^0(\Omega_{L_2})$ ($L_0=1$, $L_{k+1}$ 是 $\gamma_{k+1}$ 的层号) 逐项同形. "同形" 指外层的规则 6 一步: 两边都是 "$\psi_0(\Omega_x)$, $x$ 取链的上一项". 把它升级为 "树的基本列与 EBO 的基本列处处一致" 还要内层的对应定理 (每个 $\gamma_k$ 与 EBO 的 $\gamma_k$ 的基本列一致), 那是 [FiniteAll](FiniteAll.lagda.md)/[Translate](Translate.lagda.md) 那条路线在下标为树时的推广, 本文未做.

## §2 对角线自身的遗传步进

`Uniform` 给每个 $\gamma_{k+1}$ 发证书. 相邻两项的步进则不需要另外的假设: 第 0 步是 $1\sqsubseteq\psi_0(\Omega_1)$ ($0$ 是任何 $\psi^0$ 输出的前驱, `z≺ψ⁰`); 之后 $\gamma_n\sqsubseteq^0\gamma_{n+1}$ 经 `toLevel-⊑` 变成 $L_n\sqsubseteq^\mathsf{I}L_{n+1}$, 再经 `Ψ⁰-mono` 变成 $\gamma_{n+1}\sqsubseteq^0\gamma_{n+2}$. 于是对角线的极限本身满足 `HS`, 可以再做成层号.

```agda
  diag-step : ∀ n → γ n ⊑⁰ γ (suc n)
  diag-step zero    (≺z e) = ≺-respˡ (≅-sym e) (z≺ψ⁰ (Ω (suc zero)))
  diag-step (suc n) = Ψ⁰-mono (toLevel-⊑ (cert n) (cert (suc n)) (diag-step n))

  L-step : ∀ n → L n ⊑ᴵ L (suc n)
  L-step n = toLevel-⊑ (cert n) (cert (suc n)) (diag-step n)

  BTBO-HS : HS BTBOᴵ
  BTBO-HS = hl (cert ∘ suc) (diag-step ∘ suc)

  BTBOᴸ : Ordᴵ
  BTBOᴸ = toLevel BTBOᴵ BTBO-HS

  _ : BTBOᴸ [ 0 ]ᴵ ≡ L 1
  _ = refl

  _ : Ω BTBOᴸ ≡ lim (λ n → up (self n) (Ω (L (suc n))))
  _ = refl

  big : ℕ
  big = FGH BTBOᴵ 99
```

`diag-step zero` 的 `≺s` 情况是荒谬的 (没有树在 `zero` 之下), 覆盖检查器自行排除. `BTBOᴸ` 是 "对角对象回灌下标层": 它的 $\Omega$ 是 $\mathbb{N}$-极限 $\lim_n\Omega_{L_{n+1}}$, 逐项精确, 在交替原则下它就是 $\Omega_\Omega$ 在下标位置上的代表 (§5). `big` 是闭项 (只做类型检查).

## §3 与 src 的 BTBO 比较

src 的 [BTBO](../../../src/OCF/BTBO.lagda.md) (2026-11-01 补丁后) 与本文的对角线逐项对照:

| | src `ψⁿ`, `BTBO` | 本文 `γ`, `BTBOᴵ` |
|---|---|---|
| $\Omega_0$ | $\omega$ (`Ω zero = ω`) | $1$ (`Ω zero = suc zero`, EBO 的 $\Omega_0$) |
| 第 0 层的 $\psi_0$ | 恒等 (`ψ₀ {ℓ = zero} a = a`) | EBO 的 $\psi_0$ ($\psi^0$ 对第 0 层的树也折叠) |
| 对角线起点 | $\psi^n\,0=0$, 于是 $\psi^n\,1=\psi_0(\Omega_0)=\omega$ | $\gamma_0=\Omega_0=1$, $\gamma_1=\psi_0(\Omega_1)$ |
| 规则 6 的链起点 | $0$ (`iter (ψ< q ∘ f ∘ coe₀) zero`) | $\Omega_j$ (`iter … (Ω j)`) |
| $i=j$ 的情况 | `lfp (ψ< p ∘ f)`, 经 $\psi_p$ | 与 $i<j$ 同一条链, 经 $\psi_q$ (同目标层, 在 $\cong$ 下无差别) |
| 层号 | `ordᴰ`: 每个 `lim` 换成 `cumsum`, 基本列只共尾一致, 非主数的值被改 (Cumsum `overshoot`) | `toLevel`: 逐项不变 (`toLevel-lim`), 无填充 |
| 层间提升 | `↑` 遍历子树, 把证明写进每个 `limᵢ` | `up` 节点, 定义性 |
| 下标类型 | `Ordᴰ`, `lim` 要严格单调 | `Ordᴵ`, `lim` 要模 $\cong$ 的前驱包含 |
| 穿透的派发 | `<-dec`, 字面三歧 | `<ᴵ-dec`, 模 $\cong$, 穿透经 `tr⁻` |

值 (估计, 依 BTBOSemantics §9 与 Buchholz $\psi_0$ 的单调性): src $0,\ \omega,\ \psi_0(\Omega_\omega)=\mathsf{BO},\ \psi_0(\Omega_{\mathsf{BO}}),\ldots$; 本文 $1,\ \varepsilon_0=\psi_0(\Omega_1),\ \psi_0(\Omega_{\varepsilon_0}),\ \psi_0(\Omega_{\psi_0(\Omega_{\varepsilon_0})}),\ldots$. 两列交错 ($\psi^n\,(k+1)<\gamma_{k+1}<\psi^n\,(k+2)$, 因为 $\psi^n\,1=\omega<\varepsilon_0$ 且 $\gamma_0=1<\omega$), 极限都是 $\alpha\mapsto\psi_0(\Omega_\alpha)$ 的最小不动点, 即估计的 $\psi_0(\Omega_\Omega)$. 两边都只是估计: 本文证的是外层基本列的形状 (§1), 不是序数标签.

**FGH 测试.** 能在合理时间内归约的都写成 `refl`. src 的 $\psi^n\,1=\omega$ 与本文的 $\psi^0(\Omega_0)=\psi_0(1)=\omega$ 基本列相同 (第 $n$ 项都是 $n$), $f_\omega(2)=8$; 本文的起点 $\gamma_0=1$ 给 $f_1(2)=4$. 参数为 1 时 FGH 沿 $[1]$ 一路下降到 0, 值恒为 2; 它说明这条路径上的折叠全部能算, 包括 `Uniform` 抽象时的 $\gamma_2$ 与 `BTBOᴵ`.

```agda
_ : S.FGH (S.ψⁿ 1) 2 ≡ 8
_ = refl

_ : FGH (ψ⁰ (Ω zero)) 2 ≡ 8
_ = refl

_ : S.FGH (S.ψⁿ 2) 1 ≡ 2
_ = refl

_ : S.FGH S.BTBO 1 ≡ 2
_ = refl

module _ (Uniform : ∀ (a : Ordᴵ) → HS (ψ⁰ (Ω a))) where
  open Diagonal Uniform

  _ : FGH (γ 0) 2 ≡ 4
  _ = refl

  _ : FGH (γ 1) 1 ≡ 2
  _ = refl

  _ : FGH (γ 2) 1 ≡ 2
  _ = refl

  _ : FGH BTBOᴵ 1 ≡ 2
  _ = refl
```

**算不完的.** 下面三个在临时文件中以 `timeout 60` 检查, 都在 60 秒时被终止 (退出码 124), 没有给出结果: `FGH (γ 1) 2` ($\psi_0(\Omega_1)[2]$ 下降到 $\omega+2$ 一类的项, $f_{\omega+1}(2)=f_\omega(8)=f_8(8)$ 已远超一进制自然数能写出的范围), `S.FGH (S.ψⁿ 2) 2`, `S.FGH (S.ψⁿ 1) 3` ($f_\omega(3)=f_3(3)$, 约 $4\times10^8$, 一进制). 所以参数 $\ge2$ 的比较只到 $\gamma_0$ 与 $\psi^n\,1$.

**`Uniform` 抽象时为什么还能算.** `γ 2 = ψ⁰ (Ω (toLevel (γ 1) (Uniform (L 0))))`: `toLevel` 对 $\gamma_1$ (一棵具体的树) 递归, 层号的骨架完全算出, 只有 `lim` 的步进证据停在 `Uniform (L 0)` 上. 规则 6 的链在派发时才读步进证据 (`<ᴵ-dec` 的 `lim`/`lim` 且 $n\ne m$ 情况), 沿 $[1]$ 的路径没有碰到它. 若 `toLevel` 对证书递归 (Level §9 的最初写法), `Ω` 的参数就是一个中性项, 连第一步都算不出.

## §4 `Uniform` 买到了什么

- [Certified](Certified.lagda.md): 证书止于 $x_2=\varepsilon_0$ (`ψ⁰ʷ` 原生构造), 之后只有条件包 `CertDiag` (要求每步层号存在且遗忘后 $\approx$ 于忠实折叠); 阻挡是内涵性的 (字面 $\sqsubseteq^\mathsf{w}$).
- [Cumulative](Cumulative.lagda.md): $x_3=\psi_0(\Omega_{\varepsilon_0})$ 的**顶层**序列步进 (`x₃-step`, `x₃-literal-step`), 内部四类序列证了三类; 层号证书未做, 因为下标仍是字面的 `Ordʷ`.
- 本文: 下标证据模 $\cong$, 所以 `HS` (模 $\cong$ 的步进) 直接喂给 `toLevel`. 有了 `Uniform`, **每一项** $\gamma_k$ 都有证书, 每个层号 $L_k$ 都由 `toLevel` 逐项构造, 对角线的任何一个阶段都不用 `cumsum`; `CertDiag` 的 `faith` 条款在这里是定义性的 ($\gamma_{k+1}$ 字面上就是 $\psi^0(\Omega_{L_k})$, 不是 $\approx$). 再加上无条件的 `diag-step`, 极限 `BTBOᴵ` 自身有证书, 可以作为下一层的下标 (`BTBOᴸ`).

`Uniform` 只被用在 `next` 里 (给 $\gamma_{k+1}$ 发证书). 安全路径引理的数学内容 (第 $\ge1$ 层规则 6 链的步进, Cumulative §10 表的第四行) 全在它里面.

## §5 EBO 展望

按交替原则 ($\Omega$ 只在对象层作对角 $\mathbb{N}$-极限出现; 折叠的输出回灌下标层; 下标层保持可数):

1. 本文的下标都是第 0 层树经 `toLevel` 得来的, 所以下标层可数; `BTBOᴸ` 是第一个 "对角对象作下标": $\Omega_{\mathtt{BTBO}^\mathsf{L}}$ 是 $\lim_n\Omega_{L_{n+1}}$, 它在 EBO 里对应的是 $\Omega_\Omega$ 的位置, 但只以 $\mathbb{N}$-极限的身份出现.
2. EBO 的下一个阶段 (例如 $\psi_0(\Omega_{\Omega_\Omega})$, 规则 6 链 $\gamma_{k+1}=\psi_0(\Omega_{\Omega_{\gamma_k}})$) 的下标里含不可数的 $\Omega_{\gamma_k}$. 在这个族里它只能以某个第 0 层对角对象的层号代替; 选哪个对角对象, 以及它的 `HS` (一条 `Uniform` 型的引理, 对新的运算而不只是 $a\mapsto\psi^0(\Omega_a)$), 是缺的部分.
3. 再起一条对角线 (种子不是 1 而是 `BTBOᴵ`) 时, `next` 与 `Uniform` 可以原样使用 (`Uniform` 对一切层号成立); 缺的是种子一步 $x\sqsubseteq^0\psi^0(\Omega_{\mathtt{toLevel}\,x})$: `diag-step zero` 只对 $x=1$ 证了.
4. `Ordᴵ`/`Ordᶜ` 本身不需要改: 三歧性模 $\cong$、搬运只在 `ψ` 的穿透处, 与阶段无关. 若某个阶段要把第 $\ge1$ 层的树做成下标, 就需要 `toLevel` 的高层版本, 这违背 "下标层只收第 0 层折叠输出" 的交替原则, 不在计划内.
5. EBO 的极限 $\psi_0(\Lambda)$ (Ω-塔 `EBOψ n` 的极限) 是 "阶段的对角线": 每个阶段是一个 `Diagonal` 实例, 阶段极限之间的步进同样要种子一步引理.

## §6 结论与边界

**已形式化** (以 `Uniform` 为模块参数):

1. 无填充的对角线: `Γ`/`γ`/`cert`/`L`, `BTBOᴵ = lim (γ ∘ suc)`, 第 $n$ 项 $\psi^0(\Omega_{L_n})$, 起点 $\Omega_0=1$; 第 1 项内部的第 0 层链; 层号逐项 (`refl`).
2. EBO 的 $\psi_0(\Omega_\Omega)$ 前三项基本列 (`refl`), 与树侧同形.
3. 对角线的相邻步进 `diag-step` (无额外假设), 极限的证书 `BTBO-HS`, 极限作为层号 `BTBOᴸ` 与它的 $\Omega$ (`refl`).
4. FGH 测试: 8, 8, 4, 2, 2, 2, 2, 2 (`refl`), 其中 `FGH (γ 2) 1` 与 `FGH BTBOᴵ 1` 在 `Uniform` 抽象时归约.

**边界.**

- `Uniform` 是假设. 本文的一切无条件部分 (`diag-step` 等) 只用到 Level 的引理.
- 序数标签仍是估计: 外层基本列与 EBO 规则 6 同形, 但每个 $\gamma_k$ 的内部与 EBO 的对应未证.
- 参数 $\ge2$ 的 FGH 比较从 $\gamma_1$ 与 $\psi^n\,2$ 起在 60 秒内算不完 (§3).
- 本文不改 `src/`、`archive/` 与已有的 Align 文件.
