# 结构关系, 第十四轮 (七): 顶层第 0 格的走法路径不能对齐; 错一格的值比较

> 不读记号. 入口 [StrRel14](StrRel14.lagda.md). 接手清单第 3 项 (StrRel13 §3): "比较第 $0$ 格的走法路径 ($[0,v)$ 对 $[1,v')$, 它们可以对齐), 而不比较 $q_0$". 本文检查这一判断.
>
> 1. **(定理, 否定) `¬alCell0`**: `MonoStep Ωᴴ` 两边的第 $0$ 格 (`κc … 0`) 的走法路径 `av`, 左边是 $0\lhd 1\lhd v$ (树世界 $0$ 经 `z⊲ one`, 再经 `sum-fst`), 右边是 $1\lhd v'$; 状态的第 $0$ 层分量按闭项的字面 (左 $n_0⨾\mathrm{nl}\,(\lambda\_.\,1⨾0)$, 右 $((n_0⨾\mathrm{nl}\,d)⨾n_0)⨾\mathrm{nl}\,d'$, $d'$ 任意). 这两条路径**没有** `Al` 对齐 (对一切 $d'$, 一切领先量的上界 $L,L'$): 左边最底下多一步后继 ($0\to1$), 右边那里是极限的第 $0$ 项. 所以 StrRel13 §3 第 3 条 "它们可以对齐" 不成立 (只否定用 `StrRel4Walk.Al` 对齐这两条路径).
> 2. **(定理) `shiftV`**: 错一格的值比较. 左边 $x⨾\mathrm{nl}\,a$, 右边 $n_0⨾\mathrm{nl}\,b$; 若 $x$ 对 $b_0$, $a_n$ 对 $b_{n+1}$ 在任意底 $\gamma\le\gamma'$ 上和的值 $\le$, 则 $\Sigma_\beta(x⨾\mathrm{nl}\,a)\le\Sigma_{\beta'}(n_0⨾\mathrm{nl}\,b)$ ($\beta\le\beta'$). 这是 "左边多出来的第 $0$ 格并进右边的第 $0$ 段, 其余错一格" 的值的形状, 不用 `Al`.
>
> **范围 (判断).** `shiftV` 只是顶层比较 (`StrRel14If.TopOut`) 的一个组合引理; 两边的输出与 `shiftV` 的形状逐字对上要再展开 `Walk` 的 `lim` 一句 (右边的第 $0$ 段本身是 $n_0⨾\mathrm{nl}\ldots$), 本文没有做. 错一格以后要比的是左边坐标 $c$ 的格 (节点坐标层 `emb c`) 与右边坐标 $c+1$ 的格 (`hs (emb c)`), 这是跨坐标层的节点对, 字面 $\mathrm{emb}\,c\sqsubseteq_\infty \mathrm{hs}\,(\mathrm{emb}\,c)$ 成立 (`u∞ s∞`), 正是 `StrRel14Rk.node-red` 的前提形状; 它的三种义务没有证.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRel14Top where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; ≤l; l≤; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedTree using (D₀; n0; n1; _⨾_; nl; sum; pt; sum-fst; Lg-sum)
open import OCF.Align.HtFeedClosed using (one)
open import OCF.Align.StrRel4Walk using (Al; aS; aP; aR; aRL; aL)
```

## 1 第 0 格的两条路径

左: 状态 $Y_0\oplus\mathrm{Step}\,Y_0$ 的第 $0$ 层分量; 右: 状态 $((Y_0\oplus\mathrm{Step}\,Y_0)\oplus 0)\oplus\mathrm{Step}(\ldots)$ 的第 $0$ 层分量, 只用它的构造子形状 (最后一段 $d'$ 任意).

```agda
dL : ℕ → D₀ one
dL _ = n1 ⨾ n0

zL : D₀ one
zL = n0 ⨾ nl dL

zR : (ℕ → D₀ one) → D₀ one
zR d′ = ((n0 ⨾ nl dL) ⨾ n0) ⨾ nl d′

-- 格路径 av: 左边 树世界 0 →(z⊲ one) 1 →(sum-fst) v; 右边 树世界 1 = 运行世界 →(sum-fst) v′
avL : azero ⊲ sum one zL
avL = ⊲-tr (z⊲ one) (sum-fst one zL)

avR : ∀ d′ → one ⊲ sum one (zR d′)
avR d′ = sum-fst one (zR d′)

-- 折叠里右边的格路径是 ⊲-tr self (sum-fst …) (树世界即运行世界); 在这一形状上与 avR 定义性相同
avR≡ : ∀ d′ → ⊲-tr C.self (sum-fst one (zR d′)) ≡ avR d′
avR≡ d′ = refl

¬alCell0 : ∀ {L L′} d′ → ¬ Al L L′ avL (Lg-sum one zL tt) (avR d′) (Lg-sum one (zR d′) tt)
¬alCell0 d′ (aL (aRL ()) G)
¬alCell0 d′ (aRL (aL () G))
¬alCell0 d′ (aRL (aRL ()))
```

## 2 错一格的值比较

```agda
shiftV : ∀ {W W′} (x : D₀ W) (a : ℕ → D₀ W) (b : ℕ → D₀ W′) →
         (∀ γ γ′ → γ ≤ γ′ → sum γ x ≤ sum γ′ (b 0)) →
         (∀ n γ γ′ → γ ≤ γ′ → sum γ (a n) ≤ sum γ′ (b (suc n))) →
         ∀ β β′ → β ≤ β′ → sum β (x ⨾ nl a) ≤ sum β′ (n0 ⨾ nl b)
shiftV x a b hx ha β β′ le = l≤ (λ n → ≤l (suc n) (h n))
  where
  h : ∀ n → pt (sum β x) a n ≤ pt β′ b (suc n)
  h zero = hx β β′ le
  h (suc n) = ha n (pt (sum β x) a n) (pt β′ b (suc n)) (h n)
```
