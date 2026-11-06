# 跨高度 (四): 路径选择是真的, 世界限制换实例

> 不含记号. 入口 [HtCross](HtCross.lagda.md). 两条编译过的否定, 前提都有见证.
>
> 1. **`path-real`**: 同一个最高层 $\Lambda=\mathrm{h\Omega}\,g$, 两个合法性证明 $l_0, l_1$ (只差 $\Omega$-单调在 $0\lhd1$ 处选哪一支), 同一个输入、同一个目标, 两个实例的折叠输出**作为树不相等**: 保留节点的路径一边是 `sl 0`, 一边是 `sl 1`. 所以换实例 (哪怕只换合法性证明) 不能是树的相等, 必须像 `HtCrossSim.Rl` 那样不看路径. **`path-rel`** 是正对照: 同一对输出在 `Rl` 下相关 (前提 `Funext`).
> 2. **`no-in-2`**: 层 $2$ 不是 $\Omega$ (`Ωᴴ`) 在世界 $1$ 里的第一位置. 所以 `HtCrossInst.change` 只能把 $\psi_0(\Omega_c)$ ($c\le1$) 搬进 $\Omega$ 的实例 (闭项的世界是 $1$); 更高的分支要先换到更大的世界 (`world-bound` 的推论).
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.HtCrossNeg where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.HtGenGen using (lt-irr)
open import OCF.Align.HtFeedTree
open import OCF.Align.HtFeedHt using (emb; Ωᴴ)
open import OCF.Align.HtFeedNeg using (world-bound)
open import OCF.Align.HtFeedClosed using (ω⋅; module At; one)
open import OCF.Align.HtCrossSim using (Funext; Rl; si; s1; s0)
open import OCF.Align.HtCrossRun using (module Two)
```

## §1 两个合法性证明, 两棵输出树

$g(0)=0$, $g(c)=\lim_n 0$ ($c>0$). 单调在 $0\lhd c'$ 处要一条 $0\lhd\lim_n0$ 的路径, 第 $i$ 支 (`hlim i hself`) 都行.

```agda
L₀ : H
L₀ = hl (λ _ → hz)

g : A → H
g azero = hz
g (asuc _) = L₀
g (alim _) = L₀

mo : ℕ → ∀ {c c′} → Lg c′ → c ⊲ c′ → g c ⊲[ c′ ] g c′
mo i {c = azero} {c′ = azero} _ _ = hself
mo i {c = azero} {c′ = asuc _} _ _ = hlim i hself
mo i {c = azero} {c′ = alim _} _ _ = hlim i hself
mo i {c = asuc _} {c′ = azero} _ ()
mo i {c = asuc _} {c′ = asuc _} _ _ = hself
mo i {c = asuc _} {c′ = alim _} _ _ = hself
mo i {c = alim _} {c′ = azero} _ ()
mo i {c = alim _} {c′ = asuc _} _ _ = hself
mo i {c = alim _} {c′ = alim _} _ _ = hself

lgc : ∀ c → Lg c → LgH (g c)
lgc azero _ = tt
lgc (asuc _) _ = (λ _ → hself) , (λ _ → tt)
lgc (alim _) _ = (λ _ → hself) , (λ _ → tt)

lgi : ℕ → LgH (hΩ g)
lgi i = mo i , lgc

module M (i : ℕ) = At (hΩ g) (lgi i)
module M₀ = M 0
module M₁ = M 1

-- 输入: 世界 1 里一个层 0 的节点 (坐标 0 的分支)
x : D (hΩ g) one
x = ni (sL {c = azero} (C.suc C.self) hself) (λ _ _ _ → n1)

-- 目标: 层 L₀, 走坐标 1 的分支
tL : L₀ ⊲[ one ] hΩ g
tL = hLim {c = one} C.self hself

out₀ : D L₀ one
out₀ = M₀.yc (M₀.Run accᴸ x C.self tt hself M₀.Act n0 M₀.Y₀) (M₀.tg C.self tL tt)

out₁ : D L₀ one
out₁ = M₁.yc (M₁.Run accᴸ x C.self tt hself M₁.Act n0 M₁.Y₀) (M₁.tg C.self tL tt)

-- 顶层 ni 节点走 L₀ 的第几支
idx : ∀ {W} → D L₀ W → ℕ
idx (ni (sl n P) v) = n
idx _ = 0

idx₀ : idx out₀ ≡ 0
idx₀ = refl

idx₁ : idx out₁ ≡ 1
idx₁ = refl

path-real : ¬ (out₀ ≡ out₁)
path-real e with cong idx e
... | ()

-- 正对照: 不看路径时相关
path-rel : Funext → Rl L₀ out₀ out₁
path-rel fe = at (Run-R accᴸ accᴸ hx C.self tt hself hself (igr (λ p lW′ hw hY → Step-R hY)) s0 y0) C.self tL tL tt
  where
  open Two fe (hΩ g) (lgi 0) (hΩ g) (lgi 1)
  hx : Rl (hΩ g) x x
  hx = si (λ p l y y′ r → s1)
  y0 : StR (M₀.Y₀ {one}) (M₁.Y₀ {one})
  y0 = str zero-R refl
```

## §2 世界 1 里 $\Omega$ 之下只有 $0, 1$

```agda
two : A
two = asuc one

no-in-2 : ¬ (emb two ⊲[ one ] Ωᴴ)
no-in-2 p = lt-irr one (world-bound two p)
```
