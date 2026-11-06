# NegFab6 (四): 前缀进分支要分支的类型放得下外部结点 — 一个玩具

> 不含记号. 入口 [NegFab6](NegFab6.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不用函数外延. 只依赖 stdlib 与 `Fab6Base`. **这是玩具**, 不是候选定义: 只有 $\Omega_1$ 一个结点, 没有塔, 没有跨底折叠, 没有证书.
>
> **它说明什么.** `NegFab6Cmp.crw-br` 的效应 (折叠 $\varphi(a+\Omega_1(g))$ 的分支是 $\varphi(a+g_c)$) 要求前缀 $a$ 能放进分支. Fab6 的分支类型 `HB X⊥ (Tw X⊥ S⊥ y)` 不含外部结点, 而 $a$ 含, 所以放不进去. 让分支类型放得下 $a$ 的最直接写法是把树按世界 $B$ 编索引: 世界 $B$ 的结点在坐标 $e\rhd B$ 处的分支是世界 $e+1$ 的树. 下面 `W B` 就是这个写法, 它类型检查, 前缀进分支靠 `lift` (世界单调). 这里 CRw 的 `PH B h` 的内容 (结点在世界 $B$ 里, 分支在 $e+1$ 里) 成了索引, 所以这个写法去掉的是 "沿折叠搬运证据", 没有去掉世界本身. 没有测它在塔上的代价, 也没有证明别的写法都不行 (穷尽是判断).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegFab6Idx where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.Fab6Base using (Cd; hz; hs; hl; _⊲_; hself; hsuc; ⊲ᴮ-tr)

data W (B : Cd) : Set where
  wz : W B
  ws : W B → W B
  wl : (ℕ → W B) → W B
  wn : ((e : Cd) → B ⊲ e → W (hs e)) → W B

lift : ∀ {B B′} → B ⊲ B′ → W B → W B′
lift q wz = wz
lift q (ws a) = ws (lift q a)
lift q (wl f) = wl (λ n → lift q (f n))
lift q (wn g) = wn (λ e p → g e (⊲ᴮ-tr q p))

_⊕_ : ∀ {B} → W B → W B → W B
a ⊕ wz = a
a ⊕ ws b = ws (a ⊕ b)
a ⊕ wl f = wl (λ n → a ⊕ f n)
a ⊕ wn g = wn (λ e p → lift (hsuc p) a ⊕ g e p)

mulW : ∀ {B} → W B → ℕ → W B
mulW x zero = x
mulW x (suc n) = mulW x n ⊕ x

sumW : ∀ {B} → (ℕ → W B) → ℕ → W B
sumW f zero = f 0
sumW f (suc n) = sumW f n ⊕ f (suc n)

φW : ∀ {B} → W B → W B
φW wz = ws wz
φW (ws h) = wl (mulW (φW h))
φW (wl f) = wl (sumW (λ n → φW (f n)))
φW (wn g) = wn (λ e p → φW (g e p))

branch : ∀ {B} (a : W B) (g : (e : Cd) → B ⊲ e → W (hs e)) →
         φW (a ⊕ wn g) ≡ wn (λ e p → φW (lift (hsuc p) a ⊕ g e p))
branch a g = refl
```
