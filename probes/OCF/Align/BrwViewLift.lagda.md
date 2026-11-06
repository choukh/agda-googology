# 布劳威尔树的 View (七): 前缀抬升不是无条件的

> 不含记号. 入口 [BrwView](BrwView.lagda.md). [BrwViewOne](BrwViewOne.lagda.md) 的 `ni` 段与 [BrwViewKappa](BrwViewKappa.lagda.md) 的 `nκ` 段都用 `lift`: 第 1 层差树 $x$ 用 `nw p` 抬到更大的世界再求值, 值不低于原来的值 (`bw p (toB x) ≼ toB (nw p x)`). 这里给编译过的反例: 一棵**没有 `nκ`** 的差树 $x^p$, `lift-fails : ¬ (bw p (toB x) ≼ toB (nw p x))`, 所以 $x^p$ 不满足 `HW` (`not-HW`).
>
> $x^p=\sum_z u(z)$, 分支读**世界的路径**: 路径是 `self` (世界就是 $0$ 自己) 时给 $1$, 否则给 $0$. 在世界 $0$ 求值, 坐标 $1$ 那一支 $\ge1$; 抬到世界 $1$ 再求值, 一切分支的路径都形如 `suc _` 或 `lim _ _`, 每一格都是 $0$.
>
> 这否定的是 "前缀抬升值不变" 无条件成立, 所以本文的 View 构造要条件. **不否定**别的读法: 部分的世界可以另选 (例如 `ki` 种的坐标含世界 $W$ 自己, 那一支不用抬升), 一般的 $x ⨾ y$ 的值一致也许在更弱的条件下成立. 未判定.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BrwViewLift where

open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc; _⊲_; Lg; ss; ⊲-tr)
import OCF.Align.CumReadCF as C
open import OCF.Align.SumOneTree using (D; n0; n1; _⨾_; nl; ni; nκ; nw)
open import OCF.Align.LayerTrBase
open import OCF.Align.LayerTrOne using (one; S; toB; Ok)
open import OCF.Align.LayerTrNeg using (Zv-I)
open import OCF.Align.BrwViewOne using (HW; lift)
```

## §1 读路径的分支

```agda
isSelf : ∀ {W′} → azero ⊲ W′ → Bool
isSelf C.self = true
isSelf (C.suc _) = false
isSelf (C.lim _ _) = false

pk : ∀ {W} → Bool → D one W
pk true = n1
pk false = n0

xᵖ : D one azero
xᵖ = ni (ss C.self) (λ p l w → pk (isSelf p))

ok-xᵖ : Ok no xᵖ
ok-xᵖ p l w = kp (isSelf p)
  where
  kp : ∀ b → Ok no (pk {_} b)
  kp true = tt
  kp false = tt

-- 抬到世界 1 之后, 路径不再是 self
notSelf : ∀ {W″} (r : asuc azero ⊲ W″) → isSelf (⊲-tr (C.suc C.self) r) ≡ false
notSelf C.self = refl
notSelf (C.suc r) = refl
notSelf (C.lim n r) = refl
```

## §2 两边的值

```agda
one⊲ : Lg (asuc azero)
one⊲ = tt

big : bs (bz {azero}) ≼ toB tt xᵖ
big = ≼i C.self tt (asuc azero) tt (s≼s z≼)

ze : ∀ {W″} (p″ : asuc azero ⊲ W″) (l″ : Lg W″) (w : D azero W″) (b : B₁ W″) → Zv b →
     Zv (S C.self l″ b (pk (isSelf (⊲-tr (C.suc C.self) p″))))
ze p″ l″ w b zb = subst (λ bo → Zv (S C.self l″ b (pk bo))) (sym (notSelf p″)) zb

small : Zv (toB one⊲ (nw (C.suc C.self) xᵖ))
small p″ l″ y ly = Zv-I _ (ze p″ l″) _ C.self n0 (bw p″ bz) tt

lift-fails : ¬ (bw (C.suc C.self) (toB tt xᵖ) ≼ toB one⊲ (nw (C.suc C.self) xᵖ))
lift-fails h = no-suc {b = toB one⊲ (nw (C.suc C.self) xᵖ)} small (≼-trans (≼w big) h)

not-HW : ¬ HW xᵖ
not-HW h = lift-fails (proj₂ (lift tt one⊲ (C.suc C.self) xᵖ h))
```
