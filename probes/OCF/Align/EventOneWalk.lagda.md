# 原后继回调的全事件区间公式

这不是另一个首格样本。原事件走法的回调为 n1 时，每次都执行
原 Act/Stp，并把此前输出累加进状态。下面对任意源层、合法最高层、
事件区间、前缀和初状态给出第二层输出的完整公式；不忽略新增事件。
这个受限生成族不等于任意 Run，也不要求任意函数自然性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EventOneWalk where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.CumReadCF using (Lg)
open import OCF.Align.HtTowerTy
open import OCF.Align.EvFoldTree
open import OCF.Align.EvFoldRead using (D₂)
open import OCF.Align.EventReturnCtxValueIf using (R₂; rz; ra; rl)
open import OCF.Align.EventReturnCtxValueActual using (floor₂)
open import OCF.Align.EventReturnHistory using (Suffix; done; next)
import OCF.Align.EvFoldClosed as Closed

length : ∀ {H J} → Suf H J → ℕ
length here = zero
length (there e s) = suc (length s)

length-pair : ∀ {H H′ J J′} {p : Suf H J} {q : Suf H′ J′} →
  Suffix p q → length p ≡ length q
length-pair done = refl
length-pair (next e p) = cong suc (length-pair p)

-- 同一个 y 是区间开始时在目标处已有的累计值。
counted : ∀ {W} → ℕ → D₂ W → D₂ W
counted zero y = n0
counted (suc n) y = counted n y ⨾
  nl (λ _ → Ωd (hs (hs hz)) ⨾ (y ⨾ counted n y))

counted-related : ∀ {a H H′ x y} → R₂ a H H′ x y → ∀ n →
  R₂ a H H′ (counted n x) (counted n y)
counted-related p zero = rz
counted-related p (suc n) =
  ra (counted-related p n)
     (rl (λ _ → ra floor₂ (ra p (counted-related p n))))

module At (Λ : Ht) (lΛ : LgB Λ)
  (o₁ : ∀ {w} → hs hz ⊲[ w ] Λ) (o₂ : ∀ {w} → hs (hs hz) ⊲[ w ] Λ) where
  module R = Closed.At Λ lΛ o₁ o₂
  open R

  walk : ∀ {ly W₀ V H₁ H₂ m} (ac : AccY ly)
    (q : proj₁ W₀ OCF.Align.CumReadCF.⊲ proj₁ V)
    (t : Suf (proj₂ W₀) H₁) (s : Suf H₁ H₂) (r : Suf H₂ (proj₂ V))
    (lV : LgWε V) (ll : LW ly V) (co : D ly V) (Y : St V)
    (T : Tg V (hs (hs hz)) m) →
    yc (WalkE ac (λ _ _ → n1) q t s r lV ll Act co Y) T ≡
      counted (length s) (yc (d Y) T)
  walk ac q t here r lV ll co Y T = refl
  walk ac q t (there e s) r lV ll co Y T
    rewrite walk ac q t s (suf-tr (there e here) r) lV ll co Y T = refl
```

counted-related 把任意区间的公式接回现有第二层关系。事件的载荷
对这个常后继回调没有作用，事件次数却有作用；这个特例不能提升成
任意回调只看次数。后续可用本公式检验原 κ₁ 首格中那个未证的
κ₀ 后继内枝，而不把其零内枝版本当作替代品。
