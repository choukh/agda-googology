# YiSuc 结点：第 1 层的层号 0 结点，主线累加链对参照不累加链两向

**验收文件，档位：编译定理 (对模块参数)。** `NodeTwo.result`：参照结点 `limᵢ zero f` 与主线结点 (分支 `gm`，推进 `gk`) 折到第 0 层后两向 (`Two`)。
参数：链点上分支两向 (`hm`, `hk`)，参照分支对 `≼ˣ` 同余 (`cg`)，以及吸收用的对数 `lg` (ψ⁰ 值相同，有证书，沿主线链点严格上升)。主线链累加，参照链不累加：每步主线多出的左加数由 [YiChainBase](YiChainBase.lagda.md) 的 `ABS` 与 [YiChainBack](YiChainBack.lagda.md) 的 `ABSR` 吸收，见证取上一个链点的对数。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSucNode where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanFold
open import OCF.Lean.YiLeanTw3 using (R)
open import OCF.Lean.YiLeanAccFin using (read; read-plus)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl)
open import OCF.Align.YiVmConExact using (_≼ˣ_; ≼lˣ; lˣ; reflˣ; ≅→≼ˣ; ˣ→≼)
open import OCF.Lean.YiZeroAccP using (+ˣ)
open import OCF.Lean.YiChainBase using (T₀; transˣ; module Abs)
open import OCF.Lean.YiChainBack using (module AbsR)
open import OCF.Lean.YiUBRed using (Two)
open import OCF.Lean.YiSucLx using (T₁)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 1 两条链

```agda
module Chains (f : T₀ → T₁) (gk : R → R) where
  d : ℕ → R
  d = chain zero gk

  X : ℕ → T₀
  X n = read (d n)

  ref-step : T₀ → T₀
  ref-step y = L.ψ {i = L.zero} {k = L.suc L.zero} {ℓ = L.suc L.zero} L.zero (λ r → r) (f y)

  e : ℕ → T₀
  e = iterᴸ ref-step (L.suc L.zero)
```

## 2 结点

```agda
module NodeTwo (f : T₀ → T₁) (same : ∀ y → f y L.≅ f y) (gm gk : R → R) (lg : T₀ → T₀)
  (open Chains f gk)
  (hm : ∀ n → Two (L.ψ⁰ (f (X n))) (read (gm (d n))))
  (hk : ∀ n → Two (L.ψ⁰ (f (X n))) (read (gk (d n))))
  (cg : ∀ {y y′} → y ≼ˣ y′ → L.ψ⁰ (f y) ≼ˣ L.ψ⁰ (f y′))
  (fl : ∀ y → Two (L.ψ⁰ (f y)) (L.ψ⁰ (lg y)))
  (hs : ∀ n → L.HS (lg (X n)))
  (st : ∀ n → lg (X n) L.≺ lg (X (suc n)))
  (z0 : L.𝟎 {L.zero} L.≺ lg (L.suc L.zero)) where

  rp : ∀ n → X (suc n) L.≅ (X n L.+ read (gk (d n)))
  rp n = read-plus (d n) (gk (d n))

  record Wit (n : ℕ) : Set where
    constructor wit
    field
      c  : T₀
      lt : c L.≺ lg (X n)
      cx : Two (L.ψ⁰ c) (X n)

  absorb : ∀ n → Wit n → Two (L.ψ⁰ (lg (X n))) (X (suc n))
  absorb n (wit c lt (cx , xc)) =
    transˣ (Abs.ABS cx (ˣ→≼ xc) (lg (X n)) (hs n) lt)
      (transˣ (+ˣ (reflˣ (X n)) (≼-refl (X n)) (transˣ (proj₂ (fl (X n))) (proj₁ (hk n))))
        (≅→≼ˣ (L.≅-sym (rp n)))) ,
    transˣ (≅→≼ˣ (rp n))
      (transˣ (+ˣ (reflˣ (X n)) (≼-refl (X n)) (transˣ (proj₂ (hk n)) (proj₁ (fl (X n)))))
        (AbsR.ABSR xc (ˣ→≼ cx) (lg (X n)) (hs n) lt))

  J : ∀ n → Two (L.ψ⁰ (lg (X n))) (X (suc n))
  W : ∀ n → Wit n
  J n = absorb n (W n)
  W zero = wit L.𝟎 z0 (reflˣ _ , reflˣ _)
  W (suc n) = wit (lg (X n)) (st n) (J n)

  step≅ : ∀ y → ref-step y L.≅ L.ψ⁰ (f y)
  step≅ y = L.≅-sym (L.ψ⁰≅ψ {p = L.zero} {σ = λ r → r} (same y))

  inv : ∀ n → Two (e n) (X n)
  inv zero = reflˣ _ , reflˣ _
  inv (suc n) =
    transˣ (≅→≼ˣ (step≅ (e n)))
      (transˣ (cg (proj₁ (inv n))) (transˣ (proj₁ (fl (X n))) (proj₁ (J n)))) ,
    transˣ (proj₂ (J n))
      (transˣ (proj₂ (fl (X n))) (transˣ (cg (proj₂ (inv n))) (≅→≼ˣ (L.≅-sym (step≅ (e n))))))

  term : ∀ n → Two (L.ψ⁰ (f (e n))) (read (gm (d n)))
  term n = transˣ (cg (proj₁ (inv n))) (proj₁ (hm n)) , transˣ (proj₂ (hm n)) (cg (proj₂ (inv n)))

  result : ∀ w → Two (L.ψ⁰ (L.limᵢ {i = L.zero} L.zero f)) (read (Ψn zero zero w gm gk))
  result (keep () q)
  result fold = lˣ (λ n → ≼lˣ n (proj₁ (term n))) , lˣ (λ n → ≼lˣ n (proj₂ (term n)))
```
