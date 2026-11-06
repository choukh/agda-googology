# ValC (四): 函数外延推出 `Cd` 上的 UIP (条件; 说明值定理的前提可满足)

> 不含记号. 入口 [ValC](ValC.lagda.md). 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示. **函数外延 `Funext` 只作前提**, 本篇的结论是条件定理 (条件: Funext). 不进成品.
>
> [ValCMono](ValCMono.lagda.md) 的定理以 `uipC` (可数树 `Cd` 的相等证明唯一) 为模块参数. 本篇说明它可满足: 有函数外延就有它 (`fe→uipC`). 证明是编码-解码, 照 [AdmWUip](../Align/AdmWUip.lagda.md) 的做法重写在 `CRwBase.Cd` 上 (那边是 `HtTowerTy` 的高度, 类型不同, 不能直接用).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.ValCUip where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties using (trans-symʳ)
open import OCF.Lean.CRwBase

Funext : Set₁
Funext = ∀ {X : Set} {Y : X → Set} {f g : (x : X) → Y x} → (∀ x → f x ≡ g x) → f ≡ g

UIPC : Set
UIPC = ∀ {x y : Cd} (e e′ : x ≡ y) → e ≡ e′

Code : Cd → Cd → Set
Code hz hz = ⊤
Code (hs x) (hs y) = Code x y
Code (hl f) (hl g) = ∀ n → Code (f n) (g n)
Code (hΩ () _) _
Code hz (hs _) = ⊥
Code hz (hl _) = ⊥
Code hz (hΩ () _)
Code (hs _) hz = ⊥
Code (hs _) (hl _) = ⊥
Code (hs _) (hΩ () _)
Code (hl _) hz = ⊥
Code (hl _) (hs _) = ⊥
Code (hl _) (hΩ () _)

rc : ∀ x → Code x x
rc hz = tt
rc (hs x) = rc x
rc (hl f) = λ n → rc (f n)
rc (hΩ () _)

encode : ∀ {x y} → x ≡ y → Code x y
encode {x} refl = rc x

module _ (fe : Funext) where
  decode : ∀ x y → Code x y → x ≡ y
  decode hz hz _ = refl
  decode (hs x) (hs y) c = cong hs (decode x y c)
  decode (hl f) (hl g) c = cong hl (fe (λ n → decode (f n) (g n) (c n)))
  decode (hΩ () _) _ _
  decode hz (hs _) ()
  decode hz (hl _) ()
  decode hz (hΩ () _) _
  decode (hs _) hz ()
  decode (hs _) (hl _) ()
  decode (hs _) (hΩ () _) _
  decode (hl _) hz ()
  decode (hl _) (hs _) ()
  decode (hl _) (hΩ () _) _

  isP : ∀ x y (c c′ : Code x y) → c ≡ c′
  isP hz hz c c′ = refl
  isP (hs x) (hs y) c c′ = isP x y c c′
  isP (hl f) (hl g) c c′ = fe (λ n → isP (f n) (g n) (c n) (c′ n))
  isP (hΩ () _) _ _ _
  isP hz (hs _) ()
  isP hz (hl _) ()
  isP hz (hΩ () _) _ _
  isP (hs _) hz ()
  isP (hs _) (hl _) ()
  isP (hs _) (hΩ () _) _ _
  isP (hl _) hz ()
  isP (hl _) (hs _) ()
  isP (hl _) (hΩ () _) _ _

  r : ∀ {x y} → Code x y → x ≡ y
  r {x} {y} c = trans (decode x y c) (sym (decode y y (rc y)))

  r-enc : ∀ {x y} (e : x ≡ y) → r (encode e) ≡ e
  r-enc {x} refl = trans-symʳ (decode x x (rc x))

fe→uipC : Funext → UIPC
fe→uipC fe e e′ = trans (sym (r-enc fe e)) (trans (cong (r fe) (isP fe _ _ (encode e) (encode e′))) (r-enc fe e′))
```

## 结论 (按档)

- **[条件定理, 条件 Funext]** `fe→uipC : Funext → UIPC`. 函数外延在立方模型中成立, 本仓库只作前提.
