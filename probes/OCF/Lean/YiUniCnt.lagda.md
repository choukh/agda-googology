# YiUni 实例：可数层号上的折叠满足接口

**非验收文件。判决：编译定理，无前提。** `Bd k` 取不含 `vΩ` 的 `Lv` (谓词 `Cn`)，折叠取 [YiNextFold](YiNextFold.lagda.md) 在零、后继、ℕ 极限上的行 (与 [YiLeanFold](YiLeanFold.lagda.md) 逐字相同，块是同一份定义的另一个模块)。
Ω 结点层号上 `Bd` 为空，相应字段空真；读回域填到 `tw 1` (`dom₁`) 与第 0 层树的读回 (`lvC`)，到不了 `tw 2` (`no-tw2`)。不否定别的实例。接口 [YiUniIf](YiUniIf.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUniCnt where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
open import OCF.Lean.YiNextFold using (Ψ; Ψ-lgl; Ψ-cp)
open import OCF.Lean.YiNextTop using (lv)
open import OCF.Lean.YiUniIf using (Uni; DomTo)
```

## 1 字段

```agda
data Cn : ∀ {k} → Lv k → Set where
  c0 : Cn v0
  cs : ∀ {k} {V : Lv k} → Cn V → Cn (vs V)
  cl : ∀ {f : ℕ → LF} {V : ∀ n → Lv (f n)} {st : ∀ n → Shift (f n) (f (suc n))} → (∀ n → Cn (V n)) → Cn (vl V st)

Bc : LF → Set
Bc k = Σ (Lv k) Cn

Cnt : Uni
Cnt = record
  { Bd = Bc
  ; bS = λ { (vs V , cs c) → V , c }
  ; bL = λ { (vl V st , cl c) n → V n , c n }
  ; bC = λ { (vΩ V u , ()) }
  ; Ψ = λ m V → Ψ m (proj₁ V)
  ; cmp = λ V → cmp (proj₁ V)
  ; ωw = λ { m (vΩ V u , ()) }
  ; Kb = λ { m (vΩ V u , ()) }
  ; stp = λ { (vΩ V u , ()) }
  ; obd = λ { m (vΩ V u , ()) }
  ; cpt = λ { (vΩ V u , ()) }
  ; cpt-lgl = λ { (vΩ V u , ()) }
  ; zero-row = λ m V x → refl
  ; suc-row = λ m V x a → refl
  ; lim-row = λ m V x f → refl
  ; node-row = λ m V x r g → refl
  ; em-rowˢ = λ { m (vs V , cs c) x a → refl }
  ; em-rowˡ = λ { m (vl V st , cl c) x n a → refl }
  ; em-rowᶜ = λ { m (vΩ V u , ()) }
  ; top-row⁰ = λ { m (v0 , c0) x → refl }
  ; top-rowˢ = λ { m (vs V , cs c) x → refl }
  ; top-rowˡ = λ { m (vl V st , cl c) x → refl }
  ; top-rowᶜ = λ { m (vΩ V u , ()) }
  ; cpt-zero = λ { (vΩ V u , ()) }
  ; cpt-suc = λ { (vΩ V u , ()) }
  ; Ψ-lgl = λ m V → Ψ-lgl m (proj₁ V)
  ; Ψ-cp = λ m V → Ψ-cp m (proj₁ V)
  ; Kb-br = λ { m (vΩ V u , ()) }
  ; top-up = λ { m (vΩ V u , ()) }
  }
```

## 2 读回域

```agda
lv-cn : ∀ η l → Cn (lv η l)
lv-cn G.zero l = c0
lv-cn (G.suc a) l = cs (lv-cn a l)
lv-cn (G.lim f) (st , lf) = cl {f = λ n → ⌜ f n ⌝} (λ n → lv-cn (f n) (lf n))
lv-cn G.top l = cs c0

lvC : ∀ η → Lgl zero η → Bc ⌜ η ⌝
lvC η l = lv η l , lv-cn η l

dom₁ : DomTo Cnt 1
dom₁ = (v0 , c0) , (vs v0 , cs c0)

no-lc : ∀ {k g} → Bc (lc k g) → ⊥
no-lc (vΩ V u , ())

no-tw2 : Bc (tw 2) → ⊥
no-tw2 = no-lc
```
