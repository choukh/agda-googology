# YiXVFiniteVia
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteVia where
open import Data.Product using (Σ; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I

literal : ∀ {a b} → I.Finite a → a L.≅ᴵ b → a ≡ b
literal I.fz L.z≅ = refl
literal (I.fs ga) (L.s≅ e) = cong L.suc (literal ga e)

exact : ∀ {a b} → I.Finite a → (v : a L.≺ᴵ b) → Σ (a L.<ᴵ b) (λ q → L.via (L.≅ᴵ-refl a) q ≡ v)
exact {a} ga (L.via e q) with literal ga e
... | refl rewrite I.eq-uniqueᶠ ga ga e (L.≅ᴵ-refl a) = q , refl

strict-both : ∀ {a b} → a L.≺ᴵ b → b L.≺ᴵ a → ⊥
strict-both p q = L.≺ᴵ-irrefl (L.≺ᴵ-trans p q)
strict-equal : ∀ {a b} → a L.≺ᴵ b → a L.≅ᴵ b → ⊥
strict-equal p e = L.≺ᴵ-irrefl (L.≺ᴵ-respʳ p (L.≅ᴵ-sym e))
```
