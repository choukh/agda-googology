# 带码规范树族上的换基
候选；Read 保存 Ω 树族及加法、后继、部分和极限，source 在原地板解释，fold 在目标地板解释后折叠。
编译定理：上述构造合法，逐地板第一位置关系经 fold 保持；Ω 行与 seen 定义性相等。
内核用 YiRBSib 的无证据折叠；没有从任意原树恢复 Read 码的函数，也没有实际链上的带码闭包定理。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBSRead where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
import OCF.Lean.YiRBSib as R
open import OCF.Lean.YiBSBase

data Read : Set where
  omega : Read
  next : Read → Read
  plus : Read → Read → Read
  limit : (ℕ → Read) → Read

read : (ℓ : L) → Read → Tr⁺ ℓ
read ℓ omega = Ωt ℓ
read ℓ (next d) = next⁺ (read ℓ d)
read ℓ (plus d e) = proj₁ (read ℓ d) + proj₁ (read ℓ e) ,
  ◃t (proj₂ (read ℓ d)) (+-mono _ (proj₂ (read ℓ e)))
read ℓ (limit f) = limc⁺ (λ n → read ℓ (f n))

source : ∀ {k h} (S : Schema k h) c → Read → Tr⁺ (h c)
source S c d = subst Tr⁺ (sym (shape S c)) (read (floor S ⊕ offsets S c) d)
Domain : ∀ {k h} (S : Schema k h) c → Tr (h c) → Set
Domain S c y = Σ Read λ d → y ≡ proj₁ (source S c d)
omega-in : ∀ {k h} (S : Schema k h) c → Domain S c (proj₁ (source S c omega))
omega-in S c = omega , refl

fold : ∀ {k h} (S : Schema k h) c → Read → (j : L) → Ok j → floor S ≤ j → Tr⁺ j → Tr⁺ j
fold S c d j oj u β = R.ψ (j ⊕ offsets S c)
  (Ok⊕ j (offsets S c) oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c)))
  (R.rb-no _) (B₀ _) j (lift j (offsets S c)) β (proj₁ (read (j ⊕ offsets S c) d))

omega-row : ∀ {k h} (S : Schema k h) c j oj u β → fold S c omega j oj u β ≡ seen S j oj u β c
omega-row S c j oj u β = refl

PointStep : Read → Read → Set
PointStep d e = (ℓ : L) → ℓ ⊢ proj₁ (read ℓ d) ◃ proj₁ (read ℓ e)
next-step : ∀ d → PointStep d (next d)
next-step d ℓ = ◃l zero
plus-step : ∀ d e → PointStep d (plus d e)
plus-step d e ℓ = +-mono (proj₁ (read ℓ d)) (proj₂ (read ℓ e))
fold-step : ∀ {k h} (S : Schema k h) c d e j oj u β → PointStep d e
  → j ⊢ proj₁ (fold S c d j oj u β) ◃ proj₁ (fold S c e j oj u β)
fold-step S c d e j oj u β step = R.mono (j ⊕ offsets S c)
  (Ok⊕ j (offsets S c) oj (raiseO (floor S) j (offsets S c) u (ok-offsets S c)))
  (R.rb-no _) (B₀ _) j (lift j (offsets S c)) β (step (j ⊕ offsets S c))
```
