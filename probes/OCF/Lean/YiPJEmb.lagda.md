# 任意有限路径的嵌入与槽位
验收文件；编译定理。两端层号带等式，沿实际路径归纳给出 emb 的关系保持与 psh 的层号、分支关系保持。
self 用 YiPJPoint/Case 的有限端点换型；inc/inu 直接递归，不要求路径等于 Sb。
来源：YiHCBridge.embB/slotPsh 的效果，改对任意实际路径陈述；不改定义。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPJEmb where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiCLFam using (fn)
open import OCF.Lean.YiHCBridge using (MB; LwB)
open import OCF.Lean.YiHCRel using (mz; mU)
open import OCF.Lean.YiPJCase using (unique; levB)
open import OCF.Lean.YiPJPoint using (change; index-eq)
import OCF.Align.EboLeanDef as E

liftM : ∀ B (ℓ′ : L) (e′ : ℓ′ ≡ fn B) A (ℓ : L) (e : ℓ ≡ fn A) (o : Ok ℓ′) (u : ℓ ≤ ℓ′)
      → (y : Tr ℓ) (ey : ℓ ⊢ zero ◃ y) → ∀ {a} → MB ℓ e a y
      → MB ℓ′ e′ a (proj₁ (emb ℓ′ o u (y , ey)))
liftM B ℓ′ e′ A .ℓ′ e o self y ey m = change A B (index-eq A B ℓ′ e e′) ℓ′ e e′ m
liftM zero (nd s h) () A ℓ e o u y ey m
liftM (suc B) (nd sL h) () A ℓ e o u y ey m
liftM (suc B) (nd (sΩ k) h) () A ℓ e o u y ey m
liftM (suc B) _ refl A ℓ e o (inc tt u) y ey m = mU mz (liftM B _ refl A ℓ e (proj₂ o tt) u y ey m)
liftM (suc B) _ refl A ℓ e o (inu us) y ey m = mU mz (liftM B _ refl A ℓ e (proj₂ o tt) (us tt) y ey m)

Slot : ∀ A (ℓ : L) → ℓ ≡ fn A → ∀ B (ℓ′ : L) → ℓ′ ≡ fn B → ℓ ≤ ℓ′ → Pos⁼ ℓ → Set
Slot A ℓ e B ℓ′ e′ u t = (levB B ℓ′ e′ (psh u t) ≡ levB A ℓ e t) ×
  (∀ η c → LwB ℓ′ e′ (psh u t) η c → LwB ℓ e t η (pshBr u t c))

selfSlot : ∀ A ℓ (e : ℓ ≡ fn A) B (e′ : ℓ ≡ fn B) t → Slot A ℓ e B ℓ e′ self t
selfSlot A ℓ e B e′ t = subst (λ q → Slot A ℓ e (proj₁ q) ℓ (proj₂ q) self t)
  (unique ℓ (A , e) (B , e′)) (refl , λ η c l → l)

slotJ : ∀ B ℓ′ (e′ : ℓ′ ≡ fn B) A ℓ (e : ℓ ≡ fn A) (u : ℓ ≤ ℓ′) t → Slot A ℓ e B ℓ′ e′ u t
slotJ B ℓ′ e′ A .ℓ′ e self t = selfSlot A ℓ′ e B e′ t
slotJ zero (nd s h) () A ℓ e u t
slotJ (suc B) (nd sL h) () A ℓ e u t
slotJ (suc B) (nd (sΩ k) h) () A ℓ e u t
slotJ (suc B) _ refl A ℓ e (inc tt u) t = slotJ B _ refl A ℓ e u t
slotJ (suc B) _ refl A ℓ e (inu us) t = slotJ B _ refl A ℓ e (us tt) t
```
