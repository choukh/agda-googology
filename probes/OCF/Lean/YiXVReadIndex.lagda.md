# YiXVReadIndex
> 验收文件。档位：编译定理。实际零层源树的每个源位置给源前驱、原 lvl 字面界与分支输入双向转换。
> 复用原 h₁/lvl 与 YiXVLvlLiteral，源模拟从 YiXVSourceFamily/Basics 推广；未交一般源世界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadIndex where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.Level as L
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLSTw1 as T
import OCF.Lean.YiXVLvlLiteral as Lit
ℓ : S.Tr S.zero → S.L
ℓ = T.h₁
slot : ∀ x → S.Pos (ℓ x) → S.Tr S.zero
slot S.zero ()
slot (S.suc x) (inj₁ t) = x
slot (S.suc x) (inj₂ p) = slot x p
slot (S.lim f a) (n , inj₁ t) = f n
slot (S.lim f a) (n , inj₂ p) = slot (f n) p
slot (S.Ω () g) p
slot (S.up x () y e) p
below : ∀ x (p : S.Pos (ℓ x)) → S.zero S.⊢ slot x p ◃ x
below S.zero ()
below (S.suc x) (inj₁ t) = S.◃s
below (S.suc x) (inj₂ p) = S.◃t (below x p) S.◃s
below (S.lim f a) (n , inj₁ t) = S.◃l n
below (S.lim f a) (n , inj₂ p) = S.◃t (below (f n) p) (S.◃l n)
below (S.Ω () g) p
below (S.up x () y e) p
q : ∀ x (p : S.Pos (ℓ x)) → T.lvl (slot x p) L.<ᴵ T.lvl x
q x p = Lit.step (below x p)
inB : ∀ x (p : S.Pos (ℓ x)) → S.Tr (ℓ (slot x p)) → S.Br (ℓ x) p
inB S.zero ()
inB (S.suc x) (inj₁ t) X = X
inB (S.suc x) (inj₂ p) X = inB x p X
inB (S.lim f a) (n , inj₁ t) X = X
inB (S.lim f a) (n , inj₂ p) X = inB (f n) p X
inB (S.Ω () g) p X
inB (S.up x () y e) p X
outB : ∀ x (p : S.Pos (ℓ x)) → S.Br (ℓ x) p → S.Tr (ℓ (slot x p))
outB S.zero ()
outB (S.suc x) (inj₁ t) X = X
outB (S.suc x) (inj₂ p) X = outB x p X
outB (S.lim f a) (n , inj₁ t) X = X
outB (S.lim f a) (n , inj₂ p) X = outB (f n) p X
outB (S.Ω () g) p X
outB (S.up x () y e) p X
out-in : ∀ x p X → outB x p (inB x p X) ≡ X
out-in S.zero ()
out-in (S.suc x) (inj₁ t) X = refl
out-in (S.suc x) (inj₂ p) X = out-in x p X
out-in (S.lim f a) (n , inj₁ t) X = refl
out-in (S.lim f a) (n , inj₂ p) X = out-in (f n) p X
out-in (S.Ω () g) p X
out-in (S.up x () y e) p X
in-out : ∀ x p X → inB x p (outB x p X) ≡ X
in-out S.zero ()
in-out (S.suc x) (inj₁ t) X = refl
in-out (S.suc x) (inj₂ p) X = in-out x p X
in-out (S.lim f a) (n , inj₁ t) X = refl
in-out (S.lim f a) (n , inj₂ p) X = in-out (f n) p X
in-out (S.Ω () g) p X
in-out (S.up x () y e) p X

child-slot : ∀ x → S.Ch (ℓ x) → S.Pos (ℓ x)
child-slot S.zero ()
child-slot (S.suc x) c = inj₁ tt
child-slot (S.lim f a) n = n , inj₁ tt
child-slot (S.Ω () g) c
child-slot (S.up x () y e) c
ctoB : ∀ x (c : S.Ch (ℓ x)) → S.ChT (ℓ x) c → S.Br (ℓ x) (child-slot x c)
ctoB S.zero ()
ctoB (S.suc x) c X = X
ctoB (S.lim f a) n X = X
ctoB (S.Ω () g) c X
ctoB (S.up x () y e) c X
btoC : ∀ x (c : S.Ch (ℓ x)) → S.Br (ℓ x) (child-slot x c) → S.ChT (ℓ x) c
btoC S.zero ()
btoC (S.suc x) c X = X
btoC (S.lim f a) n X = X
btoC (S.Ω () g) c X
btoC (S.up x () y e) c X
σchild : ∀ x (c : S.Ch (ℓ x)) → L.Simᴵ (T.lvl (slot x (child-slot x c))) (T.lvl x)
σchild x c r = L.<ᴵ-trans r (q x (child-slot x c))
```
