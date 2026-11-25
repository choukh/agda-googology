# YiXVFiniteBasics
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteBasics where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Fin as F
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-refl; ≼-trans; ≼-suc; z≼; s≼s; ≼l; l≼)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
open A using (GoFam; LeFam; Gd; Le)

good-stable : ∀ n i X → GoFam n i X ≡ Gd (I.rank n i) X
good-stable zero F.zero X = refl
good-stable zero (F.suc ()) X
good-stable (suc n) F.zero X = refl
good-stable (suc n) (F.suc i) X = good-stable n i X
le-stable : ∀ n i X Y → LeFam n i X Y ≡ Le (I.rank n i) X Y
le-stable zero F.zero X Y = refl
le-stable zero (F.suc ()) X Y
le-stable (suc n) F.zero X Y = refl
le-stable (suc n) (F.suc i) X Y = le-stable n i X Y

gz : ∀ n i → GoFam n i L.zero
gz zero F.zero = tt
gz zero (F.suc ())
gz (suc n) F.zero = A.Layer.gz
gz (suc n) (F.suc i) = gz n i
gs : ∀ n i {X} → GoFam n i X → GoFam n i (L.suc X)
gs zero F.zero gx = tt
gs zero (F.suc ()) gx
gs (suc n) F.zero gx = A.Layer.gs gx
gs (suc n) (F.suc i) gx = gs n i gx
gl : ∀ n i {a : ℕ → I.T (I.rank n i)} → (∀ k → GoFam n i (a k)) → GoFam n i (L.lim a)
gl zero F.zero ga = tt
gl zero (F.suc ()) ga
gl (suc n) F.zero ga = A.Layer.gl ga
gl (suc n) (F.suc i) ga = gl n i ga

left : ∀ n i {X Y} → LeFam n i X Y → GoFam n i X
left zero F.zero p = tt
left zero (F.suc ()) p
left (suc n) F.zero p = A.Layer.left n (GoFam n) (LeFam n) p
left (suc n) (F.suc i) p = left n i p
right : ∀ n i {X Y} → LeFam n i X Y → GoFam n i Y
right zero F.zero p = tt
right zero (F.suc ()) p
right (suc n) F.zero p = A.Layer.right n (GoFam n) (LeFam n) p
right (suc n) (F.suc i) p = right n i p
rfl : ∀ n i {X} → GoFam n i X → LeFam n i X X
rfl zero F.zero {X} gx = ≼-refl X
rfl zero (F.suc ()) gx
rfl (suc n) F.zero gx = A.Layer.refl n (GoFam n) (LeFam n) gx
rfl (suc n) (F.suc i) gx = rfl n i gx
trans : ∀ n i {X Y Z} → LeFam n i X Y → LeFam n i Y Z → LeFam n i X Z
trans zero F.zero p q = ≼-trans p q
trans zero (F.suc ()) p q
trans (suc n) F.zero p q = A.Layer.trans n (GoFam n) (LeFam n) p q
trans (suc n) (F.suc i) p q = trans n i p q
z≤ : ∀ n i {Y} → GoFam n i Y → LeFam n i L.zero Y
z≤ zero F.zero gy = z≼
z≤ zero (F.suc ()) gy
z≤ (suc n) F.zero gy = A.Layer.z≤ n (GoFam n) (LeFam n) gy
z≤ (suc n) (F.suc i) gy = z≤ n i gy
s≤ : ∀ n i {X Y} → LeFam n i X Y → LeFam n i (L.suc X) (L.suc Y)
s≤ zero F.zero p = s≼s p
s≤ zero (F.suc ()) p
s≤ (suc n) F.zero p = A.Layer.s≤ n (GoFam n) (LeFam n) p
s≤ (suc n) (F.suc i) p = s≤ n i p
w≤ : ∀ n i {X Y} → LeFam n i X Y → LeFam n i X (L.suc Y)
w≤ zero F.zero p = ≼-suc p
w≤ zero (F.suc ()) p
w≤ (suc n) F.zero p = A.Layer.pack (A.Layer.left n (GoFam n) (LeFam n) p) (A.Layer.gs (A.Layer.right n (GoFam n) (LeFam n) p)) (A.Layer.ws p)
w≤ (suc n) (F.suc i) p = w≤ n i p

ll : ∀ n i {a : ℕ → I.T (I.rank n i)} {Y} → (∀ k → GoFam n i (a k)) → GoFam n i Y →
  (∀ k → LeFam n i (a k) Y) → LeFam n i (L.lim a) Y
ll zero F.zero ga gy h = l≼ h
ll zero (F.suc ()) ga gy h
ll (suc n) F.zero ga gy h = A.Layer.pack (A.Layer.gl ga) gy (A.Layer.ll h)
ll (suc n) (F.suc i) ga gy h = ll n i ga gy h
lr : ∀ n i {X} {a : ℕ → I.T (I.rank n i)} → GoFam n i X → (∀ k → GoFam n i (a k)) →
  (k : ℕ) → LeFam n i X (a k) → LeFam n i X (L.lim a)
lr zero F.zero gx ga k p = ≼l k p
lr zero (F.suc ()) gx ga k p
lr (suc n) F.zero gx ga k p = A.Layer.pack gx (A.Layer.gl ga) (A.Layer.lr k p)
lr (suc n) (F.suc i) gx ga k p = lr n i gx ga k p

Ω-model : ∀ n i → GoFam n i (L.Ω (L.natᴵ (I.rank n i))) × LeFam n i (L.suc L.zero) (L.Ω (L.natᴵ (I.rank n i)))
Ω-model zero F.zero = tt , s≼s z≼
Ω-model zero (F.suc ())
Ω-model (suc n) F.zero = node , D.pack (D.gs D.gz) node (D.aa one-up)
  where
  module D = A.Layer n (GoFam n) (LeFam n)
  one-up : D.Le D.one (L.up L.zero (L.Ω (L.natᴵ n)))
  one-up = D.trans (D.trans (D.s≤ (D.z≤ (D.gu (gz n F.zero)))) (D.upS≤ (gz n F.zero) (gs n F.zero (gz n F.zero))))
    (D.u≤ (gs n F.zero (gz n F.zero)) (proj₁ (Ω-model n F.zero)) (proj₂ (Ω-model n F.zero)))
  node : D.Gd (L.Ω (L.natᴵ (suc n)))
  node = D.gn (D.sc (λ u v gu gv o q → D.u≤ gu gv q)
    (λ u gu o → D.upS≤ gu (gs n F.zero gu)) one-up) (λ u gu o → D.gu gu)
Ω-model (suc n) (F.suc i) = Ω-model n i

actual : ∀ n → Gd n (L.Ω (L.natᴵ n))
actual n = proj₁ (Ω-model n F.zero)
```
