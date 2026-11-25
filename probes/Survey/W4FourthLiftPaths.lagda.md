# 所有有限后继层的零路径换路

第四层，无条件。相同底与起点在有限后继层上改走任一零路径，所得零层树逐枝等形。每次进入后继层的孩子，两种路径都落到该层唯一的孩子。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FourthLiftPaths where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.Unit.Base using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import W4Block hiding (R)
open import W4Ops
open import W4Path
open import W4Fold
import B19PathShape as S
import B19PathRel as Rel
open Rel.Test S.law

level : ℕ → L
level zero = zero
level (suc n) = nd sS (λ _ → level n)

peel : ∀ {j} → zero ≤ nd sS (λ _ → j) → zero ≤ j
peel (inc tt w) = w
peel (inu ws) = ws tt

-- 除了 up，换路只改变当前零观察，Ω 对角的正层输入完全共用。
form : ∀ n (o : Ok (level n)) (B : Base (level n)) (w : zero ≤ level n)
       (a : Tr⁺ zero) (x : Tr (level n)) → Tr⁺ zero
form n o B w a zero = a
form n o B w a (suc x) = next⁺ (ψ (level n) o B zero w a x)
form n o B w a (lim f h) = lim⁺ (λ i → ψ (level n) o B zero w a (f i)) (λ i → mono (level n) o B zero w a (h i))
form n o B w a (Ω p g) = node⁺ (kp (level n) o p w) (λ z → ψ (level n) o B zero w a (g z))
  (λ z → fromBr (level n) p (proj₁ (ψ (level n) o B (at (level n) p) (posW (level n) p) (B (at (level n) p) (posW (level n) p)) (g z))))
form zero o B w a (up x () y d)
form (suc n) o B w a (up x tt y d) = ψ (level n) (proj₂ o tt)
  (λ i u → ψ (level (suc n)) o B i (inc tt u) (B i (inc tt u)) x) zero (peel w) (ψ (level (suc n)) o B zero w a x) y
form n o B w a (ex x k nk y e) = E o tdNil y (opB (level n) o k nk)
  (λ i u → ψ (level n) o B i u (B i u) x) zero w (ψ (level n) o B zero w a x)

unfold : ∀ n (o : Ok (level n)) B w a x → ψ (level n) o B zero w a x ≡ form n o B w a x
unfold n o B w a zero = refl
unfold zero o B self a (suc x) = refl
unfold zero o B self a (lim f d) = refl
unfold zero o B self a (Ω () g)
unfold zero o B self a (up x () y d)
unfold zero o B self a (ex x k nk y ())
unfold (suc n) o B (inc tt w) a (suc x) = refl
unfold (suc n) o B (inu ws) a (suc x) = refl
unfold (suc n) o B (inc tt w) a (lim f d) = refl
unfold (suc n) o B (inu ws) a (lim f d) = refl
unfold (suc n) o B (inc tt w) a (Ω p g) = refl
unfold (suc n) o B (inu ws) a (Ω p g) = refl
unfold (suc n) o B (inc tt w) a (up x tt y d) = refl
unfold (suc n) o B (inu ws) a (up x tt y d) = refl
unfold (suc n) o B (inc tt w) a (ex x k nk y e) = refl
unfold (suc n) o B (inu ws) a (ex x k nk y e) = refl

any-port : ∀ {k} → Rel.Ports (nil {k})
any-port _ _ = ⊤

pair : ∀ n (o : Ok (level n)) B w v (x : Tr (level n)) a b →
  a ∼ b → ψ (level n) o B zero w a x ∼ ψ (level n) o B zero v b x
pair n o B w v zero a b h = h
pair n o B w v e@(suc x) a b h rewrite unfold n o B w a e | unfold n o B v b e =
  next {a = ψ (level n) o B zero w a x} {b = ψ (level n) o B zero v b x} (pair n o B w v x a b h)
pair n o B w v e@(lim f d) a b h rewrite unfold n o B w a e | unfold n o B v b e =
  S.l (λ i → pair n o B w v (f i) a b h)
pair n o B w v e@(Ω p g) a b h rewrite unfold n o B w a e | unfold n o B v b e =
  node (kp (level n) o p w) (kp (level n) o p v) _ _
    (λ z → fromBr (level n) p (proj₁ (ψ (level n) o B (at (level n) p) (posW (level n) p) (B (at (level n) p) (posW (level n) p)) (g z))))
    (λ z → pair n o B w v (g z) a b h)
pair zero o B w v (up x () y d) a b h
pair (suc n) o B w v e@(up x tt y d) a b h rewrite unfold (suc n) o B w a e | unfold (suc n) o B v b e =
  pair n (proj₂ o tt) (λ i u → ψ (level (suc n)) o B i (inc tt u) (B i (inc tt u)) x)
    (peel w) (peel v) y _ _ (pair (suc n) o B w v x a b h)
pair n o B w v e@(ex x k nk y ok) a b h rewrite unfold n o B w a e | unfold n o B v b e =
  eval any-port o tdNil y (opB (level n) o k nk)
    (λ base p q _ u u′ hu → pair n o base p q k u u′ hu)
    (λ i t → ψ (level n) o B i t (B i t) x) w v tt _ _ (pair n o B w v x a b h)

change : ∀ n (o : Ok (level n)) B w v a x →
  S.Shape (proj₁ (ψ (level n) o B zero w a x)) (proj₁ (ψ (level n) o B zero v a x))
change n o B w v a x = pair n o B w v x a a (S.ident (proj₁ a))
```
