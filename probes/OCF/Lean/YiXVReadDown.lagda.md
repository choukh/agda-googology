# YiXVReadDown
> 验收文件。档位：编译定理。实际孩子下降路径保留原 Dn、槽位的源对象与分支模拟。
> 从 YiXVSourceAffine*、ReadFamily 与原 Level 推广，参照侧重用 CountableFold/Retain；未交完整世界 up/node 输出、外层 n≥2 界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadDown where
open import Data.Nat using (ℕ; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLegOps as O
import OCF.Lean.YiLSTw1 as T
import OCF.Align.Level as L
open import OCF.Align.Value using (z≼)
import OCF.Lean.YiXVReadIndex as J
import OCF.Lean.YiXVReadFamily as U
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadCoordinates as C
import OCF.Lean.YiXVReadOmegaInput as Ω

data Down (top : S.Tr S.zero) : S.Tr S.zero → Set where
  here : Down top top
  down-suc : ∀ {r : S.Tr S.zero} → Down top (S.suc r) → Down top r
  down-lim : ∀ {f : ℕ → S.Tr S.zero} {d : ∀ n → S.zero S.⊢ f n ◃ f (suc n)} →
    Down top (S.lim f d) → (n : ℕ) → Down top (f n)
src : ∀ {top r} → Down top r → O.Dn (J.ℓ top) (J.ℓ r)
src here = O.stop
src (down-suc d) = O.down (src d) tt
src (down-lim d n) = O.down (src d) n
within : ∀ {top r} → Down top r → r P.≤ᵀ top
within here = P.here
within (down-suc d) = C.inside P.root (within d)
within (down-lim d n) = C.inside (P.branch n) (within d)
slot : ∀ {top r} (d : Down top r) (p : S.Pos (J.ℓ r)) →
  J.slot top (O.mv (src d) p) ≡ J.slot r p
slot here p = refl
slot (down-suc d) p = slot d (inj₂ p)
slot (down-lim d n) p = slot d (n , inj₂ p)
pull : ∀ {top r} (d : Down top r) (p : S.Pos (J.ℓ r))
  (a : S.Br (J.ℓ top) (O.mv (src d) p)) X →
  U.Fam top (O.mv (src d) p) a X → U.Fam r p (O.mvBr (src d) p a)
    (subst (λ x → L.Ordᶜ (T.lvl x)) (slot d p) X)
pull here p a X h = h
pull (down-suc d) p a X h = pull d (inj₂ p) a X h
pull (down-lim d n) p a X h = pull d (n , inj₂ p) a X h

model : Down Ω.ω (Ω.nat 2)
model = down-lim here 2
model-slot : J.slot Ω.ω (O.mv (src model) (inj₂ (inj₁ tt))) ≡ S.zero
model-slot = slot model (inj₂ (inj₁ tt))
actual : U.Fam (Ω.nat 2) (inj₂ (inj₁ tt)) S.zero (L.Ω L.zero)
actual = pull model (inj₂ (inj₁ tt)) S.zero (L.Ω L.zero) z≼
```
