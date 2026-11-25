# YiXVReadThin
> 验收文件。档位：编译定理。同一实际树上界内，互相读回值比较的两个路径对象字面相等。
> 从 YiXVSource*、YiCeilRead 与原 Level 的递归推广；未交节点行、外层 n≥2 读回界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVReadThin where
open import Data.Nat using (ℕ; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (module Trich; injᵃ; injᵇ; injᶜ)
import OCF.Lean.YiLegBlock as S
import OCF.Lean.YiLSRead as Read
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; ≺→s≼)
open import OCF.Align.RR4MonoFragment using (irr)
import OCF.Lean.YiXVReadPaths as P
import OCF.Lean.YiXVReadOmegaInput as Ω

first : S.zero P.≤ᵀ Ω.ω
first = P.below (P.branch 0)
second : S.zero P.≤ᵀ Ω.ω
second = P.below (P.under-lim 1 P.root)
same-read : Read.read S.zero ≼ Read.read S.zero
same-read = ≼-refl L.zero

bad : ∀ {x y} → x P.≺ᵀ y → Read.read y ≼ Read.read x → ⊥
bad {x} p h = irr (Read.read x) (≼-trans (≺→s≼ (Read.◃→≺ (P.raw p))) h)
suc-down : ∀ {x y} → x P.≺ᵀ S.suc y → x P.≤ᵀ y
suc-down P.root = P.here
suc-down (P.under-suc p) = P.below p
split : ∀ {x : S.Tr S.zero} {f : ℕ → S.Tr S.zero}
  {d : ∀ n → S.zero S.⊢ f n ◃ f (suc n)} → x P.≺ᵀ S.lim f d → Σ ℕ (λ n → x P.≤ᵀ f n)
split (P.branch n) = n , P.here
split (P.under-lim n p) = n , P.below p
steps : ∀ {f : ℕ → S.Tr S.zero} (d : ∀ n → S.zero S.⊢ f n ◃ f (suc n))
  {n m} → n Trich.< m → f n P.≺ᵀ f m
steps d Trich.zero = P.normal (d _)
steps d (Trich.suc p) = P.trans (steps d p) (P.normal (d _))

thin : ∀ root {x y} → x P.≤ᵀ root → y P.≤ᵀ root →
  Read.read x ≼ Read.read y → Read.read y ≼ Read.read x → x ≡ y
thin root P.here P.here xy yx = refl
thin root P.here (P.below q) xy yx = ⊥-elim (bad q xy)
thin root (P.below p) P.here xy yx = ⊥-elim (bad p yx)
thin S.zero (P.below ()) q xy yx
thin (S.suc r) (P.below p) (P.below q) xy yx = thin r (suc-down p) (suc-down q) xy yx
thin (S.lim f d) (P.below p) (P.below q) xy yx with split p | split q
... | n , pn | m , qm with Trich.<-dec n m
... | injᵃ lt = thin (f m) (P.below (P.advance pn (steps d lt))) qm xy yx
... | injᵇ lt = thin (f n) pn (P.below (P.advance qm (steps d lt))) xy yx
... | injᶜ refl = thin (f n) pn qm xy yx
thin (S.Ω () g) p q xy yx
thin (S.up r () b nb) p q xy yx

actual : S.zero ≡ S.zero
actual = thin Ω.ω first second same-read same-read
```
