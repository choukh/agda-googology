# 实际首底内链覆盖完整纯幂塔

不改变方格闭项。纯源比较对所有实际 PH 证书及 GT 种子量化，
不要求两份路径证明相等，也不使用原 ΦX 的一般单调性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GridBaseTowerCore where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdTw using (Ix; FX; gtX)
open import OCF.Lean.ThirdPS using (PH)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; l≤; ≤l; mul)
open import OCF.Lean.NegFold1Base using (≤ᵛ-refl; ≤ᵛ-trans; ⊞≤ˡ; ⊞≤ʳ)
open import OCF.Lean.OutputDrivenValue using (right)
open import OCF.Align.FrozenAbsorbNegUpper using (P; mono)
import OCF.Align.GridBaseFirst as First
import OCF.Align.BoundedCompletionCalibrateTower as Tower
import OCF.Lean.GridValueBase as Base
import OCF.Lean.OutputDrivenGrid as Grid

module X = First.X
module F = First.F
one two : Cd
one = hs hz
two = hs one

source : Cd → HB (OCF.Lean.ThirdTw.XSof S⊥)
source a = hz ⊞ ι {Ix S⊥} {FX S⊥} (inj₂ hz) (up a)

run : (b : F.GT hz) (a : Cd) → PH X.PSX two (source a) → F.GT hz
run b a p = X.ΦX hz two tt (hsuc (hsuc hself)) b (source a) p

mul-cover : ∀ a (x : F.GT hz) → a ≤ᵛ proj₁ x → ∀ n → mul a n ≤ᵛ proj₁ (F.mulG x n)
mul-cover a x p zero = p
mul-cover a x p (suc n) = ≤ᵛ-trans (⊞≤ˡ a (mul-cover a x p n))
  (⊞≤ʳ (proj₁ (F.mulG x n)) p)

in-sum : ∀ (f : ℕ → F.GT hz) n → proj₁ (f n) ≤ᵛ proj₁ (F.ΣG f n)
in-sum f zero = ≤ᵛ-refl _
in-sum f (suc n) = right (proj₁ (F.ΣG f n)) (proj₁ (f (suc n)))

pure-cover : ∀ b a (p : PH X.PSX two (source a)) → P one a ≤ᵛ proj₁ (run b a p)
pure-cover b hz p = ≤ᵛ-refl one
pure-cover b (hs a) p = l≤ (λ n → ≤l n (mul-cover (P one a) (run b a p) (pure-cover b a p) n))
pure-cover b (hl f) p = l≤ (λ n → ≤l n
  (≤ᵛ-trans (pure-cover b (f n) (p n)) (in-sum (λ n → run b (f n) (p n)) n)))
pure-cover b (hΩ () _) p

root-path : PH X.PSX two (gtX S⊥ hz one)
root-path = proj₂ (First.D.own-path zero one hself) one (X.aS hz tt)

callback : F.GT hz → F.GT hz
callback b = run b (proj₁ b) (proj₂ root-path (proj₁ b) (proj₂ b))

inner : Cd
inner = proj₁ (F.limG (F.chainG (hz , tt) callback))

actual-inner : proj₁ (First.H (hz , tt)) ≡ inner
actual-inner = refl

inner-in-first : inner ≤ᵛ First.first
inner-in-first = ≤l zero (≤ᵛ-refl inner)

callback-cover : ∀ b → P one (proj₁ b) ≤ᵛ proj₁ (callback b)
callback-cover b = pure-cover b (proj₁ b) (proj₂ root-path (proj₁ b) (proj₂ b))

coordinates : ∀ n → Tower.tower n ≤ᵛ proj₁ (F.chainG (hz , tt) callback n)
coordinates zero = callback-cover (hz , tt)
coordinates (suc n) = ≤ᵛ-trans
  (mono (≤ᵛ-refl one) (≤ᵛ-trans (coordinates n) (right hz (proj₁ (F.chainG (hz , tt) callback n)))))
  (≤ᵛ-trans (callback-cover _)
    (right (proj₁ (F.chainG (hz , tt) callback n)) _))

tower-in-first : Tower.tower-limit ≤ᵛ First.first
tower-in-first = ≤ᵛ-trans (l≤ (λ n → ≤l n (coordinates n))) inner-in-first

tower-in-grid : Tower.tower-limit ≤ᵛ Grid.closedGrid
tower-in-grid = ≤ᵛ-trans tower-in-first Base.base-in-grid
```
