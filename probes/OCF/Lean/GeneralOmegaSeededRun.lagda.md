# 原种子无累加轨道的完整树值覆盖

证明对任意种类结构、任意地板参数成立，不按有限阶段复制。保留旧Ω
只作同kind的结构递归。高层值包含止于本篇的两棵typed树，不能穿过
另一个未证单调的折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaSeededRun where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l; ≤Ω; Ω≤Ω)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; ⊞-≤ˡ; ⊞-≤ʳ)
open import OCF.Lean.GeneralOmegaSeededIf

add-mono : ∀ {S} {a b c d : HB S} → a ≤ᵛ b → c ≤ᵛ d → (a ⊞ c) ≤ᵛ (b ⊞ d)
add-mono {b = b} p q = ≤-trans (⊞-≤ˡ p _) (⊞-≤ʳ b q)
right-add : ∀ {S} (a b : HB S) → b ≤ᵛ a ⊞ b
right-add a hz = z≤
right-add a (hs b) = s≤s (right-add a b)
right-add a (hl f) = l≤ (λ n → ≤l n (right-add a (f n)))
right-add a (hΩ κ g) = Ω≤Ω (λ e → right-add a (g e))

module Run (S : KS) (seed : HB S) where
  open Prototype S seed
  left-mono : ∀ {a b} → a ≤ᵛ b → ∀ n → leftMul a n ≤ᵛ leftMul b n
  left-mono p zero = z≤
  left-mono p (suc n) = add-mono p (left-mono p n)
  seed-lower : ∀ a → seed ≤ᵛ Typed a
  seed-lower hz = ≤-refl _
  seed-lower (hs a) = ≤l 1 (seed-lower a)
  seed-lower (hl f) = ≤l zero (seed-lower (f zero))
  seed-lower (hΩ κ g) = ≤Ω (bot S κ) (seed-lower (g (bot S κ)))
  typed-mono : ∀ {a b} → a ≤ᵛ b → Typed a ≤ᵛ Typed b
  typed-mono {b = b} z≤ = seed-lower b
  typed-mono (s≤s p) = l≤ (λ n → ≤l n (left-mono (typed-mono p) n))
  typed-mono (≤s p) = ≤l 1 (typed-mono p)
  typed-mono (l≤ p) = l≤ (λ n → typed-mono (p n))
  typed-mono (≤l n p) = ≤l n (typed-mono p)
  typed-mono (≤Ω e p) = ≤Ω e (typed-mono p)
  typed-mono (Ω≤Ω p) = Ω≤Ω (λ e → typed-mono (p e))

  position : ∀ {a b W} → a ⊲[ W ] b → Typed a ⊲[ W ] Typed b
  position hself = hself
  position (hsuc p) = hlim 1 (position p)
  position (hlim n p) = hlim n (position p)
  position (hLim e p) = hLim e (position p)
  left-step : ∀ a n {W} → leftMul a n ⊲[ W ] leftMul a (suc n)
  left-step a zero = z⊲ᴮ a
  left-step a (suc n) = ⊞-⊲ a (left-step a n)
  left-legal : ∀ a → LgB a → ∀ n → LgB (leftMul a n)
  left-legal a l zero = tt
  left-legal a l (suc n) = Lg-⊞ a _ l (left-legal a l n)
  typed-legal : LgB seed → ∀ a → LgB a → LgB (Typed a)
  typed-legal ls hz l = ls
  typed-legal ls (hs a) l = (λ n → left-step (Typed a) n) , left-legal (Typed a) (typed-legal ls a l)
  typed-legal ls (hl f) (st , l) = (λ n → position (st n)) , (λ n → typed-legal ls (f n) (l n))
  typed-legal ls (hΩ κ g) (mo , l) =
    (λ lw b b′ p → position (mo lw b b′ p)) ,
    (λ lw b → typed-legal ls _ (l lw b))

  noSum-step : ∀ n {W} → NoSum n ⊲[ W ] NoSum (suc n)
  noSum-step zero = position (z⊲ᴮ seed)
  noSum-step (suc n) = position (noSum-step n)
  sum-step : ∀ n {W} → Sum n ⊲[ W ] Sum (suc n)
  sum-step n = ⊞-fst (Sum n) (Typed (Sum n))
  noSum-legal : LgB seed → ∀ n → LgB (NoSum n)
  noSum-legal l zero = l
  noSum-legal l (suc n) = typed-legal l _ (noSum-legal l n)
  sum-legal : LgB seed → ∀ n → LgB (Sum n)
  sum-legal l zero = l
  sum-legal l (suc n) = Lg-⊞ _ _ (sum-legal l n) (typed-legal l _ (sum-legal l n))
  coordinates : ∀ n → NoSum n ≤ᵛ Sum n
  coordinates zero = ≤-refl _
  coordinates (suc n) = ≤-trans (typed-mono (coordinates n)) (right-add (Sum n) (Typed (Sum n)))
  whole-cover : whole ≤ᵛ accumulated
  whole-cover = l≤ (λ n → ≤l n (coordinates n))
  laws : Laws
  laws = record
    { noSum-legal = λ l → (λ n → noSum-step n) , noSum-legal l
    ; sum-legal = λ l → (λ n → sum-step n) , sum-legal l
    ; whole-cover = whole-cover ; noSum-step = noSum-step ; sum-step = sum-step }
```

coordinates覆盖全部n，whole-cover比较完整极限；不是只比较前几项。
NoSum与Sum初值都为原seed，全部位置律在原S的同一world内成立。
这里Typed的单调性由其明确树规则证明，不推广到GeneralOmega.run。
