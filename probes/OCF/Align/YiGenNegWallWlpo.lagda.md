# YiGenNeg 第 4 项 (续)：在函数外延下是 WLPO (条件)

**判决：条件定理，前提是第 0 层的值的序列上的函数外延 `FunextR`。** [YiGenNegWall](YiGenNegWall.lagda.md) 的弱判定 `WeakEq` 加上 `FunextR` 推出 WLPO；
合起来：第 2 个链点上问到的对上 `Honest` 成立 (保留行取最弱的联系)，则 WLPO (`honest→wlpo`)。没有这个前提时只有 `WeakEq`，它推出什么没有判定。
机制与 `YiOmNegBranchFixed.fixed→wlpo` 相同 (极限层号的字面相等)；不同的是这里的目标与探针都在链问到的对里。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiGenNegWallWlpo where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false; _∨_)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1)
open import OCF.Align.YiIrrIf using (R; one; _+ʳ_; read0)
open import OCF.Align.YiIrrNegWide using (seen; flag)
open import OCF.Align.YiLvNegCum using (psum)
open import OCF.Align.YiLvFoldAdd using (plus)
open import OCF.Align.YiRawNegOmega using (WLPO)
open import OCF.Align.YiOmNegBranchFixed using (FunextR; seen-false)
open import OCF.Align.YiOmFoldBase using (RΩ)
open import OCF.Align.YiOmFoldNorm using (nrm)
open import OCF.Align.YiOmFoldChain using (pointsᴺ)
open import OCF.Align.YiGenIf using (OwnFold; Honest)
open import OCF.Align.YiGenNegShape using (B₁; B₂)
open import OCF.Align.YiGenNegAsk using (module Asked; LeftOne)
open import OCF.Align.YiGenNegLeft using (Rows)
open import OCF.Align.YiGenNegWall

false→eq : FunextR → ∀ α → (∀ n → α n ≡ false) → Eqᴸ α
false→eq fe α h =
  cong (λ W → read0 (G.lim (psum W)))
    (fe (Uᶜ α) (λ _ → one) (λ m → cong (λ b → nrm (one +ʳ flag b)) (seen-false α h m)))

weak-eq→wlpo : FunextR → WeakEq → WLPO
weak-eq→wlpo fe w α with w α
... | inj₁ no = inj₂ (λ h → no (false→eq fe α h))
... | inj₂ nn = inj₁ (λ n → not-true′ (α n) (λ p → nn (λ e → absurd (eq→false α e n) p)))
  where
  absurd : ∀ {b} → b ≡ false → b ≡ true → ⊥
  absurd refl ()
  not-true′ : ∀ b → (b ≡ true → ⊥) → b ≡ false
  not-true′ false no = refl
  not-true′ true no with no refl
  ... | ()

row→wlpo : FunextR → KeepRowAt r* (λ η e → B₁ η) → WLPO
row→wlpo fe K = weak-eq→wlpo fe (row→weak-eq K)

honest→wlpo : FunextR →
  (Out : RΩ → R → Set) (y : R) → Out (B₂ one) y → LeftOne y → Gd zero raw1 (plus zero one y) →
  (F : ∀ q → OwnFold q) →
  (∀ {q ξ} → Asked.Ask (pointsᴺ 2) Out q ξ → Honest q (F q) ξ) → WLPO
honest→wlpo fe Out y out ly e₁ F hon =
  row→wlpo fe (FromHonest.honest→row Out y out ly e₁ F hon)

chain→wlpo : FunextR → (Out : RΩ → R → Set) → Rows Out →
  (y : R) → Out (B₂ one) y → Gd zero raw1 (plus zero one y) →
  (F : ∀ q → OwnFold q) →
  (∀ {q ξ} → Asked.Ask (pointsᴺ 2) Out q ξ → Honest q (F q) ξ) → WLPO
chain→wlpo fe Out H y out e₁ F hon =
  weak-eq→wlpo fe (chain→weak-eq Out H y out e₁ F hon)
```
