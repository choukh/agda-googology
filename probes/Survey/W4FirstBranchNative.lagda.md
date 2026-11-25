# 实际 Ω₂ 对角第一次回灌的旧树下界

第四层。用 Ω₁ 观察两边的零槽和外部底，允许 W4 的真实正自槽沿合法位置超过 Ω₁。这样可以将旧 Ω₂ 对角的首次非零返回送入实际接受环境。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4FirstBranchNative where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit.Base using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; l≼; ≼l; s≼s; +-mono; ≅→≼)
import W4Block as W
import W4Ops as U
import W4Path as P
import W4Fold as F
import WVOne as R
import WVTwo as Two
import B8FreezeMain as Upper
import WKGen as G
import B12Terminal as T
import B12ActualSlots as Slots
import Survey.W4FiniteRaiseBridgePrefix as Old
import OCF.Lean.YiLSRead as V
import OCF.Lean.YiLegFold as OF
import OCF.Lean.YiLegBlock as O


j = R.lvl1
wk : W.zero W.≤ j
wk = W.inc tt W.self
Ω₁ = proj₁ (U.Ωt j)
read = R.read
rd : U.Tr⁺ W.zero → R.T₀
rd v = read (proj₁ v)

module ΩAt (o : P.Ok j) (D : F.Base j) where
  row = λ w v x → F.ψ j o D W.zero w v (R.g₁ x)
  cap : ∀ {w} → R.W1 w → ∀ v x → rd (row w v x) ≼ R.Mv (rd v) (L.suc (read x))
  cap R.wc v x = Upper.P-up {o₀ = proj₂ o tt} {Bs = λ i u → D i (W.inc tt u)} W.self v (W.suc x)
  cap R.wu v x = Upper.P-up {o₀ = proj₂ o tt} {Bs = λ i u → D i (W.inc tt u)} W.self v (W.suc x)

  idx = W.iter (R.s₁ o D) W.zero
  branch = λ w v k → proj₁ (row w v (idx k))
  output = λ w v → F.ψ j o D W.zero w v Ω₁

module Compare (o o′ : P.Ok j) (D D′ : F.Base j) (slot : rd (D W.zero wk) ≼ rd (D′ W.zero wk)) where
  module Src = ΩAt o D
  module Dst = ΩAt o′ D′

  step : ∀ {w w′} → R.W1 w → R.W1 w′ → ∀ v v′ x y → rd v ≼ rd v′ → read x ≼ read y →
         rd (Src.row w v x) ≼ rd (Dst.row w′ v′ y)
  step u u′ v v′ x y h k = ≼-trans {b = R.Mv (rd v) (L.suc (read x))} (Src.cap u v x)
    (≼-trans {b = R.Mv (rd v′) (L.suc (read y))} (R.Mv-mono h (s≼s k)) (R.G-row o′ D′ u′ v′ y))

  indices : ∀ k → read (Src.idx k) ≼ read (Dst.idx k)
  indices zero = ≼-refl _
  indices (suc k) = step R.wc R.wc _ _ _ _ slot (indices k)

  sums : ∀ {w w′} → R.W1 w → R.W1 w′ → ∀ v v′ → rd v ≼ rd v′ → ∀ k →
         read (U.cum (Src.branch w v) k) ≼ read (U.cum (Dst.branch w′ v′) k)
  sums u u′ v v′ h zero = step u u′ v v′ _ _ h (indices 0)
  sums {w} {w′} u u′ v v′ h (suc k) = ≼-trans (Upper.read-+′ (U.cum (Src.branch w v) k) (Src.branch w v (suc k)))
    (≼-trans (+-mono (sums u u′ v v′ h k) (step u u′ v v′ _ _ h (indices (suc k))))
      (R.read-+ (U.cum (Dst.branch w′ v′) k) (Dst.branch w′ v′ (suc k))))

  compare : ∀ {w w′} → R.W1 w → R.W1 w′ → ∀ v v′ → rd v ≼ rd v′ →
            rd (Src.output w v) ≼ rd (Dst.output w′ v′)
  compare R.wc R.wc v v′ h = l≼ λ k → ≼l k (sums R.wc R.wc v v′ h k)
  compare R.wc R.wu v v′ h = l≼ λ k → ≼l k (sums R.wc R.wu v v′ h k)
  compare R.wu R.wc v v′ h = l≼ λ k → ≼l k (sums R.wu R.wc v v′ h k)
  compare R.wu R.wu v v′ h = l≼ λ k → ≼l k (sums R.wu R.wu v v′ h k)

module Repeat (o o′ : P.Ok j) (seed : U.Tr⁺ j) (covers : Ω₁ Slots.⊴ proj₁ seed) where
  left  = F.opB j o Ω₁ (proj₂ (U.Ωt j))
  right = F.opB j o′ (proj₁ seed) (proj₂ seed)

  widen : ∀ D w v → rd (F.ψ j o′ D W.zero w v Ω₁) ≼ rd (F.run right D W.zero w v)
  widen D w v = extend covers
    where
    extend : ∀ {x} → Ω₁ Slots.⊴ x → rd (F.ψ j o′ D W.zero w v Ω₁) ≼ rd (F.ψ j o′ D W.zero w v x)
    extend (inj₁ refl) = ≼-refl _
    extend (inj₂ h) = Two.◃→≼ (F.mono j o′ D W.zero w v h)

  run : ∀ D D′ → rd (D W.zero wk) ≼ rd (D′ W.zero wk) → ∀ {w w′} → R.W1 w → R.W1 w′ →
        ∀ v v′ → rd v ≼ rd v′ → rd (F.run left D W.zero w v) ≼ rd (F.run right D′ W.zero w′ v′)
  run D D′ q u u′ v v′ h = ≼-trans (Compare.compare o o′ D D′ q u u′ v v′ h) (widen D′ _ v′)

  states : ∀ k D D′ → rd (D W.zero wk) ≼ rd (D′ W.zero wk) →
           rd (F.itS left k D W.zero wk) ≼ rd (F.itS right k D′ W.zero wk)
  states zero D D′ q = q
  states (suc k) D D′ q = run (F.itS left k D) (F.itS right k D′) (states k D D′ q)
    R.wc R.wc _ _ (states k D D′ q)

  values : ∀ k D D′ → rd (D W.zero wk) ≼ rd (D′ W.zero wk) → ∀ {w w′} → R.W1 w → R.W1 w′ →
           ∀ v v′ → rd v ≼ rd v′ → rd (F.itV left k D W.zero w v) ≼ rd (F.itV right k D′ W.zero w′ v′)
  values zero D D′ q u u′ v v′ h = h
  values (suc k) D D′ q u u′ v v′ h = run (F.itS left k D) (F.itS right k D′) (states k D D′ q)
    u u′ _ _ (values k D D′ q u u′ v v′ h)
```

```agda
o₁ : P.Ok j
o₁ = tt , λ _ → tt

module Actual (r : T.Run Two.lvl2) where
  module A = T.Run r
  z : W.zero W.≤ Two.lvl2
  z = P.z≤ Two.lvl2
  cover : Ω₁ Slots.⊴ proj₁ (A.bs j (W.inc tt W.self))
  cover = A.omegaB (W.inc tt W.self)
  q : R.𝟏 ≼ rd (A.bs W.zero (W.inc tt wk))
  q = A.oneB (W.inc tt wk)
  module M = G.Main A.ok A.bs z A.β cover A.oneβ q
  module Rep = Repeat o₁ M.o₁ (M.c , M.nc) cover
  src = F.B₀ j
  tgt = M.B′
  v = U.Ωt W.zero

  next-slot = Rep.run src tgt q R.wc R.wc v (tgt W.zero wk) q
  next-base = Rep.run src tgt q R.wc R.wu v A.β A.oneβ

  terms : ∀ k → read (Old.StandardOmegaOne.new-branch k) ≼
          rd (F.itV Rep.right (suc k) (F.stepS Rep.right tgt) W.zero (G.wd z) (F.run Rep.right tgt W.zero (G.wd z) A.β))
  terms k = Rep.values (suc k) (F.stepS Rep.left src) (F.stepS Rep.right tgt) next-slot R.wc R.wu _ _ next-base

  old-first = V.read (Old.OmegaOne.fold (OF.B₀ (O.suc O.zero)) Old.StandardOmegaOne.old-return)

  received : old-first ≼ rd (M.fold 1)
  received = ≼-trans {b = rd (Old.StandardOmegaOne.observe Old.StandardOmegaOne.new-return)}
    (proj₁ Old.StandardOmegaOne.value) (l≼ λ k → ≼l k (terms k))

  inside : old-first ≼ read (T.value r)
  inside = ≼-trans {b = rd (M.fold 1)} received (M.Ψg-ge 1)

module Live = Actual (T.finiteRun 1)
```

```agda
import Survey.W4LegacyFeedback as Feedback
module ThirdChild = Actual Feedback.Two.sub

in-third-cell : L.suc ThirdChild.old-first ≼ Feedback.Live.leaf 2 1
in-third-cell = ≼-trans {b = L.suc (read (T.value Feedback.Two.sub))}
  (s≼s ThirdChild.inside) Feedback.Two.strict
```
