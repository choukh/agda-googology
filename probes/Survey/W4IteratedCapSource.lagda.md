# 原二层闭项给出的统一 g 上界

第四层。把逐项上界还原成原 src 的 Ω₁ 分支，逐项给出 g 的上界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4IteratedCapSource where

open import Data.Nat.Base using (ℕ; suc)
open import Data.Product using (_,_; proj₁; proj₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; _≈ᵛ_; ≼-trans; ≼-refl; ≼-suc; s≼s; l≼; ≼l; ≼i; i≼; u≼; ≼u; z≼; ≅→≼)
open import OCF.Align.BTBOValBase using (tr₀)
import OCF.Align.BTBOValUp as U
import OCF.Align.BTBOValDn as Down
open import WVOne using (T₀; 𝟏)
open import WSLevel using (Ω₁ᴸ)
import YiLAB10Src as Y
import B12LimitSrc as A
import B12Omega3Ref as R
import B13Target as P
import B17RefAllSource as Src
import B19OldSource as Sync
import B24RExit as Exit
import Survey.W4FourthLiftCeiling as Old
import Survey.W4RoomDerivative as G
import Survey.W4IteratedCap as C
module S = Src.S
module B = Src.B

-- 同一参照族在原 src 上的定义，只用 Ω₂、右加 Ω₁ 和两种极限。
roll : A.Src₂ → S.Ord₀ → A.Src₂
roll s S.zero = s S.+ Old.unit
roll s (S.suc x) = roll s x S.+ Old.unit
roll s (S.lim f) = S.lim (λ n → roll s (f n))
block = λ s → S.limᵢ (B.suc B.zero) (roll s)

block-pres : ∀ {p q} → p L.≅ q → C.block p L.≅ C.block q
block-pres e = L.lᵢ≅ L.z≅ (λ _ _ d → C.pres e d)

module Up {s p} (w : U.Mh s p) where
  up₀ : ∀ y → U.Mh (roll s S.zero) (C.roll p y)
  up₀ L.zero = U.M-add {σ = R.idσ} w (A.Aligned.up Sync.omega-one)
  up₀ (L.suc y) = U.M-add-r {σ = L.suc} Ω₁ᴸ (up₀ y)
  up₀ (L.lim f) = U.Mlr 0 (up₀ (f 0))
  up : ∀ x y → tr₀ x ≼ y → U.Mh (roll s x) (C.roll p y)
  up (S.limᵢ () f) y d
  up S.zero y z≼ = up₀ y
  up (S.suc x) (L.suc y) (s≼s d) = U.M-add {σ = R.idσ} (up x y d) (A.Aligned.up Sync.omega-one)
  up x (L.lim f) (≼l n d) = U.Mlr n (up x (f n) d)
  up (S.lim f) y (l≼ d) = U.Mll (λ n → up (f n) y (d n))
  up x _ (≼i {p = ()} _ _ _)
  up x _ (≼u {r = ()} _)
  shift : U.Mh (block s) (C.block p)
  shift = U.Mii L.z≅ (λ x y d → up x y (U.Mh→≼ d))
  retain : ∀ y → U.Mh s (C.roll p y)
  retain L.zero = U.M-add-r {σ = L.suc} Ω₁ᴸ w
  retain (L.suc y) = U.M-add-r {σ = L.suc} Ω₁ᴸ (retain y)
  retain (L.lim f) = U.Mlr 0 (retain (f 0))
  grow : U.Mh s (C.block p)
  grow = U.Mir (λ z _ → retain z)

module Downward {s p} (w : Down.Dn p s) where
  dn₀ : ∀ x → Down.Dn (C.roll p L.zero) (roll s x)
  dn₀ S.zero = Down.Dn-add {σ = R.idσ} w (A.Aligned.dn Sync.omega-one)
  dn₀ (S.suc x) = Down.Dn-add-r Old.unit (dn₀ x)
  dn₀ (S.lim f) = Down.Rlr 0 (dn₀ (f 0))

  dn : ∀ y x → y ≼ tr₀ x → Down.Dn (C.roll p y) (roll s x)
  dn y (S.limᵢ () f) d
  dn L.zero x z≼ = dn₀ x
  dn (L.suc y) (S.suc x) (s≼s d) = Down.Dn-add {σ = R.idσ} (dn y x d) (A.Aligned.dn Sync.omega-one)
  dn (L.lim f) x (l≼ d) = Down.Rll (λ n → dn (f n) x (d n))
  dn y (S.lim f) (≼l n d) = Down.Rlr n (dn y (f n) d)
  dn _ x (i≼ {p = ()} _)
  dn _ x (u≼ {r = ()} _)

  shift : Down.Dn (C.block p) (block s)
  shift = Down.Rii L.z≅ (λ y x d → dn y x (Down.Dn→≼ d))
  retain : ∀ x → Down.Dn p (roll s x)
  retain S.zero = Down.Dn-add-r Old.unit w
  retain (S.suc x) = Down.Dn-add-r Old.unit (retain x)
  retain (S.lim f) = Down.Rlr 0 (retain (f 0))
  grow : Down.Dn p (block s)
  grow = Down.Rir (λ z → retain z)

shifted : ∀ {s p} → A.Aligned s p → A.Aligned (block s) (C.block p)
shifted ok = A.aligned (Up.shift (A.Aligned.up ok)) (Downward.shift (A.Aligned.dn ok)) (block-pres (A.Aligned.regular ok))

family : T₀ → A.Src₂
family L.zero = block Y.a
family (L.suc x) = block (family x)
family (L.lim f) = S.lim (λ i → family (f i))

aligned : ∀ x → A.Aligned (family x) (C.family x)
aligned L.zero = shifted A.omega2
aligned (L.suc x) = shifted (aligned x)
aligned (L.lim f) = A.lim (λ n → family (f n)) (λ n → C.family (f n)) (λ n → aligned (f n))

source = λ x → S.ψ₀ (Src.pass (family x))
exact : ∀ x → tr₀ (source x) ≈ᵛ C.value (C.family x)
exact x = A.fold (Exit.passed (aligned x))
upper : ∀ x → G.g x ≼ tr₀ (source x)
upper x = ≼-trans {b = C.value (C.family x)} (C.indexed x) (proj₂ (exact x))


```
