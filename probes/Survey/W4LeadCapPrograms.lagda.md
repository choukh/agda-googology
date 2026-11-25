# 两级迭代的正层分支比较

第四层。以任意能在源前缀右侧付出一份 Ω₁ 的运算为起点。第一次对角容纳源前缀上的完整 Ω₁ 分支；第二次对角容纳此前给 g 上界的整个源参数。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module Survey.W4LeadCapPrograms where

open import Data.Unit.Base using (tt)
open import Data.Nat.Base using (ℕ; zero; suc)
open import OCF.Align.BTBOValBase using (tr₀)
import OCF.Align.BTBOValUp as U
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; ≼u)
open import WVOne using (T₀; 𝟏)
open import WSLevel using (Ω₁ᴸ)
open import YiLAB7Replay using (Ω₂ᴸ)
import YiLAB10Src as Y
import B12LimitSrc as M
import B12Omega3Ref as R
import B17RefAllSource as Src
import B19OldSource as Sync
import Survey.W4FourthLiftCeiling as Old
import Survey.W4IteratedCapSource as C
import Survey.W4IteratedCapCube as Cube
module S = Src.S
module B = Src.B

Op = M.Lev₂ → M.Lev₂
iter = R.S.iter
sum : Op → T₀ → Op
sum f L.zero p = f p
sum f (L.suc x) p = L.lim (iter (sum f x) p)
sum f (L.lim xs) p = L.lim (λ n → sum f (xs n) p)
wide : Op → Op
wide f p = L.limᵢ (L.suc L.zero) (λ x → sum f x p)
higher : T₀ → Op → Op
higher L.zero f = wide f
higher (L.suc y) f p = L.lim (λ n → iter (higher y) f n p)
higher (L.lim ys) f p = L.lim (λ n → higher (ys n) f p)
roof : Op → Op
roof f p = L.limᵢ (L.suc L.zero) (λ y → higher y f p)

Cost : Op → Set
Cost f = ∀ {s : M.Src₂} {p : M.Lev₂} → U.Mh s p → U.Mh (s S.+ Old.unit) (f p)

in-sum : ∀ f y {s : M.Src₂} {p : M.Lev₂} → U.Mh s (f p) → U.Mh s (sum f y p)
in-sum f L.zero d = d
in-sum f (L.suc y) d = U.Mlr 1 (in-sum f y d)
in-sum f (L.lim ys) d = U.Mlr 0 (in-sum f (ys 0) d)

in-wide : ∀ f n {s : M.Src₂} {p : M.Lev₂} → U.Mh s (iter f p n) → U.Mh s (wide f p)
in-wide f n d = U.Mir λ { .𝟏 (L.s≅ L.z≅) → U.Mlr n d }

in-higher : ∀ y f {s : M.Src₂} {p : M.Lev₂} → U.Mh s (wide f p) → U.Mh s (higher y f p)
in-higher L.zero f d = d
in-higher (L.suc y) f d = U.Mlr 1 (in-higher y f d)
in-higher (L.lim ys) f d = U.Mlr 0 (in-higher (ys 0) f d)

many : ∀ y f n {s : M.Src₂} {p : M.Lev₂} → U.Mh s (iter f p n) → U.Mh s (higher y f p)
many y f n {p = p} d = in-higher y f {p = p} (in-wide f n {p = p} d)

module Roll (f : Op) (cost : Cost f) (s : M.Src₂) (p : M.Lev₂) (init : U.Mh (s S.+ Old.unit) (f p)) where
  pay : ∀ x y → tr₀ x ≼ y → U.Mh (C.roll s x) (sum f y p)
  pay (S.limᵢ () _) y d
  pay S.zero y z≼ = in-sum f y {p = p} init
  pay (S.suc x) (L.suc y) (s≼s d) = U.Mlr 2 (in-sum f y {p = sum f y p} (cost (pay x y d)))
  pay x (L.lim ys) (≼l n d) = U.Mlr n (pay x (ys n) d)
  pay (S.lim xs) y (l≼ d) = U.Mll (λ n → pay (xs n) y (d n))
  pay x _ (≼i {p = ()} _ _ _)
  pay x _ (≼u {r = ()} _)
  block : U.Mh (C.block s) (wide f p)
  block = U.Mii L.z≅ (λ x y d → pay x y (U.Mh→≼ d))

base = λ p → L.add p L.suc Ω₁ᴸ
spend : Cost base
spend d = U.M-add {σ = L.suc} d (U.M-↑ B.zero (U.M-Ω {a = B.suc B.zero} tt (L.s≅ L.z≅)))

actual : ∀ x y → tr₀ x ≼ y → U.Mh (Cube.native x) (higher y base Ω₂ᴸ)
actual (S.limᵢ () _) y d
actual S.zero y z≼ = in-higher y base {p = Ω₂ᴸ} (Roll.block base spend Y.a Ω₂ᴸ (spend (M.Aligned.up M.omega2)))
actual (S.suc x) (L.suc y) (s≼s d) = U.Mlr 3
  (in-higher y second {p = Ω₂ᴸ} (Roll.block second add-second (Cube.native x) Ω₂ᴸ start))
  where
  first = higher y base
  second = higher y first
  add-first : Cost first
  add-first {p = q} w = many y base 1 {p = q} (spend w)
  add-second : Cost second
  add-second {p = q} w = many y first 1 {p = q} (add-first w)
  start : U.Mh (Cube.native x S.+ Old.unit) (second Ω₂ᴸ)
  start = many y first 2 {p = Ω₂ᴸ} (add-first (actual x y d))
actual x (L.lim ys) (≼l n d) = U.Mlr n (actual x (ys n) d)
actual (S.lim xs) y (l≼ d) = U.Mll (λ n → actual (xs n) y (d n))
actual x _ (≼i {p = ()} _ _ _)
actual x _ (≼u {r = ()} _)

cube : U.Mh Cube.cube (roof base Ω₂ᴸ)
cube = U.Mii L.z≅ (λ x y r → actual x y (U.Mh→≼ r))
```
