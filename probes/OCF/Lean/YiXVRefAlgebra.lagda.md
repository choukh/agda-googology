# YiXVRefAlgebra
> 验收文件。档位：编译定理。零前缀嵌入的加法、迭代与极限比较；两项同界的和以一次后继迭代吸收。
> 复用 Level、CountableFold/MapCompare 与 ReadOmega 的构造，完整实例见代码；未接实际源世界或原外层 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVRefAlgebra where
open import Data.Nat using (ℕ; zero; suc)
import OCF.Align.Level as L
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVCountableAddFrame as Plus
import OCF.Lean.YiXVCountableIter as I
import OCF.Lean.YiXVNeutral as N
open import OCF.Lean.YiXVRefLift using (embedded; embedded-good)
lim-mono : ∀ {κ} {f g : ℕ → L.Ordᶜ κ} → (∀ n → A.Le (f n) (g n)) → A.Le (L.lim f) (L.lim g)
lim-mono {κ} h = D.pack (D.gl (λ n → D.left (h n))) (D.gl (λ n → D.right (h n)))
  (D.ll (λ n → D.pack (D.left (h n)) (D.gl (λ k → D.right (h k))) (D.lr n (h n))))
  where module D = A.Layer κ A.Gd< A.Le<
map-plus : ∀ {κ ν} (σ : L.Simᴵ κ ν) {X Y} → A.Gd X → A.Gd Y →
  A.Le (embedded σ (X L.+ Y)) (embedded σ X L.+ embedded σ Y)
map-plus {κ} {ν} σ {X} {Y} gx gy = D.pack
  (embedded-good (Add.good {σ = λ q → q} gx gy))
  (Add.good (embedded-good gx) (embedded-good gy))
  (D.ce (L.≅-trans
    (N.neutral L.z≅ (L.add-≅ (A.self gx) (A.self gy)))
    (L.≅-sym (L.add-≅ {σ = λ q → q} {σ′ = λ q → q}
      (N.neutral L.z≅ (A.self gx)) (N.neutral L.z≅ (A.self gy))))))
  where module D = A.Layer ν A.Gd< A.Le<
split : ∀ {κ ν} (σ : L.Simᴵ κ ν) {X : L.Ordᶜ ν} {Y} → A.Gd X → A.Gd Y →
  A.Le (L.add X σ Y) (X L.+ embedded σ Y)
split {ν = ν} σ {X} {Y} gx gy = D.pack (Add.good gx gy) (Add.good gx (embedded-good gy))
  (D.ce (L.≅-sym (L.add-≅ {σ = λ q → q} {σ′ = σ} (A.self gx) (N.neutral L.z≅ (A.self gy)))))
  where module D = A.Layer ν A.Gd< A.Le<
map-iter : ∀ {κ ν} (σ : L.Simᴵ κ ν) {X : L.Ordᶜ κ} {Y : L.Ordᶜ ν} →
  A.Gd X → A.Le (embedded σ X) Y → ∀ n →
  A.Le (embedded σ (iter (X L.+_) L.zero n)) (iter (Y L.+_) L.zero n)
map-iter {ν = ν} σ gx h zero = A.Layer.rfl ν A.Gd< A.Le< A.Layer.gz
map-iter {ν = ν} σ {X} gx h (suc n) = A.Layer.trans ν A.Gd< A.Le<
  (map-plus σ gx (I.good X gx n)) (Plus.mixed h (map-iter σ gx h n))
actual : A.Le (embedded (λ q → L.suc q) (L.Ω (L.suc L.zero) L.+ L.Ω (L.suc L.zero)))
  (embedded (λ q → L.suc q) (L.Ω (L.suc L.zero)) L.+ embedded (λ q → L.suc q) (L.Ω (L.suc L.zero)))
actual = map-plus (λ q → L.suc q) A.oneΩ A.oneΩ

sum-ω : ∀ {ν} {X Y F : L.Ordᶜ ν} → A.Le X F → A.Le Y F →
  A.Le (X L.+ Y) (L.lim (iter (F L.+_) L.zero))
sum-ω {ν} {F = F} xf yf = D.pack (Add.good (D.left xf) (D.left yf))
  (D.gl (I.good F (D.right xf))) (D.lr 2 (Plus.mixed {σ = λ q → q} {τ = λ q → q} xf yf))
  where module D = A.Layer ν A.Gd< A.Le<
```
