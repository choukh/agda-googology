# YiXVFiniteIter
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteIter where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; proj₂)
import Data.Fin as F
import OCF.Align.Level as L
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteAdd as Add
import OCF.Lean.YiXVFiniteFloor as Floor

good : ∀ n (X : I.T n) → A.Gd n X → ∀ k → A.Gd n (iter (X L.+_) L.zero k)
good n X gx zero = B.gz n F.zero
good n X gx (suc k) = Add.plus-good n {X = X} {Y = iter (X L.+_) L.zero k} gx (good n X gx k)
mono : ∀ n (X Y : I.T n) → A.Le n X Y → ∀ k → A.Le n (iter (X L.+_) L.zero k) (iter (Y L.+_) L.zero k)
mono n X Y p zero = B.rfl n F.zero {X = L.zero} (B.gz n F.zero)
mono n X Y p (suc k) = Add.plus n {X = X} {X′ = Y} {Y = iter (X L.+_) L.zero k} {Y′ = iter (Y L.+_) L.zero k} p (mono n X Y p k)

lim-mono : ∀ n (X Y : I.T n) → A.Le n X Y → A.Le n (L.lim (iter (X L.+_) L.zero)) (L.lim (iter (Y L.+_) L.zero))
lim-mono n X Y p = B.ll n F.zero {a = iter (X L.+_) L.zero} {Y = L.lim (iter (Y L.+_) L.zero)}
  (good n X gx) (B.gl n F.zero {a = iter (Y L.+_) L.zero} (good n Y gy))
  (λ k → B.lr n F.zero {X = iter (X L.+_) L.zero k} {a = iter (Y L.+_) L.zero} (good n X gx k) (good n Y gy) k (mono n X Y p k))
  where
  gx = B.left n F.zero {X = X} {Y = Y} p
  gy = B.right n F.zero {X = X} {Y = Y} p

strict : ∀ j {k a} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ k a) (x : L.Ordᶜ k) → A.Gd j (L.ψ p σ x) →
  A.Le j (L.suc (L.ψ p σ x)) (L.ψ p σ (L.suc x))
strict j p σ x gx = B.lr j F.zero {X = L.suc X} {a = iter (X L.+_) L.zero} (B.gs j F.zero {X = X} gx) (good j X gx) 2
  (Add.plus j {X = X} {X′ = X} {Y = L.suc L.zero} {Y′ = X} (B.rfl j F.zero {X = X} gx)
    (B.trans j F.zero {X = L.suc L.zero} {Y = L.Ω (L.natᴵ j)} {Z = X} (proj₂ (B.Ω-model j F.zero)) (Floor.floor j p σ x gx)))
  where X = L.ψ p σ x
```
