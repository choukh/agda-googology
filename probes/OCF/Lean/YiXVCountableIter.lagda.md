# YiXVCountableIter
> 验收文件。档位：编译定理。各层的迭代合法性、混合比较与折叠后继的严格余量。
> 按 YiXVFiniteFold*/FiniteChain/FiniteGamma 推广，搬运与节点比较复用 Countable 接口；未交外层源链上界或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVCountableIter where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₂)
import OCF.Align.Level as L
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Lean.YiXVCountableBase as A
import OCF.Lean.YiXVCountableOmega as O
import OCF.Lean.YiXVCountableAdd as Add
import OCF.Lean.YiXVCountableAddFrame as F
import OCF.Lean.YiXVCountableFloor as Floor

good : ∀ {κ} (X : L.Ordᶜ κ) → A.Gd X → ∀ n → A.Gd (iter (X L.+_) L.zero n)
good X gx zero = A.Layer.gz
good X gx (suc n) = Add.good gx (good X gx n)
mono : ∀ {κ} {X Y : L.Ordᶜ κ} → A.Le X Y → ∀ n → A.Le (iter (X L.+_) L.zero n) (iter (Y L.+_) L.zero n)
mono {κ} t zero = A.Layer.rfl κ A.Gd< A.Le< A.Layer.gz
mono t (suc n) = F.mixed t (mono t n)
lim-mono : ∀ {κ} {X Y : L.Ordᶜ κ} → A.Le X Y →
  A.Le (L.lim (iter (X L.+_) L.zero)) (L.lim (iter (Y L.+_) L.zero))
lim-mono {κ} {X} {Y} t = A.Layer.pack (A.Layer.gl (good X gx)) (A.Layer.gl (good Y gy))
  (A.Layer.ll (λ n → A.Layer.pack (good X gx n) (A.Layer.gl (good Y gy)) (A.Layer.lr n (mono t n))))
  where
  gx = A.Layer.left κ A.Gd< A.Le< t
  gy = A.Layer.right κ A.Gd< A.Le< t
strict : ∀ {κ ν a} (p : ν L.<ᴵ a) (σ : L.Simᴵ κ a) (X : L.Ordᶜ κ) → A.Gd (L.ψ p σ X) →
  A.Le (L.suc (L.ψ p σ X)) (L.ψ p σ (L.suc X))
strict {ν = ν} p σ X gx =
  A.Layer.pack (A.Layer.gs gx) (A.Layer.gl (good Y gx)) (A.Layer.lr 2
    (F.mixed {σ = λ q → q} {τ = λ q → q} (A.Layer.rfl ν A.Gd< A.Le< gx)
      (A.Layer.trans ν A.Gd< A.Le< (proj₂ (O.model ν)) (Floor.floor p σ X gx))))
  where Y = L.ψ p σ X

actual : A.Le (L.lim (iter (L.Ω L.ωᴵ L.+_) L.zero)) (L.lim (iter (L.Ω L.ωᴵ L.+_) L.zero))
actual = lim-mono (A.Layer.rfl L.ωᴵ A.Gd< A.Le< A.omegaΩ)
```
