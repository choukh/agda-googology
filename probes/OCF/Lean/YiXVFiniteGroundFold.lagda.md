# YiXVFiniteGroundFold
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteGroundFold where
open import Data.Nat using (zero; suc)
open import Data.Product using (proj₁)
import Data.Fin as F
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteIter as It
import OCF.Lean.YiXVFiniteFloor as Floor

good : ∀ j {a} (p : L.natᴵ j L.<ᴵ a) (σ : L.Simᴵ L.zero a) (x : I.T zero) → A.Gd j (L.ψ p σ x)
good j p σ L.zero = proj₁ (B.Ω-model j F.zero)
good j p σ (L.suc x) = B.gl j F.zero {a = iter (L.ψ p σ x L.+_) L.zero} (It.good j (L.ψ p σ x) (good j p σ x))
good j p σ (L.lim a) = B.gl j F.zero {a = λ n → L.ψ p σ (a n)} (λ n → good j p σ (a n))
good j p σ (L.limᵢ () a)
good j p σ (L.up () x)

mono : ∀ j {a b} (p : L.natᴵ j L.<ᴵ a) (q : L.natᴵ j L.<ᴵ b) (σ : L.Simᴵ L.zero a) (τ : L.Simᴵ L.zero b)
  {x y : I.T zero} → x ≼ y → A.Le j (L.ψ p σ x) (L.ψ q τ y)
mono j p q σ τ {y = y} z≼ = Floor.floor j q τ y (good j q τ y)
mono j p q σ τ (s≼s {a = x} {b = y} r) = It.lim-mono j (L.ψ p σ x) (L.ψ q τ y) (mono j p q σ τ r)
mono j p q σ τ (≼l {a = x} {f = a} n r) = B.lr j F.zero {X = L.ψ p σ x} {a = λ n → L.ψ q τ (a n)}
  (good j p σ x) (λ n → good j q τ (a n)) n (mono j p q σ τ r)
mono j p q σ τ (l≼ {f = a} {b = y} h) = B.ll j F.zero {a = λ n → L.ψ p σ (a n)} {Y = L.ψ q τ y}
  (λ n → good j p σ (a n)) (good j q τ y) (λ n → mono j p q σ τ (h n))
mono j p q σ τ (≼i {p = ()} x ex r)
mono j p q σ τ (i≼ {p = ()} h)
mono j p q σ τ (≼u {r = ()} r)
mono j p q σ τ (u≼ {r = ()} r)

actual : A.Gd 3 (L.ψ L.zero (λ q → L.suc (L.suc (L.suc (L.suc q)))) (L.suc (L.zero {ℓ = L.zero})))
actual = good 3 L.zero (λ q → L.suc (L.suc (L.suc (L.suc q)))) (L.suc L.zero)
```
