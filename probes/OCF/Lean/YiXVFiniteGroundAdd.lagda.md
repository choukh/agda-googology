# YiXVFiniteGroundAdd
> 验收文件。档位：编译定理。有限层参照侧的统一比较工具；尚无所有 pre n 或 Goal。
> 证明参照 YiOverOps 与 YiXVCan2* 并按有限层统一，不改源树与折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteGroundAdd where
open import Data.Nat using (zero; suc)
import Data.Fin as F
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B

good : ∀ n {X} → A.Gd n X → (σ : L.Simᴵ L.zero (L.natᴵ n)) (y : I.T zero) → A.Gd n (L.add X σ y)
good n gx σ L.zero = gx
good n {X} gx σ (L.suc y) = B.gs n F.zero {X = L.add X σ y} (good n {X = X} gx σ y)
good n {X} gx σ (L.lim a) = B.gl n F.zero {a = λ k → L.add X σ (a k)} (λ k → good n {X = X} gx σ (a k))
good n gx σ (L.limᵢ () a)
good n gx σ (L.up () y)

right : ∀ n {X X′} → A.Le n X X′ → (σ : L.Simᴵ L.zero (L.natᴵ n)) (y : I.T zero) → A.Le n X (L.add X′ σ y)
right n p σ L.zero = p
right n {X} {X′} p σ (L.suc y) = B.w≤ n F.zero {X = X} {Y = L.add X′ σ y} (right n {X = X} {X′ = X′} p σ y)
right n {X} {X′} p σ (L.lim a) = B.lr n F.zero {X = X} {a = λ k → L.add X′ σ (a k)}
  (B.left n F.zero {X = X} {Y = X′} p) (λ k → good n {X = X′} (B.right n F.zero {X = X} {Y = X′} p) σ (a k))
  0 (right n {X = X} {X′ = X′} p σ (a 0))
right n p σ (L.limᵢ () a)
right n p σ (L.up () y)

mono : ∀ n {X X′} {σ τ : L.Simᴵ L.zero (L.natᴵ n)} {x y : I.T zero} → A.Le n X X′ → x ≼ y → A.Le n (L.add X σ x) (L.add X′ τ y)
mono n {X} {X′} {σ} {τ} {y = y} p z≼ = right n {X = X} {X′ = X′} p τ y
mono n {X} {X′} {σ} {τ} p (s≼s {a = x} {b = y} q) = B.s≤ n F.zero {X = L.add X σ x} {Y = L.add X′ τ y}
  (mono n {X = X} {X′ = X′} {σ = σ} {τ = τ} p q)
mono n {X} {X′} {σ} {τ} p (≼l {a = x} {f = a} k q) = B.lr n F.zero {X = L.add X σ x} {a = λ j → L.add X′ τ (a j)}
  (good n {X = X} (B.left n F.zero {X = X} {Y = X′} p) σ x) (λ j → good n {X = X′} (B.right n F.zero {X = X} {Y = X′} p) τ (a j))
  k (mono n {X = X} {X′ = X′} {σ = σ} {τ = τ} p q)
mono n {X} {X′} {σ} {τ} p (l≼ {f = a} {b = y} h) = B.ll n F.zero {a = λ k → L.add X σ (a k)} {Y = L.add X′ τ y}
  (λ k → good n {X = X} (B.left n F.zero {X = X} {Y = X′} p) σ (a k)) (good n {X = X′} (B.right n F.zero {X = X} {Y = X′} p) τ y)
  (λ k → mono n {X = X} {X′ = X′} {σ = σ} {τ = τ} p (h k))
mono n p (≼i {p = ()} x ex q)
mono n p (i≼ {p = ()} h)
mono n p (≼u {r = ()} q)
mono n p (u≼ {r = ()} q)

sample : A.Gd 2 (L.add (L.Ω (L.natᴵ 2)) (λ q → L.suc (L.suc q)) (L.Ω L.zero))
sample = good 2 A.actual₂ (λ q → L.suc (L.suc q)) (L.Ω L.zero)
```
