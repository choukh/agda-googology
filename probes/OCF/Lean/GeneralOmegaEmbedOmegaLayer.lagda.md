# 原ΩL与层加法保持对应结构

本篇直接对原层算术证明闭包。Kind见证包含种类的低层对应；因此
upL遇Ω时能构造正确的lo′证书，而不是从回灌结果反推种类。
这是层结构定理，尚非原run的值定理。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralOmegaEmbedOmegaLayer where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit.Polymorphic using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay using (node; upL; _⊕L_; ΩL; twL; ΛL)
open import OCF.Lean.GeneralOmegaEmbedOmegaIf

node-layer : ∀ {x y κ κ′ f g} (p : Layer x y) (r : Kind p κ κ′) →
  (∀ {a b} → Coord p r a b → Layer (f a) (g b)) →
  Layer (node x κ f) (node y κ′ g)
node-layer {κ = ()} lz′ r h
node-layer {κ = inj₁ κ} {inj₁ κ′} (ls′ {x} {y} p) r h = node-layer {x = x} {y = y} p r h
node-layer {κ = inj₁ κ} {inj₂ _} (ls′ p) () h
node-layer {κ = inj₂ _} {inj₁ κ′} (ls′ p) () h
node-layer {κ = inj₂ _} {inj₂ _} (ls′ p) r h = lo′ p h
node-layer {κ = (n , κ)} {(.n , κ′)} (ll′ {f} {g} p) (refl , r) h = node-layer {x = f n} {y = g n} (p n) r h
node-layer {κ = (inj₁ _ , κ)} {(inj₂ b , κ′)} (lo′ p q) () h
node-layer {κ = (inj₂ a , κ)} {(inj₁ _ , κ′)} (lo′ p q) () h
node-layer {κ = (inj₁ _ , inj₁ κ)} {(inj₁ _ , inj₁ κ′)} (lo′ {k} {j} p q) r h = node-layer {x = k} {y = j} p r h
node-layer {κ = (inj₁ _ , inj₁ κ)} {(inj₁ _ , inj₂ _)} (lo′ p q) () h
node-layer {κ = (inj₁ _ , inj₂ _)} {(inj₁ _ , inj₁ κ′)} (lo′ p q) () h
node-layer {κ = (inj₁ _ , inj₂ _)} {(inj₁ _ , inj₂ _)} (lo′ p q) r h = lo′ p h
node-layer {κ = (inj₂ a , κ)} {(inj₂ b , κ′)} (lo′ {f = f} {g = g} p q) (r , s) h = node-layer {x = f a} {y = g b} (q r) s h

up-layer : ∀ {x y a b} (p : Layer x y) → Tree p a b → Layer (upL x a) (upL y b)
up-layer p tz = lz′
up-layer p (ts r) = ls′ (up-layer p r)
up-layer p (tl r) = ll′ (λ n → up-layer p (r n))
up-layer p (to r h) = node-layer p r (λ q → up-layer p (h q))

add-layer : ∀ {x y a b} → Layer x y → Layer a b → Layer (x ⊕L a) (y ⊕L b)
add-layer p lz′ = p
add-layer p (ls′ q) = ls′ (add-layer p q)
add-layer p (ll′ q) = ll′ (λ n → add-layer p (q n))
add-layer p (lo′ q h) = lo′ q (λ r → add-layer p (h r))

omega-layer : ∀ {x y} → Layer x y → Layer (ΩL x) (ΩL y)
omega-layer lz′ = ls′ lz′
omega-layer (ls′ p) = lo′ p (λ r → add-layer (omega-layer p) (up-layer p r))
omega-layer (ll′ p) = ll′ (λ n → omega-layer (p n))
omega-layer (lo′ p h) = lo′ p (λ r → omega-layer (h r))

tower-layer : ∀ n → Layer (twL n) (twL n)
tower-layer zero = lz′
tower-layer (suc n) = omega-layer (tower-layer n)
lambda-layer : Layer ΛL ΛL
lambda-layer = ll′ tower-layer
```

这里给全部原twL与ΛL的实例，故接口不是仅常值族可满足。仍须证明
原flL在该Tree关系下相关，以及实际code的Coord保持，才能接已有
Coded sound；本篇不把层关系自身读成序数值相等。
