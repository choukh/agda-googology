# YiXV：第 2 层参照的有守卫比较
> 验收文件。编译定理：关系 ≤₂ 对目标层 1、0 折叠保持；Ω₂ 与自身、提升的 Ω₁ 与 Ω₂ 都有实例。
> 两种节点分别守卫 1 与 Ω₁；提升接 YiOverRef 的比较，不取全分支三歧。
> 基于 YiOverRef 按有限公共层 2 扩展；不含第 2 层自身折叠的保持律。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVRef2 where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; l≼; ≼l; 1≼ψ⁰; iter-≼)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using (iter)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O
import OCF.Lean.YiXVRefVar as V

T₂ : Set
T₂ = L.Ordᶜ (L.suc (L.suc L.zero))
ψ₁ : T₂ → R.T₁
ψ₁ = L.ψ L.zero (λ r → r)

c : (R.T₁ → T₂) → ℕ → R.T₁
c f = iter (λ x → ψ₁ (f x)) O.Ω₁

base : (X : T₂) → O.Ω₁ R.≤ₚ ψ₁ X
base L.zero = O.Ω≤Ω
base (L.suc X) = R.≤l 1 (base X)
base (L.lim f) = R.≤l 0 (base (f 0))
base (L.limᵢ L.zero f) = R.≤l 0 (base (f O.Ω₁))
base (L.limᵢ (L.suc L.zero) f) = R.i1 (base (f (V.τ R.𝟙)))
base (L.up L.zero X) = V.base _ X

module Chain₁ (f g : R.T₁ → T₂)
  (h : ∀ x y → O.Ω₁ R.≤ₚ x → x R.≤ₚ y → ψ₁ (f x) R.≤ₚ ψ₁ (g y)) where
  floor : ∀ f n → O.Ω₁ R.≤ₚ c f n
  floor f zero = O.Ω≤Ω
  floor f (suc n) = base (f (c f n))
  bound : ∀ n → c f n R.≤ₚ c g n
  bound zero = O.Ω≤Ω
  bound (suc n) = h (c f n) (c g n) (floor f n) (bound n)

c₀ : (R.T₀ → T₂) → ℕ → R.T₀
c₀ f = iter (λ x → L.ψ (L.suc L.zero) (λ r → r) (f x)) R.𝟙

ψg≈ : (y : R.T₀) →
  (L.ψ (L.suc L.zero) (λ q → L.suc (L.suc q)) y ≼ L.ψ⁰ y) ×
  (L.ψ⁰ y ≼ L.ψ (L.suc L.zero) (λ q → L.suc (L.suc q)) y)
ψg≈ L.zero = ≼-refl _ , ≼-refl _
ψg≈ (L.suc y) = l≼ (λ n → ≼l n (iter-≼ (proj₁ (ψg≈ y)) n)) ,
  l≼ (λ n → ≼l n (iter-≼ (proj₂ (ψg≈ y)) n))
ψg≈ (L.lim f) = l≼ (λ n → ≼l n (proj₁ (ψg≈ (f n)))) , l≼ (λ n → ≼l n (proj₂ (ψg≈ (f n))))
ψg≈ (L.limᵢ () f)
ψg≈ (L.up () x)

ψu≈ : (X : R.T₁) →
  (L.ψ (L.suc L.zero) (λ q → L.suc q) X ≼ L.ψ⁰ X) ×
  (L.ψ⁰ X ≼ L.ψ (L.suc L.zero) (λ q → L.suc q) X)
ψu≈ L.zero = ≼-refl _ , ≼-refl _
ψu≈ (L.suc X) = l≼ (λ n → ≼l n (iter-≼ (proj₁ (ψu≈ X)) n)) ,
  l≼ (λ n → ≼l n (iter-≼ (proj₂ (ψu≈ X)) n))
ψu≈ (L.lim f) = l≼ (λ n → ≼l n (proj₁ (ψu≈ (f n)))) , l≼ (λ n → ≼l n (proj₂ (ψu≈ (f n))))
ψu≈ (L.limᵢ L.zero f) = l≼ (λ n → ≼l n (proj₁ (ψu≈ (f (R.δ f n))))) ,
  l≼ (λ n → ≼l n (proj₂ (ψu≈ (f (R.δ f n)))))
ψu≈ (L.limᵢ (L.suc ()) f)
ψu≈ (L.up L.zero x) = ψg≈ x

ψ₀≈ : (X : T₂) →
  (L.ψ (L.suc L.zero) (λ r → r) X ≼ L.ψ⁰ X) ×
  (L.ψ⁰ X ≼ L.ψ (L.suc L.zero) (λ r → r) X)
ψ₀≈ L.zero = ≼-refl _ , ≼-refl _
ψ₀≈ (L.suc X) = l≼ (λ n → ≼l n (iter-≼ (proj₁ (ψ₀≈ X)) n)) ,
  l≼ (λ n → ≼l n (iter-≼ (proj₂ (ψ₀≈ X)) n))
ψ₀≈ (L.lim f) = l≼ (λ n → ≼l n (proj₁ (ψ₀≈ (f n)))) , l≼ (λ n → ≼l n (proj₂ (ψ₀≈ (f n))))
ψ₀≈ (L.limᵢ L.zero f) = l≼ (λ n → ≼l n (proj₁ (ψ₀≈ (f (c f n))))) ,
  l≼ (λ n → ≼l n (proj₂ (ψ₀≈ (f (c f n)))))
ψ₀≈ (L.limᵢ (L.suc L.zero) f) = l≼ (λ n → ≼l n (proj₁ (ψ₀≈ (f (c₀ f n))))) ,
  l≼ (λ n → ≼l n (proj₂ (ψ₀≈ (f (c₀ f n)))))
ψ₀≈ (L.up L.zero X) = ψu≈ X

module Chain₀ (f g : R.T₀ → T₂)
  (h : ∀ x y → R.𝟙 ≼ x → x ≼ y → L.ψ⁰ (f x) ≼ L.ψ⁰ (g y)) where
  floor : ∀ f n → R.𝟙 ≼ c₀ f n
  floor f zero = ≼-refl _
  floor f (suc n) = ≼-trans (1≼ψ⁰ (f (c₀ f n))) (proj₂ (ψ₀≈ (f (c₀ f n))))
  bound : ∀ n → c₀ f n ≼ c₀ g n
  bound zero = ≼-refl _
  bound (suc n) = ≼-trans (proj₁ (ψ₀≈ (f (c₀ f n))))
    (≼-trans (h (c₀ f n) (c₀ g n) (floor f n) (bound n)) (proj₂ (ψ₀≈ (g (c₀ g n)))))

data _≤₂_ : T₂ → T₂ → Set where
  z₂ : ∀ {Y} → L.zero ≤₂ Y
  s₂ : ∀ {X Y} → X ≤₂ Y → L.suc X ≤₂ L.suc Y
  w₂ : ∀ {X Y} → X ≤₂ Y → X ≤₂ L.suc Y
  l₂ : ∀ {f Y} → (∀ n → f n ≤₂ Y) → L.lim f ≤₂ Y
  r₂ : ∀ {X f} n → X ≤₂ f n → X ≤₂ L.lim f
  n₀ : ∀ {f g : R.T₀ → T₂} → (∀ x y → R.𝟙 ≼ x → x ≼ y → f x ≤₂ g y) →
    L.limᵢ (L.suc L.zero) f ≤₂ L.limᵢ (L.suc L.zero) g
  n₁ : ∀ {f g : R.T₁ → T₂} → (∀ x y → O.Ω₁ R.≤ₚ x → x R.≤ₚ y → f x ≤₂ g y) →
    L.limᵢ L.zero f ≤₂ L.limᵢ L.zero g
  a₀ : ∀ {X} {g : R.T₀ → T₂} → X ≤₂ g R.𝟙 → X ≤₂ L.limᵢ (L.suc L.zero) g
  a₁ : ∀ {X} {g : R.T₁ → T₂} → X ≤₂ g O.Ω₁ → X ≤₂ L.limᵢ L.zero g
  u₁ : ∀ {X Y : R.T₁} → X R.≤ₚ Y → L.up L.zero X ≤₂ L.up L.zero Y

mono : ∀ {X Y} → X ≤₂ Y → ψ₁ X R.≤ₚ ψ₁ Y
mono z₂ = base _
mono (s₂ h) = R.l≤ (λ n → R.≤l n (O.iterₚ (mono h) n))
mono (w₂ h) = R.≤l 1 (mono h)
mono (l₂ h) = R.l≤ (λ n → mono (h n))
mono (r₂ n h) = R.≤l n (mono h)
mono (n₀ h) = R.ii (λ x y o q → mono (h (V.τ x) (V.τ y) (V.posτ o) (V.monoτ q)))
mono (n₁ {f} {g} h) = R.l≤ (λ n → R.≤l n (mono (h (c f n) (c g n)
  (Chain₁.floor f g (λ x y o q → mono (h x y o q)) f n)
  (Chain₁.bound f g (λ x y o q → mono (h x y o q)) n))))
mono (a₀ h) = R.i1 (mono h)
mono (a₁ h) = R.≤l 0 (mono h)
mono (u₁ h) = V.mono _ _ h

Ω₂ : T₂
Ω₂ = L.Ω (L.suc (L.suc L.zero))
Ω₂-refl : Ω₂ ≤₂ Ω₂
Ω₂-refl = n₁ (λ x y o q → u₁ q)

sample : L.up L.zero O.Ω₁ ≤₂ Ω₂
sample = a₁ (u₁ O.Ω≤Ω)

mono⁰ : ∀ {X Y} → X ≤₂ Y → L.ψ⁰ X ≼ L.ψ⁰ Y
mono⁰ z₂ = 1≼ψ⁰ _
mono⁰ (s₂ h) = l≼ (λ n → ≼l n (iter-≼ (mono⁰ h) n))
mono⁰ (w₂ h) = ≼l 1 (mono⁰ h)
mono⁰ (l₂ h) = l≼ (λ n → mono⁰ (h n))
mono⁰ (r₂ n h) = ≼l n (mono⁰ h)
mono⁰ (n₀ {f} {g} h) = l≼ (λ n → ≼l n (mono⁰ (h (c₀ f n) (c₀ g n)
  (Chain₀.floor f g (λ x y o q → mono⁰ (h x y o q)) f n)
  (Chain₀.bound f g (λ x y o q → mono⁰ (h x y o q)) n))))
mono⁰ (n₁ {f} {g} h) = l≼ (λ n → ≼l n (mono⁰ (h (c f n) (c g n)
  (Chain₁.floor f g (λ x y o q → mono (h x y o q)) f n)
  (Chain₁.bound f g (λ x y o q → mono (h x y o q)) n))))
mono⁰ (a₀ h) = ≼l 0 (mono⁰ h)
mono⁰ (a₁ h) = ≼l 0 (mono⁰ h)
mono⁰ (u₁ h) = R.mono⁰ h
```
