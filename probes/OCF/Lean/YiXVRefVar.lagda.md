# YiXV：有限公共上界内的模拟证明变体
> 验收文件。编译定理：任意 Simᴵ 1 2 给出的目标层 1 折叠，对第 1 层受限比较保持；Good 输入上有两向比较。
> 公共上界字面为 2，bound-unique 只消去 0<2 的有限证明；不判定裸层号。
> flat/mono 按 YiOverOps.B-flat、ψ₁-mono 推广，供 YiXVRef2 的提升行使用。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVRefVar where
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; ≼-refl; ≼-trans)
import OCF.Lean.YiOverRef as R
import OCF.Lean.YiOverOps as O

Σ₁ : Set
Σ₁ = L.Simᴵ (L.suc L.zero) (L.suc (L.suc L.zero))

Ψ : Σ₁ → R.T₁ → R.T₁
Ψ σ = L.ψ {i = L.suc L.zero} {k = L.suc L.zero} {ℓ = L.suc (L.suc L.zero)} L.zero σ

bound-unique : (p : L.zero L.<ᴵ L.suc (L.suc L.zero)) → p ≡ L.suc L.zero
bound-unique (L.suc L.zero) = refl

τ : R.T₀ → R.T₀
τ = L.tr⁻ L.z≅

posτ : ∀ {x : R.T₀} → R.𝟙 ≼ x → R.𝟙 ≼ τ x
posτ {x} p = ≼-trans p (proj₂ (O.tr⁻≈ x))

monoτ : ∀ {x y : R.T₀} → x ≼ y → τ x ≼ τ y
monoτ {x} {y} p = ≼-trans (proj₁ (O.tr⁻≈ x)) (≼-trans p (proj₂ (O.tr⁻≈ y)))

pair : (σ : Σ₁) → ∀ {X} → O.Gd X → (Ψ σ X R.≤ₚ O.ψ₁ X) × (O.ψ₁ X R.≤ₚ Ψ σ X)
pair σ O.gz = O.Ω≤Ω , O.Ω≤Ω
pair σ (O.gs gd) =
  R.l≤ (λ n → R.≤l n (O.iterₚ (proj₁ (pair σ gd)) n)) ,
  R.l≤ (λ n → R.≤l n (O.iterₚ (proj₂ (pair σ gd)) n))
pair σ (O.gl gd) =
  R.l≤ (λ n → R.≤l n (proj₁ (pair σ (gd n)))) ,
  R.l≤ (λ n → R.≤l n (proj₂ (pair σ (gd n))))
pair σ (O.gi law gb) rewrite bound-unique (σ L.zero) =
  R.ii (λ x y o q → R.trans (proj₁ (pair σ (gb (τ x) (posτ o))))
    (O.ψ₁-mono (O.SC.mo law (τ x) (τ y) (posτ o) (monoτ q)))) ,
  R.ii (λ x y o q → R.trans (O.ψ₁-mono (O.SC.mo law (τ x) (τ y) (posτ o) (monoτ q)))
    (proj₂ (pair σ (gb (τ y) (posτ (≼-trans o q))))))
pair σ (O.gu {y}) = O.B-mono (≼-refl y) , O.B-mono (≼-refl y)

base : (σ : Σ₁) → (X : R.T₁) → O.Ω₁ R.≤ₚ Ψ σ X
base σ L.zero = O.Ω≤Ω
base σ (L.suc X) = R.≤l 1 (base σ X)
base σ (L.lim f) = R.≤l 0 (base σ (f 0))
base σ (L.limᵢ L.zero f) rewrite bound-unique (σ L.zero) = R.i1 (base σ (f (τ R.𝟙)))
base σ (L.up L.zero y) = O.Ω≤B _ y

flat : (σ : Σ₁) → ∀ {σ′ : O.Sim₀} {X : R.T₁} {y : R.T₀} → R.Flat X → X ≼ y → Ψ σ X R.≤ₚ O.B σ′ y
flat σ {σ′} {y = y} fx z≼ = O.Ω≤B σ′ y
flat σ (R.fs fx) (s≼s q) = R.l≤ (λ n → R.≤l n (O.iterₚ (flat σ fx q) n))
flat σ fx (≼l n q) = R.≤l n (flat σ fx q)
flat σ (R.fl fx) (l≼ h) = R.l≤ (λ n → flat σ (fx n) (h n))
flat σ fx (≼i {p = ()} x ex q)
flat σ () (i≼ h)
flat σ fx (≼u {r = ()} q)
flat σ R.fu (u≼ q) = O.B-mono q

mono : (σ τ′ : Σ₁) → ∀ {X Y} → X R.≤ₚ Y → Ψ σ X R.≤ₚ Ψ τ′ Y
mono σ τ′ R.zz = O.Ω≤Ω
mono σ τ′ (R.ss q) = R.l≤ (λ n → R.≤l n (O.iterₚ (mono σ τ′ q) n))
mono σ τ′ (R.ws q) = R.≤l 1 (mono σ τ′ q)
mono σ τ′ (R.≤l n q) = R.≤l n (mono σ τ′ q)
mono σ τ′ (R.l≤ h) = R.l≤ (λ n → mono σ τ′ (h n))
mono σ τ′ (R.ii h) rewrite bound-unique (σ L.zero) | bound-unique (τ′ L.zero) =
  R.ii (λ x y o q → mono σ τ′ (h (τ x) (τ y) (posτ o) (monoτ q)))
mono σ τ′ (R.i1 q) rewrite bound-unique (τ′ L.zero) = R.i1 (mono σ τ′ q)
mono σ τ′ (R.fu fa q) = flat σ fa q
```
