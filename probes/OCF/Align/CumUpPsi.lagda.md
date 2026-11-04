# 带高度的世界: 折叠保结构等价

> 不含记号. 结论写在 [CumUp](CumUp.lagda.md). `ψQ`: 目标模 `≈ᴬ` 相同, 项 `≈`, 则输出 `≈`. 运行世界 $v$ 不进结论: 输出闭包的世界是规范的 (`m≈`). 对两边的项同时递归.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumUpPsi where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.BTBO using (injᵃ; injᵇ; injᶜ; module Trich)
open Trich renaming (_<_ to _<ᴺ_; <-dec to <ᴺ-dec) using (zero; suc)
open import OCF.Free.Level using (_≅_; z≅; s≅; l≅; lᵢ≅; upˡ; upʳ)
import OCF.Free.Level as FL
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; _≪_; ⊲-tr; z⊲; ≪∘; ≪S; ≪⊲; Rk; keep; rise; cmpN)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumReadBase using (Ord₀; next; _⊞_; cumA; cs)
open import OCF.Align.CumReadW using (one; Gw; gw; lgw; pos; g₀)
open import OCF.Align.CumUpW
open import OCF.Align.CumUpEq
```

## §1 累加保等价

```agda
⊞≈ : ∀ {a a′ b b′} → a ≈ᴬ a′ → b ≈ᴬ b′ → a ⊞ b ≈ᴬ a′ ⊞ b′
⊞≈ e z≈ = e
⊞≈ e (s≈ d) = s≈ (⊞≈ e d)
⊞≈ e (l≈ h) = l≈ (λ n → ⊞≈ e (h n))

cs≈ : ∀ {g g′} → (∀ n → g n ≈ᴬ g′ n) → ∀ n → cs g n ≈ᴬ cs g′ n
cs≈ h zero = h 0
cs≈ h (suc n) = ⊞≈ (cs≈ h n) (s≈ (h (suc n)))

cum≈ : ∀ {y y′ : Ord₀} → y ≅ y′ → cumA y ≈ᴬ cumA y′
cum≈ z≅ = z≈
cum≈ (s≅ e) = s≈ (cum≈ e)
cum≈ (l≅ h) = l≈ (cs≈ (λ n → cum≈ (h n)))
cum≈ (lᵢ≅ {p = ()} e h)
cum≈ (upˡ {r = ()} e)
cum≈ (upʳ {r = ()} e)

next≈ : ∀ {η η′} {y y′ : Ord₀} → η ≈ᴬ η′ → y ≅ y′ → next η y ≈ᴬ next η′ y′
next≈ e d = ⊞≈ e (s≈ (cum≈ d))

ord≅ : ∀ {u u′} (x : 𝓞 zero azero u) (y : 𝓞 zero azero u′) → x ≈ y → ord x ≅ ord y
ord≅ (ow p g x) y e = ord≅ x y e
ord≅ (oe () _) y e
ord≅ (oL () _ _ _) y e
ord≅ (oi () _) y e
ord≅ (od () _ _ _) y e
ord≅ X@o0 (ow p g y) e = ord≅ X y e
ord≅ o0 (oe () _) e
ord≅ o0 (oL () _ _ _) e
ord≅ o0 (oi () _) e
ord≅ o0 (od () _ _ _) e
ord≅ X@(os x) (ow p g y) e = ord≅ X y e
ord≅ (os x) (oe () _) e
ord≅ (os x) (oL () _ _ _) e
ord≅ (os x) (oi () _) e
ord≅ (os x) (od () _ _ _) e
ord≅ X@(ol F) (ow p g y) e = ord≅ X y e
ord≅ (ol F) (oe () _) e
ord≅ (ol F) (oL () _ _ _) e
ord≅ (ol F) (oi () _) e
ord≅ (ol F) (od () _ _ _) e
ord≅ X@(oc x h) (ow p g y) e = ord≅ X y e
ord≅ (oc x h) (oe () _) e
ord≅ (oc x h) (oL () _ _ _) e
ord≅ (oc x h) (oi () _) e
ord≅ (oc x h) (od () _ _ _) e
ord≅ o0 o0 e = z≅
ord≅ (os x) (os y) (_ , _ , _ , e) = s≅ (ord≅ x y e)
ord≅ (ol F) (ol G) e = l≅ (λ n → ord≅ (F n) (G n) (e n))
ord≅ (oc x h) (oc y h′) (_ , _ , _ , e , _) = ord≅ x y e
ord≅ o0 (os y) ()
ord≅ o0 (ol G) ()
ord≅ o0 (oc y h′) ()
ord≅ (os x) o0 ()
ord≅ (os x) (ol G) ()
ord≅ (os x) (oc y h′) ()
ord≅ (ol F) o0 ()
ord≅ (ol F) (os y) ()
ord≅ (ol F) (oc y h′) ()
ord≅ (oc x h) o0 ()
ord≅ (oc x h) (os y) ()
ord≅ (oc x h) (ol G) ()

em≈ : ∀ {u u′} {a b : Ord₀} → u ≈ᴬ u′ → a ≅ b → em {u} a ≈ em {u′} b
em≈ eu z≅ = tt
em≈ eu (s≅ e) = refl , z≈ , eu , em≈ eu e
em≈ eu (l≅ h) = λ n → em≈ eu (h n)
em≈ eu (lᵢ≅ {p = ()} e h)
em≈ eu (upˡ {r = ()} e)
em≈ eu (upʳ {r = ()} e)

ixs≈ : ∀ {m m′} (gm : Gw m) (gm′ : Gw m′) {y₀ y₀′ : Ord₀} {val : Ix m → Ord₀} {val′ : Ix m′ → Ord₀} → m ≈ᴬ m′ → y₀ ≅ y₀′ →
       (∀ i i′ → Ix.η i ≈ᴬ Ix.η i′ → val i ≅ val′ i′) → ∀ n → Ix.η (ixs gm y₀ val n) ≈ᴬ Ix.η (ixs gm′ y₀′ val′ n)
ixs≈ gm gm′ e e₀ h zero = next≈ e e₀
ixs≈ gm gm′ e e₀ h (suc n) = next≈ (ixs≈ gm gm′ e e₀ h n) (h _ _ (ixs≈ gm gm′ e e₀ h n))

yss≅ : ∀ {m m′} (gm : Gw m) (gm′ : Gw m′) {y₀ y₀′ : Ord₀} {val : Ix m → Ord₀} {val′ : Ix m′ → Ord₀} → m ≈ᴬ m′ → y₀ ≅ y₀′ →
       (∀ i i′ → Ix.η i ≈ᴬ Ix.η i′ → val i ≅ val′ i′) → ∀ n → yss gm y₀ val n ≅ yss gm′ y₀′ val′ n
yss≅ gm gm′ e e₀ h zero = e₀
yss≅ gm gm′ e e₀ h (suc n) = h _ _ (ixs≈ gm gm′ e e₀ h n)

plus≅ : ∀ {a a′ b b′ : Ord₀} → a ≅ a′ → b ≅ b′ → a +₀ b ≅ a′ +₀ b′
plus≅ e z≅ = e
plus≅ e (s≅ d) = s≅ (plus≅ e d)
plus≅ e (l≅ h) = l≅ (λ n → plus≅ e (h n))
plus≅ e (lᵢ≅ {p = ()} d h)
plus≅ e (upˡ {r = ()} d)
plus≅ e (upʳ {r = ()} d)

rep₀≅ : ∀ {y y′ : Ord₀} → y ≅ y′ → ∀ n → rep₀ y n ≅ rep₀ y′ n
rep₀≅ e zero = z≅
rep₀≅ e (suc zero) = e
rep₀≅ e (suc (suc m)) = plus≅ (rep₀≅ e (suc m)) e
```

## §2 `ψQ`

`NL q t`: 目标不是第 0 层. 第 0 层的目标走 `ψ₀`.

```agda
data NL : ℕ → A → Set where
  ns : ∀ {q t} → NL (suc q) t
  zs : ∀ {t} → NL zero (asuc t)
  zl : ∀ {f} → NL zero (alim f)

ψ⁰Q : ∀ {p a u p′ a′ u′ q t t′} (nl : NL q t) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Mis m u t a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ t′ a′ →
      t ≈ᴬ t′ → x ≈ y → ψ⁰ q t x gu m gm um tm am ≈ ψ⁰ q t′ y gu′ m′ gm′ um′ tm′ am′

ψmQ : ∀ {p a u p′ a′ u′ q t t′} (nl : NL q t) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
     v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v)
     v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (tv′ : t′ ⊲ v′) (av′ : a′ ⊲ v′) →
     t ≈ᴬ t′ → x ≈ y → ψᵐ q t x gu v gv uv tv av ≈ ψᵐ q t′ y gu′ v′ gv′ uv′ tv′ av′

ψ₀Q : ∀ {p a u p′ a′ u′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      v (gv : Gw v) (uv : u ⊲ v) (av : a ⊲ v)
      v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (av′ : a′ ⊲ v′) → x ≈ y → ψ₀ x gu v gv uv av ≅ ψ₀ y gu′ v′ gv′ uv′ av′

ψQ : ∀ {p a u p′ a′ u′ q t t′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
     v (gv : Gw v) (uv : u ⊲ v) (tv : t ⊲ v) (av : a ⊲ v)
     v′ (gv′ : Gw v′) (uv′ : u′ ⊲ v′) (tv′ : t′ ⊲ v′) (av′ : a′ ⊲ v′) →
     t ≈ᴬ t′ → x ≈ y → ψ q t x gu v gv uv tv av ≈ ψ q t′ y gu′ v′ gv′ uv′ tv′ av′
ψQ {q = zero} {t = azero} {t′ = azero} x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ z≈ e =
  ≈ow (em _) (pos gv′) g₀ (em _) (em≈ (≈ᴬ-refl one) (ψ₀Q x y gu gu′ v gv uv av v′ gv′ uv′ av′ e))
ψQ {q = zero} {t = asuc t} {t′ = asuc t′} x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ et e = ψmQ zs x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ et e
ψQ {q = zero} {t = alim t} {t′ = alim t′} x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ et e = ψmQ zl x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ et e
ψQ {q = suc q} x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ et e = ψmQ ns x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ et e

ψmQ {q = q} {t} {t′} nl x y gu gu′ v gv uv tv av v′ gv′ uv′ tv′ av′ et e
  with mx gu gv uv tv av | mx-is gu gv uv tv av | mx gu′ gv′ uv′ tv′ av′ | mx-is gu′ gv′ uv′ tv′ av′
... | mx′ m gm um tm am mv | is | mx′ m′ gm′ um′ tm′ am′ mv′ | is′ =
  ≈ow (ψ⁰ q t x gu m gm um tm am) mv′ gm′ (ψ⁰ q t′ y gu′ m′ gm′ um′ tm′ am′) (ψ⁰Q nl x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e)

-- 左边是包装: 走进去
ψ⁰lm : ∀ {p a u p′ a′ u′ q t t′} (nl : NL q t) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m)
      m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ t′ a′ →
      t ≈ᴬ t′ → x ≈ y → ψᵐ q t x gu m gm um tm am ≈ ψ⁰ q t′ y gu′ m′ gm′ um′ tm′ am′

ψ⁰rm : ∀ {p a u p′ a′ u′ q t t′} (nl : NL q t) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Mis m u t a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (am′ : a′ ⊲ m′) →
      t ≈ᴬ t′ → x ≈ y → ψ⁰ q t x gu m gm um tm am ≈ ψᵐ q t′ y gu′ m′ gm′ um′ tm′ am′

ψ⁰l : ∀ {p a u p′ a′ u′ q t t′} (nl : NL q t) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m)
      m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ t′ a′ →
      t ≈ᴬ t′ → x ≈ y → ψ q t x gu m gm um tm am ≈ ψ⁰ q t′ y gu′ m′ gm′ um′ tm′ am′
ψ⁰l {q = suc q} ns x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e = ψ⁰lm ns x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e
ψ⁰l {q = zero} zs x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e = ψ⁰lm zs x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e
ψ⁰l {q = zero} zl x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e = ψ⁰lm zl x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e

ψ⁰lm nl x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ is′ et e with mx gu gm um tm am | mx-is gu gm um tm am
... | mx′ m₁ g₁ u₁ t₁ a₁ _ | is₁ = ψ⁰Q nl x y gu gu′ m₁ g₁ u₁ t₁ a₁ is₁ m′ gm′ um′ tm′ am′ is′ et e

ψ⁰r : ∀ {p a u p′ a′ u′ q t t′} (nl : NL q t) (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Mis m u t a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (am′ : a′ ⊲ m′) →
      t ≈ᴬ t′ → x ≈ y → ψ⁰ q t x gu m gm um tm am ≈ ψ q t′ y gu′ m′ gm′ um′ tm′ am′
ψ⁰r {q = suc q} ns x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ et e = ψ⁰rm ns x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ et e
ψ⁰r {q = zero} zs x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ (s≈ d) e = ψ⁰rm zs x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ (s≈ d) e
ψ⁰r {q = zero} zl x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ (l≈ d) e = ψ⁰rm zl x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ (l≈ d) e

ψ⁰rm {q = q} {t} {t′} nl x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ et e with mx gu′ gm′ um′ tm′ am′ | mx-is gu′ gm′ um′ tm′ am′
... | mx′ m₁ g₁ u₁ t₁ a₁ mv | is₁ = ≈ow (ψ⁰ q t x gu m gm um tm am) mv g₁ (ψ⁰ q t′ y gu′ m₁ g₁ u₁ t₁ a₁) (ψ⁰Q nl x y gu gu′ m gm um tm am is m₁ g₁ u₁ t₁ a₁ is₁ et e)

ψLl : ∀ {p h k u p′ a′ u′ q t t′} (nl : NL q t) (j : h <ᴺ p) (x : Low p j k u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (km : k ⊲ m)
      m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ t′ a′ →
      t ≈ᴬ t′ → ELl j x y → ψL q t j x gu m gm um tm km ≈ ψ⁰ q t′ y gu′ m′ gm′ um′ tm′ am′
ψLl nl zero x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l nl x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e
ψLl nl (suc j) x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e = ψLl nl j x y gu gu′ m gm um tm km m′ gm′ um′ tm′ am′ is′ et e

ψLr : ∀ {p a u p′ h k u′ q t t′} (nl : NL q t) (x : 𝓞 p a u) (j : h <ᴺ p′) (y : Low p′ j k u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (tm : t ⊲ m) (am : a ⊲ m) → Mis m u t a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (tm′ : t′ ⊲ m′) (km′ : k ⊲ m′) →
      t ≈ᴬ t′ → ELr x j y → ψ⁰ q t x gu m gm um tm am ≈ ψL q t′ j y gu′ m′ gm′ um′ tm′ km′
ψLr nl x zero y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e = ψ⁰r nl x y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e
ψLr nl x (suc j) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e = ψLr nl x j y gu gu′ m gm um tm am is m′ gm′ um′ tm′ km′ et e

-- 左边包装
ψ⁰Q nl (oe es x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l nl x y gu gu′ m gm um tm (⊲-tr (C.suc C.self) am) m′ gm′ um′ tm′ am′ is′ et e
ψ⁰Q nl (oe (el n) x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l nl x y gu gu′ m gm um tm (⊲-tr (C.lim n C.self) am) m′ gm′ um′ tm′ am′ is′ et e
ψ⁰Q nl (oL j k e₁ x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLl nl j x y gu gu′ m gm um tm (⊲-tr e₁ um) m′ gm′ um′ tm′ am′ is′ et e
ψ⁰Q nl (ow p g x) y gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰l nl x y g gu′ m gm (⊲-tr p um) tm am m′ gm′ um′ tm′ am′ is′ et e
ψ⁰Q nl X@o0 (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) et e
ψ⁰Q nl X@o0 (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) et e
ψ⁰Q nl X@o0 (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr nl X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e₂ um′) et e
ψ⁰Q nl X@o0 (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q nl X@(os x) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) et e
ψ⁰Q nl X@(os x) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) et e
ψ⁰Q nl X@(os x) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr nl X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e₂ um′) et e
ψ⁰Q nl X@(os x) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q nl X@(ol F) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) et e
ψ⁰Q nl X@(ol F) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) et e
ψ⁰Q nl X@(ol F) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr nl X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e₂ um′) et e
ψ⁰Q nl X@(ol F) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q nl X@(oi r f) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) et e
ψ⁰Q nl X@(oi r f) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) et e
ψ⁰Q nl X@(oi r f) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr nl X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e₂ um′) et e
ψ⁰Q nl X@(oi r f) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q nl X@(od j k r f) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) et e
ψ⁰Q nl X@(od j k r f) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) et e
ψ⁰Q nl X@(od j k r f) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr nl X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e₂ um′) et e
ψ⁰Q nl X@(od j k r f) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
ψ⁰Q nl X@(oc x f) (oe es y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.suc C.self) am′) et e
ψ⁰Q nl X@(oc x f) (oe (el n) y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr (C.lim n C.self) am′) et e
ψ⁰Q nl X@(oc x f) (oL j₂ k₂ e₂ y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψLr nl X j₂ y gu gu′ m gm um tm am is m′ gm′ um′ tm′ (⊲-tr e₂ um′) et e
ψ⁰Q nl X@(oc x f) (ow p g y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ψ⁰r nl X y gu g m gm um tm am is m′ gm′ (⊲-tr p um′) tm′ am′ et e
-- 对角
ψ⁰Q {q = q} nl o0 o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e = ≈-Ωat q gm gm′ et
ψ⁰Q nl (os x) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (_ , ea , eu , e) =
  λ n → rep≈ et (m≈ is is′ um tm am um′ tm′ am′ eu et ea) (ψQ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ et e) gm gm′ n
ψ⁰Q nl (ol F) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et e =
  λ n → ψQ (F n) (G n) gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ et (e n)
ψ⁰Q {p} {a} {q = q} {t} {t′} nl (oi {k = k} r f) (oi {k = k′} r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (refl , ea , eu , ek , N) with <ᴺ-dec p q
... | injᵃ i = refl , refl , et , m≈ is is′ um tm am um′ tm′ am′ eu et ea , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (⊲-tr tm w) (⊲-tr am w) v′ g′ C.self (⊲-tr tm′ w′) (⊲-tr am′ w′) et
         (nI {r = r} {r′} {f} {f′} N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (W→ i i y y′ d)))
... | injᵇ _ = λ n → ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ et
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
  where
  M = m≈ is is′ um tm am um′ tm′ am′ eu et ea
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (⊲-tr (≪⊲ r) am) am) n ≈ chainᵒ gm′ (λ z₁ → ψ p k′ (f′ um′ gm′ (inS (≪S r′) z₁)) gm′ m′ gm′ C.self (⊲-tr (≪⊲ r′) am′) am′) n
  ch zero = ≈-Ωat p gm gm′ ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (⊲-tr (≪⊲ r) am) am m′ gm′ C.self (⊲-tr (≪⊲ r′) am′) am′ ek
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
... | injᶜ refl with cmpN (≪∘ r am) tm (lgw gm) | cmpN (≪∘ r′ am′) tm′ (lgw gm′)
...   | keep s | keep s′ = refl , et , m≈ is is′ um tm am um′ tm′ am′ eu et ea , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (⊲-tr tm w) (⊲-tr am w) v′ g′ C.self (⊲-tr tm′ w′) (⊲-tr am′ w′) et
         (nI {r = r} {r′} {f} {f′} N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (V→ (≪S s) (≪S s′) y y′ d)))
...   | keep s | rise q′ = ⊥-elim (clash s q′ ek et)
...   | rise q′ | keep s′ = ⊥-elim (clash s′ q′ (≈ᴬ-sym ek) (≈ᴬ-sym et))
...   | rise _ | rise _ = λ n → ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ et
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
  where
  M = m≈ is is′ um tm am um′ tm′ am′ eu et ea
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (⊲-tr (≪⊲ r) am) am) n ≈ chainᵒ gm′ (λ z₁ → ψ p k′ (f′ um′ gm′ (inS (≪S r′) z₁)) gm′ m′ gm′ C.self (⊲-tr (≪⊲ r′) am′) am′) n
  ch zero = ≈-Ωat p gm gm′ ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (⊲-tr (≪⊲ r) am) am m′ gm′ C.self (⊲-tr (≪⊲ r′) am′) am′ ek
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
ψ⁰Q {q = q} {t} {t′} nl (od {h = h₀} j k r f) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (_ , refl , ea , eu , ek , N) with <ᴺ-dec h₀ q
... | injᵃ i = refl , refl , et , m≈ is is′ um tm am um′ tm′ am′ eu et ea , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (⊲-tr tm w) (⊲-tr am w) v′ g′ C.self (⊲-tr tm′ w′) (⊲-tr am′ w′) et
         (nD {j = j} {j′} {f} {f′} N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (W→ i i y y′ d)))
... | injᵇ _ = λ n → ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ et
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
  where
  M = m≈ is is′ um tm am um′ tm′ am′ eu et ea
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (⊲-tr (≪⊲ r) um) am) n ≈ chainᵒ gm′ (λ z₁ → ψ h₀ k′ (f′ um′ gm′ (inL j′ z₁)) gm′ m′ gm′ C.self (⊲-tr (≪⊲ r′) um′) am′) n
  ch zero = ≈-Ωat h₀ gm gm′ ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (⊲-tr (≪⊲ r) um) am m′ gm′ C.self (⊲-tr (≪⊲ r′) um′) am′ ek
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
... | injᶜ refl with cmpN (≪∘ r um) tm (lgw gm) | cmpN (≪∘ r′ um′) tm′ (lgw gm′)
...   | keep s | keep s′ = refl , et , m≈ is is′ um tm am um′ tm′ am′ eu et ea , ek , (λ {v} {v′} w w′ g g′ vv y y′ d →
      ψQ (f (⊲-tr um w) g _) (f′ (⊲-tr um′ w′) g′ _) g g′ v g C.self (⊲-tr tm w) (⊲-tr am w) v′ g′ C.self (⊲-tr tm′ w′) (⊲-tr am′ w′) et
         (nD {j = j} {j′} {f} {f′} N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv _ _ (V→ (≪S s) (≪S s′) y y′ d)))
...   | keep s | rise q′ = ⊥-elim (clash s q′ ek et)
...   | rise q′ | keep s′ = ⊥-elim (clash s′ q′ (≈ᴬ-sym ek) (≈ᴬ-sym et))
...   | rise _ | rise _ = λ n → ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self tm am m′ gm′ C.self tm′ am′ et
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
  where
  M = m≈ is is′ um tm am um′ tm′ am′ eu et ea
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (⊲-tr (≪⊲ r) um) am) n ≈ chainᵒ gm′ (λ z₁ → ψ h₀ k′ (f′ um′ gm′ (inL j′ z₁)) gm′ m′ gm′ C.self (⊲-tr (≪⊲ r′) um′) am′) n
  ch zero = ≈-Ωat h₀ gm gm′ ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (⊲-tr (≪⊲ r) um) am m′ gm′ C.self (⊲-tr (≪⊲ r′) um′) am′ ek
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
ψ⁰Q nl (oc x f) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et (_ , ea , eu , e , N) =
  refl , et , m≈ is is′ um tm am um′ tm′ am′ eu et ea , ψQ x y gu gu′ m gm um tm am m′ gm′ um′ tm′ am′ et e ,
  (λ {v} {v′} w w′ g g′ vv → ψQ (f (⊲-tr um w) g) (f′ (⊲-tr um′ w′) g′) g g′ v g C.self (⊲-tr tm w) (⊲-tr am w) v′ g′ C.self (⊲-tr tm′ w′) (⊲-tr am′ w′) et (N (⊲-tr um w) (⊲-tr um′ w′) g g′ vv))
ψ⁰Q nl o0 (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl o0 (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl o0 (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl o0 (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl o0 (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (os x) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (os x) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (os x) (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (os x) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (os x) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (ol F) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (ol F) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (ol F) (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (ol F) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (ol F) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (oi r f) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (oi r f) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (oi r f) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (oi r f) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (oi r f) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (od j k r f) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (od j k r f) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (od j k r f) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (od j k r f) (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (od j k r f) (oc y f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (oc x f) o0 gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (oc x f) (os y) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (oc x f) (ol G) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (oc x f) (oi r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()
ψ⁰Q nl (oc x f) (od j′ k′ r′ f′) gu gu′ m gm um tm am is m′ gm′ um′ tm′ am′ is′ et ()

-- 第 0 层
ψ₀⁰Q : ∀ {p a u p′ a′ u′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
       m (gm : Gw m) (um : u ⊲ m) (am : a ⊲ m) → Mis m u azero a →
       ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ azero a′ →
       x ≈ y → ψ₀⁰ x gu m gm um am ≅ ψ₀⁰ y gu′ m′ gm′ um′ am′

ψ₀Q x y gu gu′ v gv uv av v′ gv′ uv′ av′ e
  with mx gu gv uv (z⊲ v) av | mx-is gu gv uv (z⊲ v) av | mx gu′ gv′ uv′ (z⊲ v′) av′ | mx-is gu′ gv′ uv′ (z⊲ v′) av′
... | mx′ m gm um tm am mv | is | mx′ m′ gm′ um′ tm′ am′ mv′ | is′ = ψ₀⁰Q x y gu gu′ m gm um am is m′ gm′ um′ am′ is′ e

ψ₀l : ∀ {p a u p′ a′ u′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (am : a ⊲ m)
      m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ azero a′ →
      x ≈ y → ψ₀ x gu m gm um am ≅ ψ₀⁰ y gu′ m′ gm′ um′ am′
ψ₀l x y gu gu′ m gm um am m′ gm′ um′ am′ is′ e with mx gu gm um (z⊲ m) am | mx-is gu gm um (z⊲ m) am
... | mx′ m₁ g₁ u₁ t₁ a₁ _ | is₁ = ψ₀⁰Q x y gu gu′ m₁ g₁ u₁ a₁ is₁ m′ gm′ um′ am′ is′ e

ψ₀r : ∀ {p a u p′ a′ u′} (x : 𝓞 p a u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
      m (gm : Gw m) (um : u ⊲ m) (am : a ⊲ m) → Mis m u azero a →
      ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : a′ ⊲ m′) →
      x ≈ y → ψ₀⁰ x gu m gm um am ≅ ψ₀ y gu′ m′ gm′ um′ am′
ψ₀r x y gu gu′ m gm um am is m′ gm′ um′ am′ e with mx gu′ gm′ um′ (z⊲ m′) am′ | mx-is gu′ gm′ um′ (z⊲ m′) am′
... | mx′ m₁ g₁ u₁ t₁ a₁ _ | is₁ = ψ₀⁰Q x y gu gu′ m gm um am is m₁ g₁ u₁ a₁ is₁ e

ψ₀Ll : ∀ {p h k u p′ a′ u′} (j : h <ᴺ p) (x : Low p j k u) (y : 𝓞 p′ a′ u′) (gu : Gw u) (gu′ : Gw u′)
       m (gm : Gw m) (um : u ⊲ m) (km : k ⊲ m)
       m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (am′ : a′ ⊲ m′) → Mis m′ u′ azero a′ →
       ELl j x y → ψ₀L j x gu m gm um km ≅ ψ₀⁰ y gu′ m′ gm′ um′ am′
ψ₀Ll zero x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e = ψ₀l x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e
ψ₀Ll (suc j) x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e = ψ₀Ll j x y gu gu′ m gm um km m′ gm′ um′ am′ is′ e

ψ₀Lr : ∀ {p a u p′ h k u′} (x : 𝓞 p a u) (j : h <ᴺ p′) (y : Low p′ j k u′) (gu : Gw u) (gu′ : Gw u′)
       m (gm : Gw m) (um : u ⊲ m) (am : a ⊲ m) → Mis m u azero a →
       ∀ m′ (gm′ : Gw m′) (um′ : u′ ⊲ m′) (km′ : k ⊲ m′) →
       ELr x j y → ψ₀⁰ x gu m gm um am ≅ ψ₀L j y gu′ m′ gm′ um′ km′
ψ₀Lr x zero y gu gu′ m gm um am is m′ gm′ um′ km′ e = ψ₀r x y gu gu′ m gm um am is m′ gm′ um′ km′ e
ψ₀Lr x (suc j) y gu gu′ m gm um am is m′ gm′ um′ km′ e = ψ₀Lr x j y gu gu′ m gm um am is m′ gm′ um′ km′ e

ψ₀⁰Q (oe es x) y gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀l x y gu gu′ m gm um (⊲-tr (C.suc C.self) am) m′ gm′ um′ am′ is′ e
ψ₀⁰Q (oe (el n) x) y gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀l x y gu gu′ m gm um (⊲-tr (C.lim n C.self) am) m′ gm′ um′ am′ is′ e
ψ₀⁰Q (oL j k e₁ x) y gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Ll j x y gu gu′ m gm um (⊲-tr e₁ um) m′ gm′ um′ am′ is′ e
ψ₀⁰Q (ow p g x) y gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀l x y g gu′ m gm (⊲-tr p um) am m′ gm′ um′ am′ is′ e
ψ₀⁰Q X@o0 (oe es y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (⊲-tr (C.suc C.self) am′) e
ψ₀⁰Q X@o0 (oe (el n) y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (⊲-tr (C.lim n C.self) am′) e
ψ₀⁰Q X@o0 (oL j₂ k₂ e₂ y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Lr X j₂ y gu gu′ m gm um am is m′ gm′ um′ (⊲-tr e₂ um′) e
ψ₀⁰Q X@o0 (ow p g y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu g m gm um am is m′ gm′ (⊲-tr p um′) am′ e
ψ₀⁰Q X@(os x) (oe es y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (⊲-tr (C.suc C.self) am′) e
ψ₀⁰Q X@(os x) (oe (el n) y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (⊲-tr (C.lim n C.self) am′) e
ψ₀⁰Q X@(os x) (oL j₂ k₂ e₂ y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Lr X j₂ y gu gu′ m gm um am is m′ gm′ um′ (⊲-tr e₂ um′) e
ψ₀⁰Q X@(os x) (ow p g y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu g m gm um am is m′ gm′ (⊲-tr p um′) am′ e
ψ₀⁰Q X@(ol F) (oe es y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (⊲-tr (C.suc C.self) am′) e
ψ₀⁰Q X@(ol F) (oe (el n) y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (⊲-tr (C.lim n C.self) am′) e
ψ₀⁰Q X@(ol F) (oL j₂ k₂ e₂ y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Lr X j₂ y gu gu′ m gm um am is m′ gm′ um′ (⊲-tr e₂ um′) e
ψ₀⁰Q X@(ol F) (ow p g y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu g m gm um am is m′ gm′ (⊲-tr p um′) am′ e
ψ₀⁰Q X@(oi r f) (oe es y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (⊲-tr (C.suc C.self) am′) e
ψ₀⁰Q X@(oi r f) (oe (el n) y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (⊲-tr (C.lim n C.self) am′) e
ψ₀⁰Q X@(oi r f) (oL j₂ k₂ e₂ y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Lr X j₂ y gu gu′ m gm um am is m′ gm′ um′ (⊲-tr e₂ um′) e
ψ₀⁰Q X@(oi r f) (ow p g y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu g m gm um am is m′ gm′ (⊲-tr p um′) am′ e
ψ₀⁰Q X@(od j k r f) (oe es y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (⊲-tr (C.suc C.self) am′) e
ψ₀⁰Q X@(od j k r f) (oe (el n) y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (⊲-tr (C.lim n C.self) am′) e
ψ₀⁰Q X@(od j k r f) (oL j₂ k₂ e₂ y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Lr X j₂ y gu gu′ m gm um am is m′ gm′ um′ (⊲-tr e₂ um′) e
ψ₀⁰Q X@(od j k r f) (ow p g y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu g m gm um am is m′ gm′ (⊲-tr p um′) am′ e
ψ₀⁰Q X@(oc x f) (oe es y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (⊲-tr (C.suc C.self) am′) e
ψ₀⁰Q X@(oc x f) (oe (el n) y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu gu′ m gm um am is m′ gm′ um′ (⊲-tr (C.lim n C.self) am′) e
ψ₀⁰Q X@(oc x f) (oL j₂ k₂ e₂ y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀Lr X j₂ y gu gu′ m gm um am is m′ gm′ um′ (⊲-tr e₂ um′) e
ψ₀⁰Q X@(oc x f) (ow p g y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = ψ₀r X y gu g m gm um am is m′ gm′ (⊲-tr p um′) am′ e
ψ₀⁰Q o0 o0 gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = s≅ z≅
ψ₀⁰Q (os x) (os y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ (_ , ea , eu , e) = l≅ (rep₀≅ (ψ₀Q x y gu gu′ m gm um am m′ gm′ um′ am′ e))
ψ₀⁰Q (ol F) (ol G) gu gu′ m gm um am is m′ gm′ um′ am′ is′ e = l≅ (λ n → ψ₀Q (F n) (G n) gu gu′ m gm um am m′ gm′ um′ am′ (e n))
ψ₀⁰Q {p} {a} (oi {k = k} r f) (oi {k = k′} r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ (refl , ea , eu , ek , N) =
  l≅ (λ n → ψ₀Q (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self am m′ gm′ C.self am′ (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n)))
  where
  M = m≈ is is′ um (z⊲ m) am um′ (z⊲ m′) am′ eu z≈ ea
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ p k (f um gm (inS (≪S r) z₁)) gm m gm C.self (⊲-tr (≪⊲ r) am) am) n ≈ chainᵒ gm′ (λ z₁ → ψ p k′ (f′ um′ gm′ (inS (≪S r′) z₁)) gm′ m′ gm′ C.self (⊲-tr (≪⊲ r′) am′) am′) n
  ch zero = ≈-Ωat p gm gm′ ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (⊲-tr (≪⊲ r) am) am m′ gm′ C.self (⊲-tr (≪⊲ r′) am′) am′ ek
      (nI {r = r} {r′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
ψ₀⁰Q (od {h = h₀} j k r f) (od j′ k′ r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ (_ , refl , ea , eu , ek , N) =
  l≅ (λ n → ψ₀Q (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self am m′ gm′ C.self am′ (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n)))
  where
  M = m≈ is is′ um (z⊲ m) am um′ (z⊲ m′) am′ eu z≈ ea
  ch : ∀ n → chainᵒ gm (λ z₁ → ψ h₀ k (f um gm (inL j z₁)) gm m gm C.self (⊲-tr (≪⊲ r) um) am) n ≈ chainᵒ gm′ (λ z₁ → ψ h₀ k′ (f′ um′ gm′ (inL j′ z₁)) gm′ m′ gm′ C.self (⊲-tr (≪⊲ r′) um′) am′) n
  ch zero = ≈-Ωat h₀ gm gm′ ek
  ch (suc n) = ψQ (f um gm _) (f′ um′ gm′ _) gm gm′ m gm C.self (⊲-tr (≪⊲ r) um) am m′ gm′ C.self (⊲-tr (≪⊲ r′) um′) am′ ek
      (nD {j = j} {j′} {f} {f′} N um um′ gm gm′ M _ _ (ch n))
ψ₀⁰Q (oc x f) (oc y f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ (_ , ea , eu , e , N) =
  l≅ (yss≅ gm gm′ (m≈ is is′ um (z⊲ m) am um′ (z⊲ m′) am′ eu z≈ ea) (ψ₀Q x y gu gu′ m gm um am m′ gm′ um′ am′ e)
    (λ i i′ ei → ψ₀Q (f (⊲-tr um (Ix.up i)) (Ix.gη i)) (f′ (⊲-tr um′ (Ix.up i′)) (Ix.gη i′)) (Ix.gη i) (Ix.gη i′)
        (Ix.η i) (Ix.gη i) C.self (⊲-tr am (Ix.up i)) (Ix.η i′) (Ix.gη i′) C.self (⊲-tr am′ (Ix.up i′))
        (N (⊲-tr um (Ix.up i)) (⊲-tr um′ (Ix.up i′)) (Ix.gη i) (Ix.gη i′) ei)))
ψ₀⁰Q o0 (os y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q o0 (ol G) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q o0 (oi r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q o0 (od j′ k′ r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q o0 (oc y f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (os x) o0 gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (os x) (ol G) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (os x) (oi r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (os x) (od j′ k′ r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (os x) (oc y f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (ol F) o0 gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (ol F) (os y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (ol F) (oi r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (ol F) (od j′ k′ r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (ol F) (oc y f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oi r f) o0 gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oi r f) (os y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oi r f) (ol G) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oi r f) (od j′ k′ r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oi r f) (oc y f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (od j k r f) o0 gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (od j k r f) (os y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (od j k r f) (ol G) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (od j k r f) (oi r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (od j k r f) (oc y f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oc x f) o0 gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oc x f) (os y) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oc x f) (ol G) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oc x f) (oi r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
ψ₀⁰Q (oc x f) (od j′ k′ r′ f′) gu gu′ m gm um am is m′ gm′ um′ am′ is′ ()
```
