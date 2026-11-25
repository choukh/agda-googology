# YiNext 验收：第 1、2 层的值下界，`T₃` 与 `T⁺`

**验收文件，档位：编译定理 (下界，不是同值) 与一条条件定理 (`FromBTBO.btbo⁺`，前提是模块参数)。** §1 到 §6 照主线 [YiLeanAccFin](YiLeanAccFin.lagda.md) 写在本前缀的块上 (`one≼` 多 `vΩ` 两行)。
§7：`read T₃ ≼ read T⁺`；`D.BTBOᴵ ≼ read T₃` 推出 `D.BTBOᴵ ≼ read T⁺`；`L.suc (read T₃) ≼ read T⁺`。
没有上界；`T⁺` 高于 `T₃` 的下界只是便宜的增长。闭项在 [YiNextTop](YiNextTop.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNextAcc where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
open import OCF.Lean.YiNextFold
open import OCF.Lean.YiNextTop using (F; T₃; T⁺; V₂)
import OCF.Align.Level as L
import OCF.Align.Value as V
import OCF.Align.RR4MonoFragment as MF
import OCF.Align.Diagonal as Diag
import OCF.Align.Uniform as Un
open import OCF.Align.YiLvValBase using (⟨_⟩; γ; γ-self; Ψ₀≼ψ⁰)
open import OCF.Align.YiLvVal2 using (T₀; T₁; ℓ₁; Ψ₀; Ψ₁; s≅⁻; l≅⁻; lᵢ≅⁻; tr⁻≼)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
open L using (_≅_)
open V using (_≼_; ≼-refl; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)

module D = Diag.Diagonal Un.Uniform
```

## 1 第 0 层

```agda
read : R → T₀
read G.zero = L.zero
read (G.suc a) = L.suc (read a)
read (G.lim f) = L.lim (λ n → read (f n))
read (G.lc () g)
read (G.em () a)
read G.top = L.suc L.zero

read-plus : ∀ x y → read (plus zero x y) ≅ (read x L.+ read y)
read-plus x G.zero = L.≅-refl⁰ (read x)
read-plus x (G.suc y) = L.s≅ (read-plus x y)
read-plus x (G.lim f) = L.l≅ (λ n → read-plus x (f n))
read-plus x (G.lc () g)
read-plus x (G.em () a)
read-plus x G.top = L.s≅ (L.≅-refl⁰ (read x))

plus≽ : ∀ θ {y : T₀} η → y ≼ read η → y ≼ read (plus zero θ η)
plus≽ θ η q = ≼-trans q (≼-trans (MF.≼-+ˡ (read θ) (read η)) (≅→≼ (L.≅-sym (read-plus θ η))))

read-copies : ∀ y {Y : T₀} → Y ≼ read y → ∀ n →
  iterᴸ (Y L.+_) L.zero (suc n) ≼ read (acc (λ _ z → plus zero y z) y n)
read-copies y low zero = low
read-copies y low (suc n) =
  ≼-trans (V.+-mono low (read-copies y low n)) (≅→≼ (L.≅-sym (read-plus y _)))

suc-lower : ∀ {k} {x : L.Ordᶜ k} a → L.ψ⁰ x ≼ read a → L.ψ⁰ (L.suc x) ≼ read (succ zero a)
suc-lower a low = l≼ λ where
  zero → z≼
  (suc n) → ≼l n (read-copies a low n)

firstn : ∀ j (w : Way zero j) gm gk {X : T₀} → X ≼ read (gm G.top) → X ≼ read (Ψn zero j w gm gk)
firstn j (keep () e) gm gk h
firstn j fold gm gk h = ≼l 0 h

first : ∀ k r (w : Way zero (lev k r)) gm gk {X : T₀} →
  X ≼ read (gm (Lay.tp (Lo k r))) → X ≼ read (ΨN zero k r w gm gk)
first (suc k) (inj₁ _) = firstn k
first (suc k) (inj₂ r) = first k r
first (lim f) (n , r) = first (f n) r
first (lc j g) (η , _ , r) = first (g η) r

firstΩ : ∀ (w : Way zero zero) K o {X : T₀} → X ≼ read (o 0) → X ≼ read (ΩT zero zero w K o)
firstΩ (keep () e) K o h
firstΩ fold K o h = ≼l 0 h

one≼ : ∀ {k} (V : Lv k) x ξ → V.𝟏 ≼ read (Ψ zero V x ξ)
one≼ V x G.zero = ≼-refl _
one≼ V x (G.suc a) = ≼l 0 (one≼ V x a)
one≼ V x (G.lim f) = ≼l 0 (one≼ V x (f 0))
one≼ {k} V x (G.lc r g) = first k r (x r) _ _ (one≼ V x (g _))
one≼ (vs V) x (G.em _ a) = one≼ V _ a
one≼ (vl V st) x (G.em n a) = one≼ (V n) _ a
one≼ v0 x G.top = ≼l 0 (≼-refl _)
one≼ {suc k} (vs V) x G.top = firstn k (x (inj₁ tt)) _ _ (one≼ V _ G.top)
one≼ (vl V st) x G.top = ≼l 0 (one≼ (V 0) _ G.top)
one≼ (vΩ V u) x (G.em (η , l) a) = one≼ (V η l) _ a
one≼ (vΩ V u) x G.top = firstΩ (x p₀) _ _ (one≼ (V G.top tt) (λ _ → fold) G.top)

fold₀ : ∀ x a → L.ψ⁰ (read a) ≼ read (Ψ zero v0 x a)
fold₀ x G.zero = ≼-refl _
fold₀ x (G.suc a) = suc-lower (Ψ zero v0 x a) (fold₀ x a)
fold₀ x (G.lim f) = l≼ (λ n → ≼l n (fold₀ x (f n)))
fold₀ x (G.lc () g)
fold₀ x (G.em () a)
fold₀ x G.top = suc-lower G.top (≼-refl _)
```

## 2 ψ₀(Ω₁)

`F (fin 1)` 的链在第 0 层，从 `top` (读成 1) 起；参照 `γ 0` 从 `Ω ⟨0⟩ = 1` 起，每步 `Ψ 0`。

```agda
fin : ℕ → R
fin zero = G.zero
fin (suc n) = G.suc (fin n)

chain₁ : ∀ n → γ 0 n ≼ read (chain zero (Ψ zero v0 (self zero)) n)
chain₁ zero = ≼-refl _
chain₁ (suc n) = ≼-trans (Ψ₀≼ψ⁰ (γ 0 n)) (plus≽ _ _
  (≼-trans (V.ψ⁰-mono⁰ (chain₁ n)) (fold₀ (self zero) (chain zero (Ψ zero v0 (self zero)) n))))

lower₁ : L.ψ⁰ (L.Ω ⟨ 1 ⟩) ≼ read (F (fin 1) tt)
lower₁ = l≼ (λ n → ≼l n (≼-trans (V.ψ⁰-mono⁰ (chain₁ n)) (fold₀ _ _)))
```

## 3 第 1 层的逐点前序

```agda
L1 : LF
L1 = suc zero

R₁ : Set
R₁ = Raw L1

infix 4 _⊴_
data _⊴_ : ∀ {k} → L.Ordᶜ k → R₁ → Set where
  z⊴ : ∀ {k} {η : R₁} → _⊴_ {k} L.zero η
  s⊴s : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → L.suc x ⊴ G.suc η
  ⊴s : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → x ⊴ G.suc η
  ⊴l : ∀ {k} {x : L.Ordᶜ k} {H : ℕ → R₁} n → x ⊴ H n → x ⊴ G.lim H
  l⊴ : ∀ {k} {H : ℕ → L.Ordᶜ k} {η} → (∀ n → H n ⊴ η) → L.lim H ⊴ η
  ⊴b : ∀ {k} {x : L.Ordᶜ k} {g : R → R₁} → x ⊴ g G.top → x ⊴ G.lc (inj₁ tt) g
  nd : ∀ {f : T₀ → T₁} {g : R → R₁} → (∀ (y : T₀) a → y ≼ read a → f y ⊴ g a) →
    L.limᵢ {i = L.zero} L.zero f ⊴ G.lc (inj₁ tt) g
  nt : ∀ {f : T₀ → T₁} → (∀ (y : T₀) a → y ≼ read a → f y ⊴ G.em tt a) →
    L.limᵢ {i = L.zero} L.zero f ⊴ G.top
  em⊴ : ∀ {y : T₀} {a} → y ≼ read a → y ⊴ G.em tt a
  u⊴ : ∀ {y : T₀} {η} → y ⊴ η → L.up {k = L.zero} L.zero y ⊴ η

⊴-embed : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → ∀ a → x ⊴ plus L1 η (G.em tt a)
⊴-embed p G.zero = p
⊴-embed p (G.suc a) = ⊴s (⊴-embed p a)
⊴-embed p (G.lim f) = ⊴l 0 (⊴-embed p (f 0))
⊴-embed p (G.lc () g)
⊴-embed p (G.em () a)
⊴-embed p G.top = ⊴s p

⊴-+ʳ : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → ∀ η′ → x ⊴ plus L1 η η′
⊴-+ʳ p G.zero = p
⊴-+ʳ p (G.suc y) = ⊴s (⊴-+ʳ p y)
⊴-+ʳ p (G.lim f) = ⊴l 0 (⊴-+ʳ p (f 0))
⊴-+ʳ p (G.lc (inj₁ _) g) = ⊴b (⊴-+ʳ p (g G.top))
⊴-+ʳ p (G.lc (inj₂ ()) g)
⊴-+ʳ p (G.em _ a) = ⊴-embed p a
⊴-+ʳ p G.top = ⊴b (⊴s p)

em-shift : ∀ θ {y b : T₀} → y ≼ b → ∀ a → b ≡ read a → y ⊴ plus L1 θ (G.em tt a)
em-shift θ z≼ a q = z⊴
em-shift θ (s≼s p) (G.suc a) refl = s⊴s (em-shift θ p a refl)
em-shift θ (s≼s p) G.top refl = s⊴s (em-shift θ p G.zero refl)
em-shift θ (≼l n p) (G.lim f) refl = ⊴l n (em-shift θ p (f n) refl)
em-shift θ (l≼ h) a q = l⊴ (λ n → em-shift θ (h n) a q)
em-shift θ (≼i {p = ()} x ex p) a q
em-shift θ (i≼ {p = ()} h) a q
em-shift θ (≼u {r = ()} p) a q
em-shift θ (u≼ {r = ()} p) a q

σ₀ : L.Simᴵ L.zero ℓ₁
σ₀ q = L.suc q

add-em : ∀ {x : T₁} {η} → x ⊴ η → ∀ {y b : T₀} → y ≼ b → ∀ a → b ≡ read a →
  L.add x σ₀ y ⊴ plus L1 η (G.em tt a)
add-em px z≼ a q = ⊴-embed px a
add-em px (s≼s p) (G.suc a) refl = s⊴s (add-em px p a refl)
add-em px (s≼s p) G.top refl = s⊴s (add-em px p G.zero refl)
add-em px (≼l n p) (G.lim f) refl = ⊴l n (add-em px p (f n) refl)
add-em px (l≼ h) a q = l⊴ (λ n → add-em px (h n) a q)
add-em px (≼i {p = ()} x ex p) a q
add-em px (i≼ {p = ()} h) a q
add-em px (≼u {r = ()} p) a q
add-em px (u≼ {r = ()} p) a q

⊴-add₀ : ∀ {x : T₁} {η} → x ⊴ η → ∀ {y : T₀} {η′} → y ⊴ η′ → L.add x σ₀ y ⊴ plus L1 η η′
⊴-add₀ px {η′ = η′} z⊴ = ⊴-+ʳ px η′
⊴-add₀ px (s⊴s q) = s⊴s (⊴-add₀ px q)
⊴-add₀ px (⊴s q) = ⊴s (⊴-add₀ px q)
⊴-add₀ px (⊴l n q) = ⊴l n (⊴-add₀ px q)
⊴-add₀ px (l⊴ h) = l⊴ (λ n → ⊴-add₀ px (h n))
⊴-add₀ px (⊴b h) = ⊴b (⊴-add₀ px h)
⊴-add₀ px (em⊴ {a = a} q) = add-em px q a refl

⊴-add₁ : ∀ {x : T₁} {η} → x ⊴ η → ∀ {x′ : T₁} {η′} → x′ ⊴ η′ → (x L.+ x′) ⊴ plus L1 η η′
⊴-add₁ px {η′ = η′} z⊴ = ⊴-+ʳ px η′
⊴-add₁ px (s⊴s q) = s⊴s (⊴-add₁ px q)
⊴-add₁ px (⊴s q) = ⊴s (⊴-add₁ px q)
⊴-add₁ px (⊴l n q) = ⊴l n (⊴-add₁ px q)
⊴-add₁ px (l⊴ h) = l⊴ (λ n → ⊴-add₁ px (h n))
⊴-add₁ px (⊴b h) = ⊴b (⊴-add₁ px h)
⊴-add₁ px (nd h) = nd (λ y a q → ⊴-add₁ px (h y a q))
⊴-add₁ px (nt h) = nd (λ y a q → ⊴-add₁ px (h y a q))
⊴-add₁ px (u⊴ q) = ⊴-add₀ px q

⊴-+ˡ : ∀ θ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → x ⊴ plus L1 θ η
⊴-+ˡ θ z⊴ = z⊴
⊴-+ˡ θ (s⊴s p) = s⊴s (⊴-+ˡ θ p)
⊴-+ˡ θ (⊴s p) = ⊴s (⊴-+ˡ θ p)
⊴-+ˡ θ (⊴l n p) = ⊴l n (⊴-+ˡ θ p)
⊴-+ˡ θ (l⊴ h) = l⊴ (λ n → ⊴-+ˡ θ (h n))
⊴-+ˡ θ (⊴b h) = ⊴b (⊴-+ˡ θ h)
⊴-+ˡ θ (nd h) = nd (λ y a q → ⊴-+ˡ θ (h y a q))
⊴-+ˡ θ (nt h) = nd (λ y a q → ⊴-+ˡ θ (h y a q))
⊴-+ˡ θ (em⊴ {a = a} q) = em-shift θ q a refl
⊴-+ˡ θ (u⊴ p) = u⊴ (⊴-+ˡ θ p)
```

## 4 目标层 1 的折叠

推进用的是目标为第 1 层自己的派发 `self L1`：层号 0 的结点原样保留在根位置。

```agda
Φ : R₁ → R₁
Φ = Ψ L1 (vs v0) (self L1)

Ω⊴top : L.Ω ℓ₁ ⊴ G.top
Ω⊴top = nt (λ y a q → u⊴ (em⊴ q))

Ω⊴Φ₀ : ∀ x a → L.Ω ℓ₁ ⊴ Ψ L1 v0 x a
Ω⊴Φ₀ x G.zero = Ω⊴top
Ω⊴Φ₀ x (G.suc a) = ⊴l 0 (Ω⊴Φ₀ x a)
Ω⊴Φ₀ x (G.lim f) = ⊴l 0 (Ω⊴Φ₀ x (f 0))
Ω⊴Φ₀ x (G.lc () g)
Ω⊴Φ₀ x (G.em () a)
Ω⊴Φ₀ x G.top = ⊴l 0 Ω⊴top

Ω⊴Φ : ∀ η → L.Ω ℓ₁ ⊴ Φ η
Ω⊴Φ G.zero = Ω⊴top
Ω⊴Φ (G.suc η) = ⊴l 0 (Ω⊴Φ η)
Ω⊴Φ (G.lim f) = ⊴l 0 (Ω⊴Φ (f 0))
Ω⊴Φ (G.lc (inj₁ _) g) = ⊴b (Ω⊴Φ (g G.top))
Ω⊴Φ (G.lc (inj₂ ()) g)
Ω⊴Φ (G.em _ a) = Ω⊴Φ₀ _ a
Ω⊴Φ G.top = ⊴b (Ω⊴Φ₀ _ G.top)

copies-⊴ : ∀ {A : T₁} {β} → A ⊴ β → ∀ n →
  iterᴸ (A L.+_) L.zero (suc n) ⊴ acc (λ _ z → plus L1 β z) β n
copies-⊴ p zero = p
copies-⊴ p (suc n) = ⊴-add₁ p (copies-⊴ p n)

suc-step : ∀ {A : T₁} {β} → A ⊴ β → L.lim (iterᴸ (A L.+_) L.zero) ⊴ succ L1 β
suc-step p = l⊴ λ where
  zero → z⊴
  (suc n) → ⊴l n (copies-⊴ p n)

Ψ₀⊴Φ₀ : ∀ x {y b : T₀} → y ≼ b → ∀ a → b ≡ read a → Ψ₀ y ⊴ Ψ L1 v0 x a
Ψ₀⊴Φ₀ x z≼ a q = Ω⊴Φ₀ x a
Ψ₀⊴Φ₀ x (s≼s p) (G.suc a) refl = suc-step (Ψ₀⊴Φ₀ x p a refl)
Ψ₀⊴Φ₀ x (s≼s p) G.top refl = suc-step (Ψ₀⊴Φ₀ x p G.zero refl)
Ψ₀⊴Φ₀ x (≼l n p) (G.lim f) refl = ⊴l n (Ψ₀⊴Φ₀ x p (f n) refl)
Ψ₀⊴Φ₀ x (l≼ h) a q = l⊴ (λ n → Ψ₀⊴Φ₀ x (h n) a q)
Ψ₀⊴Φ₀ x (≼i {p = ()} z ez p) a q
Ψ₀⊴Φ₀ x (i≼ {p = ()} h) a q
Ψ₀⊴Φ₀ x (≼u {r = ()} p) a q
Ψ₀⊴Φ₀ x (u≼ {r = ()} p) a q

Ψ₀⊴Φ : ∀ {y : T₀} {η} → y ⊴ η → Ψ₀ y ⊴ Φ η
Ψ₀⊴Φ {η = η} z⊴ = Ω⊴Φ η
Ψ₀⊴Φ (s⊴s p) = suc-step (Ψ₀⊴Φ p)
Ψ₀⊴Φ (⊴s p) = ⊴l 0 (Ψ₀⊴Φ p)
Ψ₀⊴Φ (⊴l n p) = ⊴l n (Ψ₀⊴Φ p)
Ψ₀⊴Φ (l⊴ h) = l⊴ (λ n → Ψ₀⊴Φ (h n))
Ψ₀⊴Φ (⊴b h) = ⊴b (Ψ₀⊴Φ h)
Ψ₀⊴Φ (em⊴ {a = a} q) = Ψ₀⊴Φ₀ _ q a refl

Ψ₁⊴Φ : ∀ {x : T₁} {η} → x ⊴ η → Ψ₁ x ⊴ Φ η
Ψ₁⊴Φ {η = η} z⊴ = Ω⊴Φ η
Ψ₁⊴Φ (s⊴s p) = suc-step (Ψ₁⊴Φ p)
Ψ₁⊴Φ (⊴s p) = ⊴l 0 (Ψ₁⊴Φ p)
Ψ₁⊴Φ (⊴l n p) = ⊴l n (Ψ₁⊴Φ p)
Ψ₁⊴Φ (l⊴ h) = l⊴ (λ n → Ψ₁⊴Φ (h n))
Ψ₁⊴Φ (⊴b h) = ⊴b (Ψ₁⊴Φ h)
Ψ₁⊴Φ (nd h) = nd (λ y a q → Ψ₁⊴Φ (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) q)))
Ψ₁⊴Φ (nt h) = nd (λ y a q → Ψ₁⊴Φ (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) q)))
Ψ₁⊴Φ (u⊴ p) = Ψ₀⊴Φ p
```

## 5 目标层 0 的折叠把关系送到值前序

层号 0 的结点：参照的链从 1 起每步 `ψ` 一次，被验收一侧的链从 `top` 起每步加上推进用的折叠，同步归纳。

```agda
module NodeLower (f : T₀ → T₁) (same : ∀ y → f y ≅ f y) (gm gk : R → R)
  (hk : ∀ (y : T₀) a → y ≼ read a → L.ψ⁰ (f y) ≼ read (gk a))
  (hm : ∀ (y : T₀) a → y ≼ read a → L.ψ⁰ (f y) ≼ read (gm a)) where

  ref-step : T₀ → T₀
  ref-step y = L.ψ {i = L.zero} {k = ℓ₁} {ℓ = ℓ₁} L.zero (λ r → r) (f y)

  δ : ℕ → T₀
  δ = iterᴸ ref-step (L.suc L.zero)

  step≤ : ∀ y → ref-step y ≼ L.ψ⁰ (f y)
  step≤ y = ≅→≼ (L.≅-sym (L.ψ⁰≅ψ {p = L.zero} {σ = λ r → r} (same y)))

  chain-lower : ∀ n → δ n ≼ read (chain zero gk n)
  chain-lower zero = ≼-refl _
  chain-lower (suc n) = ≼-trans (step≤ (δ n)) (plus≽ _ _ (hk (δ n) _ (chain-lower n)))

  result : ∀ w → L.ψ⁰ (L.limᵢ {i = L.zero} L.zero f) ≼ read (Ψn zero zero w gm gk)
  result (keep () e)
  result fold = l≼ (λ n → ≼l n (hm (δ n) _ (chain-lower n)))

fold-lower : ∀ (x : Ext zero L1) {k} {X : L.Ordᶜ k} {η} → X ⊴ η → X ≅ X →
  L.ψ⁰ X ≼ read (Ψ zero (vs v0) x η)
fold-lower x {η = η} z⊴ s = one≼ (vs v0) x η
fold-lower x {η = G.suc η} (s⊴s p) s = suc-lower (Ψ zero (vs v0) x η) (fold-lower x p (s≅⁻ s))
fold-lower x (⊴s p) s = ≼l 0 (fold-lower x p s)
fold-lower x (⊴l n p) s = ≼l n (fold-lower x p s)
fold-lower x (l⊴ h) s = l≼ (λ n → fold-lower x (h n) (l≅⁻ s n))
fold-lower x (⊴b h) s = firstn zero (x (inj₁ tt)) _ _ (fold-lower x h s)
fold-lower x (nd {f = f} h) s = NodeLower.result f (lᵢ≅⁻ s) _ _
  (λ y a q → fold-lower (cmp (vs v0) (inj₁ tt)) (h y a q) (lᵢ≅⁻ s y))
  (λ y a q → fold-lower x (h y a q) (lᵢ≅⁻ s y)) (x (inj₁ tt))
fold-lower x (nt {f = f} h) s = NodeLower.result f (lᵢ≅⁻ s) _ _
  (λ y a q → fold-lower (cmp (vs v0) (inj₁ tt)) (h y a q) (lᵢ≅⁻ s y))
  (λ y a q → fold-lower x (h y a q) (lᵢ≅⁻ s y)) (x (inj₁ tt))
fold-lower x {η = G.em tt a} (em⊴ q) s = ≼-trans (V.ψ⁰-mono⁰ q) (fold₀ _ a)
fold-lower x (u⊴ {y = y} p) s = fold-lower x {X = y} p (L.≅-refl⁰ y)
```

## 6 ψ₀(Ω₂)

`F (fin 2)` 的链在第 1 层，从 `top` 起，每步加上目标为第 1 层的折叠 `Φ`；参照 `γ 1` 从 `Ω ⟨1⟩` 起，每步 `Ψ 1`。

```agda
chain₂ : ∀ i → γ 1 i ⊴ chain L1 Φ i
chain₂ zero = Ω⊴top
chain₂ (suc i) = ⊴-+ˡ (chain L1 Φ i) (Ψ₁⊴Φ (chain₂ i))

lower₂ : L.ψ⁰ (L.Ω ⟨ 2 ⟩) ≼ read (F (fin 2) tt)
lower₂ = l≼ (λ i → ≼l i (fold-lower (λ r → fold) {X = γ 1 i} (chain₂ i) (γ-self 1 i)))
```

## 7 塔的第 3 项与 `T⁺`

`T₃` 的两条照主线。`T⁺` 的第 0 项定义性地是 `T₃` (V1)；以 "BTBO 的参照 ≼ 读回的 `T₃`" 为前提推出对 `T⁺` 的同一条 (V2)。
V4：`T⁺` 的第 1 项沿根结点、`top` 的保留结点、ω 倍各取第 0 项，走到 `T₃ + T₃`，所以 `T₃ + 1 ≼ T⁺` (便宜的增长，不带强度)。

```agda
T₃-Ω₁ : L.ψ⁰ (L.Ω ⟨ 1 ⟩) ≼ read T₃
T₃-Ω₁ = ≼l 0 lower₁

T₃-Ω₂ : L.ψ⁰ (L.Ω ⟨ 2 ⟩) ≼ read T₃
T₃-Ω₂ = ≼l 1 (≼l 0 (≼l 0 lower₂))

T₃≼T⁺ : read T₃ ≼ read T⁺
T₃≼T⁺ = ≼l 0 (≼-refl _)

T⁺-Ω₂ : L.ψ⁰ (L.Ω ⟨ 2 ⟩) ≼ read T⁺
T⁺-Ω₂ = ≼-trans T₃-Ω₂ T₃≼T⁺

module FromBTBO (bt : D.BTBOᴵ ≼ read T₃) where
  btbo⁺ : D.BTBOᴵ ≼ read T⁺
  btbo⁺ = ≼-trans bt T₃≼T⁺

T₃+1≼T⁺ : L.suc (read T₃) ≼ read T⁺
T₃+1≼T⁺ = ≼l 1 (≼l 0 (≼l 0 (≼l 0 (≼l 1 (≼-trans
  (V.+-mono (≼-refl (read T₃)) (one≼ V₂ (λ _ → fold) G.top)) (≅→≼ (L.≅-sym (read-plus T₃ T₃))))))))
```
