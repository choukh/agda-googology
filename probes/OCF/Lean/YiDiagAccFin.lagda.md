# YiDiag 验收：第 2 层闭项的值下界

**验收文件，档位：编译定理 (下界，不是同值)。** `lower₂`：参照 `ψ⁰ (Ω ⟨2⟩)` ≼ 读回的 `F (fin 2)`；推论 `T₃-Ω₂`：ψ₀(Ω₂) ≼ 读回的 `T₃`。办法照 [YiLeanAccFin](YiLeanAccFin.lagda.md)：跨两族的逐点前序 `_⊴_`，
两条链同步归纳；改动是 ω 倍从零起 (取第 1 项而不是第 0 项)、链不累加 (不再要 `⊴-+ˡ`)、目标层 0 只有折叠。第 1 层的同值在 [YiDiagAcc](YiDiagAcc.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDiagAccFin where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiDiagCore
open import OCF.Lean.YiDiagFold
open import OCF.Lean.YiDiagTw3 using (R; F; pt; T₃; root-mono)
open import OCF.Lean.YiDiagAcc using (read; read-plus; fold-read; cp→⊑; lower₁)
import OCF.Align.Level as L
import OCF.Align.Value as V
open import OCF.Align.YiLvValBase using (⟨_⟩; γ; γ-self)
open import OCF.Align.YiLvVal2 using (T₀; T₁; ℓ₁; Ψ₀; Ψ₁; s≅⁻; l≅⁻; lᵢ≅⁻; tr⁻≼)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
open L using (_≅_)
open V using (_≼_; ≼-refl; ≼-trans; ≅→≼; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
```

## 1 第 0 层

```agda
suc-lower : ∀ {k} {x : L.Ordᶜ k} a → L.ψ⁰ x ≼ read a → L.ψ⁰ (L.suc x) ≼ read (mult zero a)
suc-lower {x = x} a low = l≼ (λ n → ≼l n (cp n))
  where
  cp : ∀ n → iterᴸ (L.ψ⁰ x L.+_) L.zero n ≼ read (iter (plus zero a) G.zero n)
  cp zero = z≼
  cp (suc n) = ≼-trans (V.+-mono low (cp n)) (≅→≼ (L.≅-sym (read-plus a _)))

firstn : ∀ j (w : Way zero j) gm gk {X : T₀} → X ≼ read (gm G.top) → X ≼ read (Ψn zero j w gm gk)
firstn j w gm gk h = ≼l 0 h

first : ∀ k r (w : Way zero (lev k r)) gm gk {X : T₀} →
  X ≼ read (gm (Lay.tp (Lo k r))) → X ≼ read (ΨN zero k r w gm gk)
first (suc k) (inj₁ _) = firstn k
first (suc k) (inj₂ r) = first k r
first (lim f) (n , r) = first (f n) r
first (lc j g) (η , _ , r) = first (g η) r

one≼ : ∀ {k} (V : Lv k) x ξ → V.𝟏 ≼ read (Ψ zero V x ξ)
one≼ V x G.zero = ≼-refl _
one≼ V x (G.suc a) = ≼l 1 (one≼ V x a)
one≼ V x (G.lim f) = ≼l 0 (one≼ V x (f 0))
one≼ {k} V x (G.lc r g) = first k r (x r) _ _ (one≼ V x (g _))
one≼ (vs V) x (G.em _ a) = one≼ V _ a
one≼ (vl V) x (G.em n a) = one≼ (V n) _ a
one≼ v0 x G.top = ≼l 1 (≼-refl _)
one≼ {suc k} (vs V) x G.top =
  firstn k (x (inj₁ tt)) (λ η → Ψ zero V (λ r → x (inj₂ r)) η) (λ η → Ψ k V (self k) η) (one≼ V _ G.top)
one≼ (vl V) x G.top = ≼l 0 (one≼ (V 0) _ G.top)

fold₀ : ∀ x a → L.ψ⁰ (read a) ≼ read (Ψ zero v0 x a)
fold₀ x a = ≅→≼ (L.≅-sym (fold-read x a))
```

## 2 第 1 层的逐点前序

与 [YiLeanAccFin](YiLeanAccFin.lagda.md) §3 相同 (去掉只为累加的链用的 `em-shift`, `⊴-+ˡ`)。

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
```

## 3 目标层 1 的折叠

ω 倍从零起：`mult L1 β` 的第 1 项就是 `β`，所以 "某项之下" 的情形取第 1 项。

```agda
Φ : R₁ → R₁
Φ = Ψ L1 (vs v0) (self L1)

Ω⊴top : L.Ω ℓ₁ ⊴ G.top
Ω⊴top = nt (λ y a q → u⊴ (em⊴ q))

Ω⊴Φ₀ : ∀ x a → L.Ω ℓ₁ ⊴ Ψ L1 v0 x a
Ω⊴Φ₀ x G.zero = Ω⊴top
Ω⊴Φ₀ x (G.suc a) = ⊴l 1 (Ω⊴Φ₀ x a)
Ω⊴Φ₀ x (G.lim f) = ⊴l 0 (Ω⊴Φ₀ x (f 0))
Ω⊴Φ₀ x (G.lc () g)
Ω⊴Φ₀ x (G.em () a)
Ω⊴Φ₀ x G.top = ⊴l 1 Ω⊴top

Ω⊴Φ : ∀ η → L.Ω ℓ₁ ⊴ Φ η
Ω⊴Φ G.zero = Ω⊴top
Ω⊴Φ (G.suc η) = ⊴l 1 (Ω⊴Φ η)
Ω⊴Φ (G.lim f) = ⊴l 0 (Ω⊴Φ (f 0))
Ω⊴Φ (G.lc (inj₁ _) g) = ⊴b (Ω⊴Φ (g G.top))
Ω⊴Φ (G.lc (inj₂ ()) g)
Ω⊴Φ (G.em _ a) = Ω⊴Φ₀ _ a
Ω⊴Φ G.top = ⊴b (Ω⊴Φ₀ _ G.top)

suc-step : ∀ {A : T₁} {β} → A ⊴ β → L.lim (iterᴸ (A L.+_) L.zero) ⊴ mult L1 β
suc-step {A} {β} p = l⊴ (λ n → ⊴l n (cp n))
  where
  cp : ∀ n → iterᴸ (A L.+_) L.zero n ⊴ iter (plus L1 β) G.zero n
  cp zero = z⊴
  cp (suc n) = ⊴-add₁ p (cp n)

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
Ψ₀⊴Φ (⊴s p) = ⊴l 1 (Ψ₀⊴Φ p)
Ψ₀⊴Φ (⊴l n p) = ⊴l n (Ψ₀⊴Φ p)
Ψ₀⊴Φ (l⊴ h) = l⊴ (λ n → Ψ₀⊴Φ (h n))
Ψ₀⊴Φ (⊴b h) = ⊴b (Ψ₀⊴Φ h)
Ψ₀⊴Φ (em⊴ {a = a} q) = Ψ₀⊴Φ₀ _ q a refl

Ψ₁⊴Φ : ∀ {x : T₁} {η} → x ⊴ η → Ψ₁ x ⊴ Φ η
Ψ₁⊴Φ {η = η} z⊴ = Ω⊴Φ η
Ψ₁⊴Φ (s⊴s p) = suc-step (Ψ₁⊴Φ p)
Ψ₁⊴Φ (⊴s p) = ⊴l 1 (Ψ₁⊴Φ p)
Ψ₁⊴Φ (⊴l n p) = ⊴l n (Ψ₁⊴Φ p)
Ψ₁⊴Φ (l⊴ h) = l⊴ (λ n → Ψ₁⊴Φ (h n))
Ψ₁⊴Φ (⊴b h) = ⊴b (Ψ₁⊴Φ h)
Ψ₁⊴Φ (nd h) = nd (λ y a q → Ψ₁⊴Φ (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) q)))
Ψ₁⊴Φ (nt h) = nd (λ y a q → Ψ₁⊴Φ (h (L.tr⁻ L.z≅ y) a (≼-trans (tr⁻≼ y) q)))
Ψ₁⊴Φ (u⊴ p) = Ψ₀⊴Φ p
```

## 4 目标层 0 的折叠把关系送到值前序

层号 0 的结点：参照的链从 1 起每步 `ψ` 一次，被验收一侧的链从 `top` 起每步一次折叠 (不累加)，同步归纳。

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
  chain-lower (suc n) = ≼-trans (step≤ (δ n)) (hk (δ n) _ (chain-lower n))

  result : ∀ w → L.ψ⁰ (L.limᵢ {i = L.zero} L.zero f) ≼ read (Ψn zero zero w gm gk)
  result w = l≼ (λ n → ≼l n (hm (δ n) _ (chain-lower n)))

fold-lower : ∀ (x : Ext zero L1) {k} {X : L.Ordᶜ k} {η} → X ⊴ η → X ≅ X →
  L.ψ⁰ X ≼ read (Ψ zero (vs v0) x η)
fold-lower x {η = η} z⊴ s = one≼ (vs v0) x η
fold-lower x {η = G.suc η} (s⊴s p) s = suc-lower (Ψ zero (vs v0) x η) (fold-lower x p (s≅⁻ s))
fold-lower x (⊴s p) s = ≼l 1 (fold-lower x p s)
fold-lower x (⊴l n p) s = ≼l n (fold-lower x p s)
fold-lower x (l⊴ h) s = l≼ (λ n → fold-lower x (h n) (l≅⁻ s n))
fold-lower x {η = G.lc _ g} (⊴b h) s = firstn zero (x (inj₁ tt)) (λ η → Ψ zero (vs v0) x (g η))
  (λ η → Ψ zero (vs v0) (cmp (vs v0) (inj₁ tt)) (g η)) (fold-lower x h s)
fold-lower x (nd {f = f} h) s = NodeLower.result f (lᵢ≅⁻ s) _ _
  (λ y a q → fold-lower (cmp (vs v0) (inj₁ tt)) (h y a q) (lᵢ≅⁻ s y))
  (λ y a q → fold-lower x (h y a q) (lᵢ≅⁻ s y)) (x (inj₁ tt))
fold-lower x (nt {f = f} h) s = NodeLower.result f (lᵢ≅⁻ s) _ _
  (λ y a q → fold-lower (cmp (vs v0) (inj₁ tt)) (h y a q) (lᵢ≅⁻ s y))
  (λ y a q → fold-lower x (h y a q) (lᵢ≅⁻ s y)) (x (inj₁ tt))
fold-lower x {η = G.em tt a} (em⊴ q) s = ≼-trans (V.ψ⁰-mono⁰ q) (fold₀ _ a)
fold-lower x (u⊴ {y = y} p) s = fold-lower x {X = y} p (L.≅-refl⁰ y)
```

## 5 ψ₀(Ω₂)

`F (fin 2)` 的链在第 1 层，从 `top` 起，每步一次目标为第 1 层的折叠 `Φ`；参照 `γ 1` 从 `Ω ⟨1⟩` 起，每步 `Ψ 1`。

```agda
fin : ℕ → R
fin zero = G.zero
fin (suc n) = G.suc (fin n)

chain₂ : ∀ i → γ 1 i ⊴ chain L1 Φ i
chain₂ zero = Ω⊴top
chain₂ (suc i) = Ψ₁⊴Φ (chain₂ i)

lower₂ : L.ψ⁰ (L.Ω ⟨ 2 ⟩) ≼ read (F (fin 2))
lower₂ = l≼ (λ i → ≼l i (fold-lower (λ r → tt) {X = γ 1 i} (chain₂ i) (γ-self 1 i)))
```

## 6 塔的第 3 项

`T₃` 的第 0 项是 `F (fin 1)`；`F (fin 2)` 与 `F (top + top)` 相同，而 `top + top` 字面上是第 1 个链点的第一位置，由 `root-mono` 送到 `T₃` 的第 1 项。

```agda
cp→≼ : ∀ {a} b → Cp zero a b → read a ≼ read b
cp→≼ {a} b p = V.⊑→≼ (read a) (cp→⊑ b p)

two≤pt1 : Cp zero (G.suc G.top) (pt 1)
two≤pt1 = inj₂ (0 , inj₂ (2 , inj₁ refl))

T₃-Ω₁ : L.ψ⁰ (L.Ω ⟨ 1 ⟩) ≼ read T₃
T₃-Ω₁ = ≼l 0 lower₁

T₃-Ω₂ : L.ψ⁰ (L.Ω ⟨ 2 ⟩) ≼ read T₃
T₃-Ω₂ = ≼l 1 (≼-trans lower₂ (cp→≼ (F (pt 1)) (root-mono (pt 1) two≤pt1)))
```
