# 第 2 层的读回关系 `⊴²`

验收文件. 关系 `_⊴²_ : ∀ {k} → L.Ordᶜ k → R₂ → Set` (参照第 0, 1, 2 层的树对第 2 层的树), 照 [YiSyncRel](YiSyncRel.lagda.md) 的 `⊴⁺` 写: 层号 1, 0 的结点各一条规则 (`n1`, `n0`, `n0′`), `top` 一条 (`t1`), 嵌入 `e1`, `e0` 接 `⊴⁺` 与 `NA._⊴_`; 对角规则 `dg` 在层号 0 的结点上, 门槛仍是 `top + Tw 2`; `≅⊴` 换代表.
编译定理: `⊴²-cp`, `⊴²-+ˡ`, `⊴²-+ʳ`, `add₂` (左加数要 `≅` 自反), `suc-step²`, `Ω²⊴top`. 不陈述值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiStepRel2 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore hiding (Le)
open import OCF.Lean.YiNextBase
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiL1Emb using (⊴-cp)
open import OCF.Align.YiLvVal2 using (T₀; T₁; ℓ₁; ℓ₂)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
import OCF.Lean.YiSyncRel as S
open S using (_⊴⁺_; ⊴⁺-cp)
open import OCF.Lean.YiStepTree using (L2; R₂)
```

## 1 关系

```agda
T₂ : Set
T₂ = L.Ordᶜ ℓ₂

thr : R
thr = plus zero G.top (W.Tw 2)

infix 4 _⊴²_
data _⊴²_ : ∀ {k} → L.Ordᶜ k → R₂ → Set where
  z⊴ : ∀ {k} {η} → _⊴²_ {k} L.zero η
  s⊴s : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴² η → L.suc x ⊴² G.suc η
  ⊴s : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴² η → x ⊴² G.suc η
  ⊴l : ∀ {k} {x : L.Ordᶜ k} {H : ℕ → R₂} n → x ⊴² H n → x ⊴² G.lim H
  l⊴ : ∀ {k} {H : ℕ → L.Ordᶜ k} {η} → (∀ n → H n ⊴² η) → L.lim H ⊴² η
  ⊴b₁ : ∀ {k} {x : L.Ordᶜ k} {g : NA.R₁ → R₂} → x ⊴² g G.top → x ⊴² G.lc (inj₁ tt) g
  ⊴b₀ : ∀ {k} {x : L.Ordᶜ k} {g : R → R₂} → x ⊴² g G.top → x ⊴² G.lc (inj₂ (inj₁ tt)) g
  n1 : ∀ {f : T₁ → T₂} {g : NA.R₁ → R₂} → (∀ (y : T₁) a → y ⊴⁺ a → y L.≅ y → f y ⊴² g a) →
    L.limᵢ {i = ℓ₁} L.zero f ⊴² G.lc (inj₁ tt) g
  t1 : ∀ {f : T₁ → T₂} → (∀ (y : T₁) a → y ⊴⁺ a → y L.≅ y → f y ⊴² G.em tt a) →
    L.limᵢ {i = ℓ₁} L.zero f ⊴² G.top
  n0 : ∀ {f : T₀ → T₂} {g : R → R₂} → (∀ (y : T₀) a → y ≼ NA.read a → f y ⊴² g a) →
    L.limᵢ {i = L.zero} (L.suc L.zero) f ⊴² G.lc (inj₂ (inj₁ tt)) g
  n0′ : ∀ {f : T₀ → T₁} {g : R → R₂} → (∀ (y : T₀) a → y ≼ NA.read a → f y ⊴² g a) →
    L.limᵢ {i = L.zero} L.zero f ⊴² G.lc (inj₂ (inj₁ tt)) g
  e1 : ∀ {y : T₁} {a} → y ⊴⁺ a → y ⊴² G.em tt a
  e0 : ∀ {y : T₀} {a} → y NA.⊴ a → y ⊴² G.em tt a
  u1 : ∀ {y : T₁} {η} → y ⊴² η → L.up {k = ℓ₁} L.zero y ⊴² η
  u0 : ∀ {y : T₀} {η} → y ⊴² η → L.up {k = L.zero} L.zero y ⊴² η
  dg : ∀ {k} {F : ℕ → L.Ordᶜ k} {g : R → R₂} → (∀ n a → Cp zero thr a → F n ⊴² g a) →
    L.lim F ⊴² G.lc (inj₂ (inj₁ tt)) g
  ≅⊴ : ∀ {k} {x y : L.Ordᶜ k} {η} → x L.≅ y → y ⊴² η → x ⊴² η

Ω²⊴top : L.Ω ℓ₂ ⊴² G.top
Ω²⊴top = t1 (λ y a q s → u1 (e1 q))
```

## 2 右边沿第一位置上移

```agda
⊴²-cp : ∀ {k} {x : L.Ordᶜ k} {η η′} → x ⊴² η → Cp L2 η η′ → x ⊴² η′
⊴²-dn : ∀ {k} {x : L.Ordᶜ k} {η} η′ → x ⊴² η → Dn L2 η η′ → x ⊴² η′
⊴²-cp h (inj₁ refl) = h
⊴²-cp h (inj₂ p) = ⊴²-dn _ h p
⊴²-dn (G.suc η′) h p = ⊴s (⊴²-cp h p)
⊴²-dn (G.lim f) h (n , p) = ⊴l n (⊴²-cp h p)
⊴²-dn (G.lc (inj₁ _) g) h p = ⊴b₁ (⊴²-cp h p)
⊴²-dn (G.lc (inj₂ (inj₁ _)) g) h p = ⊴b₀ (⊴²-cp h p)
⊴²-dn (G.lc (inj₂ (inj₂ ())) g) h p
⊴²-dn {η = G.em _ a} (G.em _ d) z⊴ (refl , p) = z⊴
⊴²-dn {η = G.em _ a} (G.em _ d) (l⊴ h) (refl , p) = l⊴ (λ n → ⊴²-dn (G.em tt d) (h n) (refl , p))
⊴²-dn {η = G.em _ a} (G.em _ d) (e1 h) (refl , p) = e1 (⊴⁺-cp h (inj₂ p))
⊴²-dn {η = G.em _ a} (G.em _ d) (e0 h) (refl , p) = e0 (⊴-cp h (inj₂ p))
⊴²-dn {η = G.em _ a} (G.em _ d) (u1 h) (refl , p) = u1 (⊴²-dn (G.em tt d) h (refl , p))
⊴²-dn {η = G.em _ a} (G.em _ d) (u0 h) (refl , p) = u0 (⊴²-dn (G.em tt d) h (refl , p))
⊴²-dn {η = G.em _ a} (G.em _ d) (≅⊴ e h) (refl , p) = ≅⊴ e (⊴²-dn (G.em tt d) h (refl , p))
```

## 3 左右加法

`plus L2 θ (em tt a)` 是 `a` 的结构接在 θ 之上 (`add 1 B₁`), 所以嵌入的规则要另写 (`emb₁`, `emb₀`, `emsh`).

```agda
B₁ : Bld L2 (suc zero)
B₁ r = G.lc (inj₂ r)

B₀ : Bld L2 zero
B₀ r = G.lc (inj₂ (inj₂ r))

emsh : ∀ θ {y b : T₀} → y ≼ b → ∀ a → b ≡ NA.read a → y ⊴² add zero B₀ θ a
emsh θ z≼ a q = z⊴
emsh θ (s≼s p) (G.suc a) refl = s⊴s (emsh θ p a refl)
emsh θ (s≼s p) G.top refl = s⊴s (emsh θ p G.zero refl)
emsh θ (≼l n p) (G.lim f) refl = ⊴l n (emsh θ p (f n) refl)
emsh θ (l≼ h) a q = l⊴ (λ n → emsh θ (h n) a q)
emsh θ (≼i {p = ()} x ex p) a q
emsh θ (i≼ {p = ()} h) a q
emsh θ (≼u {r = ()} p) a q
emsh θ (u≼ {r = ()} p) a q

emb₀ : ∀ θ {y : T₀} {a : NA.R₁} → y NA.⊴ a → y ⊴² add (suc zero) B₁ θ a
emb₀ θ NA.z⊴ = z⊴
emb₀ θ (NA.s⊴s p) = s⊴s (emb₀ θ p)
emb₀ θ (NA.⊴s p) = ⊴s (emb₀ θ p)
emb₀ θ (NA.⊴l n p) = ⊴l n (emb₀ θ p)
emb₀ θ (NA.l⊴ h) = l⊴ (λ n → emb₀ θ (h n))
emb₀ θ (NA.⊴b h) = ⊴b₀ (emb₀ θ h)
emb₀ θ (NA.em⊴ {a = b} q) = emsh θ q b refl

emb₁ : ∀ θ {y : T₁} {a : NA.R₁} → y ⊴⁺ a → y ⊴² add (suc zero) B₁ θ a
emb₁ θ S.z⊴ = z⊴
emb₁ θ (S.s⊴s p) = s⊴s (emb₁ θ p)
emb₁ θ (S.⊴s p) = ⊴s (emb₁ θ p)
emb₁ θ (S.⊴l n p) = ⊴l n (emb₁ θ p)
emb₁ θ (S.l⊴ h) = l⊴ (λ n → emb₁ θ (h n))
emb₁ θ (S.⊴b h) = ⊴b₀ (emb₁ θ h)
emb₁ θ (S.nd h) = n0′ (λ y a q → emb₁ θ (h y a q))
emb₁ θ (S.nt h) = n0′ (λ y a q → emb₁ θ (h y a q))
emb₁ θ (S.u⊴ p) = u0 (emb₀ θ p)
emb₁ θ (S.dg h) = dg (λ n a c → emb₁ θ (h n a c))
emb₁ θ (S.≅⊴ e p) = ≅⊴ e (emb₁ θ p)

⊴²-+ˡ : ∀ θ {k} {x : L.Ordᶜ k} {η} → x ⊴² η → x ⊴² plus L2 θ η
⊴²-+ˡ θ z⊴ = z⊴
⊴²-+ˡ θ (s⊴s p) = s⊴s (⊴²-+ˡ θ p)
⊴²-+ˡ θ (⊴s p) = ⊴s (⊴²-+ˡ θ p)
⊴²-+ˡ θ (⊴l n p) = ⊴l n (⊴²-+ˡ θ p)
⊴²-+ˡ θ (l⊴ h) = l⊴ (λ n → ⊴²-+ˡ θ (h n))
⊴²-+ˡ θ (⊴b₁ h) = ⊴b₁ (⊴²-+ˡ θ h)
⊴²-+ˡ θ (⊴b₀ h) = ⊴b₀ (⊴²-+ˡ θ h)
⊴²-+ˡ θ (n1 h) = n1 (λ y a q s → ⊴²-+ˡ θ (h y a q s))
⊴²-+ˡ θ (t1 h) = n1 (λ y a q s → ⊴²-+ˡ θ (h y a q s))
⊴²-+ˡ θ (n0 h) = n0 (λ y a q → ⊴²-+ˡ θ (h y a q))
⊴²-+ˡ θ (n0′ h) = n0′ (λ y a q → ⊴²-+ˡ θ (h y a q))
⊴²-+ˡ θ (e1 h) = emb₁ θ h
⊴²-+ˡ θ (e0 h) = emb₀ θ h
⊴²-+ˡ θ (u1 p) = u1 (⊴²-+ˡ θ p)
⊴²-+ˡ θ (u0 p) = u0 (⊴²-+ˡ θ p)
⊴²-+ˡ θ (dg h) = dg (λ n a c → ⊴²-+ˡ θ (h n a c))
⊴²-+ˡ θ (≅⊴ e p) = ≅⊴ e (⊴²-+ˡ θ p)

emr₀ : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴² η → ∀ a → x ⊴² add zero B₀ η a
emr₀ p G.zero = p
emr₀ p (G.suc a) = ⊴s (emr₀ p a)
emr₀ p (G.lim f) = ⊴l 0 (emr₀ p (f 0))
emr₀ p (G.lc () g)
emr₀ p (G.em () a)
emr₀ p G.top = ⊴s p

emr₁ : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴² η → ∀ a → x ⊴² add (suc zero) B₁ η a
emr₁ p G.zero = p
emr₁ p (G.suc a) = ⊴s (emr₁ p a)
emr₁ p (G.lim f) = ⊴l 0 (emr₁ p (f 0))
emr₁ p (G.lc (inj₁ _) g) = ⊴b₀ (emr₁ p (g G.top))
emr₁ p (G.lc (inj₂ ()) g)
emr₁ p (G.em _ b) = emr₀ p b
emr₁ p G.top = ⊴b₀ (⊴s p)

⊴²-+ʳ : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴² η → ∀ η′ → x ⊴² plus L2 η η′
⊴²-+ʳ p G.zero = p
⊴²-+ʳ p (G.suc y) = ⊴s (⊴²-+ʳ p y)
⊴²-+ʳ p (G.lim f) = ⊴l 0 (⊴²-+ʳ p (f 0))
⊴²-+ʳ p (G.lc (inj₁ _) g) = ⊴b₁ (⊴²-+ʳ p (g G.top))
⊴²-+ʳ p (G.lc (inj₂ (inj₁ _)) g) = ⊴b₀ (⊴²-+ʳ p (g G.top))
⊴²-+ʳ p (G.lc (inj₂ (inj₂ ())) g)
⊴²-+ʳ p (G.em _ a) = emr₁ p a
⊴²-+ʳ p G.top = ⊴b₁ (emr₁ p G.top)
```

## 4 加法上下文与 ω 倍

```agda
σ₁₂ : L.Simᴵ ℓ₁ ℓ₂
σ₁₂ q = L.suc q

σ₀₂ : L.Simᴵ L.zero ℓ₂
σ₀₂ q = L.suc (L.suc q)

addE₀ : ∀ {x : T₂} {η} → x ⊴² η → ∀ {y b : T₀} → y ≼ b → ∀ c → b ≡ NA.read c →
  L.add x σ₀₂ y ⊴² add zero B₀ η c
addE₀ px z≼ c q = emr₀ px c
addE₀ px (s≼s p) (G.suc c) refl = s⊴s (addE₀ px p c refl)
addE₀ px (s≼s p) G.top refl = s⊴s (addE₀ px p G.zero refl)
addE₀ px (≼l n p) (G.lim f) refl = ⊴l n (addE₀ px p (f n) refl)
addE₀ px (l≼ h) c q = l⊴ (λ n → addE₀ px (h n) c q)
addE₀ px (≼i {p = ()} x ex p) c q
addE₀ px (i≼ {p = ()} h) c q
addE₀ px (≼u {r = ()} p) c q
addE₀ px (u≼ {r = ()} p) c q

addN₀ : ∀ {x : T₂} {η} → x ⊴² η → ∀ {y : T₀} {a : NA.R₁} → y NA.⊴ a → L.add x σ₀₂ y ⊴² add (suc zero) B₁ η a
addN₀ px {a = a} NA.z⊴ = emr₁ px a
addN₀ px (NA.s⊴s q) = s⊴s (addN₀ px q)
addN₀ px (NA.⊴s q) = ⊴s (addN₀ px q)
addN₀ px (NA.⊴l n q) = ⊴l n (addN₀ px q)
addN₀ px (NA.l⊴ h) = l⊴ (λ n → addN₀ px (h n))
addN₀ px (NA.⊴b h) = ⊴b₀ (addN₀ px h)
addN₀ px (NA.em⊴ {a = b} q) = addE₀ px q b refl

addN₁ : ∀ {x : T₂} {η} → x L.≅ x → x ⊴² η → ∀ {y : T₁} {a : NA.R₁} → y ⊴⁺ a →
  L.add x σ₁₂ y ⊴² add (suc zero) B₁ η a
addN₁ s px {a = a} S.z⊴ = emr₁ px a
addN₁ s px (S.s⊴s q) = s⊴s (addN₁ s px q)
addN₁ s px (S.⊴s q) = ⊴s (addN₁ s px q)
addN₁ s px (S.⊴l n q) = ⊴l n (addN₁ s px q)
addN₁ s px (S.l⊴ h) = l⊴ (λ n → addN₁ s px (h n))
addN₁ s px (S.⊴b h) = ⊴b₀ (addN₁ s px h)
addN₁ s px (S.nd h) = n0 (λ z b q → addN₁ s px (h z b q))
addN₁ s px (S.nt h) = n0 (λ z b q → addN₁ s px (h z b q))
addN₁ s px (S.u⊴ q) = addN₀ px q
addN₁ s px (S.dg h) = dg (λ n a c → addN₁ s px (h n a c))
addN₁ s px (S.≅⊴ e q) = ≅⊴ (L.add-≅ {σ = σ₁₂} {σ′ = σ₁₂} s e) (addN₁ s px q)

add₀₂ : ∀ {x : T₂} {η} → x L.≅ x → x ⊴² η → ∀ {y : T₀} {η′} → y ⊴² η′ → L.add x σ₀₂ y ⊴² plus L2 η η′
add₀₂ s px {η′ = η′} z⊴ = ⊴²-+ʳ px η′
add₀₂ s px (s⊴s q) = s⊴s (add₀₂ s px q)
add₀₂ s px (⊴s q) = ⊴s (add₀₂ s px q)
add₀₂ s px (⊴l n q) = ⊴l n (add₀₂ s px q)
add₀₂ s px (l⊴ h) = l⊴ (λ n → add₀₂ s px (h n))
add₀₂ s px (⊴b₁ h) = ⊴b₁ (add₀₂ s px h)
add₀₂ s px (⊴b₀ h) = ⊴b₀ (add₀₂ s px h)
add₀₂ s px (e0 q) = addN₀ px q
add₀₂ s px (dg h) = dg (λ n a c → add₀₂ s px (h n a c))
add₀₂ s px (≅⊴ e q) = ≅⊴ (L.add-≅ {σ = σ₀₂} {σ′ = σ₀₂} s e) (add₀₂ s px q)

add₁₂ : ∀ {x : T₂} {η} → x L.≅ x → x ⊴² η → ∀ {y : T₁} {η′} → y ⊴² η′ → L.add x σ₁₂ y ⊴² plus L2 η η′
add₁₂ s px {η′ = η′} z⊴ = ⊴²-+ʳ px η′
add₁₂ s px (s⊴s q) = s⊴s (add₁₂ s px q)
add₁₂ s px (⊴s q) = ⊴s (add₁₂ s px q)
add₁₂ s px (⊴l n q) = ⊴l n (add₁₂ s px q)
add₁₂ s px (l⊴ h) = l⊴ (λ n → add₁₂ s px (h n))
add₁₂ s px (⊴b₁ h) = ⊴b₁ (add₁₂ s px h)
add₁₂ s px (⊴b₀ h) = ⊴b₀ (add₁₂ s px h)
add₁₂ s px (n0′ h) = n0 (λ z a q → add₁₂ s px (h z a q))
add₁₂ s px (e1 q) = addN₁ s px q
add₁₂ s px (u0 q) = add₀₂ s px q
add₁₂ s px (dg h) = dg (λ n a c → add₁₂ s px (h n a c))
add₁₂ s px (≅⊴ e q) = ≅⊴ (L.add-≅ {σ = σ₁₂} {σ′ = σ₁₂} s e) (add₁₂ s px q)

add₂ : ∀ {x : T₂} {η} → x L.≅ x → x ⊴² η → ∀ {x′ : T₂} {η′} → x′ ⊴² η′ → (x L.+ x′) ⊴² plus L2 η η′
add₂ s px {η′ = η′} z⊴ = ⊴²-+ʳ px η′
add₂ s px (s⊴s q) = s⊴s (add₂ s px q)
add₂ s px (⊴s q) = ⊴s (add₂ s px q)
add₂ s px (⊴l n q) = ⊴l n (add₂ s px q)
add₂ s px (l⊴ h) = l⊴ (λ n → add₂ s px (h n))
add₂ s px (⊴b₁ h) = ⊴b₁ (add₂ s px h)
add₂ s px (⊴b₀ h) = ⊴b₀ (add₂ s px h)
add₂ s px (n1 h) = n1 (λ y a q t → add₂ s px (h y a q t))
add₂ s px (t1 h) = n1 (λ y a q t → add₂ s px (h y a q t))
add₂ s px (n0 h) = n0 (λ y a q → add₂ s px (h y a q))
add₂ s px (u1 q) = add₁₂ s px q
add₂ s px (dg h) = dg (λ n a c → add₂ s px (h n a c))
add₂ s px (≅⊴ e q) = ≅⊴ (L.add-≅ {σ = λ r → r} {σ′ = λ r → r} s e) (add₂ s px q)

copies² : ∀ {A : T₂} {β} → A L.≅ A → A ⊴² β → ∀ n →
  iterᴸ (A L.+_) L.zero (suc n) ⊴² acc (λ _ z → plus L2 β z) β n
copies² s p zero = p
copies² s p (suc n) = add₂ s p (copies² s p n)

suc-step² : ∀ {A : T₂} {β} → A L.≅ A → A ⊴² β → L.lim (iterᴸ (A L.+_) L.zero) ⊴² succ L2 β
suc-step² s p = l⊴ λ where
  zero → z⊴
  (suc n) → ⊴l n (copies² s p n)
```
