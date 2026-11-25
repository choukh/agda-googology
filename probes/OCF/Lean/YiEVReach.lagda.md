# 验收: 沿下降路径到第 2 层, ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照对一般底成立

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提, 对一切层号、证据、路线与底.
> `reach`: 层号 ℓ 沿 "后继的前驱, ℕ 极限的任一孩子, Ω 结点层号的第 0 行" 走到层号 2 (`_⇐_`), 底 B 满足 `OKB` 且 `b⊥` 与第 0 层的各分量不低于 BTBO 的参照 (`Hi`) 时, ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照不高于 ℓ 上 Ω 树以 B 为底的折叠. 层号 2 一站是 [YiMWPre](YiMWPre.lagda.md) 的 `Pre` 对一般底的代入 (`atTwo`).
> 另有 Ω 结点层号第 1 行的一步 (`Ω≽1`). 不涉及上界. 实例在 [YiEVTw2](YiEVTw2.lagda.md), [YiEVEnd](YiEVEnd.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiEVReach where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; inl; ink; inb; Ev; Rt)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read; _⊢_⊴_; ⊴r; ⊴◃; ⊴-◃; ⊴→≼; plus≽)
open import OCF.Lean.YiLSFold using (OKB; ok-dS; ok-dL; ψ⊥-⊵; ψs-⊵)
open import OCF.Lean.YiT2Frame using (ok-dW)
import OCF.Lean.YiMEBase as MB
open import OCF.Lean.YiMEAnchor using (M¹; Ω₁ᵗ; Mβ₀; one; two; module G¹)
open import OCF.Lean.YiMWPre using (module Pre)
open import OCF.Lean.YiMWLow using (rd≼; tΩ; sem0)
import OCF.Lean.YiRefTw2 as R2
open import OCF.Lean.YiNFOCase using (tA)
open import OCF.Align.EboLeanDef using (HC)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.Value using (_≼_; ≼l; ≼-refl; ≼-trans)
```

## 底的条件 `Hi` 对孩子的底封闭

孩子的底的 `b⊥` 与各分量都是父底的对应分量再折一次, 不降 (`ψ⊥-⊵`, `ψs-⊵`).

```agda
Hi : (ℓ : LF) → Base ℓ → Set
Hi ℓ B = (D.BTBOᴵ ≼ read (b⊥ B)) × ((w : zero ≤ ℓ) → D.BTBOᴵ ≼ read (bs B zero w))

hi-dS : (a : LF) (ε : Ev (suc a)) (ρ : Rt (suc a)) (B : Base (suc a)) → Hi (suc a) B
  → (x : Tr (suc a)) → Hi a (dS a ε ρ B x)
hi-dS a ε ρ B (h⊥ , h0) x = ≼-trans h⊥ (⊴→≼ (ψ⊥-⊵ (suc a) ε ρ B x))
  , λ w → ≼-trans (h0 (ins w)) (⊴→≼ (ψs-⊵ (suc a) ε ρ B zero (ins w) (bs B zero (ins w)) (ns B zero (ins w)) x))

hi-dL : (g : ℕ → LF) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) → Hi (lim g) B
  → (n : ℕ) (x : Tr (lim g)) → Hi (g n) (dL g ε ρ B n x)
hi-dL g ε ρ B (h⊥ , h0) n x = ≼-trans h⊥ (⊴→≼ (ψ⊥-⊵ (lim g) ε ρ B x))
  , λ w → ≼-trans (h0 (inl n w)) (⊴→≼ (ψs-⊵ (lim g) ε ρ B zero (inl n w) (bs B zero (inl n w)) (ns B zero (inl n w)) x))

hi-dW : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) → Hi (Ωₗ k h) B
  → (c : Tr k) (x : Tr (Ωₗ k h)) → Hi (h c) (dW k h ε ρ B c x)
hi-dW k h ε ρ B (h⊥ , h0) c x = ≼-trans h⊥ (⊴→≼ (ψ⊥-⊵ (Ωₗ k h) ε ρ B x))
  , λ w → ≼-trans (h0 (inb c w)) (⊴→≼ (ψs-⊵ (Ωₗ k h) ε ρ B zero (inb c w) (bs B zero (inb c w)) (ns B zero (inb c w)) x))
```

## 一步下降

ℕ 极限层号的第 n 个孩子 (前缀是 `cumΩ` 的前 n 项), Ω 结点层号的第 0 行与第 1 行, 后继层号的第 1 行. 后继一步用 `OKB` 的 `Ωt a ⊴ bs B a (ins self)`: 第 1 行的折叠输入是 `next (bs B a (ins self))`.

```agda
preΩ : (g : ℕ → LF) → ℕ → Tr (lim g)
preΩ g zero    = zero
preΩ g (suc n) = cumΩ g n

lim≽ : (g : ℕ → LF) (ε : Ev (lim g)) (ρ : Rt (lim g)) (B : Base (lim g)) (n : ℕ)
  → read (ψ⊥ (g n) (ε n) (proj₁ ρ n) (dL g ε ρ B n (preΩ g n)) (Ωt (g n))) ≼ read (ψ⊥ (lim g) ε ρ B (Ωt (lim g)))
lim≽ g ε ρ B zero    = ≼l zero (≼-refl _)
lim≽ g ε ρ B (suc n) = ≼l (suc n) (≼-refl _)

Ω≽0 : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h))
  → read (ψ⊥ (h zero) (proj₂ (proj₂ ε zero)) (proj₂ ρ zero) (dW k h ε ρ B zero zero) (Ωt (h zero)))
  ≼ read (ψ⊥ (Ωₗ k h) ε ρ B (Ωt (Ωₗ k h)))
Ω≽0 k h ε ρ B = ≼l zero (≼-refl _)

c1Ω : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h)) → Tr k
c1Ω k h ε ρ B = ψs (Ωₗ k h) ε ρ B k (ink self) (bs B k (ink self)) (ns B k (ink self))
  (up zero zero (Ωt (h zero)) (Ωt-nz (h zero)))

Ω≽1 : (k : LF) (h : Tr k → LF) (ε : Ev (Ωₗ k h)) (ρ : Rt (Ωₗ k h)) (B : Base (Ωₗ k h))
  → read (ψ⊥ (h (c1Ω k h ε ρ B)) (proj₂ (proj₂ ε (c1Ω k h ε ρ B))) (proj₂ ρ (c1Ω k h ε ρ B))
       (dW k h ε ρ B (c1Ω k h ε ρ B) zero) (Ωt (h (c1Ω k h ε ρ B))))
  ≼ read (ψ⊥ (Ωₗ k h) ε ρ B (Ωt (Ωₗ k h)))
Ω≽1 k h ε ρ B = ≼l 1 (plus≽ _ _ (≼-refl _))

suc≽ : (a : LF) (ε : Ev (suc a)) (ρ : Rt (suc a)) (B : Base (suc a)) → OKB (suc a) B
  → read (ψ⊥ a ε ρ (dS a ε ρ B zero) (Ωt a)) ≼ read (ψ⊥ (suc a) ε ρ B (Ωt (suc a)))
suc≽ a ε ρ B ok = ≼l 1 (plus≽ _ _ (⊴→≼ (⊴◃ (◃t (mono⊥ a ε ρ (dS a ε ρ B zero) d) (◃l zero)))))
  where
  d : a ⊢ Ωt a ◃ next (bs B a (ins self)) (ns B a (ins self))
  d = ⊴-◃ (proj₂ ok a (ins self)) (◃l zero)
```

## 层号 2: `Pre` 对一般底

`OKB` 给出第 1 层分量在 Ω₁ 之上 (`Mβ₀` 向上封闭); `Hi` 经 `sem0` 给出第 0 层分量与 `b⊥` 对着 ψ₀(Ω_Ω).

```agda
cv⊴ : ∀ {ℓ} {x y : Tr ℓ} → ℓ ⊢ x ⊴ y → MB._⊴_ x y
cv⊴ ⊴r     = MB.⊴r
cv⊴ (⊴◃ d) = MB.⊴◃ d

Lo : (ℓ : LF) → Ev ℓ → Rt ℓ → Base ℓ → Set
Lo ℓ ε ρ B = (h : HC tA) → R2.Rt h ≼ read (ψ⊥ ℓ ε ρ B (Ωt ℓ))

module AtTwo (B₂ : Base two) (ok : OKB two B₂) (hi : Hi two B₂) where
  hβ : M¹ Ω₁ᵗ (bs B₂ one (ins self))
  hβ = G¹.m⊴ Mβ₀ (cv⊴ (proj₂ ok one (ins self)))

  module P = Pre B₂ hβ tΩ (sem0 (bs B₂ zero (ins (ins self))) (proj₂ hi (ins (ins self)))) (sem0 (b⊥ B₂) (proj₁ hi))

  atTwo : Lo two tt tt B₂
  atTwo h = ≼-trans (MB.lower⁰ (MB.mL refl P.rowp) h) (rd≼ _)
```

## 下降路径与 `reach`

```agda
infix 4 _⇐_
data _⇐_ (j : LF) : LF → Set where
  ⇐r : j ⇐ j
  ⇐s : ∀ {a} → j ⇐ a → j ⇐ suc a
  ⇐l : ∀ {g} (n : ℕ) → j ⇐ g n → j ⇐ lim g
  ⇐w : ∀ {k h} → j ⇐ h zero → j ⇐ Ωₗ k h

reach : ∀ {ℓ} → two ⇐ ℓ → (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Hi ℓ B → Lo ℓ ε ρ B
reach ⇐r ε ρ B ok hi = AtTwo.atTwo B ok hi
reach (⇐s {a} p) ε ρ B ok hi hA =
  ≼-trans (reach p ε ρ (dS a ε ρ B zero) (ok-dS ε ρ B ok zero) (hi-dS a ε ρ B hi zero) hA) (suc≽ a ε ρ B ok)
reach (⇐l {g} n p) ε ρ B ok hi hA =
  ≼-trans (reach p (ε n) (proj₁ ρ n) (dL g ε ρ B n (preΩ g n)) (ok-dL g ε ρ B ok n (preΩ g n)) (hi-dL g ε ρ B hi n (preΩ g n)) hA)
    (lim≽ g ε ρ B n)
reach (⇐w {k} {h} p) ε ρ B ok hi hA =
  ≼-trans (reach p (proj₂ (proj₂ ε zero)) (proj₂ ρ zero) (dW k h ε ρ B zero zero) (ok-dW k h ε ρ B ok zero zero) (hi-dW k h ε ρ B hi zero zero) hA)
    (Ω≽0 k h ε ρ B)
```
