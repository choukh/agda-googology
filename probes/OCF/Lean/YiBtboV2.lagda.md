# 规范化层号之间的值单调, 目标只要极限逐项不降

验收文件. `BTBOFullEb.V2` 的副本, 只把目标一侧的 `St` 放宽成 `Mono` (极限逐项不降): 源严格, 值序 `tr₀ x ≼ tr₀ y` 给出累加规范化层号 `ordᴰ x` 到 `ordᴰ y` 的保序嵌入 (`V2′`). 第七次独立审查的试验 (2026-11-11), 主审移入并冷编复核. 入口: [YiBtboLower](YiBtboLower.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBtboV2 where

open import Data.Nat using (ℕ; zero; suc; _≤′_; ≤′-refl; ≤′-step) renaming (_+_ to _+ᴺ_)
open import Data.Nat.Properties using (≤⇒≤′; m≤m+n; m≤n+m)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; cong)

open import OCF.BTBO using (module Ord-Ord; module BoundedTrich)
module S = Ord-Ord
module B = BoundedTrich
open B using (Ordᴰ; cumsum; cumsum-mono)
open S using (ordᴰ; zero; suc; lim; limᵢ)
import OCF.Align.Level as L
open L using (Ordᶜ)
open import OCF.Align.BTBOValBase using (tr₀)
open import OCF.Align.BTBOValAbsorb using (St; st-s⁻; st-l₁; st-l₂; lim-≼⁻)
open import OCF.Align.Value using (_≼_; s≼s; s≼s⁻; s≼0; ≼l; l≼; ≼-refl; ≼-trans; ≼-suc; ≼lim⁻)
open import OCF.Align.BTBOFullEb using (𝕆; module Blocks; off; off-top; off-mono; Eb-off; Σ-lift; lt-add; O∘)
open Blocks 𝕆

data Mono : Ordᶜ L.zero → Set where
  mz : Mono L.zero
  ms : ∀ {a} → Mono a → Mono (L.suc a)
  ml : ∀ {f : ℕ → Ordᶜ L.zero} → (∀ n → Mono (f n)) → (∀ n → f n ≼ f (suc n)) → Mono (L.lim f)

mo-s⁻ : ∀ {a} → Mono (L.suc a) → Mono a
mo-s⁻ (ms d) = d

mo-l₁ : ∀ {f : ℕ → Ordᶜ L.zero} → Mono (L.lim f) → ∀ n → Mono (f n)
mo-l₁ (ml h s) = h

mo-l₂ : ∀ {f : ℕ → Ordᶜ L.zero} → Mono (L.lim f) → ∀ n → f n ≼ f (suc n)
mo-l₂ (ml h s) = s

g-mono′ : ∀ {g : ℕ → S.Ord₀} → Mono (tr₀ (lim g)) → ∀ {a b} → a ≤′ b → tr₀ (g a) ≼ tr₀ (g b)
g-mono′ st ≤′-refl     = ≼-refl _
g-mono′ st (≤′-step l) = ≼-trans (g-mono′ st l) (mo-l₂ st _)

V2′  : ∀ (x y : S.Ord₀) → St (tr₀ x) → Mono (tr₀ y) → tr₀ x ≼ tr₀ y → Eb (ordᴰ x) (ordᴰ y)
V2s′ : ∀ (x₀ y : S.Ord₀) → St (tr₀ x₀) → Mono (tr₀ y) → tr₀ (suc x₀) ≼ tr₀ y → Eb (B.suc (ordᴰ x₀)) (ordᴰ y)

V2s′ x₀ zero sx sy w = ⊥-elim (s≼0 w)
V2s′ x₀ (suc y₀) sx sy (s≼s w) = Eb-suc (V2′ x₀ y₀ sx (mo-s⁻ sy) w) (ordᴰ y₀) (λ p → p) B.zero
V2s′ x₀ (lim g) sx sy (≼l m w) = Eb-wk (Eb-off (O∘ g) m (V2s′ x₀ (g m) sx (mo-l₁ sy m) w)) (λ p → B.lim m p)
V2s′ x₀ (limᵢ () f) sx sy w

V2′ zero y sx sy w = Eb-zero
V2′ (suc x₀) y sx sy w = V2s′ x₀ y (st-s⁻ sx) sy w
V2′ (limᵢ () f) y sx sy w
V2′ (lim f) zero sx sy w = ⊥-elim (s≼0 (≼-trans (st-l₂ sx 0) (lim-≼⁻ w 1)))
V2′ (lim f) (suc y₀) sx sy w =
  Eb-wk (V2′ (lim f) y₀ sx (mo-s⁻ sy) (l≼ (λ n → s≼s⁻ (≼-trans (st-l₂ sx n) (lim-≼⁻ w (suc n)))))) (λ p → B.suc p)
V2′ (lim f) (lim g) sx sy w = Blk.Lim (O∘ f) Bd B∞ e₀ N Nb Nm Nc fl sp
  where
  B∞ = ordᴰ (lim g)
  bnd : ∀ n → Σ ℕ (λ m → tr₀ (suc (f n)) ≼ tr₀ (g m))
  bnd n = ≼lim⁻ (≼-trans (st-l₂ sx n) (lim-≼⁻ w (suc n)))
  M : ℕ → ℕ
  M zero    = proj₁ (bnd 0)
  M (suc n) = suc (M n +ᴺ proj₁ (bnd (suc n)))
  sM : ∀ n → tr₀ (suc (f n)) ≼ tr₀ (g (M n))
  sM zero    = proj₂ (bnd 0)
  sM (suc n) = ≼-trans (proj₂ (bnd (suc n))) (g-mono′ sy (≤′-step (≤⇒≤′ (m≤n+m (proj₁ (bnd (suc n))) (M n)))))
  Bd : ℕ → Ordᴰ
  Bd n = cumsum (O∘ g) (M n)
  e₀ : Eb (O∘ f 0) (Bd 0)
  e₀ = Eb-off (O∘ g) (M 0) (V2′ (f 0) (g (M 0)) (st-l₁ sx 0) (mo-l₁ sy (M 0)) (≼-trans (≼-suc (≼-refl _)) (sM 0)))
  eN : ∀ n → Eb (B.suc (O∘ f (suc n))) (O∘ g (M (suc n)))
  eN n = V2s′ (f (suc n)) (g (M (suc n))) (st-l₁ sx (suc n)) (mo-l₁ sy (M (suc n))) (sM (suc n))
  N : ∀ n {d} → d B.< B.suc (O∘ f (suc n)) → Ordᴰ
  N n p = off (O∘ g) (M (suc n)) (map (eN n) p)
  Nb : ∀ n {d} (p : d B.< B.suc (O∘ f (suc n))) → N n p B.< Bd (suc n)
  Nb n p = off-top (O∘ g) (M (suc n)) (below (eN n) p)
  Nm : ∀ n {d₁ d₂} (p : d₁ B.< B.suc (O∘ f (suc n))) (q : d₂ B.< B.suc (O∘ f (suc n))) → d₁ B.< d₂ → N n p B.< N n q
  Nm n p q r = off-mono (O∘ g) (M (suc n)) (mono (eN n) p q r)
  Nc : ∀ n {d₁ d₂} (p : d₁ B.< B.suc (O∘ f (suc n))) (q : d₂ B.< B.suc (O∘ f (suc n))) → d₁ ≡ d₂ → N n p ≡ N n q
  Nc n p q r = cong (off (O∘ g) (M (suc n))) (coh (eN n) p q r)
  fl : ∀ n {x} → x B.< Bd n → ∀ {d} (p : d B.< B.suc (O∘ f (suc n))) → x B.< N n p
  fl n r p = lt-add (Σ-lift (O∘ g) (≤⇒≤′ (m≤m+n (M n) _)) r) _
  sp : ∀ n {x} → x B.< Bd n → x B.< B∞
  sp n r = B.lim (M n) r
```
