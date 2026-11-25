# YiLow：严格树上的前驱嵌入，小实例

**验收文件，档位：编译定理。** 严格谓词取 `SHS` (极限处相邻两项结构上严格上升，`YiVmNegBase`)。`EmbVˢ`/`VMˢ` 是只对严格树陈述的嵌入与值单调；本文证它们在 x 有限、x = ω、x = ω+1 时对一切严格的 y 成立 (`emb-nat`, `emb-ω`, `emb-ω1`)，并给后继提升 `into-suc`。
不否定什么；`EmbVˢ` 一般情形的否定见 [YiLowNeg](YiLowNeg.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLowBase where

open import Data.Nat using (ℕ; zero; suc; _<_; s≤s)
open import Data.Nat.Properties using (m≤n⇒m<n∨m≡n)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl; subst)
open import OCF.Align.Level
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; s≼s⁻)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open PEmb
open import OCF.Align.YiMonoEmb using (PEmb-⊑; PEmb-∘; PEmb-limʳ; PEmb-suc)
open import OCF.Align.YiVmNegBase using (SHS; sz; ss; sl; SHS→HS; nat≅inj; nat≺nat; ≺ω; toLevel-ω)
open import OCF.Align.YiVmNegBound using (emb-fin)
```

## 1 陈述

```agda
EmbVˢ : Set
EmbVˢ = ∀ (x : Ordᶜ zero) (hx : HS x) (y : Ordᶜ zero) (hy : HS y) → SHS x → SHS y → x ≼ y →
  PEmb (toLevel x hx) (toLevel y hy)

VMˢ : Set
VMˢ = ∀ (x : Ordᶜ zero) (hx : HS x) (y : Ordᶜ zero) (hy : HS y) → SHS x → SHS y → x ≼ y →
  ψ⁰ (Ω (toLevel x hx)) ≼ ψ⁰ (Ω (toLevel y hy))

embˢ→vmˢ : EmbVˢ → VMˢ
embˢ→vmˢ ev x hx y hy sx sy d = Ψ-emb (ev x hx y hy sx sy d)

Into : (a : Ordᶜ zero) → HS a → Set
Into a ha = ∀ (y : Ordᶜ zero) (hy : HS y) → SHS y → a ≼ y → PEmb (toLevel a ha) (toLevel y hy)
```

## 2 后继提升与有限的 x

```agda
into-suc : ∀ {a} (ha : HS (suc a)) → Into a (hs⁻ ha) → Into (suc a) ha
into-suc ha IH zero hy sy ()
into-suc ha IH (suc b) hy (ss sb) (s≼s d) = PEmb-suc (IH b (hs⁻ hy) sb d)
into-suc ha IH (lim g) hy (sl sg st lt) (≼l k d) = PEmb-limʳ k (into-suc ha IH (g k) (hl₁ hy k) (sg k) d)
into-suc ha IH (limᵢ () f) hy sy d
into-suc ha IH (up () x) hy sy d

emb-nat : ∀ n (hx : HS (natᶜ n)) → Into (natᶜ n) hx
emb-nat n hx y hy sy d = emb-fin n hx y hy d
```

## 3 x = ω

y 是严格的极限时，ω 的第 u 个前驱映到 y 的第 u 项 (严格上升，用不到推导)；y 是后继时，推导把 ω 压到前一个点之下。

```agda
module _ {g : ℕ → Ordᶜ zero} (hy : HS (lim g)) (lt : ∀ n → g n ≺ g (suc n)) where
  G : ℕ → Ordᴵ
  G n = toLevel (g n) (hl₁ hy n)

  G-step : ∀ n → G n ≺ᴵ G (suc n)
  G-step n = toLevel-≺ (hl₁ hy n) (hl₁ hy (suc n)) (lt n)

  G-mono : ∀ {u v} → u < v → G u ≺ᴵ G v
  G-mono {u} {suc v} (s≤s p) with m≤n⇒m<n∨m≡n p
  ... | inj₁ q = ≺ᴵ-trans (G-mono q) (G-step v)
  ... | inj₂ refl = G-step v

idx : ∀ (hx : HS ωᶜ) {c} → c ≺ᴵ toLevel ωᶜ hx → Σ ℕ λ u → c ≅ᴵ natᴵ u
idx hx r = ≺ω (≺ᴵ-respʳ r (toLevel-ω hx))

emb-ω-lim : ∀ (hx : HS ωᶜ) {g} (hy : HS (lim g)) (lt : ∀ n → g n ≺ g (suc n)) →
  PEmb (toLevel ωᶜ hx) (toLevel (lim g) hy)
map (emb-ω-lim hx hy lt) r = G hy lt (proj₁ (idx hx r))
bnd (emb-ω-lim hx hy lt) r = ≺-lim (suc (proj₁ (idx hx r))) (G-step hy lt (proj₁ (idx hx r)))
mono (emb-ω-lim hx hy lt) r s c<d =
  G-mono hy lt (nat≺nat (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym (proj₂ (idx hx r))) c<d) (proj₂ (idx hx s))))
coh (emb-ω-lim hx hy lt) r s e =
  subst (λ k → G hy lt (proj₁ (idx hx r)) ≅ᴵ G hy lt k)
    (nat≅inj (≅ᴵ-trans (≅ᴵ-sym (proj₂ (idx hx r))) (≅ᴵ-trans e (proj₂ (idx hx s))))) (≅ᴵ-refl _)

emb-ω : ∀ (hx : HS ωᶜ) → Into ωᶜ hx
emb-ω hx zero hy sy (l≼ h) with h 1
... | ()
emb-ω hx (suc b) hy (ss sb) (l≼ h) =
  PEmb-∘ (emb-ω hx b (hs⁻ hy) sb (l≼ (λ n → s≼s⁻ (h (suc n))))) (PEmb-⊑ (Sim→⊑ᴵ suc))
emb-ω hx (lim g) hy (sl sg st lt) d = emb-ω-lim hx hy lt
emb-ω hx (limᵢ () f) hy sy d
emb-ω hx (up () x) hy sy d

emb-ω1 : ∀ (hx : HS (suc ωᶜ)) → Into (suc ωᶜ) hx
emb-ω1 hx = into-suc hx (emb-ω (hs⁻ hx))
```
