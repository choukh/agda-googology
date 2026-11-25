# YiLow：ω² 以下的 x 对一切严格的 y 有嵌入

**验收文件，档位：编译定理。** `into-+ω`：x = a + ω 时，若 a+1 对一切严格的 y 有读推导的嵌入，则 a + ω 也有。于是 x = ω·k + n (一切 ω² 以下的序数) 对一切严格的 y 有前驱嵌入 (`emb-ω²`)，`VMˢ` 在这些 x 上成立。
与 [YiLowNeg](YiLowNeg.lagda.md) 合读：x = ω + ω² 时同样的陈述推出 LPO。界线在 ω²，`EmbVˢ` 的否定不在更小的 x 上。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLowPos where

open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n) renaming (_+_ to _+ℕ_)
open import Relation.Nullary using (¬_)
open import Data.Nat.Properties using (<-cmp; +-monoˡ-<; m≤n+m)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import OCF.Align.Level
open import OCF.Align.Value using (_≼_; l≼; s≼s⁻; ≼lim⁻)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open PEmb
open import OCF.Align.YiMonoEmb using (PEmb-⊑; PEmb-∘)
open import OCF.Align.YiVmNegBase using (SHS; ss; sl)
open import OCF.Lean.YiLowBase using (Into; into-suc; emb-nat; G; G-step; G-mono)
open import OCF.Lean.YiLowNeg using (mulω; l≼⁻)
```

## 1 左极限 a + ω 嵌进严格的极限 y

a + ω 的前驱要么在 a+1 之下 (经 a+1 ≼ g m 的嵌入 `Pa`)，要么是点 a + (j+1)，映到 y 的第 j + m 项。

```agda
module LimEmb {a : Ordᶜ zero} (h : HS (a + ωᶜ)) {g : ℕ → Ordᶜ zero} (hy : HS (lim g))
  (lt : ∀ n → g n ≺ g (suc n)) (m : ℕ) (Pa : PEmb (toLevel (suc a) (hl₁ h 1)) (toLevel (g m) (hl₁ hy m))) where

  ltA : ∀ n → a + natᶜ n ≺ a + natᶜ (suc n)
  ltA n = ≺z (≅-refl⁰ (a + natᶜ n))

  P : ℕ → Ordᴵ
  P n = toLevel (a + natᶜ n) (hl₁ h n)

  Gy : ℕ → Ordᴵ
  Gy = G hy lt

  cls : ∀ n (hh : HS (a + natᶜ n)) {c′} → c′ <ᴵ toLevel (a + natᶜ n) hh → c′ ≺ᴵ P 1 ⊎ Σ ℕ λ j → c′ ≅ᴵ P (suc j)
  cls zero hh q = inj₁ (≺-suc (<-≅ q (toLevel-≅ hh (hs⁻ (hl₁ h 1)) (≅-refl⁰ a))))
  cls (suc zero) hh zero = inj₁ (via (toLevel-≅ (hs⁻ hh) (hs⁻ (hl₁ h 1)) (≅-refl⁰ a)) zero)
  cls (suc (suc j)) hh zero = inj₂ (j , toLevel-≅ (hs⁻ hh) (hl₁ h (suc j)) (≅-refl⁰ _))
  cls (suc n) hh (suc q) = cls n (hs⁻ hh) q

  side : ∀ {c} → c ≺ᴵ toLevel (a + ωᶜ) h → c ≺ᴵ P 1 ⊎ Σ ℕ λ j → c ≅ᴵ P (suc j)
  side (via e (lim n q)) with cls n (hl₁ h n) q
  ... | inj₁ r = inj₁ (≺ᴵ-respˡ e r)
  ... | inj₂ (j , e′) = inj₂ (j , ≅ᴵ-trans e e′)

  pick : ∀ {c} → c ≺ᴵ P 1 ⊎ (Σ ℕ λ j → c ≅ᴵ P (suc j)) → Ordᴵ
  pick (inj₁ r) = map Pa r
  pick (inj₂ (j , _)) = Gy (j +ℕ m)

  P-lt : ∀ {i k} → i < k → P i ≺ᴵ P k
  P-lt = G-mono h ltA

  no-below : ∀ j → ¬ (P (suc j) ≺ᴵ P 1)
  no-below zero p = ≺ᴵ-irrefl p
  no-below (suc j) p = ≺ᴵ-irrefl (≺ᴵ-trans (P-lt (s≤s (s≤s z≤n))) p)

  idx-lt : ∀ {i j} → P (suc i) ≺ᴵ P (suc j) → i < j
  idx-lt {i} {j} p with <-cmp i j
  ... | tri< x _ _ = x
  ... | tri≈ _ refl _ = ⊥-elim (≺ᴵ-irrefl p)
  ... | tri> _ _ x = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-trans p (P-lt (s≤s x))))

  idx-eq : ∀ {i j} → P (suc i) ≅ᴵ P (suc j) → i ≡ j
  idx-eq {i} {j} e with <-cmp i j
  ... | tri< x _ _ = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ (P-lt (s≤s x)) (≅ᴵ-sym e)))
  ... | tri≈ _ q _ = q
  ... | tri> _ _ x = ⊥-elim (≺ᴵ-irrefl (≺ᴵ-respʳ (P-lt (s≤s x)) e))

  G≤ : ∀ j → ∀ {c} → c ≺ᴵ Gy m → c ≺ᴵ Gy (j +ℕ m)
  G≤ zero r = r
  G≤ (suc j) r = ≺ᴵ-trans r (G-mono hy lt (s≤s (m≤n+m m j)))

  Q : PEmb (toLevel (a + ωᶜ) h) (toLevel (lim g) hy)
  map Q r = pick (side r)
  bnd Q r with side r
  ... | inj₁ r₁ = ≺ᴵ-trans (bnd Pa r₁) (≺-lim (suc m) (G-step hy lt m))
  ... | inj₂ (j , _) = ≺-lim (suc (j +ℕ m)) (G-step hy lt (j +ℕ m))
  mono Q r s lt′ with side r | side s
  ... | inj₁ r₁ | inj₁ s₁ = mono Pa r₁ s₁ lt′
  ... | inj₁ r₁ | inj₂ (j , _) = G≤ j (bnd Pa r₁)
  ... | inj₂ (j , e) | inj₁ s₁ = ⊥-elim (no-below j (≺ᴵ-respˡ (≅ᴵ-sym e) (≺ᴵ-trans lt′ s₁)))
  ... | inj₂ (i , e) | inj₂ (j , e′) =
    G-mono hy lt (+-monoˡ-< m (idx-lt (≺ᴵ-respʳ (≺ᴵ-respˡ (≅ᴵ-sym e) lt′) e′)))
  coh Q r s e″ with side r | side s
  ... | inj₁ r₁ | inj₁ s₁ = coh Pa r₁ s₁ e″
  ... | inj₁ r₁ | inj₂ (j , e′) = ⊥-elim (no-below j (≺ᴵ-respˡ (≅ᴵ-sym (≅ᴵ-trans e″ e′)) r₁))
  ... | inj₂ (j , e) | inj₁ s₁ = ⊥-elim (no-below j (≺ᴵ-respˡ (≅ᴵ-trans (≅ᴵ-sym e) e″) s₁))
  ... | inj₂ (i , e) | inj₂ (j , e′) =
    subst (λ k → Gy (i +ℕ m) ≅ᴵ Gy (k +ℕ m)) (idx-eq (≅ᴵ-trans (≅ᴵ-sym e) (≅ᴵ-trans e″ e′))) (≅ᴵ-refl _)
```

## 2 递推

```agda
into-+ω : ∀ {a} (h : HS (a + ωᶜ)) → Into (suc a) (hl₁ h 1) → Into (a + ωᶜ) h
into-+ω h IH zero hy sy d with l≼⁻ d 1
... | ()
into-+ω h IH (suc b) hy (ss sb) d =
  PEmb-∘ (into-+ω h IH b (hs⁻ hy) sb (l≼ (λ n → s≼s⁻ (l≼⁻ d (suc n))))) (PEmb-⊑ (Sim→⊑ᴵ suc))
into-+ω h IH (lim g) hy (sl sg st lt) d with ≼lim⁻ (l≼⁻ d 1)
... | m , dm = LimEmb.Q h hy lt m (IH (g m) (hl₁ hy m) (sg m) dm)
into-+ω h IH (limᵢ () f) hy sy d
into-+ω h IH (up () x) hy sy d

emb-ω² : ∀ k n (hx : HS (mulω k + natᶜ n)) → Into (mulω k + natᶜ n) hx
emb-ω² k (suc n) hx = into-suc hx (emb-ω² k n (hs⁻ hx))
emb-ω² zero zero hx = emb-nat 0 hx
emb-ω² (suc k) zero hx = into-+ω hx (emb-ω² k 1 (hl₁ hx 1))

vm-ω² : ∀ k n (hx : HS (mulω k + natᶜ n)) (y : Ordᶜ zero) (hy : HS y) → SHS y → mulω k + natᶜ n ≼ y →
  ψ⁰ (Ω (toLevel (mulω k + natᶜ n) hx)) ≼ ψ⁰ (Ω (toLevel y hy))
vm-ω² k n hx y hy sy d = Ψ-emb (emb-ω² k n hx y hy sy d)
```
