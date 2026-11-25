# YiVmNeg：不碰全知原则的子域

**验收文件，档位：编译定理。** 两条正面结果。`bound-⊑`：x, y 的层号若是同一个层号 z 的字面前驱 (公共上界)，值序 x ≼ y 就推出结构序 `⊑ᴵ`，于是 `VMᴸ` (`bound-vm`) 与保初始段的嵌入 (`bound-seg`) 都成立。`emb-fin`：x 有限时，由推导直接造出前驱嵌入，`VMᴸ` 成立 (`vm-fin`)。
本文不否定什么。入口：`YiVmNegSeg`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiVmNegBound where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (¬_)
open import OCF.Align.Level
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼; ≼-trans; ≅→≼; ≺→s≼)
open import OCF.Align.RR4MonoFragment using (irr)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open PEmb
open import OCF.Align.YiMonoEmb using (PEmb-suc; PEmb-limʳ)
open import OCF.Align.YiVmNegSeg using (PEmbᴰ; PEmbᴰ-⊑)
```

## 1 公共上界

`forget` 把层号读回第 0 层的树；字面前驱读回后是树的前驱 (`forget-≺`)，于是层号的结构序反向就与值序矛盾 (`no-back`)。

```agda
forget-≅ᴵ : ∀ {a b} → a ≅ᴵ b → forget a ≅ forget b
forget-≅ᴵ z≅ = z≅
forget-≅ᴵ (s≅ e) = s≅ (forget-≅ᴵ e)
forget-≅ᴵ (l≅ h) = l≅ (λ n → forget-≅ᴵ (h n))

forget-< : ∀ {a b} → a <ᴵ b → forget a ≺ forget b
forget-< {a = a} zero = ≺z (≅-refl⁰ (forget a))
forget-< (suc q) = ≺s (forget-< q)
forget-< (lim n q) = ≺l n (forget-< q)

forget-≺ : ∀ {a b} → a ≺ᴵ b → forget a ≺ forget b
forget-≺ (via e q) = ≺-respˡ (≅-sym (forget-≅ᴵ e)) (forget-< q)

no-back : ∀ x hx y hy → toLevel y hy ≺ᴵ toLevel x hx → ¬ (x ≼ y)
no-back x hx y hy p d =
  irr y (≼-trans (s≼s (≅→≼ (≅-sym (forget-toLevel y hy))))
        (≼-trans (≺→s≼ (forget-≺ p)) (≼-trans (≅→≼ (forget-toLevel x hx)) d)))

pred→⊑ : ∀ {a b} → (∀ {c} → c ≺ᴵ a → c ≺ᴵ b) → a ⊑ᴵ b
pred→⊑ {a = zero} h = z⊑
pred→⊑ {a = suc a} h = s⊑′ (h (via (≅ᴵ-refl a) zero))
pred→⊑ {a = lim f s} h = l⊑ (λ n → pred→⊑ (λ { (via e q) → h (via e (lim n q)) }))

bound-⊑ : ∀ x hx y hy {z} → toLevel x hx ≺ᴵ z → toLevel y hy ≺ᴵ z → x ≼ y → toLevel x hx ⊑ᴵ toLevel y hy
bound-⊑ x hx y hy {z} px (via e₂ q₂) d = pred→⊑ step
  where
  X = toLevel x hx
  Yl = toLevel y hy
  step : ∀ {c} → c ≺ᴵ X → c ≺ᴵ Yl
  step r with ≺ᴵ-trans r px
  ... | via e₁ q₁ with <ᴵ-dec q₁ q₂
  ...   | inj₁ t = ≺ᴵ-respʳ (≺ᴵ-respˡ e₁ t) (≅ᴵ-sym e₂)
  ...   | inj₂ (inj₁ t) = ⊥-elim (no-back x hx y hy (≺ᴵ-trans (≺ᴵ-respʳ (≺ᴵ-respˡ e₂ t) (≅ᴵ-sym e₁)) r) d)
  ...   | inj₂ (inj₂ t) = ⊥-elim (no-back x hx y hy (≺ᴵ-respˡ (≅ᴵ-trans e₂ (≅ᴵ-trans (≅ᴵ-sym t) (≅ᴵ-sym e₁))) r) d)

bound-vm : ∀ x hx y hy {z} → toLevel x hx ≺ᴵ z → toLevel y hy ≺ᴵ z → x ≼ y →
  ψ⁰ (Ω (toLevel x hx)) ≼ ψ⁰ (Ω (toLevel y hy))
bound-vm x hx y hy px py d = ⊑→≼′ (Ψ⁰-mono (bound-⊑ x hx y hy px py d))
  where
  ⊑→≼′ : ∀ {a b : Ordᶜ zero} → a ⊑ b → a ≼ b
  ⊑→≼′ {a} = OCF.Align.Value.⊑→≼ a

bound-seg : ∀ x hx y hy {z} → toLevel x hx ≺ᴵ z → toLevel y hy ≺ᴵ z → x ≼ y → PEmbᴰ (toLevel x hx) (toLevel y hy)
bound-seg x hx y hy px py d = PEmbᴰ-⊑ (bound-⊑ x hx y hy px py d)
```

## 2 有限的 x

x 有限时推导里没有左极限 (`l≼`)，零、后继、右极限三种情形都已有嵌入 (`PEmb-suc`, `PEmb-limʳ`)。

```agda
PEmb-0 : ∀ {b} → PEmb zero b
map (PEmb-0) (via e ())
bnd (PEmb-0) (via e ())
mono (PEmb-0) (via e ()) s lt
coh (PEmb-0) (via e ()) s d

emb-fin : ∀ n (hx : HS (natᶜ n)) y (hy : HS y) → natᶜ n ≼ y → PEmb (toLevel (natᶜ n) hx) (toLevel y hy)
emb-fin zero hx y hy d = PEmb-0
emb-fin (suc n) hx (suc y) hy (s≼s d) = PEmb-suc (emb-fin n (hs⁻ hx) y (hs⁻ hy) d)
emb-fin (suc n) hx (lim f) hy (≼l k d) = PEmb-limʳ k (emb-fin (suc n) hx (f k) (hl₁ hy k) d)
emb-fin (suc n) hx _ hy (≼i {p = ()} _ _ _)
emb-fin (suc n) hx _ hy (≼u {r = ()} _)

vm-fin : ∀ n (hx : HS (natᶜ n)) y (hy : HS y) → natᶜ n ≼ y →
  ψ⁰ (Ω (toLevel (natᶜ n) hx)) ≼ ψ⁰ (Ω (toLevel y hy))
vm-fin n hx y hy d = Ψ-emb (emb-fin n hx y hy d)
```
