# 第二分量实际坐标的递归分支单调性

支持谓词不是生成历史的别名：它要求每个 Ω 分支沿有字面公共界的坐标
路径值单调，并且所有分支递归满足同一性质。用于真实 ce 轨道；不是
OT/NT 的同余或任意旧低界被吸收的断言。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenSupport where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (mul; _≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l; ≤Ω; Ω≤Ω)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans; mul-≤; ⊞-≤ʳ; up-⊲)
import OCF.Align.FrozenValueSecond as S
import OCF.Align.FrozenInnerOuter as I

U : KS
U = step S⊥

Support : HB U → Set
Support hz = ⊤
Support (hs a) = Support a
Support (hl f) = ∀ n → Support (f n)
Support (hΩ (inj₁ ()) g)
Support (hΩ (inj₂ _) g) =
  (∀ {c d} → c ⊲ d → LgB d → g c ≤ᵛ g d) × (∀ c → Support (g c))

support-add : ∀ a b → Support a → Support b → Support (a ⊞ b)
support-add a hz sa sb = sa
support-add a (hs b) sa sb = support-add a b sa sb
support-add a (hl f) sa sb = λ n → support-add a (f n) sa (sb n)
support-add a (hΩ (inj₁ ()) g) sa sb
support-add a (hΩ (inj₂ _) g) sa (mo , sb) =
  (λ p ld → ⊞-≤ʳ a (mo p ld)) , (λ c → support-add a (g c) sa (sb c))

support-mul : ∀ a → Support a → ∀ n → Support (mul a n)
support-mul a sa zero = sa
support-mul a sa (suc n) = support-add (mul a n) a (support-mul a sa n) sa

pos-value : ∀ {a b : Cd} → a ⊲ b → a ≤ᵛ b
pos-value hself = ≤-refl _
pos-value (hsuc p) = ≤s (pos-value p)
pos-value (hlim n p) = ≤l n (pos-value p)

-- 参数只包装两种真实坐标作用的构造子方程，不预设任何输出比较。
module Action (H : HB U → HB U) (P : Cd → HB U)
  (pz : P hz ≡ hs hz)
  (ps : ∀ a → P (hs a) ≡ hl (mul (P a)))
  (pl : ∀ f → P (hl f) ≡ hl (λ n → P (f n)))
  (hz′ : H hz ≡ hΩ (inj₂ tt) P)
  (hs′ : ∀ a → H (hs a) ≡ hl (mul (H a)))
  (hl′ : ∀ f → H (hl f) ≡ hl (λ n → H (f n)))
  (ho′ : ∀ g → H (hΩ (inj₂ tt) g) ≡ hΩ (inj₂ tt) (λ c → H (g c))) where

  positive-P : ∀ c → hs hz ≤ᵛ P c
  positive-P hz rewrite pz = s≤s z≤
  positive-P (hs c) rewrite ps c = ≤l 0 (positive-P c)
  positive-P (hl f) rewrite pl f = ≤l 0 (positive-P (f 0))

  mono-P : ∀ {a b : Cd} → a ≤ᵛ b → P a ≤ᵛ P b
  mono-P {b = b} z≤ rewrite pz = positive-P b
  mono-P {hs a} {hs b} (s≤s p) rewrite ps a | ps b = l≤ (λ n → ≤l n (mul-≤ (mono-P p) n))
  mono-P {b = hs b} (≤s p) rewrite ps b = ≤l 0 (mono-P p)
  mono-P {hl f} (l≤ p) rewrite pl f = l≤ (λ n → mono-P (p n))
  mono-P {b = hl f} (≤l n p) rewrite pl f = ≤l n (mono-P p)

  support-P : ∀ c → Support (P c)
  support-P hz rewrite pz = tt
  support-P (hs c) rewrite ps c = support-mul (P c) (support-P c)
  support-P (hl f) rewrite pl f = λ n → support-P (f n)

  positive-H : ∀ c → H hz ≤ᵛ H c
  positive-H hz = ≤-refl _
  positive-H (hs c) rewrite hs′ c = ≤l 0 (positive-H c)
  positive-H (hl f) rewrite hl′ f = ≤l 0 (positive-H (f 0))
  positive-H (hΩ (inj₁ ()) g)
  positive-H (hΩ (inj₂ tt) g) rewrite ho′ g = ≤Ω hz (positive-H (g hz))

  mono-H : ∀ {a b} → a ≤ᵛ b → H a ≤ᵛ H b
  mono-H {b = b} z≤ = positive-H b
  mono-H {hs a} {hs b} (s≤s p) rewrite hs′ a | hs′ b = l≤ (λ n → ≤l n (mul-≤ (mono-H p) n))
  mono-H {b = hs b} (≤s p) rewrite hs′ b = ≤l 0 (mono-H p)
  mono-H {hl f} (l≤ p) rewrite hl′ f = l≤ (λ n → mono-H (p n))
  mono-H {b = hl f} (≤l n p) rewrite hl′ f = ≤l n (mono-H p)
  mono-H {b = hΩ (inj₁ ()) g} (≤Ω c p)
  mono-H {b = hΩ (inj₂ tt) g} (≤Ω c p) rewrite ho′ g = ≤Ω c (mono-H p)
  mono-H {hΩ (inj₁ ()) g} (Ω≤Ω p)
  mono-H {hΩ (inj₂ tt) g} {hΩ _ h} (Ω≤Ω p) rewrite ho′ g | ho′ h = Ω≤Ω (λ c → mono-H (p c))

  support-H : ∀ c → Support c → Support (H c)
  support-H hz p rewrite hz′ = (λ q ld → mono-P (pos-value q)) , support-P
  support-H (hs c) p rewrite hs′ c = support-mul (H c) (support-H c p)
  support-H (hl f) p rewrite hl′ f = λ n → support-H (f n) (p n)
  support-H (hΩ (inj₁ ()) g) p
  support-H (hΩ (inj₂ tt) g) (mo , p) rewrite ho′ g =
    (λ q ld → mono-H (mo q ld)) , (λ c → support-H (g c) (p c))

module Old (w : _) = Action (S.OX w) (I.P w) refl (λ a → refl) (λ f → refl)
  refl (λ a → refl) (λ f → refl) (λ g → refl)
module Frozen (w : _) = Action (S.NX w) (I.Q w) refl (λ a → refl) (λ f → refl)
  refl (λ a → refl) (λ f → refl) (λ g → refl)

up-support : ∀ c → Support (up {S⊥} c)
up-support hz = tt
up-support (hs c) = up-support c
up-support (hl f) = λ n → up-support (f n)

up-value : ∀ {a b : Cd} → a ≤ᵛ b → up a ≤ᵛ up b
up-value z≤ = z≤
up-value (s≤s p) = s≤s (up-value p)
up-value (≤s p) = ≤s (up-value p)
up-value (l≤ p) = l≤ (λ n → up-value (p n))
up-value (≤l n p) = ≤l n (up-value p)

old-support : ∀ n → Support (S.Old.ce n)
old-support zero = (λ p ld → up-value (pos-value p)) , up-support
old-support (suc n) = support-add _ _ (old-support n)
  (Old.support-H (S.Old.cw n) _ (old-support n))
frozen-support : ∀ n → Support (S.Frozen.ce n)
frozen-support zero = (λ p ld → up-value (pos-value p)) , up-support
frozen-support (suc n) = support-add _ _ (frozen-support n)
  (Frozen.support-H (S.Frozen.cw n) _ (frozen-support n))
```

全部 ce n 的分支沿字面坐标路径单调已由构造闭包推出；没有把 Same
当折叠同余。还未证明旧低界来自某条内轨道时可由冻结输出吸收。
