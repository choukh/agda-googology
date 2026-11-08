# 实际坐标的分支尊重结构双模拟

实际模型桥的坐标只能先证明 Same，不能用函数外延变成相等。
本篇证明每个实际坐标的所有 Ω 分支都尊重 Same，且这一性质递归成立。
它与 FrozenSupport 的有界路径单调不同，不从值关系反推路径。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenSupportExt where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (mul)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll; oo)
open import OCF.Align.FrozenInnerOuter using (same-refl; same-add; same-mul)
import OCF.Align.FrozenInnerOuter as I
import OCF.Align.FrozenValueSecond as S
open import OCF.Align.FrozenOutputIf using (Generated; initial; plus; old-step; frozen-step; actual-old-generated; actual-frozen-generated)

U : KS
U = step S⊥
Ext : HB U → Set
Ext hz = ⊤
Ext (hs a) = Ext a
Ext (hl f) = ∀ n → Ext (f n)
Ext (hΩ (inj₁ ()) g)
Ext (hΩ (inj₂ _) g) = (∀ {a b} → Same a b → Same (g a) (g b)) × (∀ c → Ext (g c))

ext-add : ∀ a b → Ext a → Ext b → Ext (a ⊞ b)
ext-add a hz ea eb = ea
ext-add a (hs b) ea eb = ext-add a b ea eb
ext-add a (hl f) ea eb = λ n → ext-add a (f n) ea (eb n)
ext-add a (hΩ (inj₁ ()) g) ea eb
ext-add a (hΩ (inj₂ _) g) ea (cong , eb) =
  (λ p → same-add (same-refl a) (cong p)) , (λ c → ext-add a (g c) ea (eb c))
ext-mul : ∀ a → Ext a → ∀ n → Ext (mul a n)
ext-mul a e zero = e
ext-mul a e (suc n) = ext-add (mul a n) a (ext-mul a e n) e

module Action (H : HB U → HB U) (P : Cd → HB U)
  (pz : P hz ≡ hs hz)
  (ps : ∀ a → P (hs a) ≡ hl (mul (P a)))
  (pl : ∀ f → P (hl f) ≡ hl (λ n → P (f n)))
  (hz′ : H hz ≡ hΩ (inj₂ tt) P)
  (hs′ : ∀ a → H (hs a) ≡ hl (mul (H a)))
  (hl′ : ∀ f → H (hl f) ≡ hl (λ n → H (f n)))
  (ho′ : ∀ g → H (hΩ (inj₂ tt) g) ≡ hΩ (inj₂ tt) (λ c → H (g c))) where

  same-P : ∀ {a b} → Same a b → Same (P a) (P b)
  same-P zz = same-refl _
  same-P {hs a} {hs b} (ss p) rewrite ps a | ps b = ll (same-mul (same-P p))
  same-P {hl f} {hl g} (ll p) rewrite pl f | pl g = ll (λ n → same-P (p n))
  same-P (oo {κ = ()} p)
  ext-P : ∀ c → Ext (P c)
  ext-P hz rewrite pz = tt
  ext-P (hs c) rewrite ps c = ext-mul (P c) (ext-P c)
  ext-P (hl f) rewrite pl f = λ n → ext-P (f n)

  same-H : ∀ {a b} → Same a b → Same (H a) (H b)
  same-H zz = same-refl _
  same-H {hs a} {hs b} (ss p) rewrite hs′ a | hs′ b = ll (same-mul (same-H p))
  same-H {hl f} {hl g} (ll p) rewrite hl′ f | hl′ g = ll (λ n → same-H (p n))
  same-H (oo {κ = inj₁ ()} p)
  same-H {hΩ _ f} {hΩ _ g} (oo {κ = inj₂ tt} p) rewrite ho′ f | ho′ g = oo (λ c → same-H (p c))
  ext-H : ∀ c → Ext c → Ext (H c)
  ext-H hz e rewrite hz′ = same-P , ext-P
  ext-H (hs c) e rewrite hs′ c = ext-mul (H c) (ext-H c e)
  ext-H (hl f) e rewrite hl′ f = λ n → ext-H (f n) (e n)
  ext-H (hΩ (inj₁ ()) g) e
  ext-H (hΩ (inj₂ tt) g) (cong , e) rewrite ho′ g =
    (λ p → same-H (cong p)) , (λ c → ext-H (g c) (e c))

module Old (w : _) = Action (S.OX w) (I.P w) refl (λ a → refl) (λ f → refl)
  refl (λ a → refl) (λ f → refl) (λ g → refl)
module Frozen (w : _) = Action (S.NX w) (I.Q w) refl (λ a → refl) (λ f → refl)
  refl (λ a → refl) (λ f → refl) (λ g → refl)

up-ext : ∀ c → Ext (up {S⊥} c)
up-ext hz = tt
up-ext (hs c) = up-ext c
up-ext (hl f) = λ n → up-ext (f n)
up-same : ∀ {a b : Cd} → Same a b → Same (up a) (up b)
up-same zz = zz
up-same (ss p) = ss (up-same p)
up-same (ll p) = ll (λ n → up-same (p n))

generated-ext : ∀ {c} → Generated c → Ext c
generated-ext initial = up-same , up-ext
generated-ext (plus {a} {b} p q) = ext-add a b (generated-ext p) (generated-ext q)
generated-ext (old-step w {c} p) = Old.ext-H w c (generated-ext p)
generated-ext (frozen-step w {c} p) = Frozen.ext-H w c (generated-ext p)

old-ext : ∀ n → Ext (S.Old.ce n)
old-ext n = generated-ext (actual-old-generated n)
frozen-ext : ∀ n → Ext (S.Frozen.ce n)
frozen-ext n = generated-ext (actual-frozen-generated n)
```

该性质只使实际模型桥可以在 Same 的坐标之间调用分支；它本身不是
任意带种子解释器的同余，更不是旧低界被冻结零界吸收的证明。
