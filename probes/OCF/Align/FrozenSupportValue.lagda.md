# 全部实际坐标的有界分支值单调

与路径支持分开：两坐标显式处于同一合法界 B 下，再给值关系。
本篇不从值关系构造路径，也不要求可判定坐标值比较。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenSupportValue where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (mul; _≤ᵛ_)
open import OCF.Lean.Fold1Base using (⊞-≤ʳ)
import OCF.Align.FrozenValueSecond as S
import OCF.Align.FrozenInnerOuter as I
import OCF.Align.FrozenSupport as P
open import OCF.Align.FrozenOutputIf using (Generated; initial; plus; old-step; frozen-step; actual-old-generated; actual-frozen-generated)

U : KS
U = step S⊥
ValueSupport : HB U → Set
ValueSupport hz = ⊤
ValueSupport (hs a) = ValueSupport a
ValueSupport (hl f) = ∀ n → ValueSupport (f n)
ValueSupport (hΩ (inj₁ ()) g)
ValueSupport (hΩ (inj₂ _) g) =
  (∀ {B c d} → LgB B → c ⊲ B → d ⊲ B → c ≤ᵛ d → g c ≤ᵛ g d) ×
  (∀ c → ValueSupport (g c))

value-add : ∀ a b → ValueSupport a → ValueSupport b → ValueSupport (a ⊞ b)
value-add a hz pa pb = pa
value-add a (hs b) pa pb = value-add a b pa pb
value-add a (hl f) pa pb = λ n → value-add a (f n) pa (pb n)
value-add a (hΩ (inj₁ ()) g) pa pb
value-add a (hΩ (inj₂ _) g) pa (mo , pb) =
  (λ l pc pd q → ⊞-≤ʳ a (mo l pc pd q)) , (λ c → value-add a (g c) pa (pb c))
value-mul : ∀ a → ValueSupport a → ∀ n → ValueSupport (mul a n)
value-mul a p zero = p
value-mul a p (suc n) = value-add (mul a n) a (value-mul a p n) p

old-pure : ∀ w c → ValueSupport (I.P w c)
old-pure w hz = tt
old-pure w (hs c) = value-mul _ (old-pure w c)
old-pure w (hl f) = λ n → old-pure w (f n)
frozen-pure : ∀ w c → ValueSupport (I.Q w c)
frozen-pure w hz = tt
frozen-pure w (hs c) = value-mul _ (frozen-pure w c)
frozen-pure w (hl f) = λ n → frozen-pure w (f n)

old-action : ∀ w c → ValueSupport c → ValueSupport (S.OX w c)
old-action w hz p = (λ l pc pd q → P.Old.mono-P w q) , old-pure w
old-action w (hs c) p = value-mul _ (old-action w c p)
old-action w (hl f) p = λ n → old-action w (f n) (p n)
old-action w (hΩ (inj₁ ()) g) p
old-action w (hΩ (inj₂ tt) g) (mo , p) =
  (λ l pc pd q → P.Old.mono-H w (mo l pc pd q)) , (λ c → old-action w (g c) (p c))
frozen-action : ∀ w c → ValueSupport c → ValueSupport (S.NX w c)
frozen-action w hz p = (λ l pc pd q → P.Frozen.mono-P w q) , frozen-pure w
frozen-action w (hs c) p = value-mul _ (frozen-action w c p)
frozen-action w (hl f) p = λ n → frozen-action w (f n) (p n)
frozen-action w (hΩ (inj₁ ()) g) p
frozen-action w (hΩ (inj₂ tt) g) (mo , p) =
  (λ l pc pd q → P.Frozen.mono-H w (mo l pc pd q)) , (λ c → frozen-action w (g c) (p c))

up-support : ∀ c → ValueSupport (up {S⊥} c)
up-support hz = tt
up-support (hs c) = up-support c
up-support (hl f) = λ n → up-support (f n)

generated-value : ∀ {c} → Generated c → ValueSupport c
generated-value initial = (λ l pc pd q → P.up-value q) , up-support
generated-value (plus {a} {b} p q) = value-add a b (generated-value p) (generated-value q)
generated-value (old-step w {c} p) = old-action w c (generated-value p)
generated-value (frozen-step w {c} p) = frozen-action w c (generated-value p)

old-value : ∀ n → ValueSupport (S.Old.ce n)
old-value n = generated-value (actual-old-generated n)
frozen-value : ∀ n → ValueSupport (S.Frozen.ce n)
frozen-value n = generated-value (actual-frozen-generated n)
```

实际吸收证明若只持有 c≤ᵛd，仍必须另给公共合法界的路径证据。
本篇并未解决该义务，也未证明 OT/NT 比较。
