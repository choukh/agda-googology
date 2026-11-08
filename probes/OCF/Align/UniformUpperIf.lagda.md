# 接受实际零规则的采样关系

验收关系增加一个已实证的零规则：1 的末段输出不高于最低 Ω 地板。
Ω配对仍比较所有有序可数坐标，最后的语义必须保留实际动态种子。
本接口不要求加法同余；新增零规则能否穿过任意前缀不能默认成立。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.UniformUpperIf where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
import OCF.Align.BoundedNativeTerminalReady as T
open import OCF.Align.BoundedCompletionTerminalValueClosure using (floor)

U : KS
U = step S⊥
data Rel : HB U → HB U → Set where
  rz : ∀ {b} → Rel hz b
  rs : ∀ {a b} → Rel a b → Rel (hs a) (hs b)
  rr : ∀ {a b} → Rel a b → Rel a (hs b)
  rl : ∀ {f b} → (∀ n → Rel (f n) b) → Rel (hl f) b
  ri : ∀ {a f} n → Rel a (f n) → Rel a (hl f)
  ro : ∀ {f g : Cd → HB U} → (∀ {c d} → c ≤ᵛ d → Rel (f c) (g d)) →
    Rel (hΩ (inj₂ tt) f) (hΩ (inj₂ tt) g)
  ru : ∀ {a g} → (∀ c → Rel a (g c)) → Rel a (hΩ (inj₂ tt) g)
  base : Rel (hs hz) floor

record SamplingComparison : Set₁ where
  field
    evaluate : ∀ {a b u v} → Rel a b → u ≤ᵛ v → T.fold u a ≤ᵛ T.fold v b

actual-base : Rel (hs hz) floor
actual-base = base
```

base 是原 act 的实际零输出与真实最低地板，并非不可满足的假设。
后续实例将给全部旧坐标上的采样比较，不据此直接声称序数上界。
