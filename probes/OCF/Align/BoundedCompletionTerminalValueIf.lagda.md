# 末段回灌的有向值关系接口

不能使用任取Ω坐标的裸值序来证明折叠单调。本关系的Ω配对显式要求
对有序可数坐标的异坐标分支比较；Ω右规则只准对所有分支都成立的
统一下界。它没有任取一个坐标的Ω左规则，也没有下标判等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedCompletionTerminalValueIf where
open import Data.Nat using (ℕ)
open import Data.Sum using (inj₂)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Align.BoundedDescentValueBridge using (Native)
import OCF.Align.BoundedNativeTerminalReady as T

U : KS
U = Native hz

data VRel : HB U → HB U → Set where
  vz : ∀ {b} → VRel hz b
  vs : ∀ {a b} → VRel a b → VRel (hs a) (hs b)
  vr : ∀ {a b} → VRel a b → VRel a (hs b)
  vl : ∀ {f b} → (∀ n → VRel (f n) b) → VRel (hl f) b
  vli : ∀ {a f} n → VRel a (f n) → VRel a (hl f)
  vo : ∀ {f g : Cd → HB U} →
    (∀ {c d} → c ≤ᵛ d → VRel (f c) (g d)) →
    VRel (hΩ (inj₂ tt) f) (hΩ (inj₂ tt) g)
  vor : ∀ {a : HB U} {g : Cd → HB U} →
    (∀ c → VRel a (g c)) → VRel a (hΩ (inj₂ tt) g)

record TerminalComparison : Set₁ where
  field
    compare : ∀ {a b} → VRel a b → ∀ {u v} → u ≤ᵛ v →
      T.fold u a ≤ᵛ T.fold v b
```

接口compare待实际原fold证明。其前提的实际up、地板和前缀实例在后文
给出；不得只由此接口或VRel的名字宣称单调成立。
