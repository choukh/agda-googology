# 全有限地板的有证重定位

先给任意可数层c的一步关系实例，再用原地板填所有自证前提。
这与完整raw关系的GeneralRebaseActual分开，不把两种关系混用。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.GeneralRebaseSampleActual where
open import Data.Nat using (suc)
open import Data.Sum using (inj₁; inj₂)
open import OCF.Lean.CRwBase
open import OCF.Align.BoundedDescentValueBridge using (Native)
open import OCF.Align.BoundedCompletionFiniteBridgePaths using (num)
open import OCF.Align.BoundedCompletionFiniteRunClosure using (floor)
open import OCF.Lean.RebaseLayerIf using (Value; Admit; Coord)
import OCF.Lean.RebaseLayerActual as Actual
import OCF.Lean.GeneralRebaseSampleIf as I
import OCF.Lean.GeneralRebaseSampleRun as R

enc : ∀ c → HB (Native c) → HB (Native (hs c)) → HB (Native (hs c))
enc c = I.Layer.enc (Native c) (Admit c) (Coord c)
to-generic : ∀ c {a b} → Value (hs c) a b →
  I.Layer.R⁺ (Native c) (Admit c) (Coord c) a b
to-generic c = R.relabel
  (λ { (inj₁ κ) e p → p; (inj₂ _) e p → p })
  (λ { (inj₁ κ) x y p → p; (inj₂ _) x y p → p })
from-generic : ∀ c {a b} → I.Layer.R⁺ (Native c) (Admit c) (Coord c) a b →
  Value (hs c) a b
from-generic c = R.relabel
  (λ { (inj₁ κ) e p → p; (inj₂ _) e p → p })
  (λ { (inj₁ κ) x y p → p; (inj₂ _) x y p → p })

mono : ∀ c {a b u v} → Value (hs c) a b → Value c u v →
  Value c u u → Value c v v → Value (hs c) (enc c u a) (enc c v b)
mono c p uv uu vv = from-generic c
  (R.Layer.mono (Native c) (Admit c) (Coord c) (to-generic c p) uv uu vv)
inflate : ∀ c {a b} → Value (hs c) a b → ∀ m → Value c m m →
  Value (hs c) a (enc c m b)
inflate c p m sm = from-generic c
  (R.Layer.inflate (Native c) (Admit c) (Coord c) (to-generic c p) m sm)

floor-self : ∀ n → Value (num (suc n))
  (enc (num n) (floor n) (floor (suc n)))
  (enc (num n) (floor n) (floor (suc n)))
floor-self n = mono (num n) (Actual.floor-self (suc n))
  (Actual.floor-self n) (Actual.floor-self n) (Actual.floor-self n)
floor-inflate : ∀ n → Value (num (suc n)) (floor (suc n))
  (enc (num n) (floor n) (floor (suc n)))
floor-inflate n = inflate (num n) (Actual.floor-self (suc n)) (floor n) (Actual.floor-self n)
```

前提在每个n都有实际地板实例。它没有给高层原at保持SampleValue，
也没有据此宣布EBO下界；缺口由独立Native比较路线检验。
