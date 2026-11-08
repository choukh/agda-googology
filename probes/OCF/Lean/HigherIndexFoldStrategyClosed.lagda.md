# 原反例完整组件的动态证书实例

输入与HigherIndexFoldNegComponent逐字相同：把c=flL U的整个地板
注入原Source。不是换为pureθ或常值树；新的低指标事件在组件内部更新β。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexFoldStrategyClosed where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (lz)
open import OCF.Lean.LHRecFl using (flL; Lg-flL; cxI; gcF; Lg-ι)
open import OCF.Lean.LHRecLeg using (module New)
open import OCF.Lean.HigherIndexClassIf
open import OCF.Lean.HigherIndexFoldIf using (k; g; Source)
open import OCF.Lean.HigherIndexFoldStrategyIf
import OCF.Lean.HigherIndexFoldStrategyPath as P
import OCF.Lean.HigherIndexFoldStrategyRun as R
open import OCF.Lean.HigherIndexFoldClosed using (pure-position)

omega : HB U
omega = flL k
B : HB U
B = hs omega

injected-add : ∀ {β B} c (a b : HB (Native c)) →
  Path β B (ι (inj₂ c) a) → Path β B (ι (inj₂ c) b) → Path β B (ι (inj₂ c) (a ⊞ b))
injected-add c a hz pa pb = pa
injected-add c a (hs b) pa pb = injected-add c a b pa pb
injected-add c a (hl f) pa pb = λ n → injected-add c a (f n) pa (pb n)
injected-add c a (hΩ κ f) pa pb with route c κ
... | fixed = Data.Product.proj₁ pb , λ e → injected-add c a (f e) pa (Data.Product.proj₂ pb e)
... | changing to fr rt tr = Data.Product.proj₁ pb , λ e qe le →
  injected-add c a (f (to e)) (P.mono (hsuc qe) hself (ι (inj₂ c) a) pa) (Data.Product.proj₂ pb e qe le)

nested : ∀ β (d : Cd) → d ⊲ β → ∀ (a : HB (Native (up d))) →
  Path β B (ι (inj₂ omega) (ι (inj₂ d) a))
nested β d bd hz = tt
nested β d bd (hs a) = nested β d bd a
nested β d bd (hl f) = λ n → nested β d bd (f n)
nested β d bd (hΩ κ f) with route (up d) κ
... | fixed = (hsuc hself , bd , pure-position β d κ) , λ e → nested β d bd (f e)
... | changing to fr rt tr = (hsuc hself , bd , pure-position β d κ) ,
  λ e qe le → nested (hs e) d (⊲ᴮ-tr bd (hsuc qe)) (f (to e))

inner : Cd → HB (Native omega)
inner = New.θ (cxI lz (λ d → g (up d)))
  (gcF (λ d → ι (inj₂ d) (flL (g (up d)))))

inner-path : ∀ β d → d ⊲ β → Path β B (ι (inj₂ omega) (inner d))
inner-path β hz p = tt
inner-path β (hs d) p = injected-add omega _ _
  (inner-path β d (⊲ᴮ-tr (hsuc hself) p))
  (nested β d (⊲ᴮ-tr (hsuc hself) p) (flL (g (up d))))
inner-path β (hl f) p = λ n → inner-path β (f n) (⊲ᴮ-tr (hlim n hself) p)
inner-path β (hΩ () f) p

input : HB Source
input = ι (inj₂ omega) (flL (g omega))
input-legal : LgB input
input-legal = Lg-ι (inj₂ omega) (flL (g omega)) (Lg-flL (g omega))
input-path : ∀ β → Path β B input
input-path β = (hsuc hself , tt) , λ e qe le → inner-path (hs e) e (hsuc hself)

output : HB (Native hz)
output = R.fold hz tt B (Lg-flL k) hz (z⊲ᴮ B) input (input-path hz)
```

input-path对每个β成立，与旧Path的同输入否定构成直接对照。output仍是
研究运行结果，未证明合法或值。全Source地板还需处理一般含Ω的组件高度，
特别是rank反馈坐标的递归可入条件；本例不偷填该字段。
