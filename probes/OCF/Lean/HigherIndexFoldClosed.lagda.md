# 实际含Ω坐标的全θ分支及动态输出

输入逐字取原高层地板在flL U坐标的θ分支。它包含指标旧Ω及全部Cd
分支；不是把该坐标裁成有限高度。低世界扩界保证新选的合法化Cd坐标可入。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.HigherIndexFoldClosed where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy using (ls; lz)
open import OCF.Lean.LHRecFl using (flL; Lg-flL; cxI; gcF; Lg-ι)
open import OCF.Lean.LHRecLeg using (module New)
open import OCF.Lean.HigherIndexClassIf
open import OCF.Lean.HigherIndexFoldIf
import OCF.Lean.HigherIndexFoldPath as P
import OCF.Lean.HigherIndexFoldRun as R

θ : HB U → HB Source
θ = New.θ (cxI k g) (gcF (λ d → ι (inj₂ d) (flL (g d))))

pure-position : ∀ β (d : Cd) κ → Position (tt , β) (up d) κ
pure-position β hz κ = tt
pure-position β (hs d) (inj₁ κ) = pure-position β d κ
pure-position β (hs d) (inj₂ _) = tt
pure-position β (hl f) (n , κ) = pure-position β (f n) κ
pure-position β (hΩ () f) κ

component : ∀ β B (d : Cd) → up d ⊲[ tt , β ] B →
  ∀ (a : HB (Native (up d))) → Path β B (ι (inj₂ (up d)) a)
component β B d p hz = tt
component β B d p (hs a) = component β B d p a
component β B d p (hl f) = λ n → component β B d p (f n)
component β B d p (hΩ κ f) = (p , pure-position β d κ) , λ e → component β B d p (f e)

pure-θ : ∀ β B (d : Cd) → up d ⊲[ tt , β ] B → Path β B (θ (up d))
pure-θ β B hz p = tt
pure-θ β B (hs d) p = P.add _ _
  (pure-θ β B d (⊲ᴮ-tr (hsuc hself) p))
  (component β B d (⊲ᴮ-tr (hsuc hself) p) (flL (g (up d))))
pure-θ β B (hl f) p = λ n → pure-θ β B (f n) (⊲ᴮ-tr (hlim n hself) p)
pure-θ β B (hΩ () f) p

coordinate : HB U
coordinate = flL k
coordinate-legal : LgB coordinate
coordinate-legal = Lg-flL k
input : HB Source
input = θ coordinate
input-shape : input ≡ hΩ (inj₁ tt , inj₁ (inj₂ tt)) (λ c → θ (up c))
input-shape = refl

input-legal : LgB input
input-legal = New.Lg-θ (cxI k g) _ legal-addend coordinate coordinate-legal
  where
  legal-addend : ∀ d → LgB (gcF (λ d → ι (inj₂ d) (flL (g d))) d)
  legal-addend hz = tt
  legal-addend (hs d) = Lg-ι (inj₂ d) (flL (g d)) (Lg-flL (g d))
  legal-addend (hl f) = tt
  legal-addend (hΩ κ f) = tt

input-path : ∀ β → Path β coordinate input
input-path β e qe le = pure-θ (hs e) coordinate e (hLim (hsuc hself) hself)

output : HB (Native hz)
output = R.fold hz tt coordinate coordinate-legal hz (z⊲ᴮ coordinate) input (input-path hz)
```

此output是实际结构递归计算的全输出。输入合法，路径全部实例化；尚未
证明output合法或与输入保值。完整高层floor的最高指标分支需要对任意
leg k c构造Path，pure-θ尚不覆盖其一般Ω内部层分量，不能据本闭项默认解决。
