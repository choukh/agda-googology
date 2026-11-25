# 指定 two 对象的树侧陈述
不读记号；与 YiUTTwo 完全相同的标准底、最小表、路径和层号，接线在 YiTMAccept。
TreeBound 与 ChildBound 尚未实填；合法闭项及条件归约不算完成值证明。
来源：YiUTTwo 的干净定义逐字展开 K.one/K.two；内链复用 YiTMInner。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTMObjects where
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTVPsi as Q
import OCF.Lean.YiTMInner as I

one two : B.L
one = B.nd B.sS (λ _ → B.zero)
two = B.nd B.sS (λ _ → one)
o-one : P.Ok one
o-one = tt , λ _ → tt
o-two : P.Ok two
o-two = tt , λ _ → tt , λ _ → tt
ℓ₂ : B.L
ℓ₂ = two B.⊕ B.↑ two (proj₁ (O.Ωt two))
o₂ : P.Ok ℓ₂
o₂ = P.Ok⊕ two (B.↑ two (proj₁ (O.Ωt two))) o-two
  (P.OkO↑ two two o-two P.self (proj₁ (O.Ωt two)))
a : B.Tr one → B.L
a d = two B.⊕ (B.zero B.⊕ B.↑ one (B.suc d))
module Inner = I.Inner one a o₂ (MT.rbᶻ ℓ₂) (F.B₀ ℓ₂) (O.Ωt B.zero)
output : O.Tr⁺ B.zero
output = I.collapse ℓ₂ o₂ (MT.rbᶻ ℓ₂) (F.B₀ ℓ₂) (O.Ωt B.zero)
c₁ : B.Tr one
c₁ = Inner.chain 1
v₁ : V.V one
v₁ = V.val one c₁
hv₁ : V.LegV one v₁
hv₁ = V.val-leg one c₁
opaque
  unfolding Inner.out Inner.g
  out-child : ∀ d → Inner.out d ≡ MT.ψ₀ᶻ (a d) (proj₂ o₂ d) (proj₁ (O.Ωt (a d)))
  out-child d = refl
opaque
  unfolding Inner.feed Inner.g
  input-low : V.val one (proj₁ (O.Ωt one)) V.≼ v₁
  input-low = V.◁→≼ (V.val-mono one
    (TB.mono ℓ₂ o₂ (MT.rbᶻ ℓ₂) (F.B₀ ℓ₂) one (P.ink P.self) (O.Ωt one)
      (proj₂ (O.upz {s = B.sΩ one} {h = a} B.zero (O.Ωt (a B.zero))))))
TreeBound ChildBound : Set
TreeBound = Q.Ψ one o-one v₁ hv₁ V.≼ V.val B.zero (proj₁ output)
ChildBound = Q.Ψ one o-one v₁ hv₁ V.≼ V.val B.zero (proj₁ (Inner.out c₁))
child→tree : ChildBound → TreeBound
child→tree p = V.≼-trans p (Inner.point-row 1)
```
