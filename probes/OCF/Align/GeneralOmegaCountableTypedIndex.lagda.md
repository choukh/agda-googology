# 同一原高度参照层内的严格路径反射

验收专用。只反射TypedHeight.height B自身的旧严格前驱，不反射
任意toLevel输入到完成高度。右边原种类秩的合法证由所得路径取出，
保留原旧层j与该秩参照层的字面等式，不要求任何路径证明无关。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GeneralOmegaCountableTypedIndex where
open import Data.Unit using (tt)
open import Data.Product using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.CRwBase
import OCF.Align.Level as L
open import OCF.Align.GeneralOmegaCountableTypedHeight using (height; index-bound)

record Origin (B : Cd) (lB : LgB B) (j : L.Ordᴵ) : Set where
  constructor origin
  field
    native : Cd
    path : hs native ⊲ B
    index : j ≡ height native (lgB⊲ path tt lB)

reflect : ∀ B lB {j} → j L.<ᴵ height B lB → Origin B lB j
reflect hz lB ()
reflect (hs B) lB L.zero = origin B hself refl
reflect (hs B) lB (L.suc p) with reflect B lB p
... | origin i pi eq = origin i (hsuc pi) eq
reflect (hl f) lB (L.lim n p) with reflect (f n) (proj₂ lB n) p
... | origin i pi eq = origin i (hlim n pi) eq
reflect (hΩ () f) lB p

forward : ∀ {B lB j} → Origin B lB j → j L.<ᴵ height B lB
forward {B} {lB} (origin i pi eq) = subst (λ x → x L.<ᴵ height B lB)
  (sym eq) (index-bound lB pi)
```

reflect给每条原旧严格路径一个实际native秩及原位置；forward只证
所得存在证可回送为严格前驱，不声称这条回送证明等于原p。整个
比较仍限于同一个原合法B和其同形参照层，不提供输入完成的运输。
