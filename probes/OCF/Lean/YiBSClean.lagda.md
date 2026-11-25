# 换基候选的干净 two 对象
候选；层号与 YiUTTwo 同形，标准底，读回域证据由 rbO 构造，给出合法闭项与内层整行。
out-child、feed-child 在变量孩子上展开，均为编译定理；不宣称里程碑值界。
来源：YiUTTwo 的层号和 YiE4Inner 的封装形状；验收见 YiBSAccept。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBSClean where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiBSBase
import OCF.Lean.YiBSFold as F
import OCF.Lean.YiBSInner as I
one two : L
one = nd sS (λ _ → zero)
two = nd sS (λ _ → one)
o2 : Ok two
o2 = tt , λ _ → tt , λ _ → tt
ℓ₂ : L
ℓ₂ = two ⊕ ↑ two (proj₁ (Ωt two))
o₂ : Ok ℓ₂
o₂ = Ok⊕ two (↑ two (proj₁ (Ωt two))) o2 (OkO↑ two two o2 self (proj₁ (Ωt two)))
r₂ : Rb ℓ₂
r₂ = rbO two (↑ two (proj₁ (Ωt two))) (rb-no two) o2 (OkO↑ two two o2 self (proj₁ (Ωt two)))
a : Tr one → L
a d = two ⊕ (zero ⊕ ↑ one (suc d))
level-shape : ℓ₂ ≡ nd (sΩ one) a
level-shape = refl
module Inner = I.Inner one a o₂ r₂ (B₀ ℓ₂) (Ωt zero)
-- perf: S-1/C-10，实际输出在出生处封装。
opaque
  output : Tr⁺ zero
  output = F.ψ₀ ℓ₂ o₂ r₂ (proj₁ (Ωt ℓ₂))
  output-eq : output ≡ F.ψ₀ ℓ₂ o₂ r₂ (proj₁ (Ωt ℓ₂))
  output-eq = refl
row : output ≡ limc⁺ (λ n → Inner.out (Inner.chain n))
row = trans output-eq Inner.row
opaque
  unfolding I.Inner.out I.Inner.g
  -- perf: C-9，孩子保持为变量，不展开具体链点。
  out-child : ∀ d → Inner.out d ≡ F.ψ₀ (a d) (proj₂ o₂ d) (proj₂ r₂ d) (proj₁ (Ωt (a d)))
  out-child d = refl
opaque
  unfolding I.Inner.feed I.Inner.g
  feed-child : ∀ d → Inner.feed d ≡ proj₁ (F.ψ (a d) (proj₂ o₂ d) (proj₂ r₂ d) (B₀ (a d))
    one (self ∙ proj₂ (proj₁ o₂) d) (Ωt one) (proj₁ (Ωt (a d))))
  feed-child d = refl
```
