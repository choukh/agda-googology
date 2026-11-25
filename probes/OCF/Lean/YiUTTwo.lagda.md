# two 上的完整干净试验对象
验收文件；编译定理：指定 ℓ₂ 合法、标准底闭项存在，目标全 HC 域非空。
shape 为指定闭项计算测试，原闭项接线为等式；Goal 是未填的 ψ₀(Ω_{Ω₂}) 全 HC 值界。
来源：合法性用 YiRWPath.Ok⊕/OkO↑；折叠封装与内链复用 YiE4Base/YiE4Inner；目标证书用 YiAZLocal。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUTTwo where
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiE4Base as Q
import OCF.Lean.YiE4Inner as I
import OCF.Lean.YiAZLocal as AL
import OCF.Lean.YiAbsSimInst as SI
open import OCF.Align.Value using (_≼_)

o-two : P.Ok K.two
o-two = tt , λ _ → tt , λ _ → tt
ℓ₂ : B.L
ℓ₂ = K.two B.⊕ B.↑ K.two (proj₁ (O.Ωt K.two))
o₂ : P.Ok ℓ₂
o₂ = P.Ok⊕ K.two (B.↑ K.two (proj₁ (O.Ωt K.two))) o-two
  (P.OkO↑ K.two K.two o-two P.self (proj₁ (O.Ωt K.two)))
a : B.Tr K.one → B.L
a d = K.two B.⊕ (B.zero B.⊕ B.↑ K.one (B.suc d))
shape : ℓ₂ ≡ B.nd (B.sΩ K.one) a
shape = refl
ctx : Q.Ctx
ctx = ℓ₂ , o₂ , MT.rbᶻ ℓ₂ , F.B₀ ℓ₂
opaque
  output : O.Tr⁺ B.zero
  output = Q.collapse ctx (O.Ωt B.zero)
  output-eq : output ≡ Q.collapse ctx (O.Ωt B.zero)
  output-eq = refl
  raw-output : output ≡ MT.ψ₀ᶻ ℓ₂ o₂ (proj₁ (O.Ωt ℓ₂))
  raw-output = Q.collapse-eq ℓ₂ o₂ (MT.rbᶻ ℓ₂) (F.B₀ ℓ₂) (O.Ωt B.zero)
module Inner = I.Inner K.one a o₂ (MT.rbᶻ ℓ₂) (F.B₀ ℓ₂) (O.Ωt B.zero)
row : output ≡ O.limc⁺ (λ n → Inner.out (Inner.chain n))
row = trans output-eq Inner.row
Goal : Set
Goal = (h : SI.E.HC (AL.S 2)) → SI.E.tree h ≼ K.readRW (proj₁ output)
nonempty : SI.E.HC (AL.S 2)
nonempty = AL.hc-S 2
```
