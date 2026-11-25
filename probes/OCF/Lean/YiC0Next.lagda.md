# 第 1 项的指定槽位输入尚未实填
验收文件；编译定理：内链第 2 点接回实际孩子在第 1 层上的折叠，目标 HC 域有证书。
NextSlot/ChildSlot 仅为本次继续链构造时的未填关系；RowOneAtTwo 也未填，不声称前者充分。
第 0 项已由 YiC0Accept 完成；本件不否定第 1 项或整个里程碑。
来源：计算行复用 YiUTTwo 的 Inner 定义，目标基本列公式复用 YiOLMilestone.fs1。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiC0Next where
open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiC0Local as C
import OCF.Lean.YiC0Accept as Done
import OCF.Lean.YiUTTwo as U
import OCF.Lean.YiUTTwoLocal as UL
import OCF.Lean.YiAZLocal as AL
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiRefTw2 as RT
import OCF.Lean.YiExInst as XI
import OCF.Lean.YiOLMilestone as OM
import OCF.Align.EboLeanDef as E
open U using (module Inner)
row₁ : E.T
row₁ = E.fsn (AL.S 2) 1
slot : E.T
slot = E.ψ (E.natT 1) (E.ΩTower 2) ∷ []
row₁-shape : row₁ ≡ E.ψ [] (E.Ωt slot) ∷ []
row₁-shape = OM.fs1
opaque
  row₁-hc : SI.E.HC row₁
  row₁-hc = SI.conv (RT.hω-inv (XI.back U.nonempty) refl 1)
w₁ : P._≤_ K.one C.ℓ₁
w₁ = P.self P.∙ proj₂ (proj₁ U.o₂) C.c₁
child-feed : O.Tr⁺ K.one
child-feed = TB.ψ C.ℓ₁ (proj₂ U.o₂ C.c₁) (MT.rbᶻ C.ℓ₁) (F.B₀ C.ℓ₁)
  K.one w₁ (O.Ωt K.one) (proj₁ (O.Ωt C.ℓ₁))
opaque
  unfolding Inner.feed Inner.g
  feed-child : Inner.feed C.c₁ ≡ proj₁ child-feed
  feed-child = refl
chain2-child : Inner.chain 2 ≡ proj₁ child-feed
chain2-child = trans (cong Inner.feed (sym C.c₁-eq)) feed-child
NextSlot : Set
NextSlot = H.M 1 slot (Inner.chain 2)
ChildSlot : Set
ChildSlot = H.M 1 slot (proj₁ child-feed)
slot→child : NextSlot → ChildSlot
slot→child = subst (H.M 1 slot) chain2-child
child→slot : ChildSlot → NextSlot
child→slot = subst (H.M 1 slot) (sym chain2-child)
RowOneAtTwo : Set
RowOneAtTwo = K.M⁰ row₁ (UL.P 2)
```
