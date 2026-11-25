# 第 1 层的 Ω 头消去
验收文件；编译目标是变量上的 Ω 头消去及规范实例，不重建大闭项的构造子等式。
不实填 YiC1Slot.BranchNeed，不声称实际 NextSlot 或零层第 1 项下界。
来源：头与分支观察复用 YiC1Slot，关系构造子来自 YiKVRel/YiCLFam；规范分支证明取自 YiCLFam.Mβ。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRXOmegaHead where
open import Data.List using ([])
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiANFam as A
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiC1Slot as S
import OCF.Align.EboLeanDef as E

omega-head : (t : E.T) (x : B.Tr K.one)
  → E.cof t ≡ E.cΩ [] → S.head x ≡ S.hΩ
  → (∀ η d → K.M⁰ η d → H.M 1 (E.fsT t η) (S.br x d))
  → H.M 1 t x
omega-head t B.zero co () need
omega-head t (B.suc x) co () need
omega-head t (B.lim f a) co () need
omega-head t (B.up x c y e) co () need
omega-head t (B.Ω (inj₁ ()) g) co hd need
omega-head t (B.Ω (inj₂ (tt , inj₂ ())) g) co hd need
omega-head t (B.Ω (inj₂ (tt , inj₁ tt)) g) co hd need = K.mΩ co refl need


base : B.Tr K.one
base = proj₁ (O.Ωt K.one)

base-head : S.head base ≡ S.hΩ
base-head = refl

base-cof : E.cof (E.Ωt (E.natT 1)) ≡ E.cΩ []
base-cof = refl

base-branches : ∀ η d → K.M⁰ η d
  → H.M 1 (E.fsT (E.Ωt (E.natT 1)) η) (S.br base d)
base-branches η d m = subst (λ t → H.M 1 t (S.br base d)) (sym (A.fsTΩ 0 η))
  (K.mU K.mz (K.mw m B.◃s))

base-instance : H.M 1 (E.Ωt (E.natT 1)) base
base-instance = omega-head (E.Ωt (E.natT 1)) base base-cof base-head base-branches
```
