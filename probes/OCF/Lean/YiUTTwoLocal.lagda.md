# 干净 two 对象的源关系与实际初项
验收文件；编译定理：源 Ω 树具有 Ω_{Ω₂} 的 R 关系，首链点具有有限层 ψ₁(Ω₃) 关系。
零层输出的全 HC 下界为 ψ₀(Ω₃)；feed0 为固定初项计算测试，未完成 ψ₀(Ω_{Ω₂})，没有输出上界或否定。
来源：源关系用 YiNLRaise.raiseR/YiGICheck.leaf-fin；有限层折叠用 YiTBFam.sΩ-LF；全 HC 出口用 YiKVRel.lower⁰。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUTTwoLocal where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (Σ; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; sym)
open import OCF.Lean.YiUTTwo
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiTBFam as LF
open import OCF.Lean.YiRBFam using (tu; can; pu)
open import OCF.Lean.YiCLLow using (s0; ss)
open import OCF.Lean.YiCLFam using (fn)
import OCF.Align.EboLeanDef as E
import OCF.Align.EBO as EB
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiGICheck as GC
import OCF.Lean.YiNLRaise as NR
import OCF.Lean.YiLLCheck as LL
open import OCF.Lean.YiNLCtx using (prefix)
open import OCF.Align.EboLean3Base using (Ωt-mono)
open import Data.Sum using (inj₁)
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiExInst as XI
import OCF.Lean.YiAZLocal as AL
import OCF.Lean.YiANEnd as AN
import OCF.Lean.YiNFOCase as NC
import OCF.Align.EboLeanBase as NB
import OCF.Align.EboLeanTree as ET
open import OCF.Align.Value using (_≼_; ≼-trans)
opaque
  unfolding Inner.out Inner.g
  out-child : ∀ d → Inner.out d ≡ MT.ψ₀ᶻ (a d) (proj₂ o₂ d) (proj₁ (O.Ωt (a d)))
  out-child d = refl
opaque
  unfolding Inner.feed Inner.g
  feed0 : Inner.feed B.zero ≡ proj₁ (TB.ψ (a B.zero) (proj₂ o₂ B.zero) (MT.rbᶻ (a B.zero))
    (F.B₀ (a B.zero)) K.one (P.inu (λ _ → P.inc tt P.self)) (O.Ωt K.one) (proj₁ (O.Ωt (a B.zero))))
  feed0 = refl
first : H.M 1 (E.ψ (E.natT 1) (E.Ωt (E.natT 3)) ∷ []) (Inner.chain 1)
first = subst (H.M 1 (E.ψ (E.natT 1) (E.Ωt (E.natT 3)) ∷ [])) (sym feed0)
  (LF.sΩ-LF {n = 2} {j = 1} (proj₂ o₂ B.zero) (MT.rbᶻ (a B.zero)) (tu (can (ss s0)))
    (F.B₀ (a B.zero)) (O.Ωt K.one) (λ i u → K.⊴r) (H.Mβ 0))

small : E.T
small = E.ψ [] (E.Ωt (E.natT 3)) ∷ []
zero-rel : K.M⁰ small (proj₁ (Inner.out B.zero))
zero-rel = subst (λ z → K.M⁰ small (proj₁ z)) (sym (out-child B.zero))
  (LF.sΩ-LF {n = 2} {j = 0} (proj₂ o₂ B.zero) (MT.rbᶻ (a B.zero)) (tu (pu (pu (can s0))))
    (F.B₀ (a B.zero)) (O.Ωt B.zero) (λ i u → K.⊴r) (K.m1 refl K.mz))

source : GR.R ℓ₂ (E.Ωt (E.Ωt (E.natT 2))) (proj₁ (O.Ωt ℓ₂))
source = NR.raiseR K.two (prefix K.two) [] (GR.c0 refl)
  (LL.rdown K.two (Ωt-mono (inj₁ E.[]<)) (GC.leaf-fin 2)) (GC.leaf-fin 2)

small-rel : K.M⁰ small (proj₁ output)
small-rel = subst (λ z → K.M⁰ small (proj₁ z)) (sym row)
  (K.G⁰.m-cum (λ n → Inner.out (Inner.chain n)) 0 zero-rel)
small-value : (h : SI.E.HC small) → SI.E.tree h ≼ K.readRW (proj₁ output)
small-value h = ≼-trans (XI.tree-back h) (K.lower⁰ small-rel (XI.back h))
small<row0 : small E.<ᵀ E.fsn (AL.S 2) 0
small<row0 = E.hd< (E.ar< (E.hd< (E.lv< (EB.natT<Ωs 3 []))))

small-nf : NB.NF small
small-nf = NB.nf-ψ NB.n[] (NB.nf-Ω (AN.natB 3)) (NC.flatGB (AN.fΩN 3))
opaque
  small-hc : SI.E.HC small
  small-hc = SI.conv (ET.hc small-nf (NB.c∷ NB.c[]))

P : ℕ → B.Tr B.zero
P = O.cum (λ n → proj₁ (Inner.out (Inner.chain n)))
FirstRow : Set
FirstRow = Σ ℕ λ q → K.M⁰ (E.fsn (AL.S 2) 0) (P q)
Rows : Set
Rows = ∀ n → Σ ℕ λ q → K.M⁰ (E.fsn (AL.S 2) n) (P q)
```
