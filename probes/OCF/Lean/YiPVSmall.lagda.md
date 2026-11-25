# 最小实例的一个实际孩子：F2 试搬成功
验收文件；编译定理：child (suc zero) 的原折叠输出具有 YiCLFam.M 1 关系。
来源 YiANLv.Th.tcLeaf；底、路径、合法性与输出对应经 YiMTRel.S 核对，搬运用 YiPVOne.back。
记号项为第一层内部参照 AF.ψᴺ 1 (AF.Ωᴺ 4)；未证明整个 BranchNeed 或一般可数层号 Leaf。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPVSmall where
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiLegBlock as F
open import OCF.Lean.YiBRRel
chosen : B.Tr B.zero
chosen = B.suc B.zero
child-form : S.child chosen ≡ H.fn 4
child-form = refl
child-ok : P.Ok (S.child chosen)
child-ok = proj₂ S.okay chosen
child-E : RelE (S.child chosen) (F.suc (F.suc (F.suc (F.suc F.zero)))) child-ok tt tt
child-E = eS (eS (eS (eS ez)))
target-E : RelE K.one (F.suc F.zero) (H.okf 1) tt tt
target-E = eS ez

import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWFold as RF
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
import OCF.Lean.YiBRFold as BF
import OCF.Lean.YiBRLem as BL
import OCF.Lean.YiBROps as BO
import OCF.Lean.YiMTRel as MR
import OCF.Lean.YiNRHit as NR
Fchild : F.L
Fchild = F.suc (F.suc (F.suc (F.suc F.zero)))
Fone : F.L
Fone = F.suc F.zero
Fpath : F._≤_ Fone Fchild
Fpath = F.ins (F.ins (F.ins F.self))
path-R : RelW (S.lower chosen) Fpath
path-R = winuS (winuS (wincS wself))
base-R : RelBase (S.child chosen) Fchild (S.Small.child-base chosen) (F.B₀ Fchild)
base-R = BF.B₀-R (BL.E→L child-E)
no-child : NR.NoΩ (S.child chosen)
no-child = λ _ _ _ _ → tt
import OCF.Lean.YiANFam as AF
import OCF.Lean.YiANLv as AL
import OCF.Lean.YiANKp as AK
import OCF.Lean.YiLSFold as LS
import OCF.Lean.YiMEBase as ME
import OCF.Align.EboLeanDef as E
open import Data.List using ([])
open import Data.Sum using (inj₁; inj₂)
module Lv = AL.Lv []
module Tm = AK.Tm []
gd : Tm.Gd 3 (F.B₀ Fchild)
gd = Tm.mkGd (LS.ok-B₀ Fchild) (ME.m1 refl ME.mz) (λ _ → ME.m1 refl ME.mz)
module Bs = Lv.Level.Bs 2 (Lv.thB 2) tt tt (F.B₀ Fchild) gd
source-low : Lv.Cl 3 tt tt (F.B₀ Fchild) (AF.Ωᴺ 4) (F.Ωt Fchild)
source-low = Lv.Th.tcLeaf (Lv.th 2) tt tt (F.B₀ Fchild) gd AK.• [] Bs.knRoot
-- perf: S-1/C-10，输出在出生处封装，来源关系在同一封装内接出。
opaque
  Fout : F.Tr Fone
  Fout = F.ψs Fchild tt tt (F.B₀ Fchild) Fone Fpath (F.Ωt Fone) (F.Ωt-nz Fone) (F.Ωt Fchild)
  output-R : RelT K.one Fone (proj₁ (S.Small.child-out chosen)) Fout
  output-R = proj₁ (MR.S child-E no-child (S.Small.child-base chosen) (F.B₀ Fchild)
    base-R path-R (O.Ωt K.one) (BO.Ωt-R (BL.E→L target-E))
    (BO.Ωn-R (BL.E→L target-E)) (BO.Ωt-R (BL.E→L child-E)))

  Fout-low : AF.M 1 (AF.ψᴺ 1 (AF.Ωᴺ 4)) Fout
  Fout-low = proj₁ (proj₁ source-low (inj₂ (inj₂ (inj₁ tt))))

import OCF.Lean.YiPVOne as Transfer
one-child : H.M 1 (AF.ψᴺ 1 (AF.Ωᴺ 4)) (proj₁ (S.Small.child-out chosen))
one-child = Transfer.back output-R Fout-low
```
