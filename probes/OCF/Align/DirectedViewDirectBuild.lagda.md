# 直接视图证书算法的完整结构验收

直接证明冻结 `direct` 算法的全部输入合同。ω 分支的下一项确实是
`fω`，只用已有逐项等式搬运旧 HC 子证书；不识别两份 Acc 或 HC。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DirectedViewDirectBuild where

open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)
open import OCF.Lean.CRwBase using (Cd; hz; hs; hl)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll)
open import OCF.Align.EboLeanDef
open import OCF.Align.EboLeanBase using (NF; Ctbl; nf-pred; Ctbl-pred)
open import OCF.Align.EboLeanClosure using (NFω; Tω; Ctbl-fω; Ctbl-cof)
open import OCF.Align.EboLeanTrian using (t<; T-pred)
open import OCF.Align.EboLean3Omega using (Acc′; acc)
open import OCF.Align.EboLeanView using (vω; fω; fω-eq)
open import OCF.Align.DirectedViewDirectIf using (direct; DirectContract)
import OCF.Align.DirectedViewDirectIf as I
import OCF.Align.EboLean3Tree as E
import OCF.Align.TerminalFoldAccept as R

open import OCF.Align.DirectedViewBuild using (self; compose; cast-tree)

sound : ∀ {t} (nt : NF t) (ct : Ctbl t) (ac : Acc′ t) (h : HC t) →
  Same (R.read (direct nt ct ac)) (R.read (E.tree h))
sound {t} nt ct (acc rs) h = go (cof t) refl h where
  go : ∀ c (e : cof t ≡ c) (h : HC t) →
    Same (R.read (I.DirectStep.go nt ct rs c e)) (R.read (E.tree h))
  go c0 e (h0 eh) = zz
  go c1 e (h1 eh h′) = ss (sound (nf-pred nt) (Ctbl-pred ct)
    (rs (nf-pred nt) (t< (T-pred t e))) h′)
  go cω e (hω eh h′) = ll (λ n → compose
    (sound
      (NFω nt (vω t e) n)
      (Ctbl-fω ct (vω t e) n)
      (rs (NFω nt (vω t e) n) (t< (Tω nt (vω t e) n)))
      (subst HC (fω-eq (vω t e) n) (h′ n)))
    (cast-tree (fω-eq (vω t e) n) (h′ n)))
  go c0 e (h1 eh _) with trans (sym e) eh
  ... | ()
  go c0 e (hω eh _) with trans (sym e) eh
  ... | ()
  go c1 e (h0 eh) with trans (sym e) eh
  ... | ()
  go c1 e (hω eh _) with trans (sym e) eh
  ... | ()
  go cω e (h0 eh) with trans (sym e) eh
  ... | ()
  go cω e (h1 eh _) with trans (sym e) eh
  ... | ()
  go (cΩ μ) e h = ⊥-elim (Ctbl-cof ct e)

contract : DirectContract
contract = record { sound = sound }
```
