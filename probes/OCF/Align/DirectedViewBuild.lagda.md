# 缓存共尾 View 的完整结构验收

直接证明冻结 `cached` 算法的全部输入合同。ω 分支的下一项确实是
`fω`，只用已有逐项等式搬运旧 HC 子证书；不识别两份 Acc 或 HC。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DirectedViewBuild where

open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)
open import OCF.Lean.CRwBase using (Cd; hz; hs; hl)
open import OCF.Lean.FrozenWorldLift using (Same; zz; ss; ll)
open import OCF.Align.EboLeanDef
open import OCF.Align.EboLeanBase using (NF; Ctbl; nf-pred; Ctbl-pred)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF; trian-fsn; Ctbl-fsn; Ctbl-cof)
open import OCF.Align.EboLeanTrian using (t<; T-pred)
open import OCF.Align.EboLean3Omega using (Acc′; acc)
open import OCF.Align.EboLeanView using (vω; fω; fω-eq)
open import OCF.Align.DirectedViewIf using (cached; CacheContract)
import OCF.Align.DirectedViewIf as I
import OCF.Align.EboLean3Tree as E
import OCF.Align.TerminalFoldAccept as R

self : ∀ (a : Cd) → Same a a
self hz = zz
self (hs a) = ss (self a)
self (hl f) = ll (λ n → self (f n))
self (OCF.Lean.CRwBase.hΩ () _)

compose : ∀ {a b c : Cd} → Same a b → Same b c → Same a c
compose zz zz = zz
compose (ss p) (ss q) = ss (compose p q)
compose (ll p) (ll q) = ll (λ n → compose (p n) (q n))

cast-tree : ∀ {a b} (e : a ≡ b) (h : HC a) →
  Same (R.read (E.tree (subst HC e h))) (R.read (E.tree h))
cast-tree refl h = self _

sound : ∀ {t} (nt : NF t) (ct : Ctbl t) (ac : Acc′ t) (h : HC t) →
  Same (R.read (cached nt ct ac)) (R.read (E.tree h))
sound {t} nt ct (acc rs) h = go (cof t) refl h where
  go : ∀ c (e : cof t ≡ c) (h : HC t) →
    Same (R.read (I.CachedStep.go nt ct rs c e)) (R.read (E.tree h))
  go c0 e (h0 eh) = zz
  go c1 e (h1 eh h′) = ss (sound (nf-pred nt) (Ctbl-pred ct)
    (rs (nf-pred nt) (t< (T-pred t e))) h′)
  go cω e (hω eh h′) = ll (λ n → compose
    (sound
      (subst NF (fω-eq (vω t e) n) (cl-fsn-NF nt e n))
      (subst Ctbl (fω-eq (vω t e) n) (Ctbl-fsn ct e n))
      (rs (subst NF (fω-eq (vω t e) n) (cl-fsn-NF nt e n))
        (subst (_<ᵀ t) (fω-eq (vω t e) n) (t< (trian-fsn nt e n))))
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

contract : CacheContract
contract = record { sound = sound }
```
