# Ω 构造的关系实例

原树仍对全部低层树分支；对应证明只消费相关输入。
先给所有后继层的原 `regular`，再把第二轮沿 `Named` 构造的 Ω 输出
接到本轮关系。这里没有完成 Ω_Ω 的全 raw 分支程序。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaRepOmega where

open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)
open import OCF.Align.EboLeanDef using (T; sucT; Ωt; Ωs; cof; cofψ0; cω; fsn; fsn0)
open import OCF.Align.EboLeanBase using (NF)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Align.EboLean3Omega using (Acc′; acc; wf)
open import OCF.Align.EboLeanClosure using (trian-fsn)
open import OCF.Align.EboLeanTrian using (t<)
open import OCF.Align.JiaBase using (Tree; below)
open import OCF.Align.JiaFold using (regular)
open import OCF.Align.JiaRep
open RelLayer using (rz; rs; rl; ro)
open import OCF.Align.JiaRepMove using (rep-lift)
open import OCF.Align.JiaAuditClosure using (cof-regular; fs-regular)
import OCF.Align.JiaCountPack as C
import OCF.Align.JiaSingularBranch as O

rep-regular : ∀ {i} (a : Acc′ (sucT i)) (ni : NF i) →
  Rep a (regular a ni) (Ωs i)
rep-regular {i} (acc h) ni = ro (cof-regular i)
  (λ {y} {d} r → subst (Rep (acc h) _) (sym (fs-regular i d))
    (rep-lift (h ni (<-sucT i)) (acc h) (below ni (<-sucT i)) r))

cof-omega-lim : ∀ c → cof c ≡ cω → cof (Ωt c) ≡ cω
cof-omega-lim [] ()
cof-omega-lim c@(_ ∷ _) e = cong (cofψ0 c) e

fsn-omega-lim : ∀ c → cof c ≡ cω → ∀ n → fsn (Ωt c) n ≡ Ωt (fsn c n)
fsn-omega-lim [] () n
fsn-omega-lim c@(_ ∷ _) e n = cong (λ k → fsn0 c k n) e

omega-rep : ∀ {c} (x : C.Named c) (a : Acc′ c) → Rep a (O.omega x a) (Ωt c)
omega-rep C.nz (acc h) = rs rz
omega-rep (C.ns x) a = rep-regular a (C.normal x)
omega-rep (C.nl {t = c} nc cc e f) (acc h) = rl (cof-omega-lim c e)
  (λ n → subst (Rep (acc h) _) (sym (fsn-omega-lim c e n))
    (rep-lift
      (h (C.normal (f n)) (t< (trian-fsn nc e n)))
      (acc h) (below (C.normal (f n)) (t< (trian-fsn nc e n)))
      (omega-rep (f n) (h (C.normal (f n)) (t< (trian-fsn nc e n))))))

branch-rep : ∀ a c (x : C.Named c) → Rep a (O.branchTree a (c , x)) (Ωt c)
branch-rep a c x = rep-lift (wf (C.normal x)) a
  (below (C.normal x) (C.countable-bound (C.countable x)))
  (omega-rep x (wf (C.normal x)))
```
