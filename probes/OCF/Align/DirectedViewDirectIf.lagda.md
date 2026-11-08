# 定向简化第二步：直接消费视图封闭性

这是第一版 cached 的后继研究程序，仍依赖 EBO 项，不是最终成品。
新状态已经是 fω v n，证书也直接取 NFω、Ctbl-fω、Tω，不再先走
cl-fsn-NF／Ctbl-fsn／trian-fsn 后用 fω-eq 搬回来。
本定义不使用任何基本列对应等式；对应等式只留给值验收。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DirectedViewDirectIf where

open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EboLeanDef
open import OCF.Align.EboLeanBase using (NF; Ctbl; nf-pred; Ctbl-pred)
open import OCF.Align.EboLeanClosure using (NFω; Tω; Ctbl-fω; Ctbl-cof)
open import OCF.Align.EboLeanTrian using (t<; T-pred)
open import OCF.Align.EboLean3Omega using (Acc′; acc)
open import OCF.Align.EboLeanView using (vω)
import OCF.Align.EboLean3Tree as E
import OCF.Align.TerminalFoldAccept as R
open import OCF.Lean.FrozenWorldLift using (Same)

direct : ∀ {t} → NF t → Ctbl t → Acc′ t → E.Ord
direct {t} nt ct (acc rs) = go (cof t) refl
  module DirectStep where
    go : ∀ c → cof t ≡ c → E.Ord
    go c0 e = E.zero
    go c1 e = E.suc (direct (nf-pred nt) (Ctbl-pred ct)
      (rs (nf-pred nt) (t< (T-pred t e))))
    go cω e = E.lim (λ n → direct
      (NFω nt (vω t e) n)
      (Ctbl-fω ct (vω t e) n)
      (rs (NFω nt (vω t e) n) (t< (Tω nt (vω t e) n))))
    go (cΩ μ) e = ⊥-elim (Ctbl-cof ct e)

record DirectContract : Set where
  field
    sound : ∀ {t} (nt : NF t) (ct : Ctbl t) (ac : Acc′ t) (h : HC t) →
      Same (R.read (direct nt ct ac)) (R.read (E.tree h))
```

程序与合同首次通过后冻结。构造支须交完整 Ω 塔实例；独立支检查
新状态证书的定义级依赖是否真的不再通过旧基本列。
