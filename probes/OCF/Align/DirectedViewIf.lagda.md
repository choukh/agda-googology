# 定向改写的首个完整实例：缓存共尾分派

这是研究用的记号侧程序，尚未摆脱记号。原 EboLean3 不改动。
本篇把全部内部 ω 分支改成沿已取得的 Vω 运行；规则 6 的反馈沿
该视图保存的 VΩ 调用 fΩ/γ。不是给原闭项外面套一个包装。
沿原良基证明递归，标准形与下降证据通过 fω-eq 搬到新的后继项。
合同要求对任意旧 HC 证书给结构比较，不要求两份证明相等。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.DirectedViewIf where

open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.EboLeanDef
open import OCF.Align.EboLeanBase using (NF; Ctbl; nf-pred; Ctbl-pred)
open import OCF.Align.EboLeanClosure using (cl-fsn-NF; trian-fsn; Ctbl-fsn; Ctbl-cof)
open import OCF.Align.EboLeanTrian using (t<; T-pred)
open import OCF.Align.EboLean3Omega using (Acc′; acc)
open import OCF.Align.EboLeanView using (vω; fω; fω-eq)
import OCF.Align.EboLean3Tree as E
import OCF.Align.TerminalFoldAccept as R
open import OCF.Lean.FrozenWorldLift using (Same)

cached : ∀ {t} → NF t → Ctbl t → Acc′ t → E.Ord
cached {t} nt ct (acc rs) = go (cof t) refl
  module CachedStep where
    go : ∀ c → cof t ≡ c → E.Ord
    go c0 e = E.zero
    go c1 e = E.suc (cached (nf-pred nt) (Ctbl-pred ct)
      (rs (nf-pred nt) (t< (T-pred t e))))
    go cω e = E.lim (λ n → cached
      (subst NF (fω-eq (vω t e) n) (cl-fsn-NF nt e n))
      (subst Ctbl (fω-eq (vω t e) n) (Ctbl-fsn ct e n))
      (rs (subst NF (fω-eq (vω t e) n) (cl-fsn-NF nt e n))
        (subst (_<ᵀ t) (fω-eq (vω t e) n) (t< (trian-fsn nt e n)))))
    go (cΩ μ) e = ⊥-elim (Ctbl-cof ct e)

record CacheContract : Set where
  field
    sound : ∀ {t} (nt : NF t) (ct : Ctbl t) (ac : Acc′ t) (h : HC t) →
      Same (R.read (cached nt ct ac)) (R.read (E.tree h))
```

本合同不要求裸下标的判等、三歧或更新，也没有更改记号的基本列。
这一改写若验收成功，能得到完整 EBO 的另一运行组织；它本身不算
树自足，也不预先承诺减小前三层切片成本。
