# 混合族的相关包与两类 Ω 的实际实例

Related 同时保存码、标准形、混合树及 Rep。按已知层号包进入下一层时，
只读取该包现有的码及标准形，不给一个 raw 树事后寻找码。
这里交付 Ω 种子和下一层构造；还没有新版 ψ 的实际输出反馈闭包。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaMixedPack where

open import Data.List.Base using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Align.EboLeanDef using (T; Ωt; Ωs; sucT)
open import OCF.Align.EboLeanBase using (NF; n[]; nf-Ω)
open import OCF.Align.EboLean3Base using (nf-suc)
open import OCF.Align.EboLean3Omega using (Acc′; acc; wf)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Align.JiaAuditClosure using (cof-regular; fs-regular)
open import OCF.Align.JiaMixedBase
open import OCF.Align.JiaMixedRep
open import OCF.Align.JiaMixedOmega using (omega; omega-rep; node-below)
open RelLayer using (rr)

record Related (ℓ : T) (a : Acc′ ℓ) : Set where
  constructor related
  field
    label : T
    normal-label : NF label
    value : Tree ℓ a
    witness : Rep a value label
open Related public

seed-related : ∀ {c} (nc : NF c) (a : Acc′ c) → Related c a
seed-related {c} nc a = related (Ωt c) (nf-Ω nc) (omega nc a) (omega-rep nc a)

Trees-at : ∀ {ℓ a} → Related ℓ a → Set
Trees-at x = Tree (label x) (wf (normal-label x))

next-omega : ∀ {ℓ a} (x : Related ℓ a) → Related (label x) (wf (normal-label x))
next-omega x = seed-related (normal-label x) (wf (normal-label x))

module _ {ℓ : T} {a : Acc′ ℓ} where
  data Root : Kind → Tree ℓ a → Set where
    raw-root : ∀ {j} p (f : Low ℓ a j p → Tree ℓ a) → Root regular-kind (Layer.r p f)
    coded-root : ∀ {j} p (f : CodeArg j → Tree ℓ a) → Root singular-kind (Layer.q p f)

regular-rep : ∀ {i} (ni : NF i) (a : Acc′ (sucT i)) → Rep a (regular a ni) (Ωs i)
regular-rep {i} ni (acc h) = rr (cof-regular i)
  (λ {y} {d} r → subst (Rep (acc h) _) (sym (fs-regular i d))
    (rep-lift (h ni (<-sucT i)) (acc h) (below ni (<-sucT i)) r))

regular-is-raw : ∀ {i} (ni : NF i) (a : Acc′ (sucT i)) → Root regular-kind (regular a ni)
regular-is-raw ni (acc h) = raw-root _ _

Ω : T
Ω = Ωs []

normal-Ω : NF Ω
normal-Ω = nf-Ω (nf-Ω n[])

singular : (a : Acc′ Ω) → Tree Ω a
singular = omega normal-Ω

singular-rep : ∀ a → Rep a (singular a) (Ωt Ω)
singular-rep = omega-rep normal-Ω

singular-is-coded : ∀ a → Root singular-kind (singular a)
singular-is-coded (acc h) = coded-root _ _

opaque
  closed-singular : Related Ω (wf normal-Ω)
  closed-singular = seed-related normal-Ω (wf normal-Ω)

  closed-singular-code : label closed-singular ≡ Ωt Ω
  closed-singular-code = refl
```

regular-is-raw 对所有标准形后继层成立；singular-is-coded 对实际 Ω_Ω 成立。
两者都是构造子形状定理，不是有限样本或值前沿。next-omega 接收已有的相关包；
尚未证明新 ψ 能生成所需输入包，不能把它叫作完整运行反馈闭包。
