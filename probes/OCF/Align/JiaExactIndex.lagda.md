# Ω 后继分支的有限索引诊断

本篇只读原树根结点已有的有限索引，不改树族、Rep 或分支域。
`rootIndex` 在 Ω 根读取原字段，其余根返回零码。关系和共尾度证据
共同确定该字段；不比较可及证明，也不为原始树构造对应码。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaExactIndex where

open import Data.List.Base using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import OCF.Align.EboLeanDef
  using (T; Ωt; Ωs; cof; cΩ; hd<; lv<; []<)
open import OCF.Align.EboLeanBase using (n[]; nf-Ω)
open import OCF.Align.EboLean3Omega using (Acc′; wf)
open import OCF.Align.JiaAuditClosure using (cof-suc; cof-regular)
open import OCF.Align.JiaBase using (Tree; below; module Layer)
open import OCF.Align.JiaFold using (lift; regular)
open import OCF.Align.JiaRep using (Rep; module RelLayer)
open import OCF.Align.JiaRepMove using (rep-lift)
open import OCF.Align.JiaRepOmega using (rep-regular)
open RelLayer using (rz; rs; rl; ro)

rootIndex : ∀ {ℓ} {a : Acc′ ℓ} → Tree ℓ a → T
rootIndex Layer.z = []
rootIndex (Layer.s x) = []
rootIndex (Layer.l f) = []
rootIndex (Layer.o {j} p f) = j

Omega-inj : ∀ {i j} → cΩ i ≡ cΩ j → i ≡ j
Omega-inj refl = refl

root-index : ∀ {ℓ} (a : Acc′ ℓ) {x c j} → Rep a x c → cof c ≡ cΩ j →
  rootIndex {ℓ = ℓ} {a = a} x ≡ j
root-index a rz ()
root-index a (rs {c = c} r) e with trans (sym (cof-suc c)) e
... | ()
root-index a (rl eω r) e with trans (sym eω) e
... | ()
root-index a (ro eΩ r) e = Omega-inj (trans (sym eΩ) e)

successor-point : ∀ {ℓ} (a₀ : Acc′ []) (a : Acc′ ℓ)
  (f : Tree [] a₀ → Tree ℓ a) {x d} →
  Rep a₀ x d → Rep a (f (Layer.s x)) (Ωs d) →
  rootIndex {ℓ = ℓ} {a = a} (f (Layer.s x)) ≡ d
successor-point a₀ a f {d = d} r rf = root-index a rf (cof-regular d)
```

## 逐点前提的非空实例

取 d=0、x=零。`constant-Ω` 对全部 raw 输入返回同一棵树：把原第 1 层
正规 Ω 提升到第 Ω 层。它在指定的后继输入 1 处满足逐点前提。
这里没有声称该常函数对其他 d 也保持 Ω，更没有实填全 raw Ω 映射合同。

```agda
one Ω : T
one = Ωt []
Ω = Ωs []

lifted-Ω : (a : Acc′ Ω) → Tree Ω a
lifted-Ω a = lift (wf (nf-Ω n[])) a
  (below (nf-Ω n[]) (hd< (lv< []<)))
  (regular (wf (nf-Ω n[])) n[])

constant-Ω : ∀ (a₀ : Acc′ []) (a : Acc′ Ω) → Tree [] a₀ → Tree Ω a
constant-Ω a₀ a x = lifted-Ω a

constant-zero-rep : ∀ a₀ a →
  Rep a (constant-Ω a₀ a (Layer.s Layer.z)) (Ωs [])
constant-zero-rep a₀ a = rep-lift (wf (nf-Ω n[])) a
  (below (nf-Ω n[]) (hd< (lv< []<)))
  (rep-regular (wf (nf-Ω n[])) n[])

zero-point : ∀ a₀ a →
  rootIndex {ℓ = Ω} {a = a} (constant-Ω a₀ a (Layer.s Layer.z)) ≡ []
zero-point a₀ a = successor-point a₀ a (constant-Ω a₀ a) rz (constant-zero-rep a₀ a)
```

诊断的范围是：如果全 raw 分支 f 按 Ω 后继规则对应已相关输入，
那么 f 在后继 s x 处的输出根必须恢复 x 所对应的有限层索引 d。
这比 `RawRepack` 的完整码树包弱，也不是“所有接法不可能”的定理。
本篇没有构造 raw 编码器，没有证明 LPO，没有否定路线。
