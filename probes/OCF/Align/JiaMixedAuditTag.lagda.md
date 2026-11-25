# 混合族审查：精确有限标签更新会给出相关域读码

本篇只诊断一种建议的 q 元数据补救：对每个 raw 前缀 x 都计算一个有限
标签，并要求它在 Rep x A 时恰为 A 与固定单元素码 Ω 的列表连接。
删除标签末项就能读回 A。结论是条件推论，不假定这种更新器存在，
也不是“不存在更新器”的定理，更不否定混合族或其他折叠方案。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaMixedAuditTag where

open import Data.List.Base using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; trans)
open import OCF.Align.EboLeanDef using (T; PT; ψ; sucT; Ωs)
open import OCF.Align.EboLean3Omega using (Acc′)
open import OCF.Align.JiaMixedBase using (Tree)
open import OCF.Align.JiaMixedRep using (Rep)

-- 纯有限列表运算，空列表也有定义。
init : T → T
init [] = []
init (p ∷ []) = []
init (p ∷ q ∷ A) = p ∷ init (q ∷ A)

init-snoc : ∀ A p → init (A ++ (p ∷ [])) ≡ A
init-snoc [] p = refl
init-snoc (q ∷ []) p = refl
init-snoc (q ∷ r ∷ A) p = cong (q ∷_) (init-snoc (r ∷ A) p)

init-omega-suffix : ∀ A → init (A ++ Ωs []) ≡ A
init-omega-suffix A = init-snoc A (ψ (sucT []) [])

record ExactTag (Input : Set) (R : Input → T → Set) : Set where
  field
    tag : Input → T
    law : ∀ {x A} → R x A → tag x ≡ A ++ Ωs []
open ExactTag public

module ReadBack {Input : Set} {R : Input → T → Set} (U : ExactTag Input R) where
  decode : Input → T
  decode x = init (tag U x)

  decode-law : ∀ {x A} → R x A → decode x ≡ A
  decode-law {A = A} r = trans (cong init (law U r)) (init-omega-suffix A)
```

## 合同前提的实填实例

输入本来就是有限码、关系为相等时，追加固定 Ω 后再删除末项确能读回。
这个实例证明条件接口可以居留，不把 raw 树的实例偷偷假定为已有。

```agda
code-instance : ExactTag T (λ x A → x ≡ A)
tag code-instance x = x ++ Ωs []
law code-instance refl = refl

code-instance-read : ∀ A → ReadBack.decode code-instance A ≡ A
code-instance-read A = ReadBack.decode-law code-instance refl

-- 只是原混合 raw 树的合同类型；没有给出其中的更新器。
TreeTag : ∀ {ℓ} (a : Acc′ ℓ) → Set
TreeTag {ℓ} a = ExactTag (Tree ℓ a) (Rep a)
```

因此，这类“总更新器给精确有限新标签”的方案若在原 raw 树上实填，
便同时提供一个在所有已有 Rep 输入上正确的读码函数。
这正是该补救需要额外处理的补码义务；本篇没有实填 `TreeTag`，
没有构造 raw 编码器，也没有把条件推论称为全域不可能。
不带这种标签的方案、条件 NF 的方案及其他混合折叠方式都未被否定。
