# 前缀表示的新反例：实际比较 Ω·2+1 与 ω

本篇沿参照树第三塔支的十九次基本列；每步都保存共尾度证据。
有限搜索仅提供路径，source-equation 与 counter-call 才是实际发生性证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiPrefixWitness where

open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.EboLeanDef using (T; ψ; Ωt; sucT; fsn; fsT; γT; EBOψ; cmpᵀ; gt)
open import OCF.Align.YiPrefixNames using (ω-code; left-code)
open import OCF.Align.YiSpineTrace hiding (source)

t0 : T
t0 = EBOψ 3
t1 : T
t1 = fsn t0 1
t2 : T
t2 = fsn t1 1
t3 : T
t3 = fsn t2 3
t4 : T
t4 = fsn t3 0
t5 : T
t5 = fsn t4 1
t6 : T
t6 = fsn t5 1
t7 : T
t7 = fsn t6 1
t8 : T
t8 = fsn t7 2
t9 : T
t9 = fsn t8 2
t10 : T
t10 = fsn t9 1
t11 : T
t11 = fsn t10 2
t12 : T
t12 = fsn t11 2
t13 : T
t13 = fsn t12 1
t14 : T
t14 = fsn t13 0
t15 : T
t15 = fsn t14 0
t16 : T
t16 = fsn t15 0
t17 : T
t17 = fsn t16 0
t18 : T
t18 = fsn t17 3
t19 : T
t19 = fsn t18 0

r0 : Reach t0
r0 = tower 3
r1 : Reach t1
r1 = fs-step {t = t0} r0 refl 1
r2 : Reach t2
r2 = fs-step {t = t1} r1 refl 1
r3 : Reach t3
r3 = fs-step {t = t2} r2 refl 3
r4 : Reach t4
r4 = fs-step {t = t3} r3 refl 0
r5 : Reach t5
r5 = fs-step {t = t4} r4 refl 1
r6 : Reach t6
r6 = fs-step {t = t5} r5 refl 1
r7 : Reach t7
r7 = fs-step {t = t6} r6 refl 1
r8 : Reach t8
r8 = fs-step {t = t7} r7 refl 2
r9 : Reach t9
r9 = fs-step {t = t8} r8 refl 2
r10 : Reach t10
r10 = fs-step {t = t9} r9 refl 1
r11 : Reach t11
r11 = fs-step {t = t10} r10 refl 2
r12 : Reach t12
r12 = fs-step {t = t11} r11 refl 2
r13 : Reach t13
r13 = fs-step {t = t12} r12 refl 1
r14 : Reach t14
r14 = fs-step {t = t13} r13 refl 0
r15 : Reach t15
r15 = fs-step {t = t14} r14 refl 0
r16 : Reach t16
r16 = fs-step {t = t15} r15 refl 0
r17 : Reach t17
r17 = fs-step {t = t16} r16 refl 0
r18 : Reach t18
r18 = fs-step {t = t17} r17 refl 3
r19 : Reach t19
r19 = fs-step {t = t18} r18 refl 0

parent middle source : T
parent = ψ ω-code (Ωt left-code) ∷ []
middle = ψ ω-code (Ωt parent) ∷ []
source = ψ [] (Ωt middle) ∷ []

source-equation : t19 ≡ source
source-equation = refl

source-reached : Reach source
source-reached = subst Reach source-equation r19

comparison-call : FsnCall source left-code ω-code
comparison-call = arg-step refl (index-step refl
  (arg-step refl (index-step refl (hit refl))))

counter-call : Actual left-code ω-code
counter-call = actual source source-reached refl comparison-call

counter-gt : cmpᵀ left-code ω-code ≡ gt
counter-gt = actual-gt counter-call

outer-argument : T
outer-argument = Ωt (Ωt (sucT ω-code))

target-origin : t10 ≡ (ψ [] outer-argument ∷ [])
target-origin = refl

gamma-origin : t11 ≡ (ψ [] (fsT outer-argument (γT outer-argument ω-code 2)) ∷ [])
gamma-origin = refl
```

到达 ψ₀(Ω_{ψ_ω(Ω_{ψ_ω(Ω_{Ω·2+1})})})。
最内层 ψ_ω 的参数为正规 Ω_{Ω·2+1}，其共尾层为 Ω·2；
fsnc 比较其后继 Ω·2+1 与目标 ω。ω 来自外层链带入的目标，
不是同一 Ω 结点的另一分支编号；目标是否为层号字段的字面子项在反例篇另证。

