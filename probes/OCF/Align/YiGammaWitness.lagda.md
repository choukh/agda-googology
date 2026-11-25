# 实际 γ_Ω 的来源与保留支的 Ω 基本列

第4层诊断。九个实际 ω 基本列步到达 ψ₀(Ω_{Ω+1})。
其 γ 种子是 Ω_Ω，第一次输出为 ψ_Ω(Ω_Ω)，这是 Ω 共尾的坐标，
不是参照树 Reach 直接展开的可数项。随后对这个坐标取合法 Ω 基本列支，
可以精确看到保留分支的 lt 比较；不把它伪称冻结 Actual。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiGammaWitness where

open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.EboLeanDef
  using (T; ψ; Ωt; sucT; fsn; fsT; γT; EBOψ; cof; cΩ; cmpᵀ; lt; _<ᵀ_)
open import OCF.Align.EboLeanBase using (lt→<)
open import OCF.Align.YiSpineTrace
  using (Reach; tower; fs-step; FsnCall; hit; Actual; actual)
import OCF.Align.YiTargetHistory as H
open import OCF.Align.YiTargetScan using (scan)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (_,_)
open import OCF.Align.YiPrefixNames using (ω-code)
open import OCF.Align.YiDActual using (Ω-code)

t0 t1 t2 t3 t4 t5 t6 t7 t8 t9 : T
t0 = EBOψ 3
t1 = fsn t0 1
t2 = fsn t1 0
t3 = fsn t2 0
t4 = fsn t3 2
t5 = fsn t4 1
t6 = fsn t5 0
t7 = fsn t6 0
t8 = fsn t7 2
t9 = fsn t8 0

r0 : Reach t0
r0 = tower 3
r1 : Reach t1
r1 = fs-step {t = t0} r0 refl 1
r2 : Reach t2
r2 = fs-step {t = t1} r1 refl 0
r3 : Reach t3
r3 = fs-step {t = t2} r2 refl 0
r4 : Reach t4
r4 = fs-step {t = t3} r3 refl 2
r5 : Reach t5
r5 = fs-step {t = t4} r4 refl 1
r6 : Reach t6
r6 = fs-step {t = t5} r5 refl 0
r7 : Reach t7
r7 = fs-step {t = t6} r6 refl 0
r8 : Reach t8
r8 = fs-step {t = t7} r7 refl 2
r9 : Reach t9
r9 = fs-step {t = t8} r8 refl 0

β source : T
β = Ωt (sucT Ω-code)
source = ψ [] β ∷ []

source-equation : t9 ≡ source
source-equation = refl

source-reached : Reach source
source-reached = subst Reach source-equation r9

outer-actual : Actual (sucT Ω-code) []
outer-actual = actual source source-reached refl (hit refl)

old-env : H.Env r9 ≡ ([] ∷ [] ∷ [] ∷ sucT [] ∷ [] ∷ [] ∷ [] ∷ [] ∷ [])
old-env = refl

scan-equation : scan t9 ≡ just (Ω-code , [])
scan-equation = refl

new-env : H.Env (fs-step {t = t9} r9 refl 1) ≡ Ω-code ∷ H.Env r9
new-env = refl

γ0 γ1 selected branch : T
γ0 = γT β Ω-code 0
γ1 = γT β Ω-code 1
selected = sucT ω-code
branch = ψ Ω-code (Ωt selected) ∷ []

seed-equation : γ0 ≡ Ωt Ω-code
seed-equation = refl

seed-keep-comparison : cmpᵀ (sucT []) Ω-code ≡ lt
seed-keep-comparison = refl

seed-feedback : fsT β γ0 ≡ γ0
seed-feedback = refl

first-equation : γ1 ≡ (ψ Ω-code (Ωt Ω-code) ∷ [])
first-equation = refl

first-cof : cof γ1 ≡ cΩ []
first-cof = refl

coordinate-below : selected <ᵀ Ω-code
coordinate-below = lt→< selected Ω-code refl

kept-branch-equation : fsT γ1 selected ≡ branch
kept-branch-equation = refl

branch-cof : cof branch ≡ cΩ ω-code
branch-cof = refl

branch-comparison : cmpᵀ (sucT ω-code) Ω-code ≡ lt
branch-comparison = refl

branch-column : fsT branch [] ≡ Ωt Ω-code
branch-column = refl
```

outer-actual 是冻结 Actual 中真正的外层调用 (Ω+1,0)。
kept-branch-equation 则在该 γ 输出的合法 Ω 支上运行 fsT；其下一次 fsTc
使用 branch-comparison。后者为 lt，不属于“可数源的 fsnc 调用”集合。
来源不是任意语法子项：先有真实外层 γ，再有它的 Ω 共尾输出及界内的选定坐标。
这些是编译的路径与执行等式；有限搜索只用于找到九步编号。
