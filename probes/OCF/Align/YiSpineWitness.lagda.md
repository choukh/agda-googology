# 实际发生性：从 EBO 的第三塔支到比较 Ω₂+1 与 2

本篇只沿参照树的实际 ω 基本列。十二步的分支编号固定列出，
每一步都有共尾度证据；最后的 fsnc 位于一次参数递归、一次 Ω 下标递归内。
没有把任意语法子项当成实际节点，也不使用有限搜索结果充当证明。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiSpineWitness where

open import Data.List.Base using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.EboLeanDef using (T; ψ; Ωt; sucT; fsn; fsT; γT; EBOψ)
open import OCF.Align.YiSpineNames using (two; left-code)
open import OCF.Align.YiSpineTrace hiding (source)

t₀ t₁ t₂ t₃ t₄ t₅ t₆ t₇ t₈ t₉ t₁₀ t₁₁ t₁₂ : T
t₀ = EBOψ 3
t₁ = fsn t₀ 1
t₂ = fsn t₁ 0
t₃ = fsn t₂ 1
t₄ = fsn t₃ 1
t₅ = fsn t₄ 3
t₆ = fsn t₅ 2
t₇ = fsn t₆ 0
t₈ = fsn t₇ 0
t₉ = fsn t₈ 0
t₁₀ = fsn t₉ 2
t₁₁ = fsn t₁₀ 0
t₁₂ = fsn t₁₁ 0

r₀ : Reach t₀
r₀ = tower 3
r₁ : Reach t₁
r₁ = fs-step {t = t₀} r₀ refl 1
r₂ : Reach t₂
r₂ = fs-step {t = t₁} r₁ refl 0
r₃ : Reach t₃
r₃ = fs-step {t = t₂} r₂ refl 1
r₄ : Reach t₄
r₄ = fs-step {t = t₃} r₃ refl 1
r₅ : Reach t₅
r₅ = fs-step {t = t₄} r₄ refl 3
r₆ : Reach t₆
r₆ = fs-step {t = t₅} r₅ refl 2
r₇ : Reach t₇
r₇ = fs-step {t = t₆} r₆ refl 0
r₈ : Reach t₈
r₈ = fs-step {t = t₇} r₇ refl 0
r₉ : Reach t₉
r₉ = fs-step {t = t₈} r₈ refl 0
r₁₀ : Reach t₁₀
r₁₀ = fs-step {t = t₉} r₉ refl 2
r₁₁ : Reach t₁₁
r₁₁ = fs-step {t = t₁₀} r₁₀ refl 0
r₁₂ : Reach t₁₂
r₁₂ = fs-step {t = t₁₁} r₁₁ refl 0

parent source : T
parent = ψ two (Ωt left-code) ∷ []
source = ψ [] (Ωt parent) ∷ []

source-equation : t₁₂ ≡ source
source-equation = refl

source-reached : Reach source
source-reached = subst Reach source-equation r₁₂

comparison-call : FsnCall source left-code two
comparison-call = arg-step refl (index-step refl (hit refl))

counter-call : Actual left-code two
counter-call = actual source source-reached refl comparison-call

-- 本轮目标2的来源：到达t₅后，t₅→t₆在Ω_{Ω₃}处运行γ₂链。
outer-argument : T
outer-argument = Ωt (Ωt (sucT two))

target-origin : t₅ ≡ (ψ [] outer-argument ∷ [])
target-origin = refl

gamma-origin : t₆ ≡ (ψ [] (fsT outer-argument (γT outer-argument two 2)) ∷ [])
gamma-origin = refl
```

到达的可数项为 ψ₀(Ω_{ψ₂(Ω_{Ω₂+1})})；其外层先进入 Ω 参数，
再进入该 Ω 的下标 ψ₂(Ω_{Ω₂+1})，此处参数共尾度为 Ω_{Ω₂+1}。
fsnc 因而比较 Ω₂+1 与 2，码侧为 gt。
这些是一个实际调用的构造与等式，不是强度验收或新闭项。
