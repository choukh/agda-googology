# 两个已有反例的目标第一次进入历史环境

这些是具体闭项等式及成员／非成员证明，不代替全 Reach 的 env-tags。
它们核对包络生成的方向：目标在成为后续比较目标以前，已由外层 γ 链加入，
当前层号的字段里不必出现它。本篇保留两轮反例原有的发生路径与来源分析。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiTargetExamples where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_; replicate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (_,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import OCF.Align.EboLeanDef using (T; PT)
open import OCF.Align.YiSpineNames using (two)
open import OCF.Align.YiPrefixNames using (ω-code)
import OCF.Align.YiSpineNames as AName
import OCF.Align.YiPrefixNames as BName
import OCF.Align.YiSpineWitness as A
import OCF.Align.YiPrefixWitness as B
open import OCF.Align.YiTargetScan using (scan)
open import OCF.Align.YiTargetHistory using (Env)
open import OCF.Align.YiTargets using (Targets; target-in-env)

two-before : Env A.r₅ ≡ replicate 4 []
two-before = refl

two-step : scan A.t₅ ≡ just (two , [])
two-step = refl

two-after : Env A.r₆ ≡ two ∷ replicate 4 []
two-after = refl

omega-before : Env B.r10 ≡ replicate 5 []
omega-before = refl

omega-step : scan B.t10 ≡ just (ω-code , [])
omega-step = refl

omega-after : Env B.r11 ≡ ω-code ∷ replicate 5 []
omega-after = refl

nonzero-not-in-zeroes : ∀ {x : PT} {xs : T} n → (x ∷ xs) ∈ replicate n [] → ⊥
nonzero-not-in-zeroes zero ()
nonzero-not-in-zeroes (suc n) (here ())
nonzero-not-in-zeroes (suc n) (there p) = nonzero-not-in-zeroes n p

two-absent-before : two ∈ Env A.r₅ → ⊥
two-absent-before p = nonzero-not-in-zeroes 4 (subst (λ xs → two ∈ xs) two-before p)

omega-absent-before : ω-code ∈ Env B.r10 → ⊥
omega-absent-before p = nonzero-not-in-zeroes 5 (subst (λ xs → ω-code ∈ xs) omega-before p)

two-present-after : two ∈ Env A.r₆
two-present-after = here refl

omega-present-after : ω-code ∈ Env B.r11
omega-present-after = here refl

two-actual : Targets AName.left-code two
two-actual = A.counter-call

omega-actual : Targets BName.left-code ω-code
omega-actual = B.counter-call

two-at-comparison : two ∈ Env A.r₁₂
two-at-comparison = target-in-env A.counter-call

omega-at-comparison : ω-code ∈ Env B.r19
omega-at-comparison = target-in-env B.counter-call
```

在旧反例中，2 在 t₅→t₆ 的 γ₂ 首次进入 Env，后来与 Ω₂+1 比较。
在前缀反例中，ω 在 t10→t11 的 γ_ω 首次进入 Env，后来与 Ω·2+1 比较。
这两条来源等式不证明同一层号的全部目标仅有这些，也不否定其它层号表示。
