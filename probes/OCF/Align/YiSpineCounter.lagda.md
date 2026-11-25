# (b)：实际比较 Ω₂+1 与 2 不在同一合法 CP 脊柱

主结论使用自然命名解释，不需要假设全域解释存在。
对任意保持零、后继、Ω 的总扩展，结论也相同；未解释的正参数 ψ
如何取值不会改变这两端，因此不靠任意语法编码制造反例。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiSpineCounter where

open import Data.Empty using (⊥)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (subst)
open import OCF.Align.LevelFixVal using (CP)
import OCF.Align.LevelFixVal as V
import OCF.Align.YiLevelBase as Y
open import OCF.Align.YiSpineNames
open import OCF.Align.YiSpineCommon
open import OCF.Align.YiSpinePrefix using (Ωprefix; prefix-position)
open import OCF.Align.YiSpineTrace using (Actual)
open import OCF.Align.YiSpineWitness using (counter-call)

left right : Y.Level
left = ι_L left-name
right = ι_L two-name

left-not-right : CP (Y.tree left) (Y.tree right) → ⊥
left-not-right (V.suc (V.suc ()))

right-not-left : CP (Y.tree right) (Y.tree left) → ⊥
right-not-left (V.suc (V.fst (V.fst (V.suc ()))))

no-common : Common left right → ⊥
no-common c with common→spinal {a = left} {b = right} c
... | inj₁ lr = left-not-right lr
... | inj₂ rl = right-not-left rl

actual-counter : Actual left-code two
actual-counter = counter-call

extension-no-common : (M : Extension) → Common (read M left-code) (read M two) → ⊥
extension-no-common M c with common→spinal {a = read M left-code} {b = read M two} c
... | inj₁ lr = left-not-right
  (subst (λ b → CP (Y.tree left) b) (agrees M two-name)
    (subst (λ a → CP a (Y.tree (read M two))) (agrees M left-name) lr))
... | inj₂ rl = right-not-left
  (subst (λ b → CP (Y.tree right) b) (agrees M left-name)
    (subst (λ a → CP a (Y.tree (read M left-code))) (agrees M two-name) rl))

-- 只更换Ω的这处树形，不改旧定义。
patched-left patched-right : Y.Level
patched-left = interpret Ωprefix left-name
patched-right = interpret Ωprefix two-name

patched-position : CP (Y.tree patched-right) (Y.tree patched-left)
patched-position = V.suc (prefix-position right)

patched-common : Common patched-left patched-right
patched-common = spinal→common {a = patched-left} {b = patched-right} (inj₂ patched-position)
```

不可比性是原树 CP 的否定，no-common 排除了任意合法 CP 公共界，
不是仅排除原先挑选的界。反例只针对这个 Ω／后继树表示及 CP；
没有否定采用其它树形、其它合法位置域或 S3。

前缀修补已消除这一对：新的 Ω₂ 以 2 为字面前缀，其后继也包含 2。
本篇没有证明所有实际比较对都修好，没有采用此候选重写已有定义。
