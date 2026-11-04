# 对象在折叠下怎么行动 (四): 事后对照, 记号只在本文件

> 入口 [TLBehave](TLBehave.lagda.md). **时间线:** 这个文件在 `TLBehaveDef`, `TLBehaveThm`, `TLBehaveNeg` 编译之后才写. **树与记号之间没有定理.** 比较器 `refl`, 只比写明的项.
>
> 任务书提到 "层的共尾度". 这里核对记号一侧: $\Omega\cdot2$ 与 $u=\Omega^2$ 作下标, 记号的共尾度相同 (都是 $\Omega_1$), 而树里一个是世界内的行 (不 `Ad`), 一个是顶 (`Ad`). **所以 `Ad` 不是共尾度的翻译:** 单看下标的共尾度分不开这两个. 这只说明这两个具体的项, 比较的是记号的 `cof`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLBehaveAccept where

open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EBO using (T; ψ; natT; Ωs; cof; cΩ; cω)
open import OCF.Align.CrossMAccept using (u; ψ₁; one; Ω₁)

-- Ω·2 = ψ₁(0) + ψ₁(0)
Ω·2ᵀ : T
Ω·2ᵀ = ψ one [] ∷ ψ one [] ∷ []

cof-Ω·2 : cof Ω·2ᵀ ≡ cof u
cof-Ω·2 = refl

cof-u : cof u ≡ cΩ []
cof-u = refl
```
