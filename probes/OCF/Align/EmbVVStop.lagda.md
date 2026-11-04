# 值验收 (停在哪): $\psi_1(2)$ 以上

> 入口 [EmbVV](EmbVV.lagda.md). 读记号. **这不是否定路线.** 下面只说这一版 `Sb` 到哪为止, 不说 $\psi_1(2)+\theta$ 的 `VV` 不成立.
>
> - `no-Sb-ψ²`, `no-NF-ψ²`: 现在的 `Sb` 只有 $\psi_1(1)$ 的前缀族, 所以 $\psi_0(\Omega_{\psi_1(2)})$ 不是这一版的 `NF₁`. 标签类的出口 `labelᵠ` 要 `NF₁`, `vv-row` 的前提就给不出来. `vv-ω²` 不受影响: `vv-chain` 只要基本列带标签, 不要顶带标签.
> - `shift-0`, `shift-1`, `shift-2`: 有限测试 (`refl`), 比较器是 `fsn` 的字面计算. $\psi_1(2)[k]=\psi_1(1)\cdot k$. 码 `ω^ωᶜ` 的第 2 块末尾的行是 $[1,q_0,q_1,\dots]$, $q_k$ 读 $\psi_1(1)\cdot(k+2)$ (判断, 块的偏移 $\psi_1(1)$ 与块内 $\psi_1(1)\cdot(k+1)$ 相加). 所以那里主线与参照树错开 2 位, 不是 `≃ᴵ` 的 0 或 1 位.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EmbVVStop where

open import Data.Empty using (⊥)
open import Data.List using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.EBO using (T; PT; natT; Ωt; fsn) renaming (ψ to ψᵗ)
open import OCF.Align.EmbVVLZStandardOmega using (NF₁; n∷; nψ; Sb; sC; ψ¹)
open import OCF.Align.EmbVVOZUniform3Base using (ψ₀ᵗ)

ψ² : PT
ψ² = ψᵗ (natT 1) (natT 2)

no-Sb-ψ² : Sb (ψ² ∷ []) → ⊥
no-Sb-ψ² (sC ())

no-NF-ψ² : NF₁ (ψ₀ᵗ (Ωt (ψ² ∷ []))) → ⊥
no-NF-ψ² (n∷ (nψ _ _ (n∷ (nψ _ s _ _) _ _) _) _ _) = no-Sb-ψ² s

shift-0 : fsn (ψ² ∷ []) 0 ≡ []
shift-0 = refl

shift-1 : fsn (ψ² ∷ []) 1 ≡ ψ¹ ∷ []
shift-1 = refl

shift-2 : fsn (ψ² ∷ []) 2 ≡ ψ¹ ∷ ψ¹ ∷ []
shift-2 = refl
```
