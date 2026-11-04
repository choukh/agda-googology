# 值验收 (四): `T⊤` 不能按互相 $\sqsubseteq^0$ 验收

> **验收文件, 读记号.** 入口 [ValLab](ValLab.lagda.md). 编译过的定理, 无条件.
>
> `no-val-T⊤`: `T⊤` 不 $\sqsubseteq^0$ 任何带字面标签的树, **不管读法是什么**, 所以 $\psi_0(\Omega_{\psi_1(\Omega)})$ 在规则现在写的值验收下不可能成立 (对任何参照树). 原因: `T⊤` 的第 1 个分支是码 $C_1$ 的顶, $C_1$ 里有一个位置 `m`, 它的行是 $[\omega,\ \psi_0(\Omega_{\psi_1(1)}),\ \dots]$ 而 $F_1$ 是闭包行, 是 `no-lab-pat` 的形状.
>
> **这不否定:** `T⊤` 的值就是 $\psi_0(\Omega_{\psi_1(\Omega)})$ (仍是判断); $\preccurlyeq$ 下的验收; 这棵树.
>
> $C_1$ 由 `T⊤` 的第 0 个分支算出, 下面的 `refl` 是真计算: 检查器算到 $\lceil\mathrm{lv}\,T_0\rceil$ 的前几块.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设、无洞、无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ValLabNegTop where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Free.Level hiding (up)
open import OCF.Free.Force using (forceᴺ)
open import OCF.Align.OrdLabZCorrespond using (Lab)
open import OCF.Align.LadderOrdPos
open import OCF.Align.LadderOrdCode using (ωᶜ)
open import OCF.Align.LadderOrdCert using (Gᵖ; ev₀)
open import OCF.Align.CrossMNode using (C; Node; Gbr; νT)
open import OCF.Align.CrossMInst using (𝒯)
open import OCF.Align.CrossMClosed using (T⊤)
import OCF.Align.ValLabRow

M₁ : Code
M₁ = C 𝒯 ωᶜ 1

module V¹ = OCF.Align.ValLabRow (HB M₁)

m₁ : Pos (cs M₁)
m₁ = low (low (blk 0 end))

no-any-m₁ : ∀ s → Lab (V¹.V m₁ zero) s → ⊥
no-any-m₁ = V¹.no-lab-pat {m₁} {λ i → low (low (blk 0 (low (blk i end))))} {λ i → tt}
  {λ i → low (low (blk 0 (low (blk 0 (low (blk i end))))))} {λ i → tt}
  {low (low (blk 0 (low (blk 1 (low end)))))} {tt} refl refl refl (inj₂ tt)

-- 对变量写, 检查器不去展开证书 (见 [CrossMInst](CrossMInst.lagda.md))
to-ν : ∀ (𝒩 : Node) M₀ n {c : Ordᶜ zero} → c ≺ forceᴺ _ (Gbr 𝒩 (C 𝒩 M₀ n)) → c ≺ νT 𝒩 M₀
to-ν 𝒩 M₀ n h = ≺l n h

module Br (M : Code) where
  private module VM = OCF.Align.ValLabRow (HB M)

  ≺br : ∀ {p : Pos (cs M)} → p <ᴾ end → VM.V p zero ≺ forceᴺ _ (Gbr 𝒯 M)
  ≺br {p} r = ≺-respʳ (VM.V-grow {p} {end} r) (≅-sym (VM.V-G′ end zero ev₀ (Gᵖ M end zero)))

m₁≺T⊤ : V¹.V m₁ zero ≺ T⊤
m₁≺T⊤ = to-ν 𝒯 ωᶜ 1 (Br.≺br M₁ {m₁} tt)

no-val-T⊤ : ∀ {Y t} → Lab Y t → T⊤ ⊑⁰ Y → ⊥
no-val-T⊤ lY le = V¹.no-⊑ m₁≺T⊤ no-any-m₁ lY le
```
