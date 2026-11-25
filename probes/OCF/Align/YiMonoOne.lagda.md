# YiMono：`T₃ᵐ` 不低于参照的 ψ₀(Ω_{ω+1})

**验收文件，档位：编译定理 (下界，不是同值)。** 链点 η₁ 的层号 κ₁ 里有字面前驱 X ≅ᴵ lim (n+2) (X = 1 + ω⁺ 的层号；ω⁺ = lim (n+1) 是 `T₃ᵐ` 第 0 项的第 0 支)。
`ωᴵ ⊑ᴵ X`，但 ω 本身不在 κ₁ 里 (`YiMonoBreak.no-sω-κ`)；前驱嵌入 `PEmb-suc` 把 ω+1 的顶映到 X，于是 ψ₀(Ω_{ω+1}) ≼ ψ₀(Ω_{κ₁}) (`Ψ-emb`)，再接 `T₃ᵐ-own 1`。
这是 `T₃ᵐ` 的值下界第一次越过 ψ₀(Ω_ω)；只用到 κ₁ 前两项里的有限个字面结点，不涉及 `MonoT`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiMonoOne where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
import OCF.Align.RR5IrrCore as B
open B using (module G; LF)
open import OCF.Align.YiIrrIf using (R; one; _+ʳ_; read0)
open import OCF.Align.YiLvFoldAdd using (copies)
open import OCF.Align.YiLvFoldFin using (fin)
open import OCF.Align.YiRawFoldTw3 using (T₃ᵐ)
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiBtValAdm using (toIL)
open import OCF.Align.YiBtValTw3 using (H-fin)
open import OCF.Align.YiBtValBT using (κ; T₃ᵐ-own)
open import OCF.Align.BTBOFullEmb using (PEmb; Ψ-emb)
open import OCF.Align.YiMonoEmb using (PEmb-⊑; PEmb-∘; PEmb-suc)
import OCF.Align.Level as L
open L using (_<ᴵ_; _≅ᴵ_; _⊑ᴵ_)
open import OCF.Align.Value using (_≼_; ≼-trans)
```

## 1 X 的层号 ⊒ ω

```agda
≅→⊑ : ∀ {a b} → a ≅ᴵ b → a ⊑ᴵ b
≅→⊑ L.z≅ = L.z⊑
≅→⊑ (L.s≅ e) = L.s⊑ e L.zero
≅→⊑ (L.l≅ h) = L.l⊑ (λ n → L.⊑ᴵ-trans (≅→⊑ (h n)) (L.Sim→⊑ᴵ (L.lim n)))

natFin : ∀ m pK lK → L.natᴵ m ≅ᴵ toIL (fin m) pK lK
natFin zero pK lK = L.z≅
natFin (suc m) pK lK = L.s≅ (natFin m pK lK)

atFin : ∀ m K → fin m ≡ K → ∀ pK lK → L.natᴵ m ≅ᴵ toIL K pK lK
atFin m .(fin m) refl pK lK = natFin m pK lK

ωX : ∀ pl lg → L.ωᴵ ⊑ᴵ toIL (read0 (one +ʳ G.lim (copies B.zero one))) pl lg
ωX pl lg = L.l⊑ λ n →
  L.⊑ᴵ-trans (L.Sim→⊑ᴵ (λ q → L.suc (L.suc q)))
    (L.⊑ᴵ-trans (≅→⊑ (atFin (suc (suc n)) (read0 (one +ʳ copies B.zero one n)) (sym (H-fin n)) (pl n) (proj₂ lg n)))
      (L.Sim→⊑ᴵ (L.lim n)))
```

## 2 X 是 κ₁ 的字面前驱

κ₁ 的第 1 项的第 0 项的第 1 项的第 0 项是 X 的后继 (η₁ 的第 1 项是 1 + ω⁺ + …，其中出现 1 + ω⁺ + ω)。

```agda
qX : _ <ᴵ κ 1
qX = L.lim 1 (L.lim 0 (L.lim 1 (L.lim 0 L.zero)))

emb₁ : PEmb (L.suc L.ωᴵ) (κ 1)
emb₁ = PEmb-∘ (PEmb-suc (PEmb-⊑ (ωX _ _))) (PEmb-⊑ (L.s⊑ (L.≅ᴵ-refl _) qX))

T₃ᵐ-Ωω+1 : L.ψ⁰ (L.Ω (L.suc L.ωᴵ)) ≼ read T₃ᵐ
T₃ᵐ-Ωω+1 = ≼-trans (Ψ-emb emb₁) (T₃ᵐ-own 1)
```
