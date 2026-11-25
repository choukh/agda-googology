# 记号侧: `StandardOmega.NF₁` 与 `EboLeanBase.NF` 的关系

> 验收文件 (读记号, 不进成品). 判决 (定理): `NF₁ ⊆ NF` (`nf₁→nf`, 可见参数 `Vis₁` 与 `InG` 逐构造子对应); 反向不成立: 塔第 3 行 ψ₀(Ω_{Ω_Ω}) 是 `NF` (`EboLeanTree.nf-tower 3`) 而不是 `NF₁` (`row3∉NF₁`, 下标 Ω_Ω 不是 `Sb`).
> 所以 [YiCFCofin](YiCFCofin.lagda.md) 的 `cofin` 覆盖 `cofin₁` 不覆盖的项. 两者的 `fsn` 不是同一个函数 (`EBO.fsn` 与 `EboLeanDef.fsn`), 本文不比较它们. `Standard.NF` 的可见参数不进下标, 与 `NF` 的关系本文不判.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCFRel where

open import Data.Empty using (⊥)
open import Data.List.Base using ([]; _∷_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Unit.Base using (tt)

open import OCF.Align.EboLeanDef using (EBOψ; ΩTower)
open import OCF.Align.EboLeanBase using (NF; NFP; n[]; n∷; nψ; HdLe; InG; gp; gtl; gh; gw; gc; lt→<ᴾ; eq→≡ᴾ)
open import OCF.Align.EboLeanTree using (nf-tower)
open import OCF.Align.Bachmann using (Hd≤)
import OCF.Align.StandardOmega as SO
open SO using (NF₁; NFᴾ₁; Vis₁; vh; vd; vs; vt; Sb; sC)
```

```agda
G→Vis : ∀ {u z t} → InG u z t → Vis₁ u z t
G→Vis (gp (gh l))   = vh l
G→Vis (gp (gw l i)) = vs l (G→Vis i)
G→Vis (gp (gc l i)) = vd l (G→Vis i)
G→Vis (gtl i)       = vt (G→Vis i)

hd→ : ∀ {x xs} → Hd≤ xs x → HdLe x xs
hd→ {xs = []} _ = tt
hd→ {x} {xs = y ∷ _} (inj₁ e) = inj₁ (lt→<ᴾ y x e)
hd→ {x} {xs = y ∷ _} (inj₂ e) = inj₂ (eq→≡ᴾ y x e)

nf₁→nf   : ∀ {t} → NF₁ t → NF t
nfp₁→nfp : ∀ {x} → NFᴾ₁ x → NFP x
nf₁→nf SO.n[] = n[]
nf₁→nf (SO.n∷ p n h) = n∷ (nfp₁→nfp p) (hd→ h) (nf₁→nf n)
nfp₁→nfp (SO.nψ nu su na b) = nψ (nf₁→nf nu) (nf₁→nf na) (λ i → b (G→Vis i))
```

反向: 第 3 行的参数 Ω_{Ω_Ω} 的下标 Ω_Ω 既不可数, 也不是 Ω + 可数.

```agda
ΩΩ-notSb : Sb (ΩTower 2) → ⊥
ΩΩ-notSb (sC ())

row3∉NF₁ : NF₁ (EBOψ 3) → ⊥
row3∉NF₁ (SO.n∷ (SO.nψ _ _ (SO.n∷ (SO.nψ _ s _ _) _ _) _) _ _) = ΩΩ-notSb s

row3∈NF : NF (EBOψ 3)
row3∈NF = nf-tower 3
```
