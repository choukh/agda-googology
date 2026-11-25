# YiUni 实例：`tw 2` 上的折叠 (YiNextFold) 满足接口

**非验收文件。判决：编译定理，无前提。** `Bd` 取 [YiNextBase](YiNextBase.lagda.md) 的 `Lv` (Ω 结点层号只有 `tw 2` 的 `vΩ`)，折叠取 [YiNextFold](YiNextFold.lagda.md)；接口 [YiUniIf](YiUniIf.lagda.md) 的字段全部填上，各行是 `refl`。
`stp`、`obd` 一律折叠，`ωw` 读 `p₀`，`Kb` 是累加 `Kf`。读回域填到 `tw 2` (`dom₂`)；`T₃` 就是接口的闭项形状 (`T₃-uni`)。不否定别的实例。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUniTw2 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
open import OCF.Lean.YiNextFold using (Ψ; Ψ-lgl; Ψ-cp; Up-mono; p₀)
open import OCF.Lean.YiNextTop using (V₂; T₃)
open import OCF.Lean.YiUniIf using (Uni; DomTo)
```

## 1 字段

```agda
Fv : (V : ∀ η → Lgl zero η → Lv ⌜ η ⌝) → (η : R) → Lgl zero η → R
Fv V η l = Ψ zero (V η l) (λ _ → fold) G.top

FLv : (V : ∀ η → Lgl zero η → Lv ⌜ η ⌝) → ∀ η l → Lgl zero (Fv V η l)
FLv V η l = Ψ-lgl zero (V η l) (λ _ → fold) G.top tt

Tv : ∀ m (V : ∀ η → Lgl zero η → Lv ⌜ η ⌝) → Ext m (lc zero ⌜_⌝) → R → Raw m
Tv m V x η = Ψ m (V (nrm η) (nrm-lgl η)) (λ r → x (nrm η , nrm-lgl η , r)) G.top

bS : ∀ {k} → Lv (suc k) → Lv k
bS (vs V) = V

bL : ∀ {f} → Lv (lim f) → ∀ n → Lv (f n)
bL (vl V st) = V

bC : ∀ {k g} → Lv (lc k g) → ∀ η → Lgl k η → Lv (g η)
bC (vΩ V u) = V

ωw : ∀ m {k g} → Lv (lc k g) → Ext m (lc k g) → Way m k
ωw m (vΩ V u) x = x p₀

Kb : ∀ m {k g} → Lv (lc k g) → Ext m (lc k g) → Raw k → Raw m
Kb m (vΩ V u) x = Kf m (Tv m V x)

stp : ∀ {k g} (V : Lv (lc k g)) η → Lgl k η → Ext k (g η)
stp (vΩ V u) η l r = fold

obd : ∀ m {k g} (V : Lv (lc k g)) → Ext m (lc k g) → ∀ η → Lgl k η → Ext m (g η)
obd m (vΩ V u) x η l r = fold

cpt : ∀ {k g} → Lv (lc k g) → ℕ → Raw k
cpt (vΩ V u) n = co (pts (Fv V) (FLv V) n)

cpt-lgl : ∀ {k g} (V : Lv (lc k g)) n → Lgl k (cpt V n)
cpt-lgl (vΩ V u) n = lw (pts (Fv V) (FLv V) n)
```

## 2 实例

```agda
Tw2 : Uni
Tw2 = record
  { Bd = Lv ; bS = bS ; bL = bL ; bC = bC ; Ψ = Ψ ; cmp = cmp
  ; ωw = ωw ; Kb = Kb ; stp = stp ; obd = obd ; cpt = cpt ; cpt-lgl = cpt-lgl
  ; zero-row = λ m V x → refl
  ; suc-row = λ m V x a → refl
  ; lim-row = λ m V x f → refl
  ; node-row = λ m V x r g → refl
  ; em-rowˢ = λ { m (vs V) x a → refl }
  ; em-rowˡ = λ { m (vl V st) x n a → refl }
  ; em-rowᶜ = λ { m (vΩ V u) x η l a → refl }
  ; top-row⁰ = λ { m v0 x → refl }
  ; top-rowˢ = λ { m (vs V) x → refl }
  ; top-rowˡ = λ { m (vl V st) x → refl }
  ; top-rowᶜ = λ { m (vΩ V u) x → refl }
  ; cpt-zero = λ { (vΩ V u) → refl }
  ; cpt-suc = λ { (vΩ V u) n → refl }
  ; Ψ-lgl = Ψ-lgl
  ; Ψ-cp = Ψ-cp
  ; Kb-br = λ { m (vΩ V u) x → Kf-br m (Tv m V x) (λ η → Ψ-lgl m (V (nrm η) (nrm-lgl η)) _ G.top tt) }
  ; top-up = λ { m (vΩ V u) x η l y ly → Up-mono m (u η l y ly) }
  }
```

## 3 读回域与闭项

```agda
dom₂ : DomTo Tw2 2
dom₂ = (v0 , vs v0) , V₂

T₃-uni : T₃ ≡ Uni.Ψ Tw2 zero V₂ (λ _ → fold) G.top
T₃-uni = refl
```
