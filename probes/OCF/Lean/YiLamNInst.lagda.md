# YiLam 实例: 一致折叠 (YiLamFold) 填满 `Uniᴾ` 与读回域

非验收文件. 编译定理, 无前提: `Lam : Uniᴾ` 的各行与 `cpt-zero`, `cpt-suc` 都是 `refl`; `stp` 是 `dfin`, `obd` 是外部派发的限制, `ωw` 是 `rootW`, `Kb` 是 `Kfk`. 读回域 `domΛ` 填到塔的一切项与 Λ; `TΛ`, `Tw n` 就是接口的闭项形状.
不陈述 `Uni` 本身填不填得上; 那一条在 [YiLamNRel](YiLamNRel.lagda.md). 接口 [YiLamIf](YiLamIf.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLamNInst where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev; Way; keep; fold; Ext; R)
open import OCF.Lean.YiLamFold
open import OCF.Lean.YiLamIf using (Uniᴾ; Domᴾ)
```

## 1 字段

```agda
bS : ∀ {k} → Lw (suc k) → Lw k
bS (ws V) = V

bL : ∀ {f} → Lw (lim f) → ∀ n → Lw (f n)
bL (wl V st) = V

bC : ∀ {k g} → Lw (lc k g) → ∀ η → Lgl k η → Lw (g η)
bC (wΩ V w) = V

ωw : ∀ m {k g} → Lw (lc k g) → Ext m (lc k g) → Way m k
ωw m {k} {g} (wΩ V w) x = rootW m k g w x

Kb : ∀ m {k g} → Lw (lc k g) → Ext m (lc k g) → Raw k → Raw m
Kb m {k} (wΩ V w) x =
  Kfk k (λ η → Ψ m (V (nrmk k η) (nrmk-lgl k η)) (λ r → x (nrmk k η , nrmk-lgl k η , r)) G.top)

stp : ∀ {k g} (V : Lw (lc k g)) η → Lgl k η → Ext k (g η)
stp {k} {g} (wΩ V w) η l = dfin k (g η)

obd : ∀ m {k g} (V : Lw (lc k g)) → Ext m (lc k g) → ∀ η → Lgl k η → Ext m (g η)
obd m (wΩ V w) x η l r = x (η , l , r)

cpt : ∀ {k g} → Lw (lc k g) → ℕ → Raw k
cpt {k} {g} (wΩ V w) n = Pk.co (ptsΩ k g V n)

cpt-lgl : ∀ {k g} (V : Lw (lc k g)) n → Lgl k (cpt V n)
cpt-lgl {k} {g} (wΩ V w) n = Pk.lw (ptsΩ k g V n)
```

## 2 实例

```agda
Lam : Uniᴾ
Lam = record
  { Bd = Lw ; bS = bS ; bL = bL ; bC = bC ; Ψ = Ψ ; cmp = cmpw
  ; ωw = ωw ; Kb = Kb ; stp = stp ; obd = obd ; cpt = cpt ; cpt-lgl = cpt-lgl
  ; zero-row = λ m V x → refl
  ; suc-row = λ m V x a → refl
  ; lim-row = λ m V x f → refl
  ; node-row = λ m V x r g → refl
  ; em-rowˢ = λ { m (ws V) x a → refl }
  ; em-rowˡ = λ { m (wl V st) x n a → refl }
  ; em-rowᶜ = λ { m (wΩ V w) x η l a → refl }
  ; top-row⁰ = λ { m w0 x → refl }
  ; top-rowˢ = λ { m (ws V) x → refl }
  ; top-rowˡ = λ { m (wl V st) x → refl }
  ; top-rowᶜ = λ { m (wΩ V w) x → refl }
  ; cpt-zero = λ { (wΩ V w) → refl }
  ; cpt-suc = λ { (wΩ V w) n → refl }
  ; Ψ-lgl = Ψ-lgl
  ; Ψ-cp = Ψ-cp
  ; Kb-br = λ { m {k} (wΩ V w) x → Kfk-br k _ (λ η → Ψ-lgl m (V (nrmk k η) (nrmk-lgl k η)) _ G.top tt) }
  }
```

## 3 读回域与闭项

```agda
domΛ : Domᴾ Lam
domΛ = record { bd-tw = Lw-tw ; bd-Λ = VΛ }

TΛ-uni : TΛ ≡ Uniᴾ.Ψ Lam zero (Domᴾ.bd-Λ domΛ) (λ _ → fold) G.top
TΛ-uni = refl

Tw-uni : ∀ n → Tw n ≡ Uniᴾ.Ψ Lam zero (Domᴾ.bd-tw domΛ n) (λ _ → fold) G.top
Tw-uni n = refl
```
