# 燃料搜索派发的折叠填满 `Uniᴾ` 与读回域; 两处原来折叠的派发现在保留

非验收文件. 编译定理, 无前提: `Dl : Uniᴾ` (各行与 `cpt-zero`, `cpt-suc` 是 `refl`, `stp` 是 `dl`), 读回域 `domΛ` 到塔的一切项与 Λ. 有限测试 (`refl` 或 `tt`): [YiLamNAsk](YiLamNAsk.lagda.md) 的那个结点在新的 `Tw 3` 里仍被问到 (`asked◁`), 层号仍是 `lc J (up J)`, 它的链在 `r♯` 上现在保留 (`keeps♯`), 并且对一切位置完全 (`stp-full-J`);
[YiLamVLost](YiLamVLost.lagda.md) 那个 ℕ 极限层号的结点 (坐标换成新的 `Tw 2`) 的根现在保留 (`root-kept`). 不陈述值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDlInst where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (lev; Way; keep; fold; Ext; R; ⌜_⌝; psum; ΩT)
open import OCF.Lean.YiLamFold using
  (Kfk; Kfk-br; nrmk; nrmk-lgl; Lw; w0; ws; wl; wΩ; Pk; rootW; witU; Lw-tw; VΛ)
open import OCF.Lean.YiLamNInst using (bS; bL; bC; ωw; obd)
open import OCF.Lean.YiLamIf using (Uniᴾ; Domᴾ; StpFullᴾ)
open import OCF.Lean.YiLamNFuel using (dlev-full-J)
open import OCF.Lean.YiUniIf using (IsKeep)
open import OCF.Lean.YiLamNAsk using (_◁_; here; inΣ; ΩT0; J; r♯)
open import OCF.Lean.YiDlFold
```

## 1 字段与实例

```agda
Kb : ∀ m {k g} → Lw (lc k g) → Ext m (lc k g) → Raw k → Raw m
Kb m {k} (wΩ V w) x =
  Kfk k (λ η → Ψ m (V (nrmk k η) (nrmk-lgl k η)) (λ r → x (nrmk k η , nrmk-lgl k η , r)) G.top)

stp : ∀ {k g} (V : Lw (lc k g)) η → Lgl k η → Ext k (g η)
stp {k} {g} (wΩ V w) η l = dl k (g η)

cpt : ∀ {k g} → Lw (lc k g) → ℕ → Raw k
cpt {k} {g} (wΩ V w) n = Pk.co (ptsΩ k g V n)

cpt-lgl : ∀ {k g} (V : Lw (lc k g)) n → Lgl k (cpt V n)
cpt-lgl {k} {g} (wΩ V w) n = Pk.lw (ptsΩ k g V n)

Dl : Uniᴾ
Dl = record
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

domΛ : Domᴾ Dl
domΛ = record { bd-tw = Lw-tw ; bd-Λ = VΛ }

TΛ-uni : TΛ ≡ Uniᴾ.Ψ Dl zero (Domᴾ.bd-Λ domΛ) (λ _ → fold) G.top
TΛ-uni = refl

Tw-uni : ∀ n → Tw n ≡ Uniᴾ.Ψ Dl zero (Domᴾ.bd-tw domΛ n) (λ _ → fold) G.top
Tw-uni n = refl
```

## 2 `YiLamNAsk` 的极限目标: 新的 `Tw 3` 仍问到, 链在 `r♯` 上保留

路径与 `YiLamNAsk` §2 相同 (链点 1, 再沿分量 0, 1, 0, 1, 0), 链点由新折叠算出.

```agda
obsL : ∀ {f} → Lw (lim f) → ℕ → R
obsL V n = Ψ zero (bL V n) (λ _ → fold) G.top

obsΩ : ∀ {k g} → Lw (lc k g) → ℕ → R
obsΩ V n = Ψ zero (bC V (cpt V n) (cpt-lgl V n)) (λ _ → fold) G.top

stepL : ∀ {f} (V : Lw (lim f)) n {a} → a ◁ obsL V n → a ◁ Ψ zero V (λ _ → fold) G.top
stepL (wl V st) n q = inΣ _ n q

stepΩ : ∀ {k g} (V : Lw (lc k g)) n {a} → a ◁ obsΩ V n → a ◁ Ψ zero V (λ _ → fold) G.top
stepΩ {k} {g} (wΩ V w) n q = ΩT0 k (rootW zero k g w (λ _ → fold)) _ _ (inΣ _ n q)

A B C D E : Σ LF Lw
A = _ , bC (Lw-tw 3) (cpt (Lw-tw 3) 1) (cpt-lgl (Lw-tw 3) 1)
B = _ , bL (proj₂ A) 0
C = _ , bL (proj₂ B) 1
D = _ , bL (proj₂ C) 0
E = _ , bL (proj₂ D) 1

VJ : Lw (lc J (up J))
VJ = bL (proj₂ E) 0

NJ : R
NJ = Ψ zero VJ (λ _ → fold) G.top

asked◁ : NJ ◁ Tw 3
asked◁ = stepΩ (Lw-tw 3) 1 (stepL (proj₂ A) 0 (stepL (proj₂ B) 1 (stepL (proj₂ C) 0
  (stepL (proj₂ D) 1 (stepL (proj₂ E) 0 here)))))

keeps♯ : IsKeep (stp VJ G.top tt r♯)
keeps♯ = tt

comp0 : ωw J (bL (bC VJ G.top tt) 0) (λ r → stp VJ G.top tt (0 , r)) ≡ stp VJ G.top tt r♯
comp0 = refl

-- 在这个极限目标上, 链的下一步的派发对一切位置完全 (经 `YiLamNFuel.dlev-full-J`).
stp-full-J : StpFullᴾ Dl VJ G.top tt
stp-full-J = dlev-full-J (up J G.top)
```

## 3 `YiLamVLost` 的结点: 根现在保留

```agda
V2 : Lw (tw 2)
V2 = Lw-tw 2

ξa : R
ξa = plus zero G.top (G.suc (Tw 2))

rN : Pre (tw 2)
rN = nrmk zero ξa , nrmk-lgl zero ξa , inj₁ tt

root-kept : rootW (lev (tw 2) rN) zero ⌜_⌝ (witU zero) (cmpw V2 rN) ≡ keep (0 , 0 , 0 , inj₂ (inj₁ tt)) refl
root-kept = refl
```
