# YiNext 闭项：塔的第 3 项与 `Ω̂ (tw 2 + 1)` 折到第 0 层

**判决：编译定理 (第 3 层)，无前提。** `T₃` 折 `tw 3` (读法 ψ₀(Ω_Ω))，`T⁺` 折 `upT (suc (tw 2))` (读法 ψ₀(Ω_{Ω+1}))；读法不是定理。
两者合法 (`T₃-legal`, `T⁺-legal`)；`T⁺` 的根是层号 `tw 2` 的结点的链行，第 0 项定义性地就是 `T₃` (`T⁺-term₀`)。
`tw 2` 上两个位置一律折叠 (`cmp`)，`top` 在目标 `tw 2` 上保留为层号 0 的结点 (`Ω-keep`)。值在验收文件 [YiNextAcc](YiNextAcc.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNextTop where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase
open import OCF.Lean.YiNextFold
```

## 1 第 0 层的树作层号

照主线 [YiLeanTw3](YiLeanTw3.lagda.md) §1：合法的 `η` 读成 `Lv`。`up-lv`：第 `η + y` 支的公共上界沿后继与第 0 支走下去是第 `η` 支的。

```agda
sh : ∀ {a} b → Cp zero a b → Shift ⌜ a ⌝ ⌜ b ⌝
sh b (inj₁ refl) q = q , refl
sh (G.suc b) (inj₂ p) q = inj₂ (proj₁ (sh b p q)) , proj₂ (sh b p q)
sh (G.lim f) (inj₂ (n , p)) q = (n , proj₁ (sh (f n) p q)) , proj₂ (sh (f n) p q)

lv : (η : R) → Lgl zero η → Lv ⌜ η ⌝
lv G.zero l = v0
lv (G.suc a) l = vs (lv a l)
lv (G.lim f) (st , lf) = vl (λ n → lv (f n) (lf n)) (λ n → sh (f (suc n)) (st n))
lv G.top l = vs v0

up-lv : ∀ η l y ly → Up (lv η l) (lv (plus zero η y) (plus-lgl zero η y l ly))
up-lv η l G.zero ly = ur
up-lv η l (G.suc y) ly = us (up-lv η l y ly)
up-lv η l (G.lim f) (st , lf) = ul (up-lv η l (f 0) (lf 0))
up-lv η l G.top ly = us ur

V₂ : Lv (tw 2)
V₂ = vΩ lv up-lv
```

## 2 闭项

```agda
F : (η : R) → Lgl zero η → R
F η l = Ψ zero (lv η l) (λ _ → fold) G.top

T₃ : R
T₃ = Ψ zero V₂ (λ _ → fold) G.top

T₃-legal : Lgl zero T₃
T₃-legal = Ψ-lgl zero V₂ (λ _ → fold) G.top tt

T⁺ : R
T⁺ = Ψ zero (vs V₂) (λ _ → fold) G.top

T⁺-legal : Lgl zero T⁺
T⁺-legal = Ψ-lgl zero (vs V₂) (λ _ → fold) G.top tt
```

## 3 行

`tw 3` 是层号 0 的 Ω 结点，`T₃` 的根是它的链行 (同主线)；`upT (suc (tw 2))` 是层号 `tw 2` 的 Ω 结点 (分支是读回)，
`T⁺` 的根是它的链行：链在 `Raw (tw 2)`，从 `top` 起，下一点加上目标为 `tw 2` 自己的折叠，观察是折到第 0 层。

```agda
P₃ : ℕ → Pt
P₃ = pts F (λ η l → Ψ-lgl zero (lv η l) (λ _ → fold) G.top tt)

tw₃-form : tw 3 ≡ lc zero (λ η → up ⌜ η ⌝ G.top)
tw₃-form = refl

T₃-form : T₃ ≡ G.lim (λ n → F (co (P₃ n)) (lw (P₃ n)))
T₃-form = refl

T₃-feedback : ∀ n → co (P₃ (suc n)) ≡ plus zero (co (P₃ n)) (F (co (P₃ n)) (lw (P₃ n)))
T₃-feedback n = refl

K⁺-form : upT (suc (tw 2)) ≡ lc (tw 2) (up (tw 2))
K⁺-form = refl

Φ₂ : Raw (tw 2) → Raw (tw 2)
Φ₂ = Ψ (tw 2) V₂ (self (tw 2))

T⁺-form : T⁺ ≡ G.lim (λ n → Ψ zero V₂ (λ _ → fold) (chain (tw 2) Φ₂ n))
T⁺-form = refl

T⁺-feedback : ∀ n → chain (tw 2) Φ₂ (suc n) ≡ plus (tw 2) (chain (tw 2) Φ₂ n) (Φ₂ (chain (tw 2) Φ₂ n))
T⁺-feedback n = refl

T⁺-term₀ : Ψ zero V₂ (λ _ → fold) (chain (tw 2) Φ₂ 0) ≡ T₃
T⁺-term₀ = refl

T₃⊑T⁺ : Cp zero T₃ T⁺
T₃⊑T⁺ = inj₂ (0 , inj₁ refl)

Ω-keep : Φ₂ G.top ≡ G.lc p₀ (Kf (tw 2) (λ η →
  Ψ (tw 2) (lv (nrm η) (nrm-lgl η)) (λ r → keep (nrm η , nrm-lgl η , r) refl) G.top))
Ω-keep = refl
```
