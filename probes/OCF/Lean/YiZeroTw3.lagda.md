# YiZero 塔的第 3 项：闭项与合法性证书

**判决：编译定理 (第 3 层)，无前提。** 闭项 `T₃ : R` 把 `tw 3` 折到第 0 层 (读法 ψ₀(Ω_Ω)，读法不是定理)；`T₃-legal : Lgl zero T₃`。根上的链照 [YiLeanTw3](YiLeanTw3.lagda.md)：
从 `top` 起，第 `n` 项是 `F ηₙ`，下一点是 `ηₙ + F ηₙ` (上一点放在叶上；这是 `F-up` 给出合法性的形状)。与主线的差别只在折叠的 ω 倍 ([YiZeroFold](YiZeroFold.lagda.md))。
链点读成层号与参照的比较在验收文件 [YiZeroAcc](YiZeroAcc.lagda.md)，值在 [YiZeroAccFin](YiZeroAccFin.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiZeroTw3 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiZeroCore
open import OCF.Lean.YiZeroFold
open import OCF.Lean.YiZeroLegal
```

## 1 第 0 层的树作层号

```agda
R : Set
R = Raw zero

⌜_⌝ : R → LF
⌜ η ⌝ = up zero η

sh : ∀ {a} b → Cp zero a b → Shift ⌜ a ⌝ ⌜ b ⌝
sh b (inj₁ refl) q = q , refl
sh (G.suc b) (inj₂ p) q = inj₂ (proj₁ (sh b p q)) , proj₂ (sh b p q)
sh (G.lim f) (inj₂ (n , p)) q = (n , proj₁ (sh (f n) p q)) , proj₂ (sh (f n) p q)
sh G.top (inj₂ refl) ()

lv : (η : R) → Lgl zero η → Lv ⌜ η ⌝
lv G.zero l = v0
lv (G.suc a) l = vs (lv a l)
lv (G.lim f) (st , lf) = vl (λ n → lv (f n) (lf n)) (λ n → sh (f (suc n)) (st n))
lv G.top l = vs v0

cp-tr : ∀ {a b d : R} → Cp zero a b → Cp zero b d → Cp zero a d
dn-tr : ∀ {a b : R} d → Cp zero a b → Dn zero b d → Dn zero a d
cp-tr p (inj₁ refl) = p
cp-tr p (inj₂ q) = inj₂ (dn-tr _ p q)
dn-tr (G.suc d) p q = cp-tr p q
dn-tr (G.lim f) p (n , q) = n , cp-tr p q
dn-tr G.top (inj₁ refl) refl = refl
dn-tr G.top (inj₂ ()) refl
```

## 2 各支的折叠，对层号单调

```agda
F : (η : R) → Lgl zero η → R
F η l = Ψ zero (lv η l) (λ _ → fold) G.top

F-lgl : ∀ η l → Lgl zero (F η l)
F-lgl η l = Ψ-lgl zero (lv η l) (λ _ → fold) G.top tt

F-up : ∀ η y (l : Lgl zero η) (ly : Lgl zero y) →
  Cp zero (F η l) (F (plus zero η y) (plus-lgl zero η y l ly))
F-up η G.zero l ly = inj₁ refl
F-up η (G.suc y) l ly = cp-tr (F-up η y l ly) (inj₂ (0 , inj₁ refl))
F-up η (G.lim f) l (st , lf) = cp-tr (F-up η (f 0) l (lf 0)) (inj₂ (0 , inj₁ refl))
F-up η G.top l ly = inj₂ (0 , inj₁ refl)
```

## 3 闭项

```agda
record Pt : Set where
  constructor pt
  field
    co : R
    lw : Lgl zero co
open Pt

obs : Pt → R
obs (pt η l) = F η l

nx : Pt → Pt
nx (pt η l) = pt (plus zero η (F η l)) (plus-lgl zero η (F η l) l (F-lgl η l))

pts : ℕ → Pt
pts = iter nx (pt G.top tt)

T₃ : R
T₃ = G.lim (λ n → obs (pts n))

obs-step : ∀ p → Cp zero (obs p) (obs (nx p))
obs-step (pt η l) = F-up η (F η l) l (F-lgl η l)

T₃-legal : Lgl zero T₃
T₃-legal = (λ n → obs-step (pts n)) , (λ n → F-lgl (co (pts n)) (lw (pts n)))
```

## 4 行

```agda
tw₃-form : tw 3 ≡ lc zero (λ η → up ⌜ η ⌝ G.top)
tw₃-form = refl

T₃-start : co (pts 0) ≡ G.top
T₃-start = refl

T₃-term : ∀ n → obs (pts n) ≡ Ψ zero (lv (co (pts n)) (lw (pts n))) (λ _ → fold) G.top
T₃-term n = refl

T₃-feedback : ∀ n → co (pts (suc n)) ≡ plus zero (co (pts n)) (obs (pts n))
T₃-feedback n = refl
```
