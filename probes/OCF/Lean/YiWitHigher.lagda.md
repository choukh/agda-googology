# 塔的第 3, 4 项上被去掉的见证 (有限测试)

验收文件. 原折叠: [YiDlFold](YiDlFold.lagda.md) 的 `Fold dl` 配 [YiLamFold](YiLamFold.lagda.md) 的塔 (记号 ᵒ, `lc` 层号的 Ω̂ 带 `witT` 搬来的见证); 收缩后: 同一折叠配 [YiWitFold](YiWitFold.lagda.md) 的塔. 有限测试都是 `refl`.
测试: `tw 3`, `tw 4` 的根与 `Tw 4` 下降到 `p5` 处的 top 支, 原来带见证, 收缩后没有; `p5` 的第 0 个链点上那次折叠 (目标层 1, 派发 `dl`) 原来保留成结点, 收缩后折叠成 ℕ 极限. 同样的差别在下一站 `T⁺⁺` 的第 0 个链点与 `tw 3` 的自折叠上.
编译定理 (收缩后, 无前提, 只是下界): `T⁺⁺≼Tw4`, `T⁺⁺≼TΛ`; `T⁺⁺` 是层号 `upT (suc (tw 2))` 的折叠, `Tw 4` 沿 `p6` 下降到它, 原折叠在同一位置也到它 (`at6ᵒ`). 不陈述读法.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiWitHigher where
open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (R; keep; fold; self)
import OCF.Lean.YiNextTower as T
import OCF.Lean.YiLamFold as WL
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiWitFold as WF
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiWitIntoTw3 using (St; st; desc; desc≼)
open import OCF.Lean.YiWitVBtbo using (Tw≼TΛ)
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans)
open St
```

## 1 探针

`link0`: Ω 层号的第 0 个链点 `top` 折到根层号 `k` (派发 `dl k`), 第 1 个链点是 `top` 加上它.

```agda
atW : ∀ {k} → WL.Lw k → Bool
atW (WL.wΩ V (WL.at ρ e)) = true
atW _ = false

topW : ∀ {k} → WL.Lw k → Bool
topW (WL.wΩ V w) = atW (V G.top tt)
topW _ = false

data Hd : Set where
  hl hc ho : Hd

hd : ∀ {m} → Raw m → Hd
hd (G.lim _) = hl
hd (G.lc _ _) = hc
hd _ = ho

link0 : ∀ {k} → WL.Lw k → Maybe Hd
link0 (WL.wΩ {k} {g} V w) = just (hd (W.Ψ k (V G.top tt) (W.dl k (g G.top)) G.top))
link0 _ = nothing
```

## 2 根见证

```agda
root2ᵒ : atW (WL.Lw-tw 2) ≡ true
root2ᵒ = refl
root2 : atW (WF.Lw-tw 2) ≡ true
root2 = refl
root3ᵒ : atW (WL.Lw-tw 3) ≡ true
root3ᵒ = refl
root3 : atW (WF.Lw-tw 3) ≡ false
root3 = refl
root4ᵒ : atW (WL.Lw-tw 4) ≡ true
root4ᵒ = refl
root4 : atW (WF.Lw-tw 4) ≡ false
root4 = refl

-- tw 3 的根见证: witT 经 sxU, selfU 搬来的位置
wT : WL.witT zero (up zero) (WL.witU zero) ≡ WL.at (G.suc G.zero , tt , inj₁ tt) refl
wT = refl
```

## 3 `Tw 4` 里的保留: 位置 `p5`

`p5` 的层号的 top 支是 `tw 3` 的一份; 原折叠在那里带 `wT` 的见证, 目标层 1 的派发 `dl 1 (tw 3)` 在它上保留 (`dl3`).

```agda
s3ᵒ s3 s4ᵒ s4 : St
s3ᵒ = st (tw 3) (WL.Lw-tw 3) (λ _ → fold)
s3 = st (tw 3) (WF.Lw-tw 3) (λ _ → fold)
s4ᵒ = st (tw 4) (WL.Lw-tw 4) (λ _ → fold)
s4 = st (tw 4) (WF.Lw-tw 4) (λ _ → fold)

p5 : List ℕ
p5 = 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

ly5ᵒ : ly (desc p5 s4ᵒ) ≡ lc (suc zero) (λ η → upT (up (suc zero) η))
ly5ᵒ = refl
ly5 : ly (desc p5 s4) ≡ lc (suc zero) (λ η → upT (up (suc zero) η))
ly5 = refl

top5ᵒ : topW (lw′ (desc p5 s4ᵒ)) ≡ true
top5ᵒ = refl
top5 : topW (lw′ (desc p5 s4)) ≡ false
top5 = refl

dl3 : W.dl (suc zero) (tw 3) (G.top , tt , (G.suc G.zero , tt , inj₁ tt)) ≡ keep (inj₁ tt) refl
dl3 = refl

link5ᵒ : link0 (lw′ (desc p5 s4ᵒ)) ≡ just hc
link5ᵒ = refl
link5 : link0 (lw′ (desc p5 s4)) ≡ just hl
link5 = refl

-- 对照: Tw 3 的 path₃ 上同一种位置, 保留来自 witU zero, 两边相同
p4 : List ℕ
p4 = 1 ∷ 0 ∷ 0 ∷ 0 ∷ []

link4ᵒ : link0 (lw′ (desc p4 s3ᵒ)) ≡ just hc
link4ᵒ = refl
link4 : link0 (lw′ (desc p4 s3)) ≡ just hc
link4 = refl
```

## 4 下一站 `T⁺⁺` 在 `Tw 4` 之下; 见证在它的链上的位置

```agda
p6 : List ℕ
p6 = 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

T⁺⁺ : R
T⁺⁺ = W.Ψ zero (WF.Lw-Ω̂ (suc (tw 2)) (T.Legal-tw 2) (WL.ws (WF.Lw-tw 2))) (λ _ → fold) G.top

ly6 : ly (desc p6 s4) ≡ upT (suc (tw 2))
ly6 = refl

at6 : W.Ψ zero (lw′ (desc p6 s4)) (dx (desc p6 s4)) G.top ≡ T⁺⁺
at6 = refl

at6ᵒ : W.Ψ zero (lw′ (desc p6 s4ᵒ)) (dx (desc p6 s4ᵒ)) G.top ≡
  W.Ψ zero (WL.Lw-Ω̂ (suc (tw 2)) (T.Legal-tw 2) (WL.ws (WL.Lw-tw 2))) (λ _ → fold) G.top
at6ᵒ = refl

T⁺⁺≼Tw4 : NA.read T⁺⁺ ≼ NA.read (WF.Tw 4)
T⁺⁺≼Tw4 = desc≼ p6 s4 (≼-refl (NA.read T⁺⁺))

T⁺⁺≼TΛ : NA.read T⁺⁺ ≼ NA.read WF.TΛ
T⁺⁺≼TΛ = ≼-trans T⁺⁺≼Tw4 (Tw≼TΛ 4)

-- T⁺⁺ 的 top 支是 tw 3 的一份: 第 0 个链点原来保留, 收缩后折叠 (T⁺ʷ 的链上 witU zero 的位置, 高一层)
linkᵒ : link0 (WL.Lw-Ω̂ (suc (tw 2)) (T.Legal-tw 2) (WL.ws (WL.Lw-tw 2))) ≡ just hc
linkᵒ = refl
link : link0 (WF.Lw-Ω̂ (suc (tw 2)) (T.Legal-tw 2) (WL.ws (WF.Lw-tw 2))) ≡ just hl
link = refl

-- tw 3 的自折叠的 top (T⁺ʷ 的 Φ₂ 在 tw 3 上的对应): 原来是结点, 收缩后是 ℕ 极限; tw 2 上两边都是结点
Φ3ᵒ : hd (W.Ψ (tw 3) (WL.Lw-tw 3) (self (tw 3)) G.top) ≡ hc
Φ3ᵒ = refl
Φ3 : hd (W.Ψ (tw 3) (WF.Lw-tw 3) (self (tw 3)) G.top) ≡ hl
Φ3 = refl
Φ2 : hd (W.Ψ (tw 2) (WF.Lw-tw 2) (self (tw 2)) G.top) ≡ hc
Φ2 = refl
```
