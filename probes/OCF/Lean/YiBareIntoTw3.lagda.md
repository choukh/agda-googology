# 裸折叠里读法 ψ₀(Ω_{Ω+1}) 的闭项不高于塔的第 3 项与 `TΛᵇ` (无前提)

验收文件. 编译定理 `T⁺ʷ≼Tw3 : NA.read W.T⁺ʷᵇ ≼ NA.read (W.Twᵇ 3)`, `T⁺ʷ≼TΛ`, 只是下界. [YiIntoTw3](YiIntoTw3.lagda.md) 逐字搬到 [YiBareFold](YiBareFold.lagda.md), 删去旁注 `keep₅` (原文里没有被用到).
同一条 `path₃` 仍到达 `T⁺ʷᵇ` 本身 (`at-T⁺ʷ` 是 `refl`): 第 5 步的链点不再是结点, 是 ℕ-极限, 其后三次第 0 项到层号 `up 1 (top + top)`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBareIntoTw3 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (R; Way; keep; fold; Ext; psum; ΩT)
open import OCF.Lean.YiLamFold using (Lw; w0; ws; wl; wΩ; Pk; rootW)
import OCF.Lean.YiBareFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiBareVBtbo using (psum≽; Tw≼TΛ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≼l)
open Pk
```

## 1 观察项的一步下降

目标层 0 上, Ω 结点层号的折叠是第 `n` 个链点那一支的部分和的极限, ℕ 极限层号的折叠是各分量的部分和的极限; `child` 取其中第 `n` 项, 其余公共上界不动.

```agda
record St : Set where
  constructor st
  field
    ly  : LF
    lw′ : Lw ly
    dx  : Ext zero ly
open St

child : ∀ {k} → Lw k → Ext zero k → ℕ → St
child (wΩ {k} {g} V w) x n =
  st (g (co (W.ptsΩ k g V n))) (V (co (W.ptsΩ k g V n)) (lw (W.ptsΩ k g V n)))
     (λ r → x (co (W.ptsΩ k g V n) , lw (W.ptsΩ k g V n) , r))
child (wl {f} V s) x n = st (f n) (V n) (λ r → x (n , r))
child {k} V x n = st k V x

ΩT₀ : ∀ {j} (u : Way zero j) K (o : ℕ → R) n {ℓ} {X : L.Ordᶜ ℓ} →
  X ≼ NA.read (o n) → X ≼ NA.read (ΩT zero j u K o)
ΩT₀ (keep () e) K o n q
ΩT₀ fold K o n q = ≼l n q

child≼ : ∀ {k} (V : Lw k) x n {ℓ} {X : L.Ordᶜ ℓ} →
  X ≼ NA.read (W.Ψ zero (lw′ (child V x n)) (dx (child V x n)) G.top) → X ≼ NA.read (W.Ψ zero V x G.top)
child≼ (wΩ {k} {g} V w) x n q = ΩT₀ (rootW zero k g w x) _ _ n (≼-trans q (psum≽ (λ i →
  W.Ψ zero (V (co (W.ptsΩ k g V i)) (lw (W.ptsΩ k g V i))) (λ r → x (co (W.ptsΩ k g V i) , lw (W.ptsΩ k g V i) , r)) G.top) n))
child≼ (wl V s) x n q = ≼l n (≼-trans q (psum≽ (λ i → W.Ψ zero (V i) (λ r → x (i , r)) G.top) n))
child≼ w0 x n q = q
child≼ (ws V) x n q = q

desc : List ℕ → St → St
desc [] s = s
desc (n ∷ ns) s = desc ns (child (lw′ s) (dx s) n)

desc≼ : ∀ ns s {ℓ} {X : L.Ordᶜ ℓ} → X ≼ NA.read (W.Ψ zero (lw′ (desc ns s)) (dx (desc ns s)) G.top) →
  X ≼ NA.read (W.Ψ zero (lw′ s) (dx s) G.top)
desc≼ [] s q = q
desc≼ (n ∷ ns) s q = child≼ (lw′ s) (dx s) n (desc≼ ns (child (lw′ s) (dx s) n) q)
```

## 2 位置与定理

`path₃` 的九步: `Tw 3` 的第 1 个链点 (`top + Tw 2`); 三次 ℕ 极限的第 0 项, 到层号 `upT (suc (suc zero))` (`ly-fin2`);
它的第 1 个链点, 即第 1 层的 `top` 加上 `tw 2` 的顶折到第 1 层 (裸折叠里根折叠, 是 ℕ-极限); 三次 ℕ 极限的第 0 项, 到层号 `up 1 (top + top)` (`ly-top2`); 它的第 0 个链点.

```agda
path₃ : List ℕ
path₃ = 1 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ 0 ∷ []

ly-fin2 : ly (desc (1 ∷ 0 ∷ 0 ∷ 0 ∷ []) (st (tw 3) (W.Lw-twᵇ 3) (λ _ → fold))) ≡ upT (suc (suc zero))
ly-fin2 = refl

ly-top2 : ly (desc (1 ∷ 0 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ []) (st (tw 3) (W.Lw-twᵇ 3) (λ _ → fold))) ≡
  up (suc zero) (plus (suc zero) G.top G.top)
ly-top2 = refl

ly-T⁺ʷ : ly (desc path₃ (st (tw 3) (W.Lw-twᵇ 3) (λ _ → fold))) ≡ suc (tw 2)
ly-T⁺ʷ = refl

at-T⁺ʷ : W.Ψ zero (lw′ (desc path₃ (st (tw 3) (W.Lw-twᵇ 3) (λ _ → fold)))) (dx (desc path₃ (st (tw 3) (W.Lw-twᵇ 3) (λ _ → fold)))) G.top ≡ W.T⁺ʷᵇ
at-T⁺ʷ = refl

T⁺ʷ≼Tw3 : NA.read W.T⁺ʷᵇ ≼ NA.read (W.Twᵇ 3)
T⁺ʷ≼Tw3 = desc≼ path₃ (st (tw 3) (W.Lw-twᵇ 3) (λ _ → fold)) (≼-refl (NA.read W.T⁺ʷᵇ))

T⁺ʷ≼TΛ : NA.read W.T⁺ʷᵇ ≼ NA.read W.TΛᵇ
T⁺ʷ≼TΛ = ≼-trans T⁺ʷ≼Tw3 (Tw≼TΛ 3)
```
