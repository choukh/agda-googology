# 回归: `Tw n ≼ TΛ` 与 `T⁺ʷ ≼ TΛ` 经块内部的 `Simʰ` 重新推出

验收文件. 编译定理, 无前提: `Reg.Tw⊑TΛ`, `Reg.Tw≼TΛʰ` (对任意派发 `D`, 主线带见证的上界), `T⁺ʷ⊑TΛ`, `T⁺ʷ≼TΛʰ` (主线派发 `dl`). 只是下界.
用到的只有第 0 层的左加 `la₀` 与第 0 层的自相关 `refl₀`, 没有用到 `monoʰ`: 两条回归的目标层都是第 0 层, 那里没有结点. 路径 `path₃` 与 `at-T⁺ʷ` 取自 [YiIntoTw3](YiIntoTw3.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCrossReg where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (R; Way; keep; fold; Ext; psum; ΩT)
open import OCF.Lean.YiLamFold using (Lw; w0; ws; wl; wΩ; Pk; rootW; Lw-tw; VΛ)
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiIntoTw3 using (St; st; child; desc; path₃; at-T⁺ʷ)
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiCrossIface
open import OCF.Lean.YiCrossInst using (refl₀; simʰ→≼; psum≽ʰ)
open Pk
open St

module Reg (D : ∀ k K → Ext k K) where
  open W.Fold D

  Tw⊑TΛ : ∀ n → Simʰ zero zero (Ψ zero (Lw-tw n) (λ _ → fold) G.top) (Ψ zero VΛ (λ _ → fold) G.top)
  Tw⊑TΛ n = lR n (psum≽ʰ (λ i → Ψ zero (Lw-tw i) (λ _ → fold) G.top) n
    (refl₀ (Ψ zero (Lw-tw n) (λ _ → fold) G.top)))

  Tw≼TΛʰ : ∀ n → NA.read (Ψ zero (Lw-tw n) (λ _ → fold) G.top) ≼ NA.read (Ψ zero VΛ (λ _ → fold) G.top)
  Tw≼TΛʰ n = simʰ→≼ (Tw⊑TΛ n)
```

观察项的一步下降 (`child`) 在 `Simʰ` 里: 目标层 0 上, Ω 结点层号与 ℕ 极限层号的折叠都是部分和的极限, 第 `n` 项由左加给出.

```agda
ΩT₀ʰ : ∀ {j} (u : Way zero j) K (o : ℕ → R) n {M} {X : Raw M} →
  Simʰ M zero X (o n) → Simʰ M zero X (ΩT zero j u K o)
ΩT₀ʰ (keep () e) K o n q
ΩT₀ʰ fold K o n q = lR n q

childʰ : ∀ {k} (V : Lw k) x n {M} {X : Raw M} →
  Simʰ M zero X (W.Ψ zero (lw′ (child V x n)) (dx (child V x n)) G.top) → Simʰ M zero X (W.Ψ zero V x G.top)
childʰ (wΩ {k} {g} V w) x n q = ΩT₀ʰ (rootW zero k g w x) _ _ n (psum≽ʰ (λ i →
  W.Ψ zero (V (co (W.ptsΩ k g V i)) (lw (W.ptsΩ k g V i))) (λ r → x (co (W.ptsΩ k g V i) , lw (W.ptsΩ k g V i) , r)) G.top) n q)
childʰ (wl V s) x n q = lR n (psum≽ʰ (λ i → W.Ψ zero (V i) (λ r → x (i , r)) G.top) n q)
childʰ w0 x n q = q
childʰ (ws V) x n q = q

descʰ : ∀ ns s {M} {X : Raw M} →
  Simʰ M zero X (W.Ψ zero (lw′ (desc ns s)) (dx (desc ns s)) G.top) →
  Simʰ M zero X (W.Ψ zero (lw′ s) (dx s) G.top)
descʰ [] s q = q
descʰ (n ∷ ns) s q = childʰ (lw′ s) (dx s) n (descʰ ns (child (lw′ s) (dx s) n) q)

T⁺ʷ⊑Tw3 : Simʰ zero zero W.T⁺ʷ (W.Tw 3)
T⁺ʷ⊑Tw3 = descʰ path₃ (st (tw 3) (Lw-tw 3) (λ _ → fold))
  (subst (Simʰ zero zero W.T⁺ʷ) (sym at-T⁺ʷ) (refl₀ W.T⁺ʷ))

T⁺ʷ⊑TΛ : Simʰ zero zero W.T⁺ʷ W.TΛ
T⁺ʷ⊑TΛ = lR 3 (psum≽ʰ W.Tw 3 T⁺ʷ⊑Tw3)

T⁺ʷ≼TΛʰ : NA.read W.T⁺ʷ ≼ NA.read W.TΛ
T⁺ʷ≼TΛʰ = simʰ→≼ T⁺ʷ⊑TΛ
```
