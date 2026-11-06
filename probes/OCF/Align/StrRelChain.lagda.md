# 结构关系 (四): 外层链, `MonoStep 2` 的结构证明

> 不含记号. 入口 [StrRel](StrRel.lagda.md). 同 [MonoPort2Chain](MonoPort2Chain.lagda.md): 世界 $1$, `ChainLe (hs hz)` 是两条链的极限的比较, 链点是第 1 层的差树, 动作 `StepA` 只看状态. 这里**整条链都只用结构关系**: 起点的两个状态在 $T_0$, $T_1$ 上都结构相关 (`sLR`, 单位律加 `n0 ⊑ z`), 每一步用一次 `StrRelSound.snd₁`, 最后的值比较只在末尾由 `val₀` 读出.
>
> - `HA-Stepˢ`: `StepA` 满足结构版的 `HA₁` ($T_0$ 上 $\mathrm{nl}(\lambda\_.\,1⨾\delta)$, $T_1$ 上 $\mathrm{nl}(\lambda\_.\,\Omega_1⨾\delta)$, 都对 $\delta$ 结构单调).
> - `chainˢ₁`: 链点 $\delta_n\sqsubseteq_1\delta'_n$, 各自自比, 状态 `SRel`, `Good`, 沿链保持; 两条链的 $T_0$ 读数逐项 $\sqsubseteq_0$.
> - **`mono₂ˢ : MonoStep (hs (hs hz))`**, `grow₂₃ˢ`, 无前提, 不用 `Funext`, 不经 `DValCanon.Gen`, 不用左边极限截断.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.StrRelChain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedTree using (D; hz; hs; n0; n1; _⨾_; nl; sum; sum-fst)
open import OCF.Align.HtFeedClosed using (one; TΛ)
open import OCF.Align.HtCrossInst using (module Hs; b₀)
import OCF.Align.MonoPortStep as St
import OCF.Align.HtCrossVInst as CV
open import OCF.Align.StrRelDef {one} tt
open import OCF.Align.StrRelSound {one} tt using (R₁; snd₁; Sem₁; rf)

module K = St.Ch (hs hz) tt
```

## §1 动作

```agda
StepA : Act₁
StepA p lW′ z Y′ = P.Step Y′

HA-Stepˢ : HA₁ StepA
HA-Stepˢ w w′ Y Y′ g g′ s =
  lm (λ _ → sq o1 (proj₁ s)) ,
  nl⊑ (λ _ → ⨾⊑ rfΩ rfΩ rfΩ g) (λ _ → ⨾⊑ rfΩ rfΩ rfΩ g′) (λ _ → ⨾⊑ rfΩ rfΩ rfΩ (proj₂ s))
```

## §2 外层链

```agda
CC : P.St one → ℕ → D (hs hz) one × (D (hs hz) one × P.St one)
CC Y = K.CC Y

chainˢ₁ : ∀ (Y Y′ : P.St one) → Good Y → Good Y′ → SRel Y Y′ → nl (K.segs Y) ⊑₀ nl (K.segs Y′)
chainˢ₁ Y Y′ g g′ s = lm (λ n → proj₁ (step n))
  where
  c  = λ n → proj₁ (CC Y n)
  c′ = λ n → proj₁ (CC Y′ n)
  δ  = λ n → proj₁ (proj₂ (CC Y n))
  δ′ = λ n → proj₁ (proj₂ (CC Y′ n))
  Yn  = λ n → proj₂ (proj₂ (CC Y n))
  Yn′ = λ n → proj₂ (proj₂ (CC Y′ n))
  go : ∀ n → (δ n ⊑₁ δ′ n) × (Rf (δ n) × (Rf (δ′ n) × (Good (Yn n) × (Good (Yn′ n) × SRel (Yn n) (Yn′ n)))))
  step : ∀ n → Obs (R₁ StepA (δ n) (c n) (Yn n)) (R₁ StepA (δ′ n) (c′ n) (Yn′ n))
  step n = let (hd , (rd , (rd′ , (gy , (gy′ , sy))))) = go n in snd₁ hd StepA HA-Stepˢ (c n) (c′ n) (Yn n) (Yn′ n) gy gy′ sy
  go zero = proj₂ s , (g , (g′ , (g , (g′ , s))))
  go (suc n) =
    let (hd , (rd , (rd′ , (gy , (gy′ , sy))))) = go n
        r = rf (snd₁ rd) StepA HA-Stepˢ (c n) (Yn n) gy
        r′ = rf (snd₁ rd′) StepA HA-Stepˢ (c′ n) (Yn′ n) gy′
    in proj₂ (step n) , (r , (r′ , (G⊕ gy r , (G⊕ gy′ r′ , S⊕ gy gy′ sy (step n)))))
```

## §3 起点

两个起点状态 $Y^L=Y_0⊕\mathrm{Step}\,Y_0$, $Y^R=(Y^L⊕0)⊕\mathrm{Step}(Y^L⊕0)$: 在两个目标上都是 "$x\sqsubseteq (x⨾0)⨾y$", 只用单位律与 `n0 ⊑ z`. 值的比较 (两个底 $1\le b_0$) 在这里由 `val₀` 读出, 是全文唯一用到值的地方.

```agda
g0 : Good P.Y₀
g0 = n0⊑

rS : ∀ {Y} → Good Y → Rf (o₁ (P.Step Y))
rS {Y} g = proj₂ (HA-Stepˢ n0 n0 Y Y g g (sr g))

gL : Good K.Yᴸ
gL = G⊕ {P.Y₀} {P.Step P.Y₀} g0 (rS {P.Y₀} g0)

gR₀ : Good K.Yʳ₀
gR₀ = G⊕0 {K.Yᴸ} gL

gR : Good K.Yʳ
gR = G⊕ {K.Yʳ₀} {P.Step K.Yʳ₀} gR₀ (rS {K.Yʳ₀} gR₀)

sLR : SRel K.Yᴸ K.Yʳ
sLR = tr (u1r (u1r (refl₀ x₀))) (sq (refl₀ (x₀ ⨾ n0)) z0) ,
      tr (u1ʳ gL) (tr (u1ʳ gR₀) (⨾⊑ gR₀ gR₀ gR₀ n0⊑))
  where
  x₀ = o₀ (P.d K.Yᴸ)

hb : K.bᴸ ≤ K.bʳ
hb = val₀ (proj₁ (HA-Stepˢ n0 n0 P.Y₀ K.Yʳ₀ g0 gR₀ (z0 , n0⊑))) (⊲→≤ (sum-fst one (nl (λ _ → n1 ⨾ n0))))
```

## §4 定理

```agda
chainLeˢ : K.ChainLe
chainLeˢ = val₀ (chainˢ₁ K.Yᴸ K.Yʳ gL gR sLR) hb

mono₂ˢ : Hs.MonoStep (hs (hs hz)) tt
mono₂ˢ = subst (λ X → X) (sym (K.step≡)) chainLeˢ

grow₂₃ˢ : asuc (TΛ (hs (hs hz)) tt) ≤ TΛ (hs (hs (hs hz))) tt
grow₂₃ˢ = CV.HsS.hs-reduce<′ (hs (hs hz)) tt tt mono₂ˢ
```
