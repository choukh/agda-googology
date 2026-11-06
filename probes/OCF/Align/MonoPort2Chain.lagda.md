# 第 1 层的值关系 (四): 外层链, `MonoStep 2`, $T_2<T_3$

> 不含记号. 入口 [MonoPort2](MonoPort2.lagda.md). 世界 $1$. `ChainLe (hs hz)` ([MonoPortStep](MonoPortStep.lagda.md)) 是实例 $\Lambda=2$ 里的一对链, 链的点是第 1 层的差树, 动作 `StepA` 只看状态.
>
> - `HA-Step₁`: `StepA` 满足 `HA₁` (两个读数: $T_0$ 上 $(1+\text{值})\cdot\omega$ 单调; $T_1$ 上 $\omega\cdot(\Omega_1⨾\delta)$ 对 $\delta$ 单调, 用 `rfΩ`).
> - `chain₁`: 链的点 $\delta_n\sqsubseteq\delta'_n$ 且各自自比, 状态 `SRel` 且 `Good`, 底 $\le$, 沿链保持: 每一步用一次 `MonoPort2Sound.snd`, (a) 给读数与状态的值, (b) 给下一个点.
> - 起点 (`gL`, `gR`, `sLR`, `hb`) 都是几行.
> - **`mono₂ : MonoStep (hs (hs hz))`**, **`grow₂₃ : asuc (TΛ 2) ≤ TΛ 3`**, `grow₀₃ : TΛ 0 + 3 ≤ TΛ 3`. 无前提, 不用 `Funext`.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPort2Chain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (subst; sym)
open import OCF.Align.CumReadCF using (A; azero; asuc)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_; z≤; s≤; ≤l; l≤; ≤-refl; ≤-trans; ⊲→≤)
open import OCF.Align.HtFeedTree using (D; hz; hs; hsuc; hself; n0; n1; _⨾_; nl; sum; pt; sum-fst; accL)
open import OCF.Align.HtFeedClosed using (one; TΛ)
open import OCF.Align.MonoPortBridge using (val; smono)
open import OCF.Align.HtCrossInst using (module Hs; b₀)
import OCF.Align.MonoPortStep as St
import OCF.Align.MonoPortOne as One
import OCF.Align.HtCrossVInst as CV
open import OCF.Align.MonoPort2Rel {one} tt
open import OCF.Align.MonoPort2Sound {one} tt using (R₁; snd; Sem₁; rf)

module K = St.Ch (hs hz) tt
```

## §1 动作

```agda
StepA : Act₁
StepA p lW′ z Y′ = P.Step Y′

HA-Step₁ : HA₁ StepA
HA-Step₁ w w′ c c′ Y Y′ g g′ s cb = l≤ (λ n → ≤l n (go n)) , nl⊑ (λ _ → r) (λ _ → r′) (λ _ → ⨾⊑ rfΩ rfΩ rfΩ (proj₂ s))
  where
  δ  = o₀ (P.d Y)
  δ′ = o₀ (P.d Y′)
  r = ⨾⊑ rfΩ rfΩ rfΩ g
  r′ = ⨾⊑ rfΩ rfΩ rfΩ g′
  go : ∀ n → pt c (λ _ → n1 ⨾ δ) n ≤ pt c′ (λ _ → n1 ⨾ δ′) n
  go zero = cb
  go (suc n) = smono {x = n1 ⨾ δ} {x′ = n1 ⨾ δ′} (go n) (smono {b = one} {b′ = one} {x = δ} {x′ = δ′} (≤-refl one) (proj₁ s))
```

## §2 外层链

```agda
CC : P.St one → ℕ → D (hs hz) one × (D (hs hz) one × P.St one)
CC Y = K.CC Y

chain₁ : ∀ (Y Y′ : P.St one) b b′ → Good Y → Good Y′ → SRel Y Y′ → b ≤ b′ → sum b (nl (K.segs Y)) ≤ sum b′ (nl (K.segs Y′))
chain₁ Y Y′ b b′ g g′ s cb = l≤ (λ n → ≤l n (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (go n))))))))
  where
  c  = λ n → proj₁ (CC Y n)
  c′ = λ n → proj₁ (CC Y′ n)
  δ  = λ n → proj₁ (proj₂ (CC Y n))
  δ′ = λ n → proj₁ (proj₂ (CC Y′ n))
  Yn  = λ n → proj₂ (proj₂ (CC Y n))
  Yn′ = λ n → proj₂ (proj₂ (CC Y′ n))
  go : ∀ n → (δ n ⊑ δ′ n) × (Rf (δ n) × (Rf (δ′ n) × (Good (Yn n) × (Good (Yn′ n) ×
             (SRel (Yn n) (Yn′ n) × (pt b (K.segs Y) n ≤ pt b′ (K.segs Y′) n))))))
  go zero = proj₂ s , (g , (g′ , (g , (g′ , (s , cb)))))
  go (suc n) =
    let (hd , (rd , (rd′ , (gy , (gy′ , (sy , gb)))))) = go n
        h = λ e₁ e₂ (eb : e₁ ≤ e₂) → snd hd StepA HA-Step₁ (c n) (c′ n) e₁ e₂ (Yn n) (Yn′ n) gy gy′ sy eb
        r = rf (snd rd) StepA HA-Step₁ (c n) (Yn n) gy
        r′ = rf (snd rd′) StepA HA-Step₁ (c′ n) (Yn′ n) gy′
    in proj₂ (h azero azero z≤) ,
       (r , (r′ , (G⊕ gy r , (G⊕ gy′ r′ , (S⊕ gy gy′ sy (h _ _ (proj₁ sy)) , proj₁ (h _ _ gb))))))
```

## §3 起点

```agda
g0 : Good P.Y₀
g0 = n0⊑

rS : ∀ {Y} → Good Y → Rf (o₁ (P.Step Y))
rS {Y} g = proj₂ (HA-Step₁ n0 n0 azero azero Y Y g g (sr g) z≤)

gL : Good K.Yᴸ
gL = G⊕ {P.Y₀} {P.Step P.Y₀} g0 (rS {P.Y₀} g0)

gR₀ : Good K.Yʳ₀
gR₀ = G⊕0 {K.Yᴸ} gL

gR : Good K.Yʳ
gR = G⊕ {K.Yʳ₀} {P.Step K.Yʳ₀} gR₀ (rS {K.Yʳ₀} gR₀)

sLR : SRel K.Yᴸ K.Yʳ
sLR = ⊲→≤ (sum-fst (vY K.Yʳ₀) (o₀ (P.Step K.Yʳ₀))) ,
      tr (u1ʳ gL) (tr (u1ʳ gR₀) (⨾⊑ gR₀ gR₀ gR₀ n0⊑))

hb : K.bᴸ ≤ K.bʳ
hb = proj₁ (HA-Step₁ n0 n0 one b₀ P.Y₀ K.Yʳ₀ g0 gR₀ (z≤ , n0⊑) (⊲→≤ (sum-fst one (nl (λ _ → n1 ⨾ n0)))))
```

## §4 定理

```agda
chainLe₁ : K.ChainLe
chainLe₁ = chain₁ K.Yᴸ K.Yʳ K.bᴸ K.bʳ gL gR sLR hb

mono₂ : Hs.MonoStep (hs (hs hz)) tt
mono₂ = subst (λ X → X) (sym (K.step≡)) chainLe₁

grow₂₃ : asuc (TΛ (hs (hs hz)) tt) ≤ TΛ (hs (hs (hs hz))) tt
grow₂₃ = CV.HsS.hs-reduce<′ (hs (hs hz)) tt tt mono₂

grow₀₃ : asuc (asuc (asuc (TΛ hz tt))) ≤ TΛ (hs (hs (hs hz))) tt
grow₀₃ = ≤-trans (s≤ One.grow₀₁₂) grow₂₃
```
