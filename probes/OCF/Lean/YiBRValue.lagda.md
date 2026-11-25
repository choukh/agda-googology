# 新旧块的逐层关系: 值搬到精简块

> 验收文件. 编译定理, 无前提: 精简块第 0 层的读回 `readRW`; 相关的第 0 层树读回 `≅` (`rel≅`, 对 `YiMEBase` 的同文读回 `rel≅ᴹ`), 所以两块的闭项读回 `≅` (`same-tw`, `same-EBO`); 由此 F2 的值定理搬到精简块: `btbo-tw1ᴿ`, `btbo-EBOᴿ`, `btbo-twᴿ`, `bho-lowerᴿ`.
> 只是下界的搬运, 不涉及上界. F2 一侧的定理原样引用 (`YiLSBtbo`, `YiEBBtbo`, `YiT2Mono`, `YiMEAnchor`).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiBRValue where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (proj₁; _,_)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWFold
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRTw using (twᶜ-R; EBOᶜ-R; two; Ok-two; two-R)
open import OCF.Lean.YiLSRead using (read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Lean.YiLSBtbo using (btbo-tw1)
open import OCF.Lean.YiEBBtbo using (btbo-EBO)
open import OCF.Lean.YiT2Mono using (btbo-tw)
open import OCF.Lean.YiMEAnchor using (bho-lowerᴹ; t₂)
open import OCF.Lean.YiMEBase using (Rt)
import OCF.Lean.YiMEBase as ME
import OCF.Align.EboLeanDef as E
```

## 第 0 层的读回

```agda
readRW : Tr zero → L.Ordᶜ L.zero
readRW zero      = L.zero
readRW (suc x)   = L.suc (readRW x)
readRW (lim f _) = L.lim (λ n → readRW (f n))

rel≅ : {x : Tr zero} {x′ : F.Tr F.zero} → RelT zero F.zero x x′ → readRW x L.≅ read x′
rel≅ {x = zero}    iz             = L.z≅
rel≅ {x = suc x}   (is r)         = L.s≅ (rel≅ r)
rel≅ {x = lim f a} (il (rf , _))  = L.l≅ (λ n → rel≅ (rf n))

-- `YiMEBase` 另有一个同文的读回
rel≅ᴹ : {x : Tr zero} {x′ : F.Tr F.zero} → RelT zero F.zero x x′ → readRW x L.≅ ME.read x′
rel≅ᴹ {x = zero}    iz             = L.z≅
rel≅ᴹ {x = suc x}   (is r)         = L.s≅ (rel≅ᴹ r)
rel≅ᴹ {x = lim f a} (il (rf , _))  = L.l≅ (λ n → rel≅ᴹ (rf n))

same-tw : (n : ℕ) → readRW (twᶜ n) L.≅ read (F.twᶜ n)
same-tw n = rel≅ (twᶜ-R n)

same-EBO : readRW EBOᶜ L.≅ read F.EBOᶜ
same-EBO = rel≅ EBOᶜ-R
```

## 搬值

```agda
up≼ : ∀ {Y : L.Ordᶜ L.zero} {x : Tr zero} {x′ : F.Tr F.zero} → RelT zero F.zero x x′ → Y ≼ read x′ → Y ≼ readRW x
up≼ r q = ≼-trans q (≅→≼ (L.≅-sym (rel≅ r)))

btbo-tw1ᴿ : D.BTBOᴵ ≼ readRW (twᶜ 1)
btbo-tw1ᴿ = up≼ (twᶜ-R 1) btbo-tw1

btbo-EBOᴿ : D.BTBOᴵ ≼ readRW EBOᶜ
btbo-EBOᴿ = up≼ EBOᶜ-R btbo-EBO

btbo-twᴿ : (n : ℕ) → D.BTBOᴵ ≼ readRW (twᶜ (suc n))
btbo-twᴿ n = up≼ (twᶜ-R (suc n)) (btbo-tw n)

bho-lowerᴿ : (h : E.HC t₂) → Rt h ≼ readRW (proj₁ (ψ₀ two Ok-two (proj₁ (Ωt two))))
bho-lowerᴿ h = ≼-trans (bho-lowerᴹ h) (≅→≼ (L.≅-sym (rel≅ᴹ two-R)))
```
