# 值序反例: 对接干净对象与读回值序

> 验收文件 (导入闭包读记号), 不进成品; 编译定理, 无前提. (a) [YiVNIdx](YiVNIdx.lagda.md) 的实例 `G₁` 在 `Ωt two` 处的输出就是 `YiUTTwo.output` (`out-eq`), 由此得它的树侧下界 (`output-above`, `output-lower`); 把下标 `Ωt two` 换成值互相 ≼ 的 c′ 后输出 ≼ `ψ₀ᶻ two (Ωt two)` 的 ω 倍 (`swap-upper`).
> (b) 把结论的值序换成读回 `readRW` 后 `OCF.Align.Value` 的 ≼, 下标单调同样推出矛盾 (`no-value-index-monoᴿ`). 无环引理照 `YiNFO.s≼-irrefl` 写.
> 不给出什么: `YiUTTwo.output` 的上界, 以及它与 ψ₀(Ω_{Ω₂}) 的比较; 下界只到 `ψ₀ᶻ G₁.K⁺ (Ωt G₁.K⁺)` (第 3 层), 不涉及记号的值.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVNTwo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiMTTab using (ψ₀ᶻ)
open import OCF.Lean.YiVWVal using (V; val; _≈_; z≼; s≼s; ≼l; l≼; ≼Ω; Ω≼)
import OCF.Lean.YiVWVal as V
open import OCF.Lean.YiVNIdx using (module Gen; module G₁)
import OCF.Lean.YiUTTwo as U
open import OCF.Lean.YiKVRel using (readRW)
import OCF.Align.Level as O
import OCF.Align.Value as AV
```

## (a) 干净对象

```agda
ℓ₂-eq : U.ℓ₂ ≡ G₁.ℓ G₁.ΩK
ℓ₂-eq = refl

out-eq : proj₁ U.output ≡ G₁.out G₁.ΩK
out-eq = cong proj₁ U.raw-output

output-above : zero ⊢ proj₁ (ψ₀ᶻ G₁.K⁺ G₁.oK⁺ (proj₁ (Ωt G₁.K⁺))) ◃ proj₁ U.output
output-above = subst (λ t → zero ⊢ proj₁ (ψ₀ᶻ G₁.K⁺ G₁.oK⁺ (proj₁ (Ωt G₁.K⁺))) ◃ t) (sym out-eq) G₁.st5

output-lower : V.suc G₁.U V.≼ val zero (proj₁ U.output)
output-lower = subst (λ t → V.suc G₁.U V.≼ val zero t) (sym out-eq) G₁.lower

swap-same : val G₁.K G₁.ΩK ≈ val G₁.K G₁.c′
swap-same = G₁.le₁ , G₁.le₂

swap-upper : val zero (G₁.out G₁.c′) V.≼ G₁.U
swap-upper = G₁.upper
```

## (b) 读回值序

`rd` 把第 0 层的树侧值逐构造子读成 `Ordᶜ zero` (第 0 层没有 Ω 槽位); 读回与它互相 ≼, 所以值序的上下界原样搬过去.

```agda
rd : V zero → O.Ordᶜ O.zero
rd V.zero    = O.zero
rd (V.suc v) = O.suc (rd v)
rd (V.lim f) = O.lim (λ n → rd (f n))
rd (V.Ω () h)

rd-mono : {a b : V zero} → a V.≼ b → rd a AV.≼ rd b
rd-mono z≼               = AV.z≼
rd-mono (s≼s d)          = AV.s≼s (rd-mono d)
rd-mono (≼l n d)         = AV.≼l n (rd-mono d)
rd-mono (l≼ h)           = AV.l≼ (λ n → rd-mono (h n))
rd-mono (≼Ω {p = ()} z d)
rd-mono (Ω≼ {p = ()} h)

r→rd : (x : Tr zero) → readRW x AV.≼ rd (val zero x)
r→rd zero          = AV.z≼
r→rd (suc x)       = AV.s≼s (r→rd x)
r→rd (lim f a)     = AV.l≼ (λ n → AV.≼l n (r→rd (f n)))
r→rd (Ω () g)
r→rd (up x () y e)

rd→r : (x : Tr zero) → rd (val zero x) AV.≼ readRW x
rd→r zero          = AV.z≼
rd→r (suc x)       = AV.s≼s (rd→r x)
rd→r (lim f a)     = AV.l≼ (λ n → AV.≼l n (rd→r (f n)))
rd→r (Ω () g)
rd→r (up x () y e)

s≼-irrefl : (a : O.Ordᶜ O.zero) → O.suc a AV.≼ a → ⊥
s≼-irrefl O.zero ()
s≼-irrefl (O.suc a) (AV.s≼s d) = s≼-irrefl a d
s≼-irrefl (O.lim f) (AV.≼l n d) =
  s≼-irrefl (f n) (AV.≼-trans {ℓ₂ = O.zero} (AV.s≼s {ℓ₁ = O.zero} {ℓ₂ = O.zero} (AV.≼l n (AV.≼-refl (f n)))) d)
s≼-irrefl (O.limᵢ () f)
s≼-irrefl (O.up () x)

module R (k : L) (ok : Ok k) where
  open Gen k ok

  IdxMonoᴿ : Set
  IdxMonoᴿ = (t t′ : Tr K) → val K t ≈ val K t′ → readRW (out t) AV.≼ readRW (out t′)

  lowerᴿ : O.suc (rd U) AV.≼ readRW (out ΩK)
  lowerᴿ = AV.≼-trans (rd-mono lower) (rd→r (out ΩK))

  upperᴿ : readRW (out c′) AV.≼ rd U
  upperᴿ = AV.≼-trans (r→rd (out c′)) (rd-mono upper)

  no-value-index-monoᴿ : IdxMonoᴿ → ⊥
  no-value-index-monoᴿ H = s≼-irrefl (rd U) (AV.≼-trans lowerᴿ (AV.≼-trans (H ΩK c′ (le₁ , le₂)) upperᴿ))
```
