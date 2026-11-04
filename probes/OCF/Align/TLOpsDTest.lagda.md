# 动态高度: 有限测试

> 入口 [TLOps](TLOps.lagda.md). **有限测试, 不是证明.** `refl` 只看数据树头部的构造子. 盲区: 不看世界, 不看值, 不算证书, [TLOpsDW](TLOpsDW.lagda.md) 上没有证书. 只说明 $\psi_0(\Omega_{\Omega^2})$, $\psi_0(\Omega_{\Omega^2+1})$ 的数据写得出来, 算得动.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLOpsDTest where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.CumReadCF using (A; azero; asuc; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLOpsDW

data Sh : Set where
  s0 ss sl si sd sc se sL sw : Sh

sh : ∀ {p a u} → 𝓞 p a u → Sh
sh o0 = s0
sh (os _) = ss
sh (ol _) = sl
sh (oi _ _) = si
sh (od _ _ _ _) = sd
sh (oc _ _) = sc
sh (oe _ _) = se
sh (oL _ _ _ _) = sL
sh (ow _ _ _) = sw

Ω² : H
Ω² = hh one azero

-- Ω̇: 第 0 行是闭包, 后继是 Ω-极限
_ : sh (Ω̇ Ω² azero) ≡ sc
_ = refl

_ : sh (Ω̇ Ω² one) ≡ si
_ = refl

-- ψ₀(Ω_{Ω²}), ψ₀(Ω_{Ω²+1}): 闭项
T² T²⁺¹ : 𝓞 hz azero one
T² = Tᴰ Ω² azero one tt g₀ (z⊲ one , z⊲ one)
T²⁺¹ = Tᴰ Ω² one one tt g₀ (z⊲ one , C.self)

_ : sh T² ≡ sw
_ = refl

_ : sh T²⁺¹ ≡ sw
_ = refl
```
