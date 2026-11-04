# 验收: $\psi_0(\Omega_{\Omega+1})$ 的标签, 与有限测试

> **验收节: 只有本文件读记号, 塔, 带记号的测试.** 结论写在 [GuardCert](GuardCert.lagda.md).
>
> - `label-Ω+1`: **定理.** `T₀ʷ` 的证书的计值带标签 $\psi_0(\Omega_{\Omega+1})$. 由 `value-Ω+1` 与主线已有的 `label-Ω̇` 得到. 标签不进证书, 这是验收.
> - `fgh-agree`: FGH 与主线的树逐点相等 (定理, 不读记号, 放这里是因为跟着标签).
> - `same-u11`: 这棵树就是 [GuardWeakAccept](GuardWeakAccept.lagda.md) 测过的 `u11` (`refl`).
> - `s₁`, `s₂`: 形状的有限测试, 说明不是退化的树.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.GuardCertAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z)
open import OCF.Free.Force using (Goodᴺ; forceᴺ)
open import OCF.Free.Main using (GᴺΩ̇)
open import OCF.Free.Lab.Correspond using (Lab; Lab-≅; l0; l1)
open import OCF.Free.Lab.Uniform3Base using (ψ₀ᵗ)
open import OCF.Free.Lab.GoodLBase using (nf1)
open import OCF.Free.Lab.Uniform5Label using (Ωs₊)
open import OCF.Free.Lab.UniformNF5Accept using (module AΩ̇)
open import OCF.Align.EBO using (natT)
open import OCF.Align.GuardWeakAccept using (u11)
open import OCF.Align.GuardWeakTree using (T₀ʷ)
open import OCF.Align.GuardCertHi using (cT; tcʷ)
open import OCF.Align.GuardTightCert using (wf₁; sf₁)
open import OCF.Align.GuardTightLv using (module Lv; Dom₀)
open Lv Dom₀ using (s≈)
open import OCF.Align.GuardCertMain using (Good-Ω+1; value-Ω+1; ev₀; ≲-Ω+1)

lab₁ : Lab (suc zero) (natT 1)
lab₁ = l1 refl (s≅ z≅) (l0 refl z≅)

label-Ω+1 : Lab (forceᴺ _ Good-Ω+1) (ψ₀ᵗ (Ωs₊ (natT 1)))
label-Ω+1 = Lab-≅ value-Ω+1 (AΩ̇.label-Ω̇ (suc zero) (hs hz) lab₁ nf1 (s≅ z≅) ev₀ zero)

fgh-agree : ∀ n → FGH (forceᴺ _ Good-Ω+1) n ≡ FGH (forceᴺ _ (GᴺΩ̇ (suc zero) ev₀ zero)) n
fgh-agree = FGH-≅ value-Ω+1

same-u11 : T₀ʷ cT (wf₁ , s≈ sf₁) tcʷ ≡ u11
same-u11 = refl

data Sh : Set where
  sz ss sl : Sh

sh : Ordᶜ zero → Sh
sh zero = sz
sh (suc _) = ss
sh (lim _) = sl
sh (limᵢ () _)
sh (up () _)

s₁ : sh (forceᴺ _ Good-Ω+1) ≡ sl
s₁ = refl
```
