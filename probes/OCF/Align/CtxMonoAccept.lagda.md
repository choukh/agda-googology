# 验收: 带上下文的层单调, 参照树与剩下的前提

> **验收文件.** 读 `OCF.Free.Lab`, `BTBOᴵ`. 结论写在 [CtxMono](CtxMono.lagda.md).
>
> - `Ref`: `OCF.Free` 的 $\psi_0(\Omega_{\Omega+1})$ (`GᴺΩ̇ 1`), `label-Ref` 是它的标签 (同 `GuardCertAccept.label-Ω+1` 的来源).
> - `term0`: `NoCumNode` 的第 0 项对任何证书 $\cong$ `BTBOᴵ`. 基本列第 0 项没有毛刺 (相对过基本列验收的 $\psi_0(\Omega_\Omega)$).
> - `accept-Ω+1`: 两个前提给序数值验收. 前提都没有证.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CtxMonoAccept where

open import Data.Nat using (ℕ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.Level using (_≅_)
open import OCF.Align.Value using (_≼_; _≈ᵛ_)
import OCF.Align.NoCumsum as N
open N using (BTBOᴵ)
open import OCF.Free.Level using (suc; zero; hs; hz; s≅; z≅)
open import OCF.Free.Force using (forceᴺ)
open import OCF.Free.Main using (GᴺΩ̇)
open import OCF.Free.Lab.Correspond using (Lab; l0; l1)
open import OCF.Free.Lab.Uniform3Base using (ψ₀ᵗ)
open import OCF.Free.Lab.GoodLBase using (nf1)
open import OCF.Free.Lab.Uniform5Label using (Ωs₊)
open import OCF.Free.Lab.UniformNF5Accept using (module AΩ̇)
open import OCF.Align.EBO using (natT)
open import OCF.Align.GuardCertMain using (ev₀)
open import OCF.Align.CumUpAcceptSim using (fr)
open import OCF.Align.CumReadCF using (azero)
import OCF.Align.CumReadCF as C
open import OCF.Align.NoCumW
open import OCF.Align.NoCumNodeE
open import OCF.Align.NoCumNodeMain using (G₁; T₁)
open import OCF.Align.NoCumNodeAccept using (anyΩ)
open import OCF.Align.CtxMono using (tm; accept-if)
```

## §1 参照树

```agda
Ref = forceᴺ _ (GᴺΩ̇ (suc zero) ev₀ zero)

lab₁ : Lab (suc zero) (natT 1)
lab₁ = l1 refl (s≅ z≅) (l0 refl z≅)

label-Ref : Lab Ref (ψ₀ᵗ (Ωs₊ (natT 1)))
label-Ref = AΩ̇.label-Ω̇ (suc zero) (hs hz) lab₁ nf1 (s≅ z≅) ev₀ zero
```

## §2 第 0 项

```agda
term0 : ∀ {m gm um am} (d : E (Ω̇ 1 one) g₀ m gm um am) → fr (tm {m} {gm} {um} {am} d 0) ≅ BTBOᴵ
term0 {m} {gm} {um} {am} (rg nz Es st) = anyΩ {Mx.m M₂} {Mx.gm M₂} {Mx.um M₂} {Mx.am M₂} (Es 0)
  where
  M₁ = Mz gm gm C.self (C.⊲-tr (C.suc C.self) am)
  M₂ = Mz g₀ (Mx.gm M₁) (C.⊲-tr (pos gm) (Mx.um M₁)) (Mx.am M₁)
term0 (rv () vz Es tS st)
```

## §3 剩下的两个前提

`Up`: 逐项上界, 就是 "带上下文的层单调" 的实例. `Lo`: 参照树压在 `T₁` 之下. 两条都没有证.

```agda
M₀ = Mz g₀ g₀ C.self C.self

Up : Set
Up = ∀ n → fr (tm {Mx.m M₀} {Mx.gm M₀} {Mx.um M₀} {Mx.am M₀} G₁ n) ≼ fr Ref

Lo : Set
Lo = fr Ref ≼ fr T₁

accept-Ω+1 : Up → Lo → fr T₁ ≈ᵛ fr Ref
accept-Ω+1 u l = accept-if {Mx.m M₀} {Mx.gm M₀} {Mx.um M₀} {Mx.am M₀} G₁ u l
```
