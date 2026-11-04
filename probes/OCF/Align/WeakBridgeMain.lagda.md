# 不带高度的树接上带高度的树 (七): 证书, 对一切 $\theta$

> 不含记号. 结论写在 [WeakBridge](WeakBridge.lagda.md). `≲-θ θ`: `T₀ʷ` 在 $\psi_0(\Omega_{\Omega+\theta})$ 上的界不高于 [LadderInfTree](LadderInfTree.lagda.md) 实例 ℕ 高度 0 的树. `Good-θ θ`: 经 `Good-≲` 把 [LadderInfMain](LadderInfMain.lagda.md) 的 `GᴺTᵠ 0 θ` 搬过来. `value-θ`: 计值 $\cong$. 对一切 $\theta$, 无模块参数作假设.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WeakBridgeMain where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; toZ)
open import OCF.Free.Floor using (Ev)
open import OCF.Free.Force using (Goodᴺ; forceᴺ)
import OCF.Free.Tree as FT
open import OCF.Align.GuardBridgeZ using (_≲ᶻ_; Good-≲)
open import OCF.Align.GuardTightLv
open Lv Dom₀ using (∅)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.GuardCertHi using (cT; tcʷ)
open import OCF.Align.GuardTightCert using (wf₁; sf₁)
open import OCF.Align.GuardWeakTree using (T₀ʷ; module FoldW)
open import OCF.Align.GuardCertRel using (Rz)
open import OCF.Align.LadderInfNat using (HSℕ)
import OCF.Align.LadderInfMain
module IM = OCF.Align.LadderInfMain HSℕ
open import OCF.Align.WeakBridgeBase
open import OCF.Align.WeakBridgeRel using (module I)
open import OCF.Align.WeakBridgeEmb using (RΩ̇⁺)
import OCF.Align.WeakBridgeSel as WS
import OCF.Align.WeakBridgeFold as WF

ev₀ : Ev (suc zero) FT.Fl
ev₀ = tt , (λ q → q)

T⁺ : Ordᴵ → Z
T⁺ θ = T₀ʷ (c⁺ θ) (cf⁺ θ) (tc⁺ θ)

R⁺ : Ordᴵ → Z
R⁺ θ = toZ (I.Tᵠ 0 θ ev₀ zero)

≲-θ : ∀ θ → T⁺ θ ≲ᶻ R⁺ θ
≲-θ θ = Rz (WF.R-ψ θ I.ok₀ (λ i h r → I.ok₀ i) (∅ zero) (FoldW.t0) (WS.tg0) (λ ()) (λ ()) (λ ()) (RΩ̇⁺ (≅ᴵ-refl θ)) ev₀ zero)

Good-θ : ∀ θ → Goodᴺ (T⁺ θ)
Good-θ θ = proj₁ (Good-≲ (≲-θ θ) (IM.GᴺTᵠ 0 θ ev₀ zero))

value-θ : ∀ θ → forceᴺ _ (Good-θ θ) ≅ forceᴺ _ (IM.GᴺTᵠ 0 θ ev₀ zero)
value-θ θ = proj₂ (Good-≲ (≲-θ θ) (IM.GᴺTᵠ 0 θ ev₀ zero))
```

## 闭项与 FGH

`Good-Ω+2`, `Good-Ω+ω`: 闭项. `fgh`: 树上的 FGH, 与对面逐点相等 (`fgh-agree`). `same-Ω+1`: $\theta=1$ 就是 [GuardCertMain](GuardCertMain.lagda.md) 的那棵树.

```agda
Good-Ω+2 : Goodᴺ (T⁺ (suc (suc zero)))
Good-Ω+2 = Good-θ (suc (suc zero))

Good-Ω+ω : Goodᴺ (T⁺ ωᴵ)
Good-Ω+ω = Good-θ ωᴵ

Good-Ω+ω+1 : Goodᴺ (T⁺ (suc ωᴵ))
Good-Ω+ω+1 = Good-θ (suc ωᴵ)

fgh : Ordᴵ → ℕ → ℕ
fgh θ = FGH (forceᴺ (T⁺ θ) (Good-θ θ))

fgh-agree : ∀ θ n → fgh θ n ≡ FGH (forceᴺ _ (IM.GᴺTᵠ 0 θ ev₀ zero)) n
fgh-agree θ = FGH-≅ (value-θ θ)

same-Ω+1 : T⁺ (suc zero) ≡ T₀ʷ cT (wf₁ , Lv.s≈ sf₁) tcʷ
same-Ω+1 = refl
```
