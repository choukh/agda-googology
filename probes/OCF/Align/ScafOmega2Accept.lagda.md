# 脚手架 (五): 站点形状的树, 有限检查

> **验收节, 有限测试, 不是证明.** 结论写在 [ScafOmega2](ScafOmega2.lagda.md). 这里直接写出 $\psi_0(\psi_\Omega(\psi_\tau(\Omega_\Omega)))$ 的树 `Sτ`, 不经过走路径, 第 0 层上是字面闭包 `ĉᴸ c`. 比较器是 [Uniform4TwoWalk](Uniform4TwoWalk.lagda.md) 的 `firstBad`, 只比种类, 闭包只走第 0 个孩子. [ScafOmega2Site](ScafOmega2Site.lagda.md) 的 `site-label` 才是定理; 本文只确认那个定理说的站点与 `node`, `through` 说的节点形状相符.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafOmega2Accept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Align.Level
open import OCF.Align.Prefix using (Ordˢ; Ord₊ˢ; toZ)
open import OCF.Align.Uniform3Base using (Ev; fk; flo; cvFlo; _⊔_; ψ₀ᵗ; bound; Bd)
open import OCF.Align.Uniform4Base using (Fl)
open import OCF.Align.Uniform4Two using (ψᵒ; ψ̄; tl; Ω̇)
open import OCF.Align.Uniform4TwoWalk using (firstBad)
open import OCF.Align.ScafOmega2Family using (ω⁺)
open import OCF.Align.ScafOmega2Node using (ℓ₀; ev₀)
open import OCF.Align.ScafOmega2Site using (site; site₀; ψᵤ; Ω₁ᵗ; ΩΩᵗ; ω+1ᵗ; ωᵗ)
import OCF.Align.EBO as E
open E using (T; natT; sucT)

x₂ : Ordˢ ω⁺
x₂ = ψ̄ (Ω̇ zero) ev₀ zero

ℓ₁ : Ordᴵ
ℓ₁ = suc ω⁺

evS : Ev ℓ₁ (Fl ⊔ flo ω⁺)
evS = ev₀ , (λ q → suc q)

Sτ : Ordˢ zero
Sτ = ψ̄ (ψᵒ {α = suc zero} zero (tl {c = suc zero} (flo ω⁺) (cvFlo ω⁺) x₂)) evS (suc (suc (lim 1 zero)))

-- 与站点一致, 种类, 深 5
agree-site : firstBad 5 Sτ site ≡ []
agree-site = refl
```

```agda
open import OCF.Align.Prefix using (kind; kc)
open import OCF.Align.ScafOmega2Node using (module Node)

-- 站点的第 0 层节点是字面闭包, 界就是 ψ_{ω+1}(Ω_Ω) 的 c: 穿过 ψ_Ω, ψ₀ 不变 (`refl`)
head-c : kind Sτ ≡ kc (Node.c ev₀ zero)
head-c = refl

deep : firstBad 7 Sτ site ≡ []
deep = refl

-- 对照: 换成 3, 比较器报告不一致
ctl : firstBad 3 Sτ (natT 3) ≡ ([] ∷ [])
ctl = refl
```
