# 判决的规格: 帧塔在 $\psi_{\Omega+1}$ 上被拒绝 (底座)

> 底座, 文本不含记号. 结论写在 [VerdictSpec](VerdictSpec.lagda.md). `Tᶰ` 是 [Uniform4Expt](Uniform4Expt.lagda.md) 的朴素帧 (定义逐字抄来, 这里不导入那个文件; 但 `Uniform3Base` 的导入链经过 `Prefix` 到记号模块, 所以定义切片是 0, 模块层面不是).
>
> **`frame-rejected`.** 帧塔的 $\psi_0(\psi_{\Omega+1}(\Omega_{\Omega+1}))$ 与 `PF` 按折叠方程算出的树, 在路径 $[1,0,0,1,0,0,0]$ 上头不同, **对一切 `S`**. `S` 是变量而证明是 `()`, 所以这段计算里 `S` 没有被问到: 拒绝帧塔的是折叠方程, 不是判决. 帧塔的错不在任何比较.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.VerdictSpecFrame where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import OCF.Align.Level using (Ordᴵ; suc; zero)
open import OCF.Align.Prefix using (Ordˢ; walkˢ; kind; Kind; kz; ks; kl; kc; kĉ)
open import OCF.Align.Uniform3Base using (Sym; ∅ᵀ; ψᵀ; Flr; fz; fk; _⊔_; A)
open import OCF.Align.Uniform3OmegaPlus1 using (module OmegaPlus)
open OmegaPlus using (Ω⁺)

import OCF.Align.InaccTreeBase as B
open B using (Lv; Ordᴸ; toLv; Tree; Ω)
open import OCF.Align.InaccFloorTree using (Sib; fin; bel; natL; module PF)
open import OCF.Align.VerdictSpecReject using (H; hz; hs; hl; hd)
```

## §1 帧塔

```agda
Bᶰ : ∀ d → A (suc d) (fz ⊔ fk zero)
Bᶰ d = Ω⁺ ∅ᵀ d

Ψ₁ᶰ : ∀ {φ} → Sym φ → Sym ((fz ⊔ fk zero) ⊔ φ)
Ψ₁ᶰ Y d P = Y (suc d) (Bᶰ d) P

one : Ordᴵ
one = suc zero

Tᶰ : Ordˢ zero
Tᶰ = ψᵀ (Ψ₁ᶰ (Ψ₁ᶰ ∅ᵀ)) {i = zero} {ℓ = one} (tt , ((tt , (λ q → q)) , ((tt , (λ q → q)) , tt))) zero

hF : Kind → H
hF kz     = hz
hF ks     = hs
hF kl     = hl
hF (kc _) = hl
hF kĉ     = hl
```

## §2 折叠方程给的树

`sq`, `pw` 与 `Prefix.walkˢ` 同形: 在非极限处停在原地. `walkˢ` 在闭包节点上只走第 0 个孩子, 这条路径上闭包节点的孩子都是第 0 个.

```agda
sq : Ordᴸ Lv.zero → ℕ → Ordᴸ Lv.zero
sq (Tree.lim f) n = f n
sq x            n = x

pw : List ℕ → Ordᴸ Lv.zero → Ordᴸ Lv.zero
pw []      x = x
pw (n ∷ p) x = pw p (sq x n)

fp : List ℕ
fp = 1 ∷ 0 ∷ 0 ∷ 1 ∷ 0 ∷ 0 ∷ 0 ∷ []

module Spec (S : Sib) where
  open PF S

  LΩ⁺ : Lv
  LΩ⁺ = Lv.suc (toLv (Ω (natL 1)))

  -- ψ_{Ω+1}(Ω_{Ω+1})
  x₁ : Ordᴸ LΩ⁺
  x₁ = ψᵖ (bel (λ r → r , refl)) (Ω LΩ⁺)

  Tˢ : Ordᴸ Lv.zero
  Tˢ = ψᵖ (fin 0 refl) x₁

  frame-rejected : hF (kind (walkˢ Tᶰ fp)) ≢ hd (pw fp Tˢ)
  frame-rejected ()
```
