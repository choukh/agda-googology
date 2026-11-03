# 终局 (五): 验收. 塔的前几项与 EBO, 有限检查

> **验收节.** 记号只在本文件. 结论写在 [EBOTop](EBOTop.lagda.md). 全部是**有限检查** (宽度、深度、路径都是有限的), 不是定理. `S` 是变量的检查说明路径上没有问到 `S`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.EBOTopAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)

open import OCF.Align.InaccTreeBase using (Lv; Ordᴸ; rise; zero; suc; Tree)
open import OCF.Align.InaccFloorTree using (Sib)
open import OCF.Align.EBOTopRaw hiding (natT)
import OCF.Align.EBO as E
open E using (fsn; Ωt; natT; sucT) renaming (T to Tm; ψ to ψᵗ)
open import OCF.Align.InaccTreeAccept using (diff; walkB)
open import OCF.Align.Stage2 using (Ωᵗ)
open import OCF.Align.Uniform5Wall using (p₁; p₂; W)
open import OCF.Align.StandardOmega using (walk)
open import OCF.Align.EBOTopLow using (instᶜ)
import OCF.Align.EBOTopLow as Low
import OCF.Align.Level as L
open import OCF.Align.Diagonal using (module Diagonal)
import OCF.Align.EBOTopStage as St
open St using (Stage; O₀; module Top)
import OCF.Align.EBOI as I
```

## §1 $x_n$ 就是 `EBOψ n`

```agda
ψ₀t : Tm → Tm
ψ₀t a = ψᵗ [] a ∷ []

module AllS (S : Sib) where
  open Raw S

  e0 : diff 6 3 (E.EBOψ 0) (x 0) ≡ nothing
  e0 = refl
  e1 : diff 6 3 (E.EBOψ 1) (x 1) ≡ nothing
  e1 = refl
  e2 : diff 6 3 (E.EBOψ 2) (x 2) ≡ nothing
  e2 = refl
  e3 : diff 5 2 (E.EBOψ 3) (x 3) ≡ nothing
  e3 = refl
  e4 : diff 5 2 (E.EBOψ 4) (x 4) ≡ nothing
  e4 = refl
```

## §2 $x_3$ 里字面地有 $\psi_k$, 对 $k=1,2,\omega$

项与树同时走. 与 `EBOTopRaw` 的 `reach-*` 同路径.

```agda
  tmAt : List ℕ → Tm
  tmAt q = proj₁ (walkB q (E.EBOψ 3) (x 3))

  trAt : List ℕ → Ordᴸ zero
  trAt q = proj₂ (walkB q (E.EBOψ 3) (x 3))

  ψ[_] : Tm → Tm → Tm
  ψ[ u ] a = ψᵗ u a ∷ []

  ωt : Tm
  ωt = ψ₀t (natT 1)

  -- 到第 3 项里的 ψ₀(Ω_{Ω_2})
  n4 : tmAt (1 ∷ 0 ∷ 0 ∷ 2 ∷ []) ≡ ψ₀t (Ωt (Ωt (natT 2)))
  n4 = refl
  n4ᵀ : trAt (1 ∷ 0 ∷ 0 ∷ 2 ∷ []) ≡ T₁ (St′ 1)
  n4ᵀ = refl

  -- 第 5 站: ψ₁ 第一次出现
  n5 : tmAt (1 ∷ 0 ∷ 0 ∷ 2 ∷ 1 ∷ []) ≡ ψ₀t (Ωt (ψ[ natT 1 ] (Ωt (Ωt (natT 1)))))
  n5 = refl

  -- ψ₂
  n6 : tmAt (1 ∷ 0 ∷ 0 ∷ 3 ∷ 1 ∷ []) ≡ ψ₀t (Ωt (ψ[ natT 2 ] (Ωt (Ωt (natT 2)))))
  n6 = refl

  -- ψ_ω
  n7 : tmAt (1 ∷ 0 ∷ 1 ∷ 2 ∷ 2 ∷ 1 ∷ []) ≡ ψ₀t (Ωt (Ωt (sucT ωt)))
  n7 = refl
  n7ᵀ : trAt (1 ∷ 0 ∷ 1 ∷ 2 ∷ 2 ∷ 1 ∷ []) ≡ T₁ (suc ω′)
  n7ᵀ = refl

  n8 : tmAt (1 ∷ 0 ∷ 1 ∷ 2 ∷ 2 ∷ 1 ∷ 1 ∷ []) ≡ ψ₀t (Ωt (ψ[ ωt ] (Ωt (Ωt ωt))))
  n8 = refl

  -- 这些站点上树与项一致 (S 为变量)
  c4 : diff 3 2 (tmAt (1 ∷ 0 ∷ 0 ∷ 2 ∷ [])) (trAt (1 ∷ 0 ∷ 0 ∷ 2 ∷ [])) ≡ nothing
  c4 = refl
```

$W$ ([Uniform5Wall](Uniform5Wall.lagda.md)) 也在 $x_3$ 之下: 目标是不可数的 $\Omega\cdot2$, $\Omega+1$. 所以目标不只自然数与可数序数. 这一步只走记号 (树的路径上要问 `S`, 见 [InaccFloorAccept](InaccFloorAccept.lagda.md)).

```agda
  reach-W : walk (E.EBOψ 3) (p₁ ++ p₂) ≡ W
  reach-W = refl
```

## §3 闭项本身与 $\psi_0(\Lambda)$

`EBOᵀ` 就是 `lim x` (`refl`, 无条件), 第 $n$ 项对应 `EBOψ n` (§1, 有限检查). `ψ₀Λ-tower` 是 [EBOI](EBOI.lagda.md) 的定理: $\psi_0(\Lambda)[n]$ 是 `EBOψ n`. 两者合起来: **闭项的基本列的形状与 $\psi_0(\Lambda)$ 对得上, 有限深度内每一项也对得上; 这不是 `Lab`.**

```agda
  fs-top : I.fsn (I.ψ [] I.Λ ∷ []) 3 ≡ I.ιT (E.EBOψ 3)
  fs-top = I.ψ₀Λ-tower 3

  top-lim : EBOᵀ ≡ Tree.lim x
  top-lim = refl
```

## §4 低端实例的闭项对 $\psi_0(\Omega_\Omega)$

`Top.EBOᵀ instᶜ` 是通用定义在低端实例上的值. 它的第 $n$ 项对 `fsn (EBOψ 2) n`. 比较器重写到 `O₀`. 标签定理是 [Label](Label.lagda.md), 这里只是核对通用定义确实落到了那棵树上.

```agda
diff₀  : ℕ → ℕ → Tm → O₀ → Maybe (List ℕ)
diffs₀ : ℕ → ℕ → ℕ → Tm → (ℕ → O₀) → Maybe (List ℕ)
diff₀ zero w t x = nothing
diff₀ (suc d) w t x with E.cof t | x
... | E.c0 | O₀.zero  = nothing
... | E.c1 | O₀.suc a = diff₀ d w (E.pred t) a
... | E.cω | O₀.lim f = diffs₀ w d w t f
... | _    | _        = just []
diffs₀ zero d w t f = nothing
diffs₀ (suc n) d w t f with diff₀ d w (fsn t n) (f n)
... | just p  = just (n ∷ p)
... | nothing = diffs₀ n d w t f

low-ok : diff₀ 6 3 (E.EBOψ 2) (Top.EBOᵀ instᶜ) ≡ nothing
low-ok = refl

-- 通用的闭项就是 Diagonal 的 BTBOᴵ (定理, 不是有限检查)
module Same (Uni : ∀ a → L.HS (L.ψ⁰ (L.Ω a))) where
  open Low.Low Uni using (inst; nx; Lᴸ)
  open Diagonal Uni using (BTBOᴵ) renaming (L to Lᴰ)

  L-same : ∀ n → Lᴸ n ≡ Lᴰ n
  L-same zero    = refl
  L-same (suc n) = cong nx (L-same n)

  EBOᵀ≅BTBO : Top.EBOᵀ inst St.≅⁰ Low.rd BTBOᴵ
  EBOᵀ≅BTBO = St.l≅ λ n → subst (λ ℓ → Low.rd (L.ψ⁰ (L.Ω (Lᴸ n))) St.≅⁰ Low.rd (L.ψ⁰ (L.Ω ℓ))) (L-same n) (St.≅⁰-refl _)
```
