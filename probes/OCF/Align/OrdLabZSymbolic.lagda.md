# Symbolic (主线上的切片)

> **验收用, 不在证书的闭包内.** 由 `Survey/scripts/ordlab/mk_rebase.py` 从 [Symbolic](Symbolic.lagda.md) 切出: 只留 `LadderLab*` 标签链的定义级切片里碰到树的块, 代码行逐字, 导入改指主线 `OCF.Free.*`, 与主线重合的块和纯记号块转出. 讲解见原文件. 结论写在 [OrdLab](OrdLab.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.OrdLabZSymbolic where

open import Function using (_∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst) 
open import OCF.BTBO using (module Ord-Ord)
open import OCF.Align.OrdLabZLevel
open import OCF.Align.OrdLabZUniform using (Good; Good-add; Good-ψ⁰; Good-ψ; Good-Ω; Good→HS; ψ⁰-cong; ψ-cong; add-cong; Ω-monoᵒ; idO; zero-l; Uniform)
import OCF.Align.OrdLabZNoCumsum as N
import OCF.Align.EBO as E
open import OCF.Align.OrdLabZCorrespond using (Lab; l0; l1; lω; Lab-≅; βᴱ)
open import OCF.Align.OrdLabZLabel using (BTBO-label; Good-lift)
open import OCF.Align.OrdLabZStage2 using (Ωᵗ; t2; ctx)
open import OCF.Free.Aux public using (Fs; Fst; Mlev)
open import OCF.Align.Symbolic public using (X₂ᵗ)
```

```agda
open Ord-Ord using (iter)
open E using (T; cω; cΩ; cof; fsn; natT; Ωt) renaming (ψ to ψᵗ)
```

## §4 逐步现造的公共层号与上下文链

```agda
record Ctx : Set where
  field
    c  : Ordᴵ
    t₀ : Ordᶜ zero
    E  : (η : Ordᴵ) → c ⊑ᴵ η → Ordᶜ zero
    h₀ : HS t₀
    hE : ∀ η e → HS (E η e)
    d₀ : c ⊑ᴵ toLevel t₀ h₀
    dE : ∀ η e → c ⊑ᴵ toLevel (E η e) (hE η e)
    m₀ : ∀ η e → t₀ ⊑⁰ E η e
    mE : ∀ η e η′ e′ → η ⊑ᴵ η′ → E η e ⊑⁰ E η′ e′

record Pt (C : Ctx) : Set where
  constructor pt
  field
    x  : Ordᶜ zero
    hx : HS x
    dx : Ctx.c C ⊑ᴵ toLevel x hx

module _ (C : Ctx) where
  open Ctx C

  lvP : Pt C → Ordᴵ
  lvP p = toLevel (Pt.x p) (Pt.hx p)

  stepP : Pt C → Pt C
  stepP p = pt (E (lvP p) (Pt.dx p)) (hE _ _) (dE _ _)

  Γᶜ : ℕ → Pt C
  Γᶜ = iter stepP (pt t₀ h₀ d₀)

  χᶜ : ℕ → Ordᶜ zero
  χᶜ n = Pt.x (Γᶜ n)

  χᶜ-step : ∀ n → χᶜ n ⊑⁰ χᶜ (suc n)
  χᶜ-step zero    = m₀ _ _
  χᶜ-step (suc n) = mE _ _ _ _ (toLevel-⊑ (Pt.hx (Γᶜ n)) (Pt.hx (Γᶜ (suc n))) (χᶜ-step n))
```

## §7 检验 2: Stage2 的失败点与它的下一层

```agda
σ1 : ∀ {L} → zero <ᴵ L → Simᴵ (suc zero) L
σ1 z zero    = z
σ1 z (suc ())
```

## §12 结论与边界
