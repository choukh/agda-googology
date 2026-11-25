# 抽象理论 (十): 带条件的第 0 层出口

> 判决: 编译定理, 无前提; 只导入标准库与 `YiAbs*`. `YiAbsGSuff.Suff.Tower` 的改写: 第 0 层的 `Base` 记录换成带条件的出口 `Exit₀` (条件放在关系的证明上), 龙骨不再带 `g₀` (`Keel⁻`). 龙骨每行只折一次 (`folded`), 所以出口的条件只要在这一次的证明上成立 (`ex`); 结论与原来相同 (`K`, `endpoint`).
> 用途: 封闭的关系上出口只对标准形的见证项成立 ([YiDCExit](YiDCExit.lagda.md) `exitᴰ`), 填不出 `Base` 记录; 实例在 [YiExInst](YiExInst.lagda.md).
> 不给出什么: 不构造关系, 不填 `Leaf`, `Lift`, `LowKeep`; 不说明 `ex` 在塔上可满足.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}

module OCF.Lean.YiExSuff where

open import Data.Nat using (ℕ; zero; suc)

open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
open import OCF.Lean.YiAbsGIface

module ExSuff {𝔹 : Block} {𝔽 : Fold 𝔹} {ℜ : Rows 𝔹 𝔽} {𝕋 : Ref} {𝕍 : Val}
              (𝔾 : Graded 𝔹 𝔽 ℜ 𝕋 𝕍) (𝔻 : Doms 𝔹 𝔽) where
  open Laws 𝔾 𝔻

  record Exit₀ : Set₁ where
    field
      Ex   : ∀ {t x} → R ℓ₀ t x → Set
      exit : ∀ {t x} (r : R ℓ₀ t x) → Ex r → (h : HC t) → tree h ≼ v x
```

`Keel⁻` 是 `YiAbsGIface.Keel` 去掉 `g₀` 一项 (那一项只给 `Base` 用).

```agda
  record Keel⁻ : Set where
    field
      tw      : ℕ → Lv
      κ₀      : T
      rd-tw0  : Rd (tw 0) κ₀
      tw-step : ∀ n {ν} → Rd (lift (tw n) (Ωt (tw n))) ν → Rd (tw (suc n)) ν
      gl      : ∀ n → Gl (tw n) (Ωt (tw n))
      b₀      : ∀ n → Bs (tw n)
      w₀      : ∀ n → ℓ₀ ⊑ tw n
      β₀      : ∀ n → Bt ℓ₀
      K₀      : ∀ n → Cx (tw n) ℓ₀
      gb      : ∀ n → Gb (tw n) (b₀ n)
      wl      : ∀ n → Wl (w₀ n)
      bd      : ∀ n → Bd (b₀ n) (w₀ n) (β₀ n) (K₀ n)
      gx      : ∀ n → Gx (tw n) (Ωt (tw n))

    kt : ℕ → T
    kt zero    = κ₀
    kt (suc n) = Ωr (kt n)

    twc : ℕ → Tr ℓ₀
    twc n = ψ (tw n) (b₀ n) ℓ₀ (w₀ n) (β₀ n) (Ωt (tw n))

    row : ℕ → T
    row n = app (K₀ n) (Ωr (kt n))

  module TowerE (lf : Leaf) (li : Lift) (𝔨 : Keel⁻) where
    open Keel⁻ 𝔨

    keel : ∀ n → Rd (tw n) (kt n)
    keel zero    = rd-tw0
    keel (suc n) = tw-step n (li (gl n) (lf (keel n)))

    keelᴿ : ∀ n → R (tw n) (Ωr (kt n)) (Ωt (tw n))
    keelᴿ n = lf (keel n)

    folded : LowKeep → ∀ n → R ℓ₀ (row n) (twc n)
    folded L n = L (b₀ n) (w₀ n) (β₀ n) (K₀ n) (gb n) (wl n) (bd n) (gx n) (keelᴿ n)

    module _ (L : LowKeep) (𝔢 : Exit₀) (ex : ∀ n → Exit₀.Ex 𝔢 (folded L n)) where
      open Exit₀ 𝔢

      K : ∀ n (h : HC (row n)) → tree h ≼ v (twc n)
      K n h = exit (folded L n) (ex n) h

      endpoint : (Y : V) → (∀ n → v (twc n) ≼ Y) → (hs : ∀ n → HC (row n)) → vl (λ n → tree (hs n)) ≼ Y
      endpoint Y up hs = l≼ (λ n → ≼-trans (K n (hs n)) (up n))
```
