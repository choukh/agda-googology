# 抽象理论 (九): 分级模拟的充分性

> 判决: 编译定理, 无前提; 只导入标准库与 `YiAbs*`. 对任意块, 折叠, 参照系统与值前序: `Leaf`, `Lift` 给出塔每一项的龙骨对应 (`keel`, `keelᴿ`); 再加 `LowKeep` 与第 0 层的 `Base`, 塔每一项的闭项不低于参照行 (`K`), 终点不低于各行参照树的上确界 (`endpoint`).
> 充分性只用到 `Leaf`, `Lift`, `LowKeep`, `Base` 四项; 其余的律用来导出这四项 (见 [YiAbsGRow](YiAbsGRow.lagda.md)). 回灌链的律由 `SelfKeep` 与 `Weak` 导出 (`chain`).
> 不给出什么: 不构造任何关系; 不涉及上界. EBO 参照的实例在 [YiAbsGEbo](YiAbsGEbo.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAbsGSuff where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (Σ; _×_; _,_)

open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
open import OCF.Lean.YiAbsGIface

module Suff {𝔹 : Block} {𝔽 : Fold 𝔹} {ℜ : Rows 𝔹 𝔽} {𝕋 : Ref} {𝕍 : Val}
            (𝔾 : Graded 𝔹 𝔽 ℜ 𝕋 𝕍) (𝔻 : Doms 𝔹 𝔽) where
  open Laws 𝔾 𝔻
```

## 第 0 层的下界

```agda
  base-lower : (𝔟 : Base) → ∀ {t x} → R ℓ₀ t x → Base.G₀ 𝔟 x → (h : HC t) → tree h ≼ v x
  base-lower 𝔟 r g h = Sim.lower v (λ x → x) G₀ _⇝ˢ_ _⇝_ strict weak (R ℓ₀) inv1 invω r g h
    where open Base 𝔟
```

## 折到低层再到值

`LowKeep` 在目标为 `ℓ₀` 的一条路径上, 加第 0 层的下界: 第 ℓ 层的对应给出折叠值的下界.

```agda
  low-lower : LowKeep → (𝔟 : Base) → ∀ {ℓ} (b : Bs ℓ) (w : ℓ₀ ⊑ ℓ) (β : Bt ℓ₀) (K : Cx ℓ ℓ₀)
    → Gb ℓ b → Wl w → Bd b w β K → ∀ {a x} → Gx ℓ x → R ℓ a x → Base.G₀ 𝔟 (ψ ℓ b ℓ₀ w β x)
    → (h : HC (app K a)) → tree h ≼ v (ψ ℓ b ℓ₀ w β x)
  low-lower L 𝔟 b w β K gb wl bd gx r g h = base-lower 𝔟 (L b w β K gb wl bd gx r) g h
```

## 龙骨

```agda
  module Tower (lf : Leaf) (li : Lift) {𝔟 : Base} (𝔨 : Keel 𝔟) where
    open Keel 𝔨

    keel : ∀ n → Rd (tw n) (kt n)
    keel zero    = rd-tw0
    keel (suc n) = tw-step n (li (gl n) (lf (keel n)))

    keelᴿ : ∀ n → R (tw n) (Ωr (kt n)) (Ωt (tw n))
    keelᴿ n = lf (keel n)

    K : LowKeep → ∀ n (h : HC (row n)) → tree h ≼ v (twc n)
    K L n h = low-lower L 𝔟 (b₀ n) (w₀ n) (β₀ n) (K₀ n) (gb n) (wl n) (bd n) (gx n) (keelᴿ n) (g₀ n) h

    endpoint : LowKeep → (Y : V) → (∀ n → v (twc n) ≼ Y) → (hs : ∀ n → HC (row n)) → vl (λ n → tree (hs n)) ≼ Y
    endpoint L Y up hs = l≼ (λ n → ≼-trans (K L n (hs n)) (up n))
```

接口的全部律在手时的同一结论.

```agda
  module FromGSim (𝔰 : GSim) {𝔟 : Base} (𝔨 : Keel 𝔟) where
    open GSim 𝔰
    open Keel 𝔨
    open Tower leaf liftᴿ 𝔨 public using (keel; keelᴿ)

    Kᴳ : ∀ n (h : HC (row n)) → tree h ≼ v (twc n)
    Kᴳ = Tower.K leaf liftᴿ 𝔨 lowᴷ

    endpointᴳ : (Y : V) → (∀ n → v (twc n) ≼ Y) → (hs : ∀ n → HC (row n)) → vl (λ n → tree (hs n)) ≼ Y
    endpointᴳ = Tower.endpoint leaf liftᴿ 𝔨 lowᴷ
```

## 回灌链

折到自身的 F 以 β 为底值; 链 z 每一步越过 F (`F (z k) ◃ z (k+1)`). 参照一侧的链: `γ 0 = g₀`, `γ (k+1) = cl ℓ (P ⊕ γ k)`. 起点对上, 链就逐项对上.

```agda
  module Chain (sk : SelfKeep) (wk : Weak) {ℓ : Lv} (b : Bs ℓ) (β : Bt ℓ) (gb : Gb ℓ b)
               (P g₀ : T) (z : ℕ → Tr ℓ)
               (zs : ∀ k → ψ ℓ b ℓ self β (z k) ◃ z (suc k)) where

    γ : ℕ → T
    γ zero    = g₀
    γ (suc k) = cl ℓ (P ⊕ γ k)

    chain : R ℓ (cl ℓ P) (bt β) → R ℓ g₀ (z 0) → ∀ k → R ℓ (γ k) (z k)
    chain hP r0 zero    = r0
    chain hP r0 (suc k) = wk (sk b β gb hP (chain hP r0 k)) (zs k)
```
