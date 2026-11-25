# 抽象理论 (十一): 分级模拟的配对否定

> 判决: 编译定理, 只导入标准库与 `YiAbs*`. (一) 值封顶: 折到第 0 层的输出值不高于 U 而参照行的树严格高于 U, 则 `LowKeep` (连同 `Base`) 不成立 (`cap→¬low`); 分支侧一行与结点一行的两种形状是推论 (`branch-cap→¬`, `node-cap→¬`). 前提 `irr` 是值序的严格性.
> (二) 槽位不保留: 目标层的关系由六条规则生成时, 余尾为 Ω 的参照项只能对着含结点的树 (`inv`); 所以参照一侧上下文保持余尾 Ω 而折叠输出不含结点, `LowKeep` 在这一点不成立 (`unkept→¬low`), 不经过值.
> 不否定什么: 两条都只否定给定量化域上的 `LowKeep`; (二) 只对生成的关系. 前提可满足的实例在 [YiAbsGToy](YiAbsGToy.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAbsGNeg where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _×_; _,_)

open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGSuff
open import OCF.Lean.YiAbsGRow

module Neg {𝔹 : Block} {𝔽 : Fold 𝔹} {ℜ : Rows 𝔹 𝔽} {𝕋 : Ref} {𝕍 : Val}
           (𝔾 : Graded 𝔹 𝔽 ℜ 𝕋 𝕍) (𝔻 : Doms 𝔹 𝔽) where
  open Laws 𝔾 𝔻
  open Suff 𝔾 𝔻
  open Row 𝔾 𝔻
```

## 值封顶

```agda
  module Cap (irr : ∀ {a} → vs a ≼ a → ⊥) (𝔟 : Base) where
    open Base 𝔟

    cap→¬low : ∀ {ℓ} (b : Bs ℓ) (w : ℓ₀ ⊑ ℓ) (β : Bt ℓ₀) (K : Cx ℓ ℓ₀) → Gb ℓ b → Wl w → Bd b w β K
      → ∀ {a x} → Gx ℓ x → R ℓ a x → G₀ (ψ ℓ b ℓ₀ w β x)
      → (h : HC (app K a)) (U : V) → v (ψ ℓ b ℓ₀ w β x) ≼ U → vs U ≼ tree h → LowKeep → ⊥
    cap→¬low b w β K gb wl bd gx r g h U cap big L =
      irr (≼-trans big (≼-trans (low-lower L 𝔟 b w β K gb wl bd gx r g h) cap))
```

分支侧一行: 嵌入 `up x c y` 的折叠值不高于 U (例如孩子的底不读前缀, 输出停在 "本层 Ω 树加可数偏移" 之下), 参照行 `app K (t ⊕ s)` 的树严格高于 U. 则 `Emb` 与 `LowKeep` 不能同时成立.

```agda
    branch-cap→¬ : ∀ {ℓ} (b : Bs ℓ) (w : ℓ₀ ⊑ ℓ) (β : Bt ℓ₀) (K : Cx ℓ ℓ₀) → Gb ℓ b → Wl w → Bd b w β K
      → (c : Ch ℓ) {t s : T} {x : Tr ℓ} (y : ChT ℓ c) → R ℓ t x → R (chL ℓ c) s (chT ℓ c y)
      → Gx ℓ (up x c y) → G₀ (ψ ℓ b ℓ₀ w β (up x c y))
      → (h : HC (app K (t ⊕ s))) (U : V) → v (ψ ℓ b ℓ₀ w β (up x c y)) ≼ U → vs U ≼ tree h
      → Emb → LowKeep → ⊥
    branch-cap→¬ b w β K gb wl bd c y r ry gx g h U cap big E L =
      cap→¬low b w β K gb wl bd gx (E c y r ry) g h U cap big L
```

结点一行: 结点 `nd p g` 的折叠值不高于 U (例如只取到一部分分支位置上的值), 分支逐项对着 `fsT t η`, 参照行 `app K t` 的树严格高于 U. 则 `Node` 与 `LowKeep` 不能同时成立.

```agda
    node-cap→¬ : ∀ {ℓ} (b : Bs ℓ) (w : ℓ₀ ⊑ ℓ) (β : Bt ℓ₀) (K : Cx ℓ ℓ₀) → Gb ℓ b → Wl w → Bd b w β K
      → (p : Sl ℓ) {t κ : T} (g : SlT ℓ p → Tr ℓ) → CΩ t κ → Nu ℓ p κ
      → (∀ η c → R (slL ℓ p) η (slT ℓ p c) → R ℓ (fsT t η) (g c))
      → Gx ℓ (nd p g) → G₀ (ψ ℓ b ℓ₀ w β (nd p g))
      → (h : HC (app K t)) (U : V) → v (ψ ℓ b ℓ₀ w β (nd p g)) ≼ U → vs U ≼ tree h
      → Node → LowKeep → ⊥
    node-cap→¬ b w β K gb wl bd p g e nu hyp gx g₀ h U cap big N L =
      cap→¬low b w β K gb wl bd gx (N p g e nu hyp) g₀ h U cap big L
```

## 槽位不保留

固定目标层 j 与余尾下标 κ. `H o`: 树 o 含结点 (任意谓词, 只要对结点成立, 沿第一位置序向上保持, 并在嵌入处由 "和的余尾是 Ω" 得出). 参照一侧余尾 0, 1, ω 都与余尾 Ω 互斥.

```agda
  module Inv {j : Lv} (G : Gen j) (κ : T) (H : Tr j → Set)
      (d0 : ∀ {s} → C0 s → CΩ s κ → ⊥)
      (d1 : ∀ {s} → C1 s → CΩ s κ → ⊥)
      (dω : ∀ {s} → Cω s → CΩ s κ → ⊥)
      (hΩ : (p : Sl j) (g : SlT j p → Tr j) → H (nd p g))
      (hw : ∀ {x x′} → H x → x ◃ x′ → H x′)
      (hU : (c : Ch j) {t s : T} {x : Tr j} (y : ChT j c) → CΩ (t ⊕ s) κ → (CΩ t κ → H x)
          → R (chL j c) s (chT j c y) → H (up x c y)) where

    inv : ∀ {s o} → R j s o → CΩ s κ → H o
    inv = G (λ s o → CΩ s κ → H o) (record
      { qz = λ e c → ⊥-elim (d0 e c)
      ; q1 = λ e _ _ c → ⊥-elim (d1 e c)
      ; qL = λ e _ _ c → ⊥-elim (dω e c)
      ; qΩ = λ p g _ _ _ _ _ → hΩ p g
      ; qU = λ c y _ q ry e → hU c y e q ry
      ; qw = λ _ q d e → hw (q e) d })

    unkept→¬low : ∀ {ℓ} (b : Bs ℓ) (w : j ⊑ ℓ) (β : Bt j) (K : Cx ℓ j) → Gb ℓ b → Wl w → Bd b w β K
      → ∀ {a x} → Gx ℓ x → R ℓ a x → CΩ (app K a) κ → (H (ψ ℓ b j w β x) → ⊥) → LowKeep → ⊥
    unkept→¬low b w β K gb wl bd gx r e no L = no (inv (L b w β K gb wl bd gx r) e)
```
