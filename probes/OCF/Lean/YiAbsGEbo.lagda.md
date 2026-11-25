# 抽象理论 (十三): 充分性定理在 EBO 参照上的实例

> 验收文件 (读记号). 判决: 编译定理, 无前提. EBO 记号的 (`cof`, `pred`, `fsn`, `fsT`, `++`, Ω_ν) 是 `YiAbsGIface.Ref` 的实例 (`refᴱ`); 值前序取 `YiAbsSimInst.𝕍`.
> 对任意块上以 `refᴱ` 为参照的分级结构: `Leaf`, `Lift`, `LowKeep`, `Base` 与塔 (起点下标是 1, 标准上下文是 ψ₀) 给出 `toL EBO-tree′ ≼ Y`, 只要 Y 不低于塔每一项的闭项与 ψ₀(1) 的参照 (`ebo-end`).
> 不给出什么: 没有构造满足这四项的块; 第 0 行 ψ₀(1) 作前提.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiAbsGEbo where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanTree as ET
open import OCF.Lean.YiMonoExit using (toL)
open import OCF.Lean.YiAbsSimInst using (𝕍; conv; toL-tree)
open import OCF.Lean.YiAbsFrame
open import OCF.Lean.YiAbsSim
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiAbsGSuff

refᴱ : Ref
refᴱ = record
  { T = E.T ; C0 = λ t → E.cof t ≡ E.c0 ; C1 = λ t → E.cof t ≡ E.c1 ; Cω = λ t → E.cof t ≡ E.cω
  ; CΩ = λ t κ → E.cof t ≡ E.cΩ κ ; pred = E.pred ; fsn = E.fsn ; fsT = E.fsT ; _⊕_ = _++_ ; Ωr = E.Ωt }

module Ebo {𝔹 : Block} {𝔽 : Fold 𝔹} {ℜ : Rows 𝔹 𝔽} (𝔾 : Graded 𝔹 𝔽 ℜ refᴱ 𝕍) (𝔻 : Doms 𝔹 𝔽) where
  open Laws 𝔾 𝔻
  open Suff 𝔾 𝔻

  module _ (lf : Leaf) (li : Lift) (lk : LowKeep) {𝔟 : Base} (𝔨 : Keel 𝔟)
           (e0 : Keel.κ₀ 𝔨 ≡ E.natT 1)
           (eK : ∀ n a → app (Keel.K₀ 𝔨 n) a ≡ E.ψ [] a ∷ []) where
    open Keel 𝔨

    kt≡ : ∀ n → kt n ≡ E.ΩTower n
    kt≡ zero    = e0
    kt≡ (suc n) = cong E.Ωt (kt≡ n)

    row≡ : ∀ n → row n ≡ E.EBOψ (suc n)
    row≡ n = trans (eK n (Ωr (kt n))) (cong (λ a → E.ψ [] (E.Ωt a) ∷ []) (kt≡ n))

    K′ : ∀ n {t} → row n ≡ t → (h : HC t) → tree h ≼ v (twc n)
    K′ n refl h = Tower.K lf li 𝔨 lk n h

    ebo-row : (Y : V) (hs : ∀ k → E.HC (E.EBOψ k)) → toL (ET.tree (hs zero)) ≼ Y → (∀ n → v (twc n) ≼ Y)
      → ∀ k → toL (ET.tree (hs k)) ≼ Y
    ebo-row Y hs y0 up zero    = y0
    ebo-row Y hs y0 up (suc n) =
      ≼-trans (toL-tree (hs (suc n))) (≼-trans (K′ n (row≡ n) (conv (hs (suc n)))) (up n))

    ebo-end : (Y : V) → toL (ET.tree (ET.hc-tower zero)) ≼ Y → (∀ n → v (twc n) ≼ Y) → toL ET.EBO-tree′ ≼ Y
    ebo-end Y y0 up = l≼ (ebo-row Y ET.hc-tower y0 up)
```
