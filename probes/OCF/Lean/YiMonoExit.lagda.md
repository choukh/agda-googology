# 终点的出口: EBO 参照树的下界归约到对基本列封闭的一族

验收文件 (读记号). 编译定理, 无前提: `exit`, `ebo-lower`. 只要有一族 (记号项, 第 0 层的树) 对后继余尾走到 `pred`、对 ω 余尾逐项走到 `fsn`, 并含塔的每一项且对应的树不高于 Y, 就有 `EBO-tree′` 不高于 Y.
不给出这样一族; 不读主线的块. 来自第十一次路线审查 ([RR11](../../Survey/RR11-RouteOverview.md)), 代码未改, 只换模块名.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
-- 终点的出口引理: EBO-tree′ ≼ Y 归约到 "第 0 层上对 pred / fsn 封闭的一族 (记号项, 树)".
module OCF.Lean.YiMonoExit where

open import Data.Nat.Base using (ℕ)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.EboLeanDef using (T; HC; h0; h1; hω; cof; c1; cω; pred; fsn; EBOψ)
open import OCF.Align.EboLeanTree using (Ord; tree; hc-tower; EBO-tree′)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-trans)

toL : Ord → L.Ordᶜ L.zero
toL Ord.zero = L.zero
toL (Ord.suc a) = L.suc (toL a)
toL (Ord.lim f) = L.lim (λ n → toL (f n))

record Closed (P : T → L.Ordᶜ L.zero → Set) : Set where
  field
    step1 : ∀ {t X} → P t X → cof t ≡ c1 → Σ (L.Ordᶜ L.zero) λ X′ → P (pred t) X′ × (L.suc X′ ≼ X)
    stepω : ∀ {t X} → P t X → cof t ≡ cω → ∀ n → Σ (L.Ordᶜ L.zero) λ X′ → P (fsn t n) X′ × (X′ ≼ X)
open Closed

exit : ∀ {P} → Closed P → ∀ {t X} → P t X → (h : HC t) → toL (tree h) ≼ X
exit C p (h0 _) = z≼
exit C p (h1 e h) =
  ≼-trans (s≼s (exit C (proj₁ (proj₂ (step1 C p e))) h)) (proj₂ (proj₂ (step1 C p e)))
exit C p (hω e h) = l≼ (λ n →
  ≼-trans (exit C (proj₁ (proj₂ (stepω C p e n))) (h n)) (proj₂ (proj₂ (stepω C p e n))))

-- 终点: 只要塔的每一项都在这一族里, 并且对应的树不高于 Y.
ebo-lower : ∀ {P} → Closed P → (Y : L.Ordᶜ L.zero) →
  (∀ k → Σ (L.Ordᶜ L.zero) λ X → P (EBOψ k) X × (X ≼ Y)) → toL EBO-tree′ ≼ Y
ebo-lower C Y tw = l≼ (λ k →
  ≼-trans (exit C (proj₁ (proj₂ (tw k))) (hc-tower k)) (proj₂ (proj₂ (tw k))))
```
