# Ω 前缀容纳读回层引入的指标种类

公共界混合后仍缺局部折叠。这里先证明一个实际字段：读回 upL k
遇到种类 κ 时，node 引入的指标层 step(Lv(lvl k κ)) 已经包含在
ΩL k 前缀中。由种类结构给出上下文，不比较裸层号，也不假设折叠。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedIndexContext where

open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay
open import OCF.Lean.LHRecLeg using (Ctx; here; viaS; viaL)
open import OCF.Lean.BoundedContextRun using (compose)

kind-context : ∀ k κ → Ctx (Lv k) (step (Lv (lvl k κ)))
kind-context lz ()
kind-context (ls k) (inj₁ κ) = compose (viaS here) (kind-context k κ)
kind-context (ls k) (inj₂ _) = here
kind-context (ll f) (n , κ) = compose (viaL here n) (kind-context (f n) κ)
kind-context (lΩ k g) (inj₁ _ , inj₁ κ) =
  compose (viaS (viaL here (inj₁ tt))) (kind-context k κ)
kind-context (lΩ k g) (inj₁ _ , inj₂ _) = viaL here (inj₁ tt)
kind-context (lΩ k g) (inj₂ c , κ) =
  compose (viaL here (inj₂ c)) (kind-context (g c) κ)

omega-context : ∀ k κ → Ctx (Lv (ΩL k)) (step (Lv (lvl k κ)))
omega-context lz ()
omega-context (ls k) (inj₁ κ) =
  compose (viaS (viaL here (inj₁ tt))) (kind-context k κ)
omega-context (ls k) (inj₂ _) = viaL here (inj₁ tt)
omega-context (ll f) (n , κ) =
  compose (viaL here n) (omega-context (f n) κ)
omega-context (lΩ k g) (inj₁ _ , inj₁ κ) =
  compose (viaS (viaL here (inj₁ tt))) (kind-context k κ)
omega-context (lΩ k g) (inj₁ _ , inj₂ _) = viaL here (inj₁ tt)
omega-context (lΩ k g) (inj₂ c , κ) =
  compose (viaL here (inj₂ c)) (omega-context (g c) κ)

-- 实际新指标种类，非空接口实例。
first-index : Ctx (Lv (ΩL (ls lz))) (step S⊥)
first-index = omega-context (ls lz) (inj₂ tt)
```

这是全部 k 与 κ 的结构定理。它给出指标层到前缀的正向包含，尚未
给出反向树折叠、同一坐标的不同拷贝相容，或从 ΩL k 折到 k。
下一步可据此检验相对 ΩL k 的局部塔分类；不能把这个上下文当作
keep 的全部世界与坐标律。翻译账：沿用现有层族，新增字段来自
局部折叠对实际 node 指标分量的要求，无新层构造子或记号依赖。
