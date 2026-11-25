# 冻结接口的配对否定 (三): 对一切树的基底单调作为字段

> 验收文件 (否定), 编译定理. 候选字段 `BMI` (对一切层号, 证据, 路线, 树, 底按 `_⊴_` 变大时 `ψ⊥` 的值不降) 与 `legI` 矛盾 (`no-bm-legI`, 由 `YiLPNoBM.no-bm-all`); 对任何在第 1 层坏树 `xbad` 的两个底上与合法块的 `ψ⊥` 相同的实例也矛盾 (`no-bm-agree`, 前提 `Agree`, `legI` 满足).
> 反例不在规范域: `xbad` 的分支函数对坐标不单调, 读作 "谓词太宽". 重推 `no-bm-all`, 改写成对接口的陈述.
> 不否定什么: 规范域上的 `YiLPMono.BaseMonoΩt`, `CoordMono`; 第 0 层的基底单调 (`bm-zero⊥` 已证). 对任意实例的否定没有给出: 接口的律不约束零与后继两行.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLNBM where

open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegPath
open import OCF.Lean.YiLegFold using (Base; B₀)
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiLPVal using (val; _≼_)
open import OCF.Lean.YiLPMono using (_⊴_)
open import OCF.Lean.YiLPNoBM using (no-bm-all; no-bm; one; xbad; B′)
open import OCF.Lean.YiLPIface using (Iface)
open import OCF.Lean.YiLPInst using (legI)
```

## 候选字段与否定

```agda
BMI : Iface → Set
BMI I = (ℓ : L) (ε : Ev ℓ) (ρ : Rt ℓ) (x : Tr ℓ) (B₁ B₂ : Base ℓ) → B₁ ⊴ B₂
  → val zero (Iface.ψ⊥ I ℓ ε ρ B₁ x) ≼ val zero (Iface.ψ⊥ I ℓ ε ρ B₂ x)

no-bm-legI : BMI legI → ⊥
no-bm-legI h = no-bm-all (λ ℓ x ε ρ B₁ B₂ d → h ℓ ε ρ x B₁ B₂ d)

Agree : Iface → Set
Agree I = (Iface.ψ⊥ I one tt tt (B₀ one) xbad ≡ F.ψ⊥ one tt tt (B₀ one) xbad)
        × (Iface.ψ⊥ I one tt tt B′ xbad ≡ F.ψ⊥ one tt tt B′ xbad)

agree-legI : Agree legI
agree-legI = refl , refl

no-bm-agree : (I : Iface) → Agree I → BMI I → ⊥
no-bm-agree I (a₀ , a₁) h =
  proj₂ no-bm (subst (λ t → val zero t ≼ val zero (F.ψ⊥ one tt tt B′ xbad)) a₀
                (subst (λ t → val zero (Iface.ψ⊥ I one tt tt (B₀ one) xbad) ≼ val zero t) a₁
                  (h one tt tt xbad (B₀ one) B′ (proj₁ no-bm))))
```
