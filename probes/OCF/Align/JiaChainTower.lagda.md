# 甲脚手架：零起步码链覆盖实际 Ω 塔

实例化 `JiaChain.zero-tower`。本篇只用现有的标准形与 Ω 视图，
证明实际参照 Ω 塔每一站的零起步码链均保持标准形；含 Ω_Ω，
不是有限测试，也没有额外未填字段。仍未证明这些码就是新树上 ψ 的码。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.JiaChainTower where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (_×_; proj₁; proj₂)
open import Data.Sum.Base using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Align.EboLeanDef using (T; ψ; Ωt; ΩTower; EBOψ; cof; cΩ; _<ᵀ_; []<)
open import OCF.Align.EboLeanBase using (NF; n[]; nf-ψ)
open import OCF.Align.EboLeanView using (VΩ; ωr; ωl; fΩ)
open import OCF.Align.EboLean3Tree using (nf-ΩT; G0)
open import OCF.Align.JiaChain using (chain; zero-tower; zero-chain-normal)
open import OCF.Align.JiaAuditClosure using (fromZero)

tower-positive : ∀ k → [] <ᵀ ΩTower k
tower-positive zero = []<
tower-positive (suc k) = []<

tower-parent-normal : ∀ k → NF (EBOψ k)
tower-parent-normal k = nf-ψ n[] (nf-ΩT k)
  (λ i → subst (_<ᵀ ΩTower k) (sym (G0 k i)) (tower-positive k))

tower-cof : ∀ k → cof (ΩTower (suc k)) ≡ cΩ []
tower-cof zero = refl
tower-cof (suc k) = subst (λ c →
  OCF.Align.EboLeanDef.cofψ0 (ΩTower (suc k)) c ≡ cΩ [])
  (sym (tower-cof k)) refl

tower-view : ∀ k → VΩ (ΩTower (suc k)) []
tower-view zero = ωr refl
tower-view (suc k) = ωl (tower-cof k) (tower-view k)

-- 整个实际 Ω 塔，不按阶段定制链不变量。
tower-zero-normal : ∀ k n → NF (fromZero (ΩTower (suc k)) [] n)
tower-zero-normal k = zero-chain-normal
  (tower-parent-normal (suc k)) (tower-view k) (inj₂ refl)

-- Ω_Ω 对应 k=1，已含在上一条全塔结论里。
singular-zero-normal : ∀ n → NF (fromZero (ΩTower 2) [] n)
singular-zero-normal = tower-zero-normal 1
```

前提居留：`tower-parent-normal` 与 `tower-view` 都是全 k 的构造，
目标层与共尾层同为零，次序前提就是 `inj₂ refl`。这排除了把
“非正规层不满足错位引理前提”误当作标准形封闭失败的判断。
