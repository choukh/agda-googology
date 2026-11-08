# 弱更新的实例不自动接收请求世界

这不是新的 sup 壁垒。只对本轮定稿接口检查实际的冻结实例，
并给出无下标判等的正面对照，避免把“冻结不接收”误读成“接收不可构造”。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.SupCollapseNegReceive where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.SupCollapseIf
open import OCF.Lean.SupCollapseStay using (stay)

S = step S⊥
Family : ⊤ → KS
Family _ = S
Legal : ((i : ⊤) → Wd S) → Set
Legal W = ∀ i → LgW S (W i)

no-stay-receives : Readback ⊤ Family Legal (stay ⊤ Family Legal) → ⊥
no-stay-receives R with proj₂
  (Readback.receives R tt (λ _ → tt , hz) (tt , hs hz)
    (λ _ → tt , tt) (tt , tt))
... | ()

-- 同质分量允许全体覆盖，无须判等下标。
module Homogeneous (I : Set) where
  FamilyI : I → KS
  FamilyI _ = S
  LegalI : ((i : I) → Wd S) → Set
  LegalI W = ∀ i → LgW S (W i)
  replace-all : WeakUpdate I FamilyI LegalI
  replace-all = record
    { update = λ i W v j → v
    ; preserves = λ i W v lW lv j → lv }
  receives-all : Readback I FamilyI LegalI replace-all
  receives-all = record { receives = λ i W v lW lv → tt , hself }
```

否定实例使用合法旧世界 0 与合法请求世界 1；请求在同一分量中，
所需结论是 1 为 0 的第一位置，已由空模式排除。
正面对照对任意索引类型成立，但会覆盖全部旧分量；当前两个记录都没有
要求旧信息保留。这仅校准接口范围，不声称它提供 ψ₀Λ 的下界。
翻译账：无新树构造子、无记号，未改变原折叠。
