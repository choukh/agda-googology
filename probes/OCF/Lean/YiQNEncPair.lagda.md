# 不单射的孩子编码: 最小实例 `Tr (sc zero) ↠ Tr w₁`

> 判决: 条件定理 (排中律, 函数外延作参数). `w₁ = nd sL (λ _ → zero)` 的树单射地嵌进 `sc zero` 的树 (`E₁`, 一步嵌入的实例: 孩子编号 n 与槽位编号 n 都记成目标层的有限标签 `natT n`, 用 Ω 对与原像拼在一起), 排中律取逆得满射 `surj₁`.
> 于是 `PS (sc w₁) (sc (sc zero))`, 前者的每棵树被后者的某棵树按值支配 (`tp₂′`); 反方向是 `YiQNCollapse.tp₂`. 一般层号对见 `YiQNEncGen` (含本对).
> 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiQNEncPair where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import OCF.Lean.YiRWBlock
import OCF.Lean.YiVWVal as W
open W using (val; _≼_)
open import OCF.Lean.YiRVLevel using (LEM; sc)
open import OCF.Lean.YiQNReg using (Surj; PS; eqSurj; TpS; w₁)
open import OCF.Lean.YiQNEncBase
open import OCF.Lean.YiQNEncStep
```

```agda
one : L
one = sc zero
```

## 一步数据

w₁ 的槽位只有 `inj₂ (n , inj₁ tt)` (层号 zero), 全送到 `sc zero` 的唯一槽位, 分支类型相同, ρ 取恒等; 孩子嵌入取恒等.

```agda
πW : Pos w₁ → Pos one
πW (inj₂ (n , inj₁ tt)) = inj₂ (tt , inj₁ tt)

ρW : (p : Pos w₁) → Br one (πW p) → Br w₁ p
ρW (inj₂ (n , inj₁ tt)) w = w

ρsW : (p : Pos w₁) (z : Br w₁ p) → Σ (Br one (πW p)) λ w → ρW p w ≡ z
ρsW (inj₂ (n , inj₁ tt)) z = z , refl

ρbW : (p : Pos w₁) → ρW p (b₀ (Sig one) (πW p)) ≡ b₀ (Sig w₁) p
ρbW (inj₂ (n , inj₁ tt)) = refl

tagPW : Pos w₁ → Tr one
tagPW (inj₂ (n , inj₁ tt)) = natT n

tagPWi : ∀ {p q} → tagPW p ≡ tagPW q → p ≡ q
tagPWi {inj₂ (n , inj₁ tt)} {inj₂ (m , inj₁ tt)} e = cong (λ k → inj₂ (k , inj₁ tt)) (natT-inj e)

DW : StepData sL (λ _ → zero) sS (λ _ → zero)
DW = record
  { χ = λ _ → tt ; emb = λ _ → idE zero
  ; π = πW ; ρ = ρW ; ρs = ρsW ; ρb = ρbW
  ; tagP = tagPW ; tagPi = tagPWi
  ; tagC = natT ; tagCi = natT-inj }
```

## 满射与值支配

```agda
module _ (lem : LEM) (fe : Funext) where
  E₁ : Emb w₁ one
  E₁ = Step.step lem fe DW

  surj₁ : Surj (Tr one) (Tr w₁)
  surj₁ = inj→surj lem zero (σ E₁ , inj E₁)

  ps₂′ : PS (sc w₁) (sc one)
  ps₂′ (inj₂ (tt , inj₁ tt))                         = inj₂ (tt , inj₁ tt) , surj₁
  ps₂′ (inj₂ (tt , inj₂ (inj₂ (n , inj₁ tt))))       = inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt))) , eqSurj refl

  tp₂′ : (x : Tr (sc w₁)) → Σ (Tr (sc one)) λ x′ → val (sc w₁) x ≼ val (sc one) x′
  tp₂′ = TpS ps₂′
```
