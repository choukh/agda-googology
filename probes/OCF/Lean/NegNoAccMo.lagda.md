# 去累加, 否定一路 (二): 值合法 `Mo` 推不出 `LgB`

> 不含记号. 入口 [NegNoAcc](NegNoAcc.lagda.md). 本篇**不依赖**构造一路的接口. 只导入 [HtTowerTy](../Align/HtTowerTy.lagda.md), [LFReTy](../Align/LFReTy.lagda.md) (`S⊥`), [Fab5ValRel](../Align/Fab5ValRel.lagda.md) (值关系 `≤`, 值合法 `Mo`), [Fab5Val](../Align/Fab5Val.lagda.md) (`cr⊥`), [NegCRwAcc](NegCRwAcc.lagda.md) 的小引理. 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示, 不开 K, 不用 UIP, 不用函数外延.
>
> **问题.** 若构造一路把证书的合法性换成值合法 `Mo` (`Fab5ValRel`), 闭项能否由此得到标准的 `LgB` 证书? `Fab5Val.lgB-not-mo` 说 `LgB` 推不出 `Mo` (第 1 层). 本篇写反方向.
>
> 1. **`Mo-triv` (定理).** 第 0 层 (`S⊥`, 闭项与 FGH 所在的层) 上 `Mo` 对一切树成立. 所以 `Mo` 在闭项那一层不含任何信息.
> 2. **`mo⇏lgB` (定理, 反例).** 第 0 层一棵 ℕ-极限 $h=\lim(\omega',\omega+1,\omega+2,\dots)$ ($\omega'=\lim(1,2,3,\dots)$): 值合法 (`Mo`), 相邻项的值**严格**递增 ($f_n+1\le f_{n+1}$, 用 `Fab5ValRel` 的 `≤`), 但不满足 `LgB` ($\omega'\not\lhd\omega+1$). 所以即使在 `Mo` 上再加 "ℕ-极限按值严格递增", 也推不出字面合法. (反过来要求字面步进按值严格, 推出 LPO: `BrwViewNeg.strict→LPO`.)
>
> **前提实例.** 无前提 (两条都是闭的陈述); `cr⊥` 来自 `Fab5Val`.
>
> **只否定什么.** 只否定: `Mo` (或 `Mo` 加 ℕ-极限的值严格递增) 推出 `LgB`. **不否定**: 用 `Mo` 证值的定理 (`Fab5Val` 的 `Ψ-mono≤`, `Mo-Ψ`); 闭项另有 `LgB` 证书 (例如读输入的 `LgB`). 结论是: 若构造一路的证书用 `Mo`, 闭项的标准 `LgB` 证书必须另行给出, `Mo` 不提供它.
>
> **对纲领与目标.** 纲领 1 的 View 要求 ℕ-极限 "相邻项按目标树自己的合法性步进" (第一位置, 不按值); `mo⇏lgB` 说值合法不能替代这一条. 两条合法性 (`LgB` 为比较, `Mo` 为值) 互不推出 (与 `lgB-not-mo` 合起来).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.NegNoAccMo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.HtTowerTy
open import OCF.Align.LFReTy using (S⊥)
open import OCF.Align.Fab5ValRel using (module Rel)
open import OCF.Align.Fab5Val using (cr⊥)
open import OCF.Lean.NegCRwAcc using (num; at; lim-not-fin)

open Rel cr⊥
```

## §1 第 0 层上 `Mo` 恒真

```agda
Mo-triv : ∀ (h : HB S⊥) → Mo tt h
Mo-triv hz = tt
Mo-triv (hs h) = Mo-triv h
Mo-triv (hl f) = λ n → Mo-triv (f n)
Mo-triv (hΩ () _)
```

## §2 值合法且值严格递增, 但字面不合法

```agda
ω̂ ω̂′ : HB S⊥
ω̂ = hl num
ω̂′ = hl (λ n → num (suc n))

sucs : ℕ → HB S⊥ → HB S⊥
sucs zero x = x
sucs (suc k) x = hs (sucs k x)

hf : ℕ → HB S⊥
hf zero = ω̂′
hf (suc n) = sucs (suc n) ω̂

h⋆ : HB S⊥
h⋆ = hl hf

ω̂′≤ω̂ : ω̂′ ≤[ tt ] ω̂
ω̂′≤ω̂ = l≤ (λ n → ≤l (suc n) (≤-refl _))

-- 相邻项按值严格递增
hf-strict : ∀ n → hs (hf n) ≤[ tt ] hf (suc n)
hf-strict zero = s≤s ω̂′≤ω̂
hf-strict (suc n) = ≤-refl _

Mo-h⋆ : Mo tt h⋆
Mo-h⋆ = Mo-triv h⋆

¬ω̂′⊲ω̂ : ¬ (ω̂′ ⊲[ tt ] ω̂)
¬ω̂′⊲ω̂ p = go p refl
  where
  go : ∀ {b} → ω̂′ ⊲[ tt ] b → b ≡ ω̂ → ⊥
  go hself e = one≢zero (cong (λ h → at h 0) e)
    where
    one≢zero : ¬ (num {S⊥} 1 ≡ hz)
    one≢zero ()
  go (hsuc p) ()
  go (hlim n q) refl = lim-not-fin n q
  go (hLim {κ = ()} e q) _

¬LgB-h⋆ : ¬ LgB h⋆
¬LgB-h⋆ (st , _) = go (st {tt} 0)
  where
  go : ¬ (ω̂′ ⊲[ tt ] hs ω̂)
  go (hsuc p) = ¬ω̂′⊲ω̂ p

mo⇏lgB : Σ (HB S⊥) (λ h → Mo tt h × (Σ (ℕ → HB S⊥) (λ f → (h ≡ hl f) × (∀ n → hs (f n) ≤[ tt ] f (suc n)))) × ¬ LgB h)
mo⇏lgB = h⋆ , Mo-h⋆ , (hf , refl , hf-strict) , ¬LgB-h⋆
```

## 结论 (按档)

- **[定理]** **`Mo-triv`** (第 0 层 `Mo` 恒真); `ω̂′≤ω̂`, `hf-strict`, `¬ω̂′⊲ω̂`, `¬LgB-h⋆`, **`mo⇏lgB`** (值合法, 值严格递增, 不 `LgB`).
- **[判断]** 构造一路若用 `Mo` 作证书, 闭项的 `LgB` 证书要另走一条路 (例如读输入的 `LgB`); 是否容易, 未测.
