# 那一行是否出现: 塔第 2 项及以后

> 检验文件 (不读记号), 不进成品. 编译定理, 无前提: `twᶜ 2` 的计算触发那一行 (`hit-tw2`). 位置: 顶层 Ω 结点的回灌链由第 1 个链元算第 2 个 (从第 0 个数起; 目标 tw 1) 时, 经孩子层下到 ℕ 极限层号 tw 1 ⊕ ↑ (tw 1) (proj₁ (next⁺ (Ωt (tw 1)))) 的孩子 1, 其下 ℕ 后继层号的链调用底, 底的闭包把那个 ℕ 极限层号的左项按 "经孩子 1" 重折, ℕ 极限一行把右项嵌进孩子 1.
> 参数 (`P₂`): 层号 tw 1 ⊕ ↑ (tw 1) (b₁ + b₁) (下标层 0), 目标 tw 1 ⊕ ↑ (tw 1) b₁, c′ = c = 0, 其中 b₁ 是 tw 1 的 Ω 树. 由 `step`, 塔每一项 n ≥ 2 都以同样的参数触发 (`hit-tw≥2`; 路径经顶层第一个和项逐项下到第 2 项的那一处).
> 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNRTw2 where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiNRHit using (Site; HitTw; step)
```

见证依次是: 链的第 1 步 (算第 2 个链元), 保留结点的分支 0, ℕ 极限的第 1 项, 保留结点的分支 0, ℕ 后继层号上链的第 0 步.

```agda
b₁ : Tr (tw 1)
b₁ = proj₁ (Ωt (tw 1))

P₂ : Site
P₂ k h j c′ c = (nd (sΩ k) h ≡ tw 1 ⊕ ↑ (tw 1) (b₁ + b₁)) × (j ≡ tw 1 ⊕ ↑ (tw 1) b₁)
              × (_≡_ {A = Σ L Tr} (k , c′) (zero , zero)) × (_≡_ {A = Σ L Tr} (k , c) (zero , zero))

hit-tw2 : HitTw P₂ 2
hit-tw2 = 1 , inj₂ (zero , (1 , (zero , (0 , inj₂ (refl , refl , refl , refl)))))

hit-tw≥2 : (n : ℕ) → HitTw P₂ (suc (suc n))
hit-tw≥2 zero    = hit-tw2
hit-tw≥2 (suc n) = step P₂ (suc (suc n)) (hit-tw≥2 n)
```
