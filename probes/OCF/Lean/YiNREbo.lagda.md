# 那一行是否出现: EBO 闭项

> 检验文件 (不读记号), 不进成品. 编译定理, 无前提: `EBOᶜ` 的计算在 Λ 的孩子 tw 2 与 tw 1 本身的层号上触发那一行. 两处都是: Λ 的孩子 n 的折叠往下调用底, Λ 的底把 Λ 的左项 (部分和) 按 "经孩子 n" 重折, ℕ 极限一行把右项嵌进 tw n, 嵌入是 `up zero 0 …`.
> `hit-Λ2` (`PΛ2`): 层号 tw 2, 目标 0, c′ = c = 0. `hit-Λ1` (`PΛ1`): 层号 tw 1, 目标 0, c = 0, c′ = next⁺ (next⁺ 1), 指定孩子与嵌入孩子不同.
> 不否定什么.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNREbo where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiNRHit using (Site; HitΛ)
```

`hit-Λ2`: Λ 的第 2 项, tw 2 结点链元 0 的和项, tw 1 结点链的第 0 步. `hit-Λ1`: Λ 的第 1 项, tw 1 结点链元 1 的和项, 两层 ℕ 极限的第 0 项, ℕ 后继层号上链的第 0 步.

```agda
PΛ2 : Site
PΛ2 k h j c′ c = (nd (sΩ k) h ≡ tw 2) × (j ≡ zero)
               × (_≡_ {A = Σ L Tr} (k , c′) (tw 1 , zero)) × (_≡_ {A = Σ L Tr} (k , c) (tw 1 , zero))

hit-Λ2 : HitΛ PΛ2
hit-Λ2 = 2 , (0 , inj₁ (0 , inj₂ (refl , refl , refl , refl)))

PΛ1 : Site
PΛ1 k h j c′ c = (nd (sΩ k) h ≡ tw 1) × (j ≡ zero)
               × (_≡_ {A = Σ L Tr} (k , c′) (zero , proj₁ (next⁺ (next⁺ (Ωt zero)))))
               × (_≡_ {A = Σ L Tr} (k , c) (zero , zero))

hit-Λ1 : HitΛ PΛ1
hit-Λ1 = 1 , (1 , inj₁ (0 , (0 , (0 , inj₂ (refl , refl , refl , refl)))))
```
