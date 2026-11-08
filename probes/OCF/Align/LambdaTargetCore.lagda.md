# 极限参照的值验收核心

无记号的通用验收接口。参数 R 是参照阶段族；`LambdaTarget` 给出它
与实际 WfFsn 阶段的预期实例化（该实例编译受 6G 堆墙阻止，不计通过）。
本核心的定理对任意 R 成立，不要求阶段单调或逐项 Lab。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import Data.Nat using (ℕ)
open import OCF.Align.Level using (Ordᶜ; zero; lim)
module OCF.Align.LambdaTargetCore (R : ℕ → Ordᶜ zero) where

open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Align.OCFSpecBase using (_≼_; _≈ᵛ_; l≼; ≼l; ≼-refl; ≼-trans)

record Lower (candidate : Ordᶜ zero) : Set where
  field
    stage-bound : ∀ n → R n ≼ candidate
open Lower public

sound : ∀ {candidate} → Lower candidate → lim R ≼ candidate
sound p = l≼ (stage-bound p)

complete : ∀ {candidate} → lim R ≼ candidate → Lower candidate
complete p = record { stage-bound = λ n → ≼-trans (≼l n (≼-refl (R n))) p }

record Cover (f : ℕ → Ordᶜ zero) : Set where
  field
    cover : ∀ n → Σ ℕ (λ k → R n ≼ f k)
open Cover public

cover-sound : ∀ {f} → Cover f → Lower (lim f)
cover-sound c = record { stage-bound = λ n → ≼l (proj₁ (cover c n)) (proj₂ (cover c n)) }

self-cover : Cover R
self-cover = record { cover = λ n → n , ≼-refl (R n) }

self-lower : Lower (lim R)
self-lower = cover-sound self-cover

record Exact (candidate : Ordᶜ zero) : Set where
  field
    lower : Lower candidate
    upper : candidate ≼ lim R

exact-sound : ∀ {candidate} → Exact candidate → candidate ≈ᵛ lim R
exact-sound e = Exact.upper e , sound (Exact.lower e)
```

`OCFSpecBase` 的值序与 `Value` 的构造子一致，但不经后者导入记号。
这里不提供新的强度下界，提供的是验收律的准确、可满足定义域。
