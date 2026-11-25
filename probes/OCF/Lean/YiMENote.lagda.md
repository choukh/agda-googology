# 值接口的记号直连实例 (二): 记号一侧的算式

> 验收文件 (读记号). 判决: 编译定理, 无前提. ψ_u(b) 的余尾与基本列按 b 的余尾分情形的等式 (规则 4, 5, 5Ω, 6), 以及和 t + s 的余尾, 前驱, 基本列落在 s 上的等式. 都是对项的首层分情形, 不用标准形.
> 余尾 Ω 的情形留着比较 `cmpᵀ (ν+1) u` 不算, 由使用处代入具体的 u, ν.
> 不给出什么: 只是 `EboLeanDef` 的定义的展开, 没有新的数学内容.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMENote where

open import Data.Nat using (ℕ)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import OCF.Align.EboLeanDef
```

## ψ_u(b)

```agda
cofψ1 : ∀ u b → cof b ≡ c1 → cof (ψ u b ∷ []) ≡ cω
cofψ1 u []       ()
cofψ1 u (y ∷ ys) e = cong (cofA u) e

fsnψ1 : ∀ u b n → cof b ≡ c1 → fsn (ψ u b ∷ []) n ≡ replicate n (ψ u (pred b))
fsnψ1 u []       n ()
fsnψ1 u (y ∷ ys) n e = cong (λ c → fsn₊ u (y ∷ ys) c n) e

cofψω : ∀ u b → cof b ≡ cω → cof (ψ u b ∷ []) ≡ cω
cofψω u []       ()
cofψω u (y ∷ ys) e = cong (cofA u) e

fsnψω : ∀ u b n → cof b ≡ cω → fsn (ψ u b ∷ []) n ≡ ψ u (fsn b n) ∷ []
fsnψω u []       n ()
fsnψω u (y ∷ ys) n e = cong (λ c → fsn₊ u (y ∷ ys) c n) e

cofψΩ : ∀ u b {ν} → cof b ≡ cΩ ν → cof (ψ u b ∷ []) ≡ cofψ₊ u ν (cmpᵀ (sucT ν) u)
cofψΩ u []       ()
cofψΩ u (y ∷ ys) e = cong (cofA u) e

fsnψΩ : ∀ u b {ν} n → cof b ≡ cΩ ν → fsn (ψ u b ∷ []) n ≡ fsnc u b ν (cmpᵀ (sucT ν) u) n
fsnψΩ u []       n ()
fsnψΩ u (y ∷ ys) n e = cong (λ c → fsn₊ u (y ∷ ys) c n) e

fsTψΩ : ∀ u b {ν} η → cof b ≡ cΩ ν → fsT (ψ u b ∷ []) η ≡ fsTc u b ν (cmpᵀ (sucT ν) u) η
fsTψΩ u []       η ()
fsTψΩ u (y ∷ ys) η e = cong (λ c → fsT₊ u (y ∷ ys) c η) e
```

## 和

```agda
cof++ : ∀ t y ys → cof (t ++ y ∷ ys) ≡ cof (y ∷ ys)
cof++ []           y ys = refl
cof++ (x ∷ [])     y ys = refl
cof++ (x ∷ z ∷ t)  y ys = cof++ (z ∷ t) y ys

pred++′ : ∀ t y ys → pred (t ++ y ∷ ys) ≡ t ++ pred (y ∷ ys)
pred++′ []           y ys = refl
pred++′ (x ∷ [])     y ys = refl
pred++′ (x ∷ z ∷ t)  y ys = cong (x ∷_) (pred++′ (z ∷ t) y ys)

fsn++′ : ∀ t y ys n → fsn (t ++ y ∷ ys) n ≡ t ++ fsn (y ∷ ys) n
fsn++′ []           y ys n = refl
fsn++′ (x ∷ [])     y ys n = refl
fsn++′ (x ∷ z ∷ t)  y ys n = cong (x ∷_) (fsn++′ (z ∷ t) y ys n)

cof++1 : ∀ t s → cof s ≡ c1 → cof (t ++ s) ≡ c1
cof++1 t []       ()
cof++1 t (y ∷ ys) e = trans (cof++ t y ys) e

cof++ω : ∀ t s → cof s ≡ cω → cof (t ++ s) ≡ cω
cof++ω t []       ()
cof++ω t (y ∷ ys) e = trans (cof++ t y ys) e

pred++ : ∀ t s → cof s ≡ c1 → pred (t ++ s) ≡ t ++ pred s
pred++ t []       ()
pred++ t (y ∷ ys) e = pred++′ t y ys

fsn++ : ∀ t s n → cof s ≡ cω → fsn (t ++ s) n ≡ t ++ fsn s n
fsn++ t []       n ()
fsn++ t (y ∷ ys) n e = fsn++′ t y ys n
```
