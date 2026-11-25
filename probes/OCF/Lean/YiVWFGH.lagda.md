# 新主线的 FGH
> 成品候选。`FGH` 与 `fghᶻ` 落地主审临时文件 `SelfCheck-SC2FGH`；值一致与参数 1 的证明搬自 `YiLPFGH`。
> 第 0 层没有 Ω 槽位与嵌入孩子；`fghᶻ = FGH EBOᶻ` 是闭的 ℕ → ℕ 函数。
> 编译定理 `FGH-val`、`FGH-1`、`fghᶻ-1`；不作 EBO 强度或函数增长率的验收。有限求值另见 `YiVWTest`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVWFGH where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps using (iter)
open import OCF.Lean.YiMTTab using (EBOᶻ)
open import OCF.Lean.YiVWVal using (V; zero; suc; lim; Ω; val)

FGH : Tr zero → ℕ → ℕ
FGH zero          n = suc n
FGH (suc a)       n = iter (FGH a) n n
FGH (lim f _)     n = FGH (f n) n
FGH (Ω () _)      n
FGH (up _ () _ _) n

FGHᵥ : V zero → ℕ → ℕ
FGHᵥ zero     n = suc n
FGHᵥ (suc a)  n = iter (FGHᵥ a) n n
FGHᵥ (lim f)  n = FGHᵥ (f n) n
FGHᵥ (Ω () _) n

iter-cong : {A : Set} (f g : A → A) → ((a : A) → f a ≡ g a) → (a : A) (n : ℕ) → iter f a n ≡ iter g a n
iter-cong f g e a zero    = refl
iter-cong f g e a (suc n) = trans (cong f (iter-cong f g e a n)) (e (iter g a n))

FGH-val : (x : Tr zero) (n : ℕ) → FGHᵥ (val zero x) n ≡ FGH x n
FGH-val zero          n = refl
FGH-val (suc a)       n = iter-cong (FGHᵥ (val zero a)) (FGH a) (FGH-val a) n n
FGH-val (lim f _)     n = FGH-val (f n) n
FGH-val (Ω () _)      n
FGH-val (up _ () _ _) n

FGH-1 : (x : Tr zero) → FGH x 1 ≡ 2
FGH-1 zero          = refl
FGH-1 (suc a)       = FGH-1 a
FGH-1 (lim f _)     = FGH-1 (f 1)
FGH-1 (Ω () _)
FGH-1 (up _ () _ _)

fghᶻ : ℕ → ℕ
fghᶻ = FGH EBOᶻ

fghᶻ-1 : FGH EBOᶻ 1 ≡ 2
fghᶻ-1 = FGH-1 EBOᶻ

```
