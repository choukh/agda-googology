# 合法块的 View: 第 0 层的 FGH 与闭项

> 判决: 成品候选 (FGH). 第 0 层的树只有零, 后继, ℕ 极限 (第 0 层没有槽位与孩子), FGH 逐行照 `BTBO.FGH`; `fgh = FGH EBOᶜ` 是闭的 ℕ → ℕ 函数, `EBOᶜ` 取自合法块的折叠 `YiLegFold`.
> 编译定理: 树的 FGH 与它的值 (`YiLPVal.val`) 的 FGH 相同 (`FGH-val`); 对一切第 0 层树 `FGH x 1 ≡ 2` (`FGH-1`), 所以 `FGH EBOᶜ 1 ≡ 2` (`fgh-1`). 有限测试 (由 `refl` 算出): `fgh 0 ≡ 0`.
> 不否定什么. 测试只说明闭项在检查器里能沿第 0 项求值到底, 不反映强度. 对参照框架的验收在 [YiLPRead](YiLPRead.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLPFGH where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps using (iter)
open import OCF.Lean.YiLegFold using (EBOᶜ)
open import OCF.Lean.YiLPVal using (V; zero; suc; lim; Ω; val)
```

```agda
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

fgh : ℕ → ℕ
fgh = FGH EBOᶜ

fgh-1 : FGH EBOᶜ 1 ≡ 2
fgh-1 = FGH-1 EBOᶜ

test₀ : fgh 0 ≡ 0
test₀ = refl
```
