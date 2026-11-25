# 合法块的 View: 第 0 层读进参照框架

> 验收文件 (导入参照框架 `OCF.Align.Level`, `OCF.Align.Value`). 编译定理, 无前提: 合法块第 0 层的树读进参照树 (`readᴸ`) 与它的值的读回互相 `≼` (`read≼V`, `V≼read`); 值前序推出参照框架的 `≼` (`≼→ᴸ`, `≼→read`); 参照框架的 FGH 在读回上与 `YiLPFGH.FGH` 逐点相等 (`FGH-read`).
> 不否定什么. 只涉及第 0 层. Into 在 [YiLPInto](YiLPInto.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLPRead where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps using (iter)
import OCF.Align.Level as L
open import OCF.Align.Value using ()
  renaming (_≼_ to _≼ᴸ_; z≼ to z≼ᴸ; s≼s to s≼sᴸ; ≼l to ≼lᴸ; l≼ to l≼ᴸ; ≼-trans to ≼-transᴸ)
open import OCF.BTBO using (module Ord-Ord)
open import OCF.Lean.YiLPVal
open import OCF.Lean.YiLPFGH using (FGH)
```

```agda
T₀ : Set
T₀ = L.Ordᶜ L.zero

readᴸ : Tr zero → T₀
readᴸ zero          = L.zero
readᴸ (suc x)       = L.suc (readᴸ x)
readᴸ (lim f _)     = L.lim (λ n → readᴸ (f n))
readᴸ (Ω () _)
readᴸ (up _ () _ _)

readV : V zero → T₀
readV zero     = L.zero
readV (suc v)  = L.suc (readV v)
readV (lim f)  = L.lim (λ n → readV (f n))
readV (Ω () _)

read≼V : (x : Tr zero) → readᴸ x ≼ᴸ readV (val zero x)
read≼V zero          = z≼ᴸ
read≼V (suc x)       = s≼sᴸ (read≼V x)
read≼V (lim f _)     = l≼ᴸ (λ n → ≼lᴸ n (read≼V (f n)))
read≼V (Ω () _)
read≼V (up _ () _ _)

V≼read : (x : Tr zero) → readV (val zero x) ≼ᴸ readᴸ x
V≼read zero          = z≼ᴸ
V≼read (suc x)       = s≼sᴸ (V≼read x)
V≼read (lim f _)     = l≼ᴸ (λ n → ≼lᴸ n (V≼read (f n)))
V≼read (Ω () _)
V≼read (up _ () _ _)

≼→ᴸ : {v w : V zero} → v ≼ w → readV v ≼ᴸ readV w
≼→ᴸ z≼       = z≼ᴸ
≼→ᴸ (s≼s d)  = s≼sᴸ (≼→ᴸ d)
≼→ᴸ (≼l n d) = ≼lᴸ n (≼→ᴸ d)
≼→ᴸ (l≼ h)   = l≼ᴸ (λ n → ≼→ᴸ (h n))
≼→ᴸ (≼Ω {p = ()} _ _)
≼→ᴸ (Ω≼ {p = ()} _)

≼→read : {x y : Tr zero} → val zero x ≼ val zero y → readᴸ x ≼ᴸ readᴸ y
≼→read {x} {y} d = ≼-transᴸ (read≼V x) (≼-transᴸ (≼→ᴸ d) (V≼read y))
```

参照框架的 FGH (`Level.FGH`, 与 `BTBO.FGH` 逐行同形) 在读回上与本块的 FGH 相等.

```agda
iter-cong : {A : Set} (f g : A → A) → ((a : A) → f a ≡ g a) → (a : A) (n : ℕ)
          → Ord-Ord.iter f a n ≡ iter g a n
iter-cong f g e a zero    = refl
iter-cong f g e a (suc n) = trans (cong f (iter-cong f g e a n)) (e (iter g a n))

FGH-read : (x : Tr zero) (n : ℕ) → L.FGH (readᴸ x) n ≡ FGH x n
FGH-read zero          n = refl
FGH-read (suc a)       n = iter-cong (L.FGH (readᴸ a)) (FGH a) (λ m → FGH-read a m) n n
FGH-read (lim f _)     n = FGH-read (f n) n
FGH-read (Ω () _)      n
FGH-read (up _ () _ _) n
```
