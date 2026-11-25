# 内部 View: 第 0 层的值就是读回

> 验收文件 (导入参照框架 `OCF.Align.Level`, `OCF.Align.Value`). 编译定理: 第 0 层的值读进参照树后与 `YiFreshValRead.read` 结构互模拟 (`read-val`); 第 0 层值前序与参照框架的 `≼` 互相蕴涵 (`≼→ᴸ`, `≼←ᴸ`);
> 参照框架的 FGH 在读回上与 `YiViewFGH.FGH` 逐点相等 (`FGH-read`). 无前提.
> 不否定什么. 只涉及第 0 层.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiViewRead where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import OCF.Lean.YiFreshBlock
open import OCF.Lean.YiFreshValRead using (T₀; read)
import OCF.Align.Level as L
open import OCF.Align.Value using () renaming (_≼_ to _≼ᴸ_; z≼ to z≼ᴸ; s≼s to s≼sᴸ; ≼l to ≼lᴸ; l≼ to l≼ᴸ)
open import OCF.BTBO using (module Ord-Ord)
open import OCF.Lean.YiViewVal
open import OCF.Lean.YiViewFGH using (FGH)
open import OCF.Lean.YiFreshFold using (iter)
```

## 读回

```agda
readV : V zero → T₀
readV zero     = L.zero
readV (suc v)  = L.suc (readV v)
readV (lim f)  = L.lim (λ n → readV (f n))
readV (Ω () _)

read-val : (x : Tr zero) → read x L.≅ readV (val zero x)
read-val zero        = L.z≅
read-val (suc x)     = L.s≅ (read-val x)
read-val (lim f)     = L.l≅ (λ n → read-val (f n))
read-val (Ω () _)
read-val (up _ () _)
```

## 值前序互相蕴涵

```agda
≼→ᴸ : {v w : V zero} → v ≼ w → readV v ≼ᴸ readV w
≼→ᴸ z≼       = z≼ᴸ
≼→ᴸ (s≼s d)  = s≼sᴸ (≼→ᴸ d)
≼→ᴸ (≼l n d) = ≼lᴸ n (≼→ᴸ d)
≼→ᴸ (l≼ h)   = l≼ᴸ (λ n → ≼→ᴸ (h n))
≼→ᴸ (≼Ω {p = ()} _ _ _)
≼→ᴸ (Ω≼ {p = ()} _)

≼←ᴸ : (v w : V zero) → readV v ≼ᴸ readV w → v ≼ w
≼←ᴸ zero     w        d           = z≼
≼←ᴸ (suc v)  (suc w)  (s≼sᴸ d)    = s≼s (≼←ᴸ v w d)
≼←ᴸ (suc v)  (lim g)  (≼lᴸ n d)   = ≼l n (≼←ᴸ (suc v) (g n) d)
≼←ᴸ (lim f)  zero     (l≼ᴸ h)     = l≼ (λ n → ≼←ᴸ (f n) zero (h n))
≼←ᴸ (lim f)  (suc w)  (l≼ᴸ h)     = l≼ (λ n → ≼←ᴸ (f n) (suc w) (h n))
≼←ᴸ (lim f)  (lim g)  (l≼ᴸ h)     = l≼ (λ n → ≼←ᴸ (f n) (lim g) (h n))
≼←ᴸ (lim f)  (lim g)  (≼lᴸ n d)   = ≼l n (≼←ᴸ (lim f) (g n) d)
≼←ᴸ (suc v)  zero     ()
≼←ᴸ (Ω () _) w        d
≼←ᴸ v        (Ω () _) d
```

## FGH

参照框架的 FGH (`Level.FGH`, 与 `BTBO.FGH` 逐行同形) 在读回上与本块的 FGH 相等.

```agda
iter-cong : {A : Set} (f g : A → A) → ((a : A) → f a ≡ g a) → (a : A) (n : ℕ)
          → Ord-Ord.iter f a n ≡ iter g a n
iter-cong f g e a zero    = refl
iter-cong f g e a (suc n) = trans (cong f (iter-cong f g e a n)) (e (iter g a n))

FGH-read : (x : Tr zero) (n : ℕ) → L.FGH (read x) n ≡ FGH x n
FGH-read zero        n = refl
FGH-read (suc a)     n = iter-cong (L.FGH (read a)) (FGH a) (λ m → FGH-read a m) n n
FGH-read (lim f)     n = FGH-read (f n) n
FGH-read (Ω () _)    n
FGH-read (up _ () _) n
```
