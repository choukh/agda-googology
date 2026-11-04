# 严格列: 有限测试

> 入口 [TLCode](TLCode.lagda.md). **有限测试, 不是证明.** 比较器都是 `refl`.
>
> - §1 头部与 FGH 的小值: 盲区: 小值不区分强度.
> - §2 秩的小例子: 比较器看字面项. 盲区: 只看几个位置.
> - §3 输出的字面拷贝: `below b w d x y` 在 $y$ 的路径上找 $x$ 的拷贝, 路径长不超过 $b$, 每个极限看前 $w$ 项, 相等只比到深度 $d$ (每个极限看前 3 项). `true` 也不是证据: 相等是截断的. 找不到不说明没有. 盲区很大: 只测了最低的高度, 最低的几项; `y₀ ≺ y₁` 这个预算内没有找到, 也没有否定.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TLCodeTest where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level hiding (up; sim; out)
open import OCF.Free.Force using (forceᴺ)
open import OCF.Align.TLCodeShape using (end; low; blk)
open import OCF.Align.TLCodeLit
open import OCF.Align.TLCodeArith
open import OCF.Align.TLCodeCert
```

## §1 头部与 FGH

```agda
data Hd : Set where
  hz hs hl : Hd

hd : Ordᶜ zero → Hd
hd zero    = hz
hd (suc _) = hs
hd (lim _) = hl
hd _       = hz

_ : hd Tω·2ᴸ ≡ hl
_ = refl

_ : hd Tω²ᴸ ≡ hl
_ = refl

_ : hd Tω^ωᴸ ≡ hl
_ = refl

_ : hd Tε₀ᴸ ≡ hl
_ = refl

_ : fghω·2ᴸ 0 ≡ 1
_ = refl

_ : fghω²ᴸ 0 ≡ 1
_ = refl

_ : fghω^ωᴸ 0 ≡ 1
_ = refl

_ : fghε₀ᴸ 0 ≡ 1
_ = refl

_ : fghω·2ᴸ 1 ≡ 2
_ = refl
```

## §2 秩

```agda
_ : rkT Lω² (low (blk 0 end)) ≡ ωᴵ
_ = refl

_ : rkT Lω² (low (blk 1 end)) ≡ ω·ᴸ 1
_ = refl

_ : rkT Lω² end ≡ ω²ᴸ
_ = refl

_ : rkT Lε₀ (low (blk 1 end)) ≡ tw 1
_ = refl
```

## §3 输出的字面拷贝

```agda
O : Set
O = Ordᶜ zero

eq : ℕ → O → O → Bool
eq zero _ _ = true
eq (suc d) zero zero = true
eq (suc d) (suc a) (suc b) = eq d a b
eq (suc d) (lim f) (lim g) = eq d (f 0) (g 0) ∧ (eq d (f 1) (g 1) ∧ eq d (f 2) (g 2))
eq (suc d) _ _ = false

anyℕ : ℕ → (ℕ → Bool) → Bool
anyℕ zero p = false
anyℕ (suc n) p = p n ∨ anyℕ n p

below : ℕ → ℕ → ℕ → O → O → Bool
below zero w d x y = false
below (suc b) w d x (suc a) = eq d x a ∨ below b w d x a
below (suc b) w d x (lim f) = anyℕ w (λ i → below b w d x (f i))
below (suc b) w d x _ = false

pick : O → ℕ → O
pick (lim f) n = f n
pick x n = x

Y y₀ a₀ a₁ a₂ : O
Y = forceᴺ _ (Gᴸ lz end zero)
y₀ = pick Y 0
a₀ = pick y₀ 0
a₁ = pick y₀ 1
a₂ = pick y₀ 2

_ : below 5 3 3 a₀ a₁ ≡ true
_ = refl

_ : below 6 3 3 a₁ a₂ ≡ true
_ = refl
```
