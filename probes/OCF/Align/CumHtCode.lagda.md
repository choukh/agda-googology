# 序数高度的世界: 码进世界

> 不含记号, 不含累加的链. 结论写在 [CumHt](CumHt.lagda.md). `cA c`: 码 `c` ([LadderOrdPos](LadderOrdPos.lagda.md) 的 `Code`) 读成字面合法的下标. `cl g` 的读法是 $\sum_j(g_j+1)$, 与 `plus` 同形, 这是码自己的累积和, 不是折叠的累加链. `rkA`: 位置读成下标, 是字面的第一位置 (`rk⊲`). 闭包定理不要码, 只要 `Gw`; 这一篇只是说码都进得来.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.CumHtCode where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_; proj₁; proj₂; _×_)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim; _⊲_; Lg; ⊲-tr; z⊲)
import OCF.Align.CumReadCF as C
open import OCF.Align.CumHtBase
open import OCF.Align.LadderOrdPos using (Code; cz; cs; cl; Pos; end; low; blk)

plusA : A → Code → A
SbA   : A → (ℕ → Code) → ℕ → A
plusA b cz     = b
plusA b (cs c) = asuc (plusA b c)
plusA b (cl g) = alim (SbA b g)
SbA b g zero    = b
SbA b g (suc i) = asuc (plusA (SbA b g i) (g i))

plus-fst : ∀ b c → b ⊲ plusA b c
plus-fst b cz = C.self
plus-fst b (cs c) = C.suc (plus-fst b c)
plus-fst b (cl g) = C.lim 0 C.self

Sb-step : ∀ b g i → SbA b g i ⊲ SbA b g (suc i)
Sb-step b g i = C.suc (plus-fst (SbA b g i) (g i))

Lg-plus : ∀ b c → Lg b → Lg (plusA b c)
Lg-Sb   : ∀ b g → Lg b → ∀ i → Lg (SbA b g i)
Lg-plus b cz w = w
Lg-plus b (cs c) w = Lg-plus b c w
Lg-plus b (cl g) w = Sb-step b g , Lg-Sb b g w
Lg-Sb b g w zero = w
Lg-Sb b g w (suc i) = Lg-plus (SbA b g i) (g i) (Lg-Sb b g w i)

cA : Code → A
cA = plusA azero

Lg-cA : ∀ c → Lg (cA c)
Lg-cA c = Lg-plus azero c tt

-- 位置读成下标
rkA : ∀ {c} → A → Pos c → A
rkA b (end {c}) = plusA b c
rkA b (low p) = rkA b p
rkA {cl g} b (blk j p) = rkA (SbA b g j) p

rk⊲ : ∀ {c} b (p : Pos (cs c)) → rkA b p ⊲ asuc (plusA b c)
rk⊲l : ∀ {c} b (p : Pos c) → rkA b p ⊲ plusA b c
rk⊲ b end = C.suc C.self
rk⊲ b (low p) = C.suc (rk⊲l b p)
rk⊲l b end = C.suc C.self
rk⊲l b (low p) = C.suc (rk⊲l b p)
rk⊲l {cl g} b (blk j p) = C.lim (suc j) (rk⊲ (SbA b g j) p)

-- 世界: 码的后继. 不低于 1
-- 世界: 码的后继. 不低于 1
one⊲ : ∀ b c → one ⊲ asuc b → one ⊲ asuc (plusA b c)
one⊲S : ∀ b g → one ⊲ asuc b → ∀ i → one ⊲ asuc (SbA b g i)
one⊲ b cz e = e
one⊲ b (cs c) e = C.suc (one⊲ b c e)
one⊲ b (cl g) e = C.suc (C.lim 1 (one⊲ (SbA b g 0) (g 0) e))
one⊲S b g e zero = e
one⊲S b g e (suc i) = C.suc (one⊲ (SbA b g i) (g i) (one⊲S b g e i))

W : Code → A
W c = asuc (cA c)

gW : ∀ c → Gw (W c)
gW c = gw (Lg-cA c) (one⊲ azero c C.self)

-- 位置 p 的第 0 层在世界 W c 之下
e⊲W : ∀ c (p : Pos (cs c)) → D⊲ (rkA azero p) azero (W c)
e⊲W c p = rk⊲ azero p ,ᵈ z⊲ (W c)
```
