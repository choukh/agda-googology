# 实际第二分量的读取位置

这是实际地板第二分量的展开与世界读取定理，不是序数同值定理。
外层回灌只写第二分量的高界；折叠分支已经出现第二分量的旧 Ω，
它读的是低界。因此只消去最高种类的依赖还不足以比较完整轨道。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenValueSecond where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (Lv; top; ΣT)
open import OCF.Lean.Fold1Base using (Wi; updAt)
import OCF.Lean.Fold1Fold as O
import OCF.Lean.SupCollapseFrozen as N
import OCF.Lean.SupCollapseClosed as C

W : Wd (Lv C.ω)
W = Wi C.ω

prefix : HB (Lv C.ω)
prefix = ΣT S⊥ hz C.num 1

branch : HB (step S⊥) → HB (Lv C.ω)
branch c = prefix ⊞ ι 2 (up c)

writeHigh : Wd (Lv C.ω) → HB (step S⊥) → Wd (Lv C.ω)
writeHigh w e = updAt w 2 (proj₁ (w 2) , e)

OX : Wd (Lv C.ω) → HB (step S⊥) → HB (step S⊥)
OX w c = O.Φ C.ω C.legal-ω (hs hz) (hlim 2 (hsuc hself)) w (branch c)
OT : Wd (Lv C.ω) → HB (step S⊥) → Cd
OT w c = O.Φ C.ω C.legal-ω hz (z⊲ᴮ C.ω) w (branch c)
NX : Wd (Lv C.ω) → HB (step S⊥) → HB (step S⊥)
NX w c = N.Φ C.ω C.legal-ω (hs hz) (hlim 2 (hsuc hself)) w (branch c)
NT : Wd (Lv C.ω) → HB (step S⊥) → Cd
NT w c = N.Φ C.ω C.legal-ω hz (z⊲ᴮ C.ω) w (branch c)

module Old = O.Col _⊞_ _⊞_ W (top (hs hz)) writeHigh OX OT
module Frozen = N.Col _⊞_ _⊞_ W (top (hs hz)) (λ w e → w) NX NT

old-second : O.Φ C.ω C.legal-ω hz (z⊲ᴮ C.ω) W
  (ΣT S⊥ hz C.num 2) ≡ hl Old.oO
old-second = refl
frozen-second : N.Φ C.ω C.legal-ω hz (z⊲ᴮ C.ω) W
  (ΣT S⊥ hz C.num 2) ≡ hl Frozen.oO
frozen-second = refl

old-high : ∀ n → proj₂ (Old.cw (suc n) 2) ≡ Old.ce (suc n)
old-high n = refl
old-low : ∀ n → proj₂ (proj₁ (Old.cw n 2)) ≡ hz
old-low zero = refl
old-low (suc n) = refl
frozen-high : ∀ n → proj₂ (Frozen.cw n 2) ≡ top (hs hz)
frozen-high zero = refl
frozen-high (suc n) = refl
frozen-low : ∀ n → proj₂ (proj₁ (Frozen.cw n 2)) ≡ hz
frozen-low zero = refl
frozen-low (suc n) = refl

-- 实际首坐标输入，不是另造的常值分支。
first-input : branch (top (hs hz)) ≡
  hΩ (2 , inj₁ (inj₂ tt)) (λ c → prefix ⊞ ι 2 (up (up c)))
first-input = refl

-- 第二分量旧 Ω 的原更新：保留高界，低界写入可数轨道。
writeLow : Wd (Lv C.ω) → Cd → Wd (Lv C.ω)
writeLow w e = updAt w 2 ((proj₁ (proj₁ (w 2)) , e) , proj₂ (w 2))
low-after-write : ∀ w e → proj₂ (proj₁ (writeLow w e 2)) ≡ e
low-after-write w e = refl
high-after-low-write : ∀ w e → proj₂ (writeLow w e 2) ≡ proj₂ (w 2)
high-after-low-write w e = refl
```

所有等式都来自实际折叠的定义规约。它们给出精确障碍：
首坐标已经触发旧 Ω；外层低界虽然恒为零，旧 Ω 内部的原更新会写入可数树，
冻结版仍不写。要获得值比较，还须比较该内层回灌在累加前缀上的作用。
这里没有证明其作用可忽略，也没有证明两个第二分量不同值。
