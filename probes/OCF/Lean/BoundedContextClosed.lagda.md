# Ω 坐标界内的全自然数分量闭项

k=ls lz，坐标本身含 Ω 构造子。取合法 B=Ω、低层界 ω，所有有限坐标
up(num n) 都字面位于 B；混合树同时使用这些分量，没有截为固定分量。
这是一棵合法高层树及其重定位结果，尚不是可数折叠，也不声称值提高。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.BoundedContextClosed where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.LHRecTy
open import OCF.Lean.LHRecLay
open import OCF.Lean.LHRecFl using (up-⊲; Lg-up)
open import OCF.Lean.BoundedContextTree

num : ℕ → HB S⊥
num zero = hz
num (suc n) = hs (num n)

k : LH
k = ls lz
w : Wd (Lv k)
w = tt , hl num
legal-w : LgW (Lv k) w
legal-w = tt , ((λ n → hsuc hself) , (λ n → legal-num n))
  where
  legal-num : ∀ n → LgB (num n)
  legal-num zero = tt
  legal-num (suc n) = legal-num n

B : HB (Lv k)
B = hΩ (inj₂ tt) up
legal-B : LgB B
legal-B = (λ lw b b′ p → up-⊲ p) ,
  (λ lw b → Lg-up _ (lgB⊲ b (proj₁ lw) (proj₂ lw)))

module M = Family (ΩL k) k w B

member : ℕ → M.I
member n = up (num n) , hLim (hlim n hself) hself

input : HB M.S
input = M.mixed member
legal-input : LgB input
legal-input = M.mixed-legal member

output : HB M.T
output = M.relocated member
legal-output : LgB output
legal-output = M.relocated-legal member
```

界 B 的 Ω 分支坐标全在公共低界 ω 下，所有 n 共用同一个合法世界。
这里搬运的是原本就带 B 支撑的分量；不构造任意裸坐标的 B 支撑证明。
下一义务是把指标种类的回灌与升 B 接上，及相应合法性和序数值定理。
