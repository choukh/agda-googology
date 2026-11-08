# 冻结 sup 更新的合法闭项

沿用 Fold1 的地板与初始世界，交出真正使用 sup 层的冻结折叠闭项。
没有赋予其 ψ 读法，也没有声称与旧闭项同值。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.SupCollapseClosed where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (top)
open import OCF.Lean.Fold1Base using (Wi; lgWi; lg-top*; lgB⊥)
open import OCF.Lean.SupCollapseFrozen using (Φ; Φ-lg)

T : (m : Cd) → LgB m → Cd
T m lm = Φ m lm hz (z⊲ᴮ m) (Wi m) (top m)
legal-T : ∀ m lm → LgB (T m lm)
legal-T m lm = lgB⊥ _ (Φ-lg m lm hz (z⊲ᴮ m) (lgWi m) (top m) (lg-top* m))

num : ℕ → Cd
num zero = hz
num (suc n) = hs (num n)
legal-num : ∀ n → LgB (num n)
legal-num zero = tt
legal-num (suc n) = legal-num n
ω : Cd
ω = hl num
legal-ω : LgB ω
legal-ω = (λ n → hsuc hself) , legal-num

Tω : Cd
Tω = T ω legal-ω
legal-Tω : LgB Tω
legal-Tω = legal-T ω legal-ω

-- 次序与 Fold1.FGH 相同；直接在本闭项的可数树上递归。
iter : (ℕ → ℕ) → ℕ → ℕ → ℕ
iter f x zero = x
iter f x (suc n) = f (iter f x n)
FGH : Cd → ℕ → ℕ
FGH hz n = suc n
FGH (hs a) n = iter (FGH a) n n
FGH (hl f) n = FGH (f n) n
FGH (hΩ () _) n
fghω : ℕ → ℕ
fghω = FGH Tω
```

翻译账：无新树节点；地板和层号沿用 Fold1。Frozen 是原证明的实验
复制，不是压缩；新增整份折叠脚手架只用于检验更新对值的实际作用。
第 4 层没有倒改前 3 层，旧定义未动。本文件尚无值定理。
