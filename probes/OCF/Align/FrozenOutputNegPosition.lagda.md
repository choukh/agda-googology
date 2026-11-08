# 第一位置支持不能替代值单调

本篇只校准输出比较所需的分支条件，不否定 FrozenOutputIf 的 Generated 比较。
坐标变换 J 保持第一位置与合法性，却不保持值序。反例两个合法坐标有字面公共界，
所以差距不是由裸下标比较造成。J 并非实际生成族中的算子。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenOutputNegPosition where

open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; ≤s; l≤; ≤l)

J : Cd → Cd
J hz = hz
J (hs a) = hs (J a)
J (hl f) = hs (hl (λ n → J (f n)))

position : ∀ {a b w} → a ⊲[ w ] b → J a ⊲[ w ] J b
position hself = hself
position (hsuc p) = hsuc (position p)
position (hlim n p) = hsuc (hlim n (position p))

legal : ∀ a → LgB a → LgB (J a)
legal hz l = tt
legal (hs a) l = legal a l
legal (hl f) (s , l) = (λ n → position (s n)) , (λ n → legal (f n) (l n))

a b bound : Cd
a = hl (λ _ → hs hz)
b = hs hz
bound = a
la : LgB a
la = (λ n → hself) , (λ n → tt)
lb : LgB b
lb = tt
pa : a ⊲ bound
pa = hself
pb : b ⊲ bound
pb = hlim 0 hself

value-forward : a ≤ᵛ b
value-forward = l≤ (λ n → s≤s z≤)
value-back : b ≤ᵛ a
value-back = ≤l 0 (s≤s z≤)

one-not-zero : b ≤ᵛ hz → ⊥
one-not-zero ()
lim-not-zero : a ≤ᵛ hz → ⊥
lim-not-zero (l≤ p) = one-not-zero (p 0)
image-not-zero : J a ≤ᵛ hz → ⊥
image-not-zero ()
image-not-below : J a ≤ᵛ J b → ⊥
image-not-below (s≤s p) = lim-not-zero p
image-not-below (≤s p) = image-not-zero p
```

因此仅有沿第一位置的支持律，无法免费使用“输入值序推出输出值序”。
上面的反例同时给出了合法性、两个方向的值序以及字面公共界的实例。
实际冻结输出是否有终点下界仍未判定：可以针对 Generated 另证更强支持，
也可直接证实际输出的错位覆盖；本定理都没有排除。

翻译账：J 只是值验收的反例坐标变换，不进入候选树或闭项证书；无记号规则。
