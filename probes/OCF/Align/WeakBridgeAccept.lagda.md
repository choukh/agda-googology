# 不带高度的树接上带高度的树: 验收 (有限测试)

> **验收节: 记号, 带记号的测试只在本文件.** 结论写在 [WeakBridge](WeakBridge.lagda.md). 这里的 `refl` 是有限测试, 不是证明. 比较器 `mis d w v`, `chk` 来自 [GuardWeakAccept](GuardWeakAccept.lagda.md): 逐闭包比界, 读数 `vE`.
>
> **盲区.** $\ge\omega^2$ 的界读得粗; `lim` 下标与分支 $+k$ 只取 $<w=3$, 所以 $\theta=\omega$ 的测试只进 $f\,0,f\,1,f\,2$, 跑得快不说明测得深; $\omega$ 探针只取分支 $\omega+j$, $j<v$.
>
> **这里比的是两棵树的界相等**, 比 `≲-θ` (只要 $\sqsubseteq$) 多. 比到的范围内相等.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.WeakBridgeAccept where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (true)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Free.Level
open import OCF.Align.GuardWeakAccept using (mis; code; chk; L; F; nz?; u12)
open import OCF.Align.GuardTightAccept using (dfZ; tΩ11)
open import OCF.Align.WeakBridgeMain using (T⁺; R⁺; fgh)
```

## §1 就是测过的树

```agda
same-u12 : T⁺ (natᴵ 2) ≡ u12
same-u12 = refl
```

## §2 对 `LadderInfTree` 实例 ℕ 高度 0: 穷尽, 看界

```agda
m-0 : code (mis 7 3 2 [] (T⁺ zero) (R⁺ zero)) ≡ 0
m-0 = refl

m-1 : code (mis 6 3 2 [] (T⁺ (natᴵ 1)) (R⁺ (natᴵ 1))) ≡ 0
m-1 = refl

m-2 : code (mis 6 3 2 [] (T⁺ (natᴵ 2)) (R⁺ (natᴵ 2))) ≡ 0
m-2 = refl

m-2′ : code (mis 7 3 1 [] (T⁺ (natᴵ 2)) (R⁺ (natᴵ 2))) ≡ 0
m-2′ = refl

m-ω : code (mis 7 3 2 [] (T⁺ ωᴵ) (R⁺ ωᴵ)) ≡ 0
m-ω = refl

m-ω1 : code (mis 4 3 2 [] (T⁺ (suc ωᴵ)) (R⁺ (suc ωᴵ))) ≡ 0
m-ω1 = refl
```

## §3 对照: 比较器看得见差别

```agda
ctl : nz? (code (chk [] (L 1 ∷ F ∷ L 2 ∷ []) (T⁺ (natᴵ 1)) (R⁺ (natᴵ 2)))) ≡ true
ctl = refl
```

## §4 种类: 对记号

这一条读记号 (`dfZ`, `tΩ11`), 也是审计的正对照.

```agda
k-1 : dfZ 8 2 tΩ11 (T⁺ (natᴵ 1)) ≡ nothing
k-1 = refl
```

## §5 FGH (计算, 测试)

```agda
f-2 : fgh (natᴵ 2) 0 ≡ 1
f-2 = refl

f-ω : fgh ωᴵ 0 ≡ 1
f-ω = refl
```
