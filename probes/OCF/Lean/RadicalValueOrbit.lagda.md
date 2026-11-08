# 去掉多层程序语法的算子闭包实验

直接使用作者 BTBO 的树折叠作为原语；不经过 Q、Flr、Env 或 cap。
闭包的完整输出重新转成层号，再进入原折叠。这里没有抄写 EBO 基本列。
这是一个新实验，不声称替代已验高实例或到达 EBO。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.RadicalValueOrbit where
open import Data.Nat using (ℕ; zero; suc)
open import OCF.BTBO using (module Ord-Ord)
module S = Ord-Ord
open import OCF.Lean.CRwBase using (Cd; hz; hs; hl; LgB)
open import OCF.Lean.CRw using (leg; Lg-leg)
open import OCF.Lean.CountableCompletionRun using (inflation)
open import OCF.Lean.Fold1If using (_≤ᵛ_; ≤l)
open import OCF.Lean.Fold1Base using (≤-refl; ≤-trans)

J : S.Ord₀ → S.Ord₀
J a = S.ψ₀ (S.Ω (S.ordᴰ a))

close : (S.Ord₀ → S.Ord₀) → S.Ord₀ → S.Ord₀
close f a = S.lim (S.iter f a)

operator : ℕ → S.Ord₀ → S.Ord₀
operator zero = J
operator (suc n) a = J (close (operator n) a)

read : S.Ord₀ → Cd
read S.zero = hz
read (S.suc a) = hs (read a)
read (S.lim f) = hl (λ n → read (f n))
read (S.limᵢ () f)

raw : Cd
raw = hl (λ n → read (close (operator n) S.zero))

tree : Cd
tree = leg raw

legal : LgB tree
legal = Lg-leg raw

-- 原 BTBO 是第一整条闭包轨道，不是附加的已求值常量。
btbo-lower : read S.BTBO ≤ᵛ tree
btbo-lower = ≤-trans (≤l zero (≤-refl (read S.BTBO))) (inflation raw)
```

定理仅给原 BTBO 的完整下界及闭项合法性。更高 operator 确实再次执行
完整闭包输出的层号化与折叠，但尚无其对 EmbVV 高行的比较，也没有
证明这类单原语迭代能模拟任意高种类的反馈。不能由“闭包的闭包”命名
推断 EBO；所缺正是结构参数统一的高种类模拟与全塔下界。
