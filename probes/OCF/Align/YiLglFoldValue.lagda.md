# 已知常输出的局部替代：返回常值体

只回答本轮反例能否不用判定避开。若构造已经知道每支输出都是 W，
可以直接返回 W，而不是构造 lim constW；这里证明该具体替代严格合法且同值。
不改 gt 规则，不判定任意函数是否常值，也不提供完整 ψ 或通用优化器。
值验收只读没有 Ω 结点的可数输出；没有把高层树送进固定可数类型。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLglFoldValue where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_×_; _,_)
import OCF.Align.YiLglCore as F
import OCF.Align.YiLglVal as V
open import OCF.Align.YiLglStrict using (Legalˢ)
open import OCF.Align.YiLglFoldIf using (copies; successor; successor-legal)
open import OCF.Align.CumReadCF using (A; azero; asuc; alim)
open import OCF.Align.TLRuleSpec using (_≤_; ≤-refl; l≤; ≤l)

data Countable : F.LF → Set where
  cz : Countable F.zero
  cs : ∀ {x} → Countable x → Countable (F.suc x)
  cl : ∀ {f} → (∀ n → Countable (f n)) → Countable (F.lim f)

read : ∀ {x} → Countable x → A
read cz = azero
read (cs c) = asuc (read c)
read (cl c) = alim (λ n → read (c n))

add-countable : ∀ {a b} → Countable a → Countable b → Countable (V._+ᴸ_ a b)
add-countable a cz = a
add-countable a (cs b) = cs (add-countable a b)
add-countable a (cl b) = cl (λ n → add-countable a (b n))

copies-countable : ∀ x → Countable x → ∀ n → Countable (copies x n)
copies-countable x c zero = cz
copies-countable x c (suc n) = add-countable c (copies-countable x c n)

one W paused replacement : F.LF
one = F.suc F.zero
W = successor one
paused = F.lim (λ _ → W)
replacement = W

W-countable : Countable W
W-countable = cl (copies-countable one (cs cz))

paused-countable : Countable paused
paused-countable = cl (λ _ → W-countable)

replacement-legal : Legalˢ replacement
replacement-legal = successor-legal one tt tt

paused≤replacement : read paused-countable ≤ read W-countable
paused≤replacement = l≤ (λ _ → ≤-refl (read W-countable))

replacement≤paused : read W-countable ≤ read paused-countable
replacement≤paused = ≤l zero (≤-refl (read W-countable))

same-value : (read paused-countable ≤ read W-countable) ×
  (read W-countable ≤ read paused-countable)
same-value = paused≤replacement , replacement≤paused
```

这是所给两棵可数输出在既有 A 值前序中的双向验收，不是全 LF 的解释，
也不是原高层源值与某完整 ψ 的值定理。返回 W 不要求链起点移位或抽取子列。
一般程序如何在构造时得到“常输出”证据仍未实现；本篇不据此宣称所有停顿都能消掉。
