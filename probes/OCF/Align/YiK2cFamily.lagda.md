# K2′ 续做：任意有限层嵌套与 Ω₁·ω 的合法闭输出

本篇沿用上轮的加法链，把固定 Ω₁ 前缀推广为任意合法正输出种子。
定义有限和 `S(n)=Ω₁·(n+1)`，再取 `lim S`。所有 lc 层号都字面为 zero。
这是闭族与其独立递归折叠，**不是全部 Only0 Source 上的 ψ**；
不能用这个子族冒充主任务的完整递归器。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiK2cFamily where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_,_; proj₁)
open import Data.Sum.Base using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.LevelFixCore as F
import OCF.Align.LevelFixVal as V
import OCF.Align.YiCarry as C
import OCF.Align.YiK2Base as A
import OCF.Align.YiK2bBase as B
import OCF.Align.YiK2bNested as N
open import OCF.Align.YiRegBase using (Reg)
open import OCF.Align.YiDispBase using (cp-edge; e-first)
open F using (module G)

prefix-reg : ∀ x → Reg x → ∀ a → Reg (x V.+ᴸ V.up F.zero a)
prefix-reg x rx G.zero = rx
prefix-reg x rx (G.suc a) = prefix-reg x rx a
prefix-reg x rx (G.lim f) = λ n → prefix-reg x rx (f n)
prefix-reg x rx (G.lc () c t g)
prefix-reg x rx (G.em () a)
prefix-reg x rx G.top = rx

prefix-carry : ∀ x → C.Carry x → ∀ a → C.Carry (x V.+ᴸ V.up F.zero a)
prefix-carry x rx G.zero = rx
prefix-carry x rx (G.suc a) = prefix-carry x rx a
prefix-carry x rx (G.lim f) = λ n → prefix-carry x rx (f n)
prefix-carry x rx (G.lc () c t g)
prefix-carry x rx (G.em () a)
prefix-carry x rx G.top = rx

module Append (seed : B.Output) where

  out : C.PointB F.zero A.one → B.Output
  out p = B.output (N.tail (B.raw seed) (C.coordinate p))
    (N.tail-legal (B.raw seed) (B.legal seed) (B.positive seed)
      (C.coordinate p) (proj₁ (C.bounds p)))
    (N.tail-positive (B.raw seed) (B.positive seed) (C.coordinate p))

  mono : ∀ p q → F.Gd F.zero (C.coordinate p) (C.coordinate q) →
    F.Cp F.zero (B.raw (out p)) (B.raw (out q))
  mono p q d = N.tail-cp (B.raw seed) (proj₁ d)

  module Chain = B.AddChain A.one out mono

  initial : C.PointB F.zero A.one
  initial = C.start0-B C.tw2-carry

  result : B.Output
  result = Chain.collapse initial

  seed-position : F.Cp F.zero (B.raw seed) (B.raw result)
  seed-position = inj₂ (zero , inj₂ (1 , inj₁ refl))

  row : B.raw result ≡ G.lim (λ n →
    N.tail (B.raw seed) (C.coordinate (Chain.chain initial n)))
  row = refl

  additive : ∀ p → C.coordinate (Chain.next p) ≡
    A._+ʳ_ (C.coordinate p) (N.tail (B.raw seed) (C.coordinate p))
  additive p = refl
```

初项的坐标、守卫与 LglB 固定为原 start0-B 的规范 1。
下方另外证明：对有限和每一项，取其自身 Carry 调 start0-B，也给相同点包。

```agda
sum : ℕ → F.LF
sum zero = V.Ω₁
sum (suc n) = sum n V.+ᴸ V.Ω₁

sum-step : ∀ n → V.CP (sum n) (sum (suc n))
sum-step n = V.fst (V.suc V.self)

sum-first-one : ∀ n → V.CP (F.suc F.zero) (F.suc (sum n))
sum-first-one zero = V.suc (V.fst V.self)
sum-first-one (suc n) = V.suc (V.fst (sum-first-one n))

sum-only : ∀ n → B.Only0 (sum n)
sum-only zero = N.Ω₁-only
sum-only (suc n) = sum-only n ,
  (λ η e → B.prefix-only (sum n) (sum-only n) η)

sum-legal : ∀ n → V.Legal (sum n)
sum-legal zero = V.Legal-tw 2
sum-legal (suc n) = V.Legal-add (sum n) V.Ω₁ (sum-legal n) (V.Legal-tw 2)

sum-reg : ∀ n → Reg (sum n)
sum-reg zero = C.forget C.tw2-carry
sum-reg (suc n) = cp-edge (sum-first-one n) e-first , tt , sum-reg n ,
  (λ η e → prefix-reg (sum n) (sum-reg n) η)

sum-carry : ∀ n → C.Carry (sum n)
sum-carry zero = C.tw2-carry
sum-carry (suc n) = sum-reg (suc n) , tt , sum-carry n ,
  (λ η e b → prefix-carry (sum n) (sum-carry n) η)

sum-source : ℕ → B.Source0
sum-source n = B.source0 (C.source (sum n) (sum-carry n) (sum-legal n)) (sum-only n)

fold : ℕ → B.Output
fold zero = N.inner
fold (suc n) = Append.result (fold n)

fold-step : ∀ n → F.Cp F.zero (B.raw (fold n)) (B.raw (fold (suc n)))
fold-step n = Append.seed-position (fold n)

fold-start : ∀ n →
  C.start0-B (sum-carry (suc n)) ≡ Append.initial (fold n)
fold-start n = refl

second-is-previous-input : sum 1 ≡ N.nested
second-is-previous-input = refl

second-is-previous-output : B.raw (fold 1) ≡ B.raw N.closed
second-is-previous-output = refl

limit : F.LF
limit = F.lim sum

limit-source : B.Source0
limit-source = B.source0 (C.source limit sum-carry (sum-step , sum-legal)) sum-only

closed : B.Output
closed = B.lim-output fold fold-step

closed-B : C.LglB F.zero (B.raw closed)
closed-B = B.output-B closed

closed-legal : V.Legal (V.up F.zero (B.raw closed))
closed-legal = B.output-legal closed

closed-positive : F.Dn F.zero G.zero (B.raw closed)
closed-positive = B.positive closed

closed-row : B.raw closed ≡ G.lim (λ n → B.raw (fold n))
closed-row = refl
```

每个 Append.next 的返回类型都保存原守卫与 LglB；其 Chain.chain-grow 是
真正由加法生成的增长，不是额外 Grow 假设。有限和、极限及所有分支的
Carry／Legal／Only0 均由结构递归交出。
