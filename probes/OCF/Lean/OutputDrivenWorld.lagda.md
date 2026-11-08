# 实际输出生成整底世界，并在新世界继续运行

固定旧底 `Sb n` 的合法世界，每个槽 `m` 的输出来自完整
`XSof(Tw(Sb n)m)` 源；原 `m` 可以不合法，因为它仅选树种类结构，
实际比较界是该结构内合法的 `1`。不把一个有界目标族补成全族。

各轮代表坐标取当前槽的实际界 (`topT`)，不是始终取 `bot`。
输出经富合法化只用于新世界的界；运行源仍是原完整高地板。
每轮更新的是 `Wd(Sb(suc n))`，不是把局部 step 世界冒称底世界。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.OutputDrivenWorld where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw)
open import OCF.Lean.ThirdTw using (Sb; fl; topT)
import OCF.Lean.ThirdRichLegBuild as Rich
import OCF.Lean.ThirdRichWorldSections as Frames
import OCF.Lean.OutputDrivenBuild as Build
import OCF.Lean.OutputDrivenTop as Top

module Driven (n : ℕ) (u : Wd (Sb n)) (lu : LgW (Sb n) u) where
  U = Sb n
  module F = Frames.Frames n u lu

  record State : Set where
    field
      index : HB U
      index-legal : LgB index
      bounds : F.Section
      bounds-legal : ∀ m → LgB (bounds m)
  open State public

  output : (s : State) → F.Section
  output s m = Build.Whole.output (Tw U m)
    (F.world (bounds s) m) (F.world-legal (bounds s) (bounds-legal s) m)
    (topT U (fl n) m) (Rich.legT n m) (Rich.Lg-legT n m)
    (Top.topT n m (F.world (bounds s) m))
    (Top.topT-bd n m (F.world (bounds s) m))

  next : State → State
  next s = record
    { index = hs (index s ⊞ Rich.legS n (output s hz))
    ; index-legal = Lg-⊞ _ _ (index-legal s) (Rich.Lg-legS n (output s hz))
    ; bounds = F.next (bounds s) (output s)
    ; bounds-legal = λ m → F.feedback-legal (bounds s) (bounds-legal s) (output s) m }

  world : State → Wd (Sb (suc n))
  world s = F.full (index s) (bounds s)

  legal : ∀ s → LgW (Sb (suc n)) (world s)
  legal s = F.full-legal (index s) (index-legal s) (bounds s) (bounds-legal s)

  grows : ∀ s → _≤w_ (Sb (suc n)) (world s) (world (next s))
  grows s (inj₁ _) = Frames.rfS n u , hsuc (⊞-fst (index s) (Rich.legS n (output s hz)))
  grows s (inj₂ c) = F.grow (bounds s) (output s) (hs c)

  initial : State
  initial = record { index = hz ; index-legal = tt ; bounds = λ _ → hz ; bounds-legal = λ _ → tt }

  orbit : ℕ → State
  orbit zero = initial
  orbit (suc r) = next (orbit r)

  feedback-admitted : ∀ s m → Bd (Sb (suc n)) (inj₂ m , inj₂ tt)
    (F.feedback (bounds s) (output s) m) (world (next s))
  feedback-admitted s m = F.full-admitted (index (next s)) (bounds s) (output s) m
```

`orbit` 每次重新调用同一个完整高源程序，但环境是上次实际输出更新的
全底世界。此处没有声称把上次高树输入证书搬到新世界；源地板的路径证书
由通用定理重新实填。尚存的 `Er` 与旧指标取枝由原运行器决定，值代价另审。
