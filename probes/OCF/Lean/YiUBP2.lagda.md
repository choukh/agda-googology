# YiUB 链上：`FoldB`、`P2₂` 与 BTBO 下界归约到链点上的 `Str`

**验收文件，档位：编译定理 (m = 0) 与条件定理。** `foldB : ∀ m → Str (co (pts m)) (lw (pts m)) → FoldB m` (链点上的折叠与它自己层号上的参照两向)，m = 0 无条件 (`foldB₀`)；
接 [YiFlatChain](YiFlatChain.lagda.md) 的 `p2-from-fold` 与 [YiEmb2](YiEmb2.lagda.md) 的 `btbo-cond₂`：`btbo-str : StrChain → D.BTBOᴵ ≼ read T₃`，n = 1 的实例 `p2₂-1`、`γ₂-str` 只要 `Str (co (pts 1))`。
`StrChain` 未证：它含链点里每个后继子树上的 `SucP` (第 2 层起) 与每个极限子树上相邻两支的结构前驱。不否定什么。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiUBP2 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Product.Base using (_×_; _,_)
open import OCF.Lean.YiLeanTw3 using (pts; obs; T₃; module Pt)
open Pt using (co; lw)
open import OCF.Lean.YiLeanAccFin using (read)
open import OCF.Lean.YiLeanValFin using (κ)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_)
open import OCF.Align.YiVmConExact using (_≼ˣ_)
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Lean.YiEmb2 using (P2₂; p2₂-0; btbo-cond₂; γ₂-cond)
open import OCF.Lean.YiFlatChain using (FoldB; step₂; p2-from-fold)
open import OCF.Lean.YiUBRed using (Str; FOLD2)
```

```agda
foldB : ∀ m → Str (co (pts m)) (lw (pts m)) → FoldB m
foldB m s = FOLD2 (co (pts m)) (lw (pts m)) s

foldB₀ : FoldB 0
foldB₀ = FOLD2 (co (pts 0)) (lw (pts 0)) tt

StrChain : Set
StrChain = ∀ n → Str (co (pts (suc n))) (lw (pts (suc n)))

p2₂-str : StrChain → P2₂
p2₂-str str = p2-from-fold (λ n → foldB (suc n) (str n))

btbo-str : StrChain → D.BTBOᴵ ≼ read T₃
btbo-str str = btbo-cond₂ (p2₂-str str)
```

n = 1：`P2₂` 的第 1 项，以及参照第 2 项与第 2 个链点两向 (经 `γ₂-cond`)。

```agda
p2₂-1 : Str (co (pts 1)) (lw (pts 1)) →
  (L.ψ⁰ (L.Ω (κ 1)) ≼ˣ read (co (pts 2))) × (read (co (pts 2)) ≼ˣ L.ψ⁰ (L.Ω (κ 1)))
p2₂-1 s = step₂ 0 p2₂-0 (foldB 1 s)

γ₂-str : Str (co (pts 1)) (lw (pts 1)) →
  (D.γ 2 ≼ˣ read (co (pts 2))) × (read (co (pts 2)) ≼ˣ D.γ 2)
γ₂-str s = γ₂-cond (p2₂-1 s)
```
