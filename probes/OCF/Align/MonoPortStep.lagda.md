# 单调的移植 (四): 一切后继高度上 `MonoStep` 就是一对链的比较

> 不含记号. 入口 [MonoPort](MonoPort.lagda.md). 对一切合法的 $\Lambda$, 实例 $\Lambda+1$ 里的 `MonoStep (hs Λ)` **字面就是**两条链的极限的比较 (`step≡`, `refl`): 链的点是层 $\Lambda$ 上的差树, 链的动作只看状态 (`StepA`), 两边只差起点 (底 $1$ 对 $b_0$, 状态 `Yᴸ` 对 `Yʳ`). 这是对结构参数 $\Lambda$ 的一步陈述: 新用到的字段只有 `hs` 的节点 `ss hself` (`rkT` 对一切 $\Lambda$ 计算出 `rise`: `cmpH` 的第一句).
>
> $\Lambda=0$ 时链的点是第 0 层的树, [MonoPortZero](MonoPortZero.lagda.md) 的 `chain` 给出 `ChainLe hz` (`mono₁′`, 与 [MonoPortOne](MonoPortOne.lagda.md) 的 `mono₁` 是同一个证明). $\Lambda\ge1$ 时链的点是层 $\Lambda$ 上**带节点**的树, 下一个点是上一个点的折叠在层 $\Lambda$ 目标上的读数: 要的是层 $\Lambda$ 上一个值关系, 它 (a) 让第 0 层的读数单调, (b) 对折叠在层 $\Lambda$ 上的输出封闭. 本组没有做 (b), 见入口.
>
> 全文 `--safe --without-K --lossy-unification`, 无公设, 无洞, 无停机或正性编译指示.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.MonoPortStep where

open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Product using (_×_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Align.CumReadCF using (A)
import OCF.Align.CumReadCF as C
open import OCF.Align.TLRuleSpec using (_≤_)
open import OCF.Align.HtFeedTree using (H; LgH; D; hz; hs; hsuc; hself; _⊲[_]_; accL; nl; sum)
open import OCF.Align.HtFeedClosed using (module At; one)
open import OCF.Align.HtCrossInst using (module Hs; b₀)
import OCF.Align.MonoPortOne as One

module Ch (Λ : H) (l : LgH Λ) where
  module Q = At (hs Λ) l

  hk : Λ ⊲[ one ] hs Λ
  hk = hsuc hself

  -- 链的动作: 分支是常数 n1, 归约到一步 Step, 只看状态
  StepA : Q.Ig Λ one
  StepA p lW′ z Y′ = Q.Step Y′

  CC : Q.St one → ℕ → D Λ one × (D Λ one × Q.St one)
  CC Y = Q.Chn (accL Λ) hk tt StepA Y

  segs : Q.St one → ℕ → D hz one
  segs Y n = Q.yc (Q.Run (accL Λ) (proj₁ (proj₂ (CC Y n))) C.self tt hk StepA (proj₁ (CC Y n)) (proj₂ (proj₂ (CC Y n)))) (Q.τ₀ {one} tt)

  Yᴸ Yʳ₀ Yʳ : Q.St one
  Yᴸ = Q._⊕⟨_⟩_ Q.Y₀ tt (Q.Step Q.Y₀)
  Yʳ₀ = Q._⊕⟨_⟩_ (Q._⊕⟨_⟩_ Q.Y₀ tt (Q.Step Q.Y₀)) tt Q.zeroD
  Yʳ = Q._⊕⟨_⟩_ Yʳ₀ tt (Q.Step Yʳ₀)

  bᴸ bʳ : A
  bᴸ = sum one (Q.yc (Q.Step Q.Y₀) (Q.τ₀ {one} tt))
  bʳ = sum b₀ (Q.yc (Q.Step Yʳ₀) (Q.τ₀ {one} tt))

  ChainLe : Set
  ChainLe = sum bᴸ (nl (segs Yᴸ)) ≤ sum bʳ (nl (segs Yʳ))

  step≡ : Hs.MonoStep (hs Λ) l ≡ ChainLe
  step≡ = refl

-- Λ = 0: 第 0 层的链
mono₁′ : Hs.MonoStep (hs hz) tt
mono₁′ = subst (λ X → X) (sym (Ch.step≡ hz tt)) One.mono₁
```
