# 带表的那一行: 一般底上, 经 ℕ 极限孩子朝第 0 层的折叠不低于 BTBO

> 验收文件 (F2 对照块 [YiVTFold](YiVTFold.lagda.md) 上, 读记号), 不进成品. 编译定理 (新写): 层号 `tw 1` 上的底 B 满足 `OKB` 与 `Start` 时, Ω 树朝第 0 层、经字面是 ℕ 极限的孩子 c 的折叠, 对一切路径 w 与起点 b, 不低于 BTBO 的参照 (`hiΩ`).
> 做法: 链点与 `YiVTEBBtbo.Btbo` 的相同 (`chainV`, `emb`, 原样引用); 各行不低于标准底的 `G (pt k)` ([YiVTEmb](YiVTEmb.lagda.md) 的 `rowG`), 再用 `lower-↑`.
> 用处: 原 F2 上 `YiEVEnd.hi0` 靠回退行的输出形状 `_ + ι zero (twᶜ 1)`, 带表时那一处走条目, 改由这里给出孩子 c₁ 的底的 `Hi`. 不给出孩子字面是零或后继的情形.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTHi where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; inb; Ev-tw; Rt-tw)
open import OCF.Lean.YiVTFold
open import OCF.Lean.YiLSRead using (read; limcum≽)
open import OCF.Lean.YiVTLSFold using (OKB)
open import OCF.Lean.YiVTLSTw1 using (h₁; lower-↑)
open import OCF.Lean.YiVTT2Frame using (IsLim)
open import OCF.Lean.YiVTEBBtbo using (Start; module Chain; module Lemmas; module Btbo)
open import OCF.Lean.YiVTEmb using (rowT; rowG)
open import OCF.Align.BTBOFullEmb using (Ψ-emb)
open import OCF.Align.Value using (_≼_; ≼-trans; l≼)
open import OCF.Align.YiBtValBT using (module D)

module HiΩ (B : Base (tw 1)) (ok : OKB (tw 1) B) (st : Start B) where
  open Chain B using (pt)
  open Btbo B ok st using (emb; chainV)

  hiΩ : (c : Tr zero) → IsLim c → (w : zero ≤ h₁ c) (b : Tr zero) (nb : zero ⊢ zero ◃ b)
    → D.BTBOᴵ ≼ read (ψs (tw 1) (Ev-tw 1) (Rt-tw 1) B zero (inb c w) b nb (Ωt (tw 1)))
  hiΩ c lc w b nb =
    kp-ind (tw 1) (Ev-tw 1) (Rt-tw 1) (inj₁ (inj₁ tt)) (inb c w) (λ X → D.BTBOᴵ ≼ read X)
      {K = λ q cv → Ω q (λ z → rowT B c w b nb (cv z))} (λ ())
      (l≼ (λ n → ≼-trans (Ψ-emb (emb n (proj₁ (chainV n)) (proj₂ (chainV n))))
        (limcum≽ (λ k → rowT B c w b nb (pt k))
          (λ k → nzs (tw 1) (Ev-tw 1) (Rt-tw 1) B zero (inb c w) b nb (up zero (pt k) (Ωt (h₁ (pt k))) (Ωt-nz (h₁ (pt k)))))
          (suc (proj₁ (chainV n)))
          (≼-trans (lower-↑ (pt (suc (proj₁ (chainV n))))) (rowG B c lc w b nb (pt (suc (proj₁ (chainV n)))))))))
```
