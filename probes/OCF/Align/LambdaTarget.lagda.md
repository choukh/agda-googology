# ψ₀Λ 的值验收接口：阶段下界不要求阶段对齐

> **草案，未通过编译：6G 检查归档依赖时退出 251（堆耗尽）。以下实际 EBO 实例化不计为定理。已编译的通用核心见 LambdaTargetCore。**

这是验收文件，读记号，不进最终定义。`WfFsn.EBO-tree` 是 Ω-塔各站
带标签树的 ℕ-极限；这里把终点下界化成各站对**整个**候选的下界。
并不要求每一参照站落进某一候选基本列项；后者只是充分条件。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.LambdaTarget where

open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import OCF.Align.Level using (Ordᶜ; zero; lim)
open import OCF.Align.Value using (_≼_; _≈ᵛ_; l≼; ≼l; ≼-refl; ≼-trans)
open import OCF.Align.AccTreeLab using (treeᴴ)
import OCF.Align.WfFsn as R

Stage : ℕ → Ordᶜ zero
Stage n = treeᴴ (R.S.hc (R.S.p-tower n))

record Lower (candidate : Ordᶜ zero) : Set where
  field
    stage-bound : ∀ n → Stage n ≼ candidate
open Lower public

lower-sound : ∀ {candidate} → Lower candidate → R.EBO-tree ≼ candidate
lower-sound p = l≼ (stage-bound p)

lower-complete : ∀ {candidate} → R.EBO-tree ≼ candidate → Lower candidate
lower-complete p = record
  { stage-bound = λ n → ≼-trans (≼l n (≼-refl (Stage n))) p }

-- 自身实例验证前提非空；这不是记号无关的候选。
reference-instance : Lower R.EBO-tree
reference-instance = lower-complete (≼-refl R.EBO-tree)

-- 可重新索引，每一站只需在某一项取得下界，不要求同下标。
record StageCover (f : ℕ → Ordᶜ zero) : Set where
  field
    cover : ∀ n → Σ ℕ (λ k → Stage n ≼ f k)
open StageCover public

cover-sound : ∀ {f} → StageCover f → Lower (lim f)
cover-sound c = record { stage-bound = λ n →
  ≼l (proj₁ (cover c n)) (proj₂ (cover c n)) }

cover-instance : StageCover Stage
cover-instance = record { cover = λ n → n , ≼-refl (Stage n) }

record Exact (candidate : Ordᶜ zero) : Set where
  field
    lower : Lower candidate
    upper : candidate ≼ R.EBO-tree

exact-sound : ∀ {candidate} → Exact candidate → candidate ≈ᵛ R.EBO-tree
exact-sound e = Exact.upper e , lower-sound (Exact.lower e)
```

与 ψ₀Λ 的联系以仓库指定的参照定义为准：`Stage n` 的 `Lab` 定理
是 `WfFsn.ebo-lab n`，目标是其极限 `EBO-tree`。这里只新增值比较接口，
没有把 `Lab` 放进候选定义。接口既不要求世界索引，也不要求逐项基本列
一致；候选可来自其他记号无关的树侧构造。

当前缺口仍是树侧候选及 `stage-bound` 的实例，不是本文件几行极限证明。
已有 `EmbVVInstO2` 的精确值验收到固定下标量级，不能直接填充对所有
Ω-塔站的 `StageCover`。评估：先寻找跨站统一的值关系，比继续要求
候选与参照的基本列逐项对应更符合终点要求；这只是策略判断。

编译状态（2026-11-06）：实际实例化尚未通过复核。以 6G 编译时，
归档依赖 Mahlo 的检查耗尽堆，退出 251；不是类型错误，也不是通过。
独立于归档的接口核心在 `LambdaTargetCore`，已编译退出 0。
