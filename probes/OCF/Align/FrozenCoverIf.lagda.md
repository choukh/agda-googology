# 显式种子前缀的错位覆盖接口

这是一条验收变换，不改已有树或折叠。D 在每个 Ω 分支前显式插入其坐标，
用来检验冻结折叠能否模拟动态种子。它尚未证明保持合法性，也尚未证明
D c 被实际冻结外层轨道覆盖；模型值覆盖不能替代这两项。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.FrozenCoverIf where
open import Data.Nat using (ℕ)
open import Data.Sum using (inj₁; inj₂)
open import Data.Unit using (tt)
open import OCF.Lean.CRwBase
open import OCF.Lean.Fold1If using (_≤ᵛ_)
open import OCF.Align.FrozenOutputIf using (Generated; actual-old-generated; changing; frozen)
import OCF.Align.FrozenOutputIf as If
import OCF.Align.FrozenValueSecond as S

D : HB (step S⊥) → HB (step S⊥)
D hz = hz
D (hs c) = hs (D c)
D (hl f) = hl (λ n → D (f n))
D (hΩ (inj₁ ()) g)
D (hΩ (inj₂ tt) g) = hΩ (inj₂ tt) (λ e → up e ⊞ D (g e))

module Candidate (A : Cd) where
  open If.Model A
  Covers : Cd → HB (step S⊥) → Set
  Covers b c = run changing b c ≤ᵛ run frozen hz (up b ⊞ D c)

  record GeneratedCover : Set where
    field
      cover : ∀ b c → Generated c → Covers b c

  -- 实际所有原轨道的待验收输入，不添加逐 n 的特殊构造。
  actual-input : ℕ → HB (step S⊥)
  actual-input n = D (S.Old.ce n)
  actual-source : ∀ n → Generated (S.Old.ce n)
  actual-source = actual-old-generated
```

接口冻结后不改变 D 或 Covers。需要独立处理：模型值覆盖、输入合法性、
以及对实际冻结族的覆盖。任一项失败都只否定相应声称，不自动否定其余两项。
