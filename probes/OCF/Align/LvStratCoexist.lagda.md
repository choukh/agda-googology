# 分层的 $\approx$: 新旧并排 (陈述)

> 不含记号. 只用来把两组定理放在同一个类型检查里. [LvStrat](LvStrat.lagda.md) 的其余文件不导入它, 也不导入 `LevelKNeg`, 除了 [LvStratNeg](LvStratNeg.lagda.md) 复用 `LevelKWorld` 的反例族.
>
> **改变的前提恰好一个: `Stage` 没有 `low-≈`, 也没有 `low-noo`.** 旧 `Stage` 的 `low-≈` 说两个 $\approx$ 的低层字面相同. 旧 `¬both-low`, `¬lowΩ₁` 都依赖它或 `low-noo`. 新 `Stage` 把它换成 `low≈`, `tr-A`. 新阶段上 `low-≈` 是假的 (`¬low-≈`), 所以旧定理的前提在这里不成立, 两者不矛盾.

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.LvStratCoexist where

open import Data.Empty using (⊥)
open import Data.Product using (_×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import OCF.Align.InaccTreeBase using (Lv; zero; limᴼ; toLv; Ω)
open import OCF.Align.InaccFloorTree using (Sib; natL)
import OCF.Align.LevelKBase as OldB
import OCF.Align.LevelKChain as OldC
import OCF.Align.LevelKNeg as OldN
import OCF.Align.LvStratBase as NewB
open import OCF.Align.LvStratOmega using (module Base; Ω₁L; module TopΩ; module TopΩ2; Ω₁·2)
open import OCF.Align.LvStratNeg using (module Copy; Ω₁′)

module Both (S : Sib) where
  private
    module O  = OldN.Sep1 S
    module OF = OldB.Fl (OldB.Stage.fl (OldN.Canon.St S 1))
    module N  = NewB.Fl (NewB.Stage.fl (Base.T₀ S))
    module NL = NewB.Leaf (NewB.Stage.fl (Base.T₀ S))
    module OL = OldB.Leaf (OldB.Stage.fl (OldN.Canon.St S 1))

  -- 旧: 在 `low-≈` 之下, 两个分支在地板上一致、外面不同的 `limᴼ` 不能同时低
  old-¬both : (∀ {a b} → OF.Lw a → OF.Lw b → a OL.≈ᴮ b → a ≡ b) → OF.Lw (limᴼ zero O.g₀) → OF.Lw (limᴼ zero O.g₁) → ⊥
  old-¬both = O.¬both-low

  -- 旧: `Stage` 的低层不含 Ω₁
  old-¬lowΩ₁ : OF.Lw (toLv (Ω (natL 1))) → ⊥
  old-¬lowΩ₁ = OldC.NoTop.¬lowΩ₁ (OldN.Canon.St S 1)

  -- 新: 两个 `limᴼ` 同时低, `low-≈` 假, Ω₁ 低
  new-both : N.Lw Ω₁L × N.Lw Ω₁′
  new-both = Copy.both-low S

  new-¬low-≈ : (∀ {a b} → N.Lw a → N.Lw b → a NL.≈ᴮ b → a ≡ b) → ⊥
  new-¬low-≈ = Copy.¬low-≈ S
```
