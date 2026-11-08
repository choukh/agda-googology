# 首站的全部可数高度：洗法不删 Ω 节点

实际 first 使用底 S⊥，其内部高度只有 Cd 的三个构造子。
因此高底中穿过 Ω 高度而删除节点的 sf 分支在这里不可达。
以下覆盖所有可数高度及所有裸输入，不是有限样本。
值双向只比较洗法前后；不允许把高层值等价穿任意折叠。

```agda
{-# OPTIONS --safe --without-K #-}
module OCF.Align.GridCheckCountableSan where
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.CRwBase
open import OCF.Lean.ThirdIf using (Tw; Pos)
open import OCF.Lean.Fold1If using (_≤ᵛ_; z≤; s≤s; l≤; ≤l; Ω≤Ω)
import OCF.Lean.ThirdSan as S

module At (fb : Cd) where
  open S S⊥ tt tt fb using (sf; san)

  sf-success : ∀ (m : Cd) (κ : K (Tw S⊥ m)) →
    Σ (Pos S⊥ tt m κ) (λ p → sf m κ ≡ inj₁ p)
  sf-success hz ()
  sf-success (hs m) (inj₂ _) = tt , refl
  sf-success (hs m) (inj₁ κ) = sf-success m κ
  sf-success (hl f) (n , κ) = sf-success (f n) κ
  sf-success (hΩ () f) κ

  lower : ∀ (m : Cd) (a : HB (Tw S⊥ m)) → a ≤ᵛ san m a
  lower m hz = z≤
  lower m (hs a) = s≤s (lower m a)
  lower m (hl f) = l≤ (λ n → ≤l n (lower m (f n)))
  lower m (hΩ κ g) with sf-success m κ
  ... | p , eq rewrite eq = Ω≤Ω (λ e → lower m (g e))

  upper : ∀ (m : Cd) (a : HB (Tw S⊥ m)) → san m a ≤ᵛ a
  upper m hz = z≤
  upper m (hs a) = s≤s (upper m a)
  upper m (hl f) = l≤ (λ n → ≤l n (upper m (f n)))
  upper m (hΩ κ g) with sf-success m κ
  ... | p , eq rewrite eq = Ω≤Ω (λ e → upper m (g e))

  both : ∀ m a → (a ≤ᵛ san m a) × (san m a ≤ᵛ a)
  both m a = lower m a , upper m a

-- 原 first 的底地板参数就是零；这不是引入新的洗法。
module Actual = At hz
```

这排除“因为高底 Er 会删 Ω，所以 first 已被同一机制压平”的推论。
仍未证明 first 的具名强度或上界。零项从旧 ψ 的 Ω_target 改为 1、
原累计链及每次回灌的 Rich 完成，仍需完整生成域上的比较证明。
