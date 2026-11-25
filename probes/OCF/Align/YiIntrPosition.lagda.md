# YiIntr：构造前的位置条件

本篇只在原 LF 上核对拟内置字段的含义，不改原 Reg。
`Parts k t` 说第一支 t 已经是 suc k，或在内部包含 suc k 的真路径。
条件只涉及已有部分 k、t，不引用尚未构造的 lc。
它足以给原 Reg 的根位置，但不是原根位置的等价改写：
原位置也可能只经 Ω 分支到达，下面给有 Reg、Carry⁺、Legal 的闭例。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIntrPosition where

open import Data.Unit.Base using (tt)
open import Data.Empty using (⊥)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Align.LevelFixCore as F
import OCF.Align.LevelFixVal as V
open import OCF.Align.YiDispBase
  using (Below; one; more; e-first; e-branch)
open import OCF.Align.YiRegBase using (Reg)
open import OCF.Align.YiCarryPlus using (Carry⁺)

Parts : F.LF → F.LF → Set
Parts k t = (F.suc k ≡ t) ⊎ Below (F.suc k) t

parts-below : ∀ {k c t g} → Parts k t →
  Below (F.suc k) (F.lc k c t g)
parts-below (inj₁ refl) = one e-first
parts-below (inj₂ p) = more p e-first

-- 非空实例：第一支正好取字段的后继。
parts-instance : ∀ k → Parts k (F.suc k)
parts-instance k = inj₁ refl

raw1 : F.Raw F.zero
raw1 = F.G.suc F.G.zero

first-node : F.LF
first-node = F.lc F.zero raw1 (F.suc F.zero) (λ _ _ → F.suc F.zero)

first-bound : Below (F.suc F.zero) first-node
first-bound = parts-below {k = F.zero} {c = raw1}
  {t = F.suc F.zero} {g = λ _ _ → F.suc F.zero} (parts-instance F.zero)

branch-node : F.LF
branch-node = F.lc F.zero raw1 F.zero (λ _ _ → F.suc F.zero)

branch-bound : Below (F.suc F.zero) branch-node
branch-bound = one (e-branch raw1 (inj₁ refl , tt))

branch-reg : Reg branch-node
branch-reg = branch-bound , tt , tt , (λ _ _ → tt)

branch-carry⁺ : Carry⁺ branch-node
branch-carry⁺ = branch-reg , tt , tt , tt , (λ _ _ _ → tt)

branch-legal : V.Legal branch-node
branch-legal = tt , (λ _ _ → V.suc V.self) ,
  (λ _ _ _ _ _ → V.self) , (λ _ _ _ → refl) , tt , (λ _ _ → tt)

no-below-zero : ∀ {a} → Below a F.zero → ⊥
no-below-zero (one ())
no-below-zero (more p ())

branch-no-parts : Parts F.zero F.zero → ⊥
branch-no-parts (inj₁ ())
branch-no-parts (inj₂ p) = no-below-zero p
```

平行骨架不把这个旧 LF 的 Parts 直接导入构造子。它用块内的归纳
`Reach a b` 表示相等或有限子树路径，端点仍是新 LF；这样不在守卫中
增加 LF 上的字面等式，也不通过异层打包相等重演 LevelFixCore 的 P1。
拟内置条件是 `Reach (suc k) t`，语义对应本篇 Parts；
若骨架获接受，需在新 LF 上另证对应关系，不能把本篇旧类型定理直接搬用。

第一支条件被选择为易核对的充分条件，不宣称它覆盖全部原 Carry⁺ 源。
规范 Ω 是否满足该加强，尤其迭代后的第一支，属于骨架通过后的独立义务。
