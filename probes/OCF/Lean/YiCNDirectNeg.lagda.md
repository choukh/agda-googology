# 规范域内直接 Ω 行所需字段的边界
验收文件；编译否定：从任意孩子的后继读法提取下标层上的前驱读法，这个字段在 `tw 1` 已不成立。
反例取下标层 0、孩子树 2、读法 2；`cn-source`、`rd-source` 实填输入，`leaf-source` 仍成立。
不否定 `Cn` 上的 Leaf；它排除保持目标读法、直接以同一个前驱作 Ω 共尾参数的这一种证明办法。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCNDirectNeg where
open import Data.Empty using (⊥)
open import Data.List using ([])
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiCNDomain
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiCNTw1 as T1
open import OCF.Lean.YiGICheck using (rd-fin)
import OCF.Align.EboLeanDef as E

two : Tr zero
two = suc (suc zero)

cn-source : Cn (Ωc zero)
cn-source = cw cz

rd-source : GR.Rd (zero ⊕ ↑ zero two) (E.natT 2)
rd-source = rd-fin 2

NuFromChild : Set
NuFromChild = ∀ {k} → Cn k → (c : Tr k) {ν : E.T} → E.cof ν ≡ E.c1
  → GR.Rd (k ⊕ ↑ k c) ν → GR.Rd k (E.pred ν)

no-NuFromChild : NuFromChild → ⊥
no-NuFromChild f = bad (T1.rd-zero (f {k = zero} cz two refl rd-source))
  where
  bad : E.natT 1 ≡ [] → ⊥
  bad ()

leaf-source : GR.R (tw 1) (E.Ωt (E.natT 2)) (proj₁ (O.Ωt (tw 1)))
leaf-source = T1.leaf-tw1 {ν = E.natT 2} (GR.rd-child (sΩ zero) (λ c → zero ⊕ ↑ zero c) two rd-source)
```
