# 实际链点的树侧比较义务
不读记号；实际对象直接取 YiSLStart，出生处封装并导出等式。
TreeBound 是固定 c₁ 上的待证命题，尚未交付居民；不作值下界结论。
来源：YiSLStart.Step 与 YiTVPsi；与 YiE4 的接线放在验收文件。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTVActual where
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiSLStart as S
import OCF.Lean.YiTVPsi as Q

-- perf: S-1/C-9，先在变量 n 上封装整个函数，再在 c₁ 处调用。
opaque
  out : (n : ℕ) → B.Tr (B.tw n) → O.Tr⁺ B.zero
  out n = S.Step.out n
  out-eq : ∀ n → out n ≡ S.Step.out n
  out-eq n = refl

opaque
  c₁ : B.Tr (B.tw 2)
  c₁ = S.Step.chain 2 1
  c₁-eq : c₁ ≡ S.Step.chain 2 1
  c₁-eq = refl
  output : O.Tr⁺ B.zero
  output = out 2 c₁
  output-eq : output ≡ out 2 c₁
  output-eq = refl

v₁ : V.V (B.tw 2)
v₁ = V.val (B.tw 2) c₁
hv₁ : V.LegV (B.tw 2) v₁
hv₁ = V.val-leg (B.tw 2) c₁

TreeBound : Set
TreeBound = Q.Ψ (B.tw 2) (P.Ok-tw 2) v₁ hv₁ V.≼ V.val B.zero (proj₁ output)

child : B.L
child = S.Step.child 2 c₁
child-ok : P.Ok child
child-ok = proj₂ (P.Ok-tw 3) c₁
```
