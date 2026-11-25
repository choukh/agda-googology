# 原 q=2 输出的连续 22 次第 0 分支
验收文件；沿原实际输出连续取第 0 分支 22 次得到 next⁺(betaᴱ3)，故其读回值不高于该输出。
不更改实际底、起点或链；不声称 FirstMissing 或新增终点强度。
来源：分支选择复用 YiS1Shape.branch0，迭代复用 YiRWOps.iter；实际折叠按 YiFRStep.Step 展开。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMSValue where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiFRStep as S
import OCF.Lean.YiGIInst as GI
open import OCF.Align.Value using (_≼_; z≼; ≼l; ≼-refl; ≼-trans)
open import OCF.Lean.YiS1Shape using () renaming (branch0 to first)
first≤ : ∀ x → K.readRW (first x) ≼ K.readRW x
first≤ B.zero = z≼
first≤ (B.suc x) = ≼-refl _
first≤ (B.lim f a) = ≼l 0 (≼-refl _)
first≤ (B.Ω () _)
first≤ (B.up _ () _ _)
follow : ℕ → B.Tr B.zero → B.Tr B.zero
follow n x = O.iter first x n
follow≤ : ∀ n x → K.readRW (follow n x) ≼ K.readRW x
follow≤ zero x = ≼-refl _
follow≤ (suc n) x = ≼-trans (first≤ (follow n x)) (follow≤ n x)
c₂ = S.Step.chain 2 2
ℓ = S.Step.child 2 c₂
β = GI.betaᴱ 3
out = proj₁ (S.Step.out 2 c₂)
point-form : follow 22 out ≡ proj₁ (O.next⁺ β)
point-form = refl
value-next : K.readRW (proj₁ (O.next⁺ β)) ≼ K.readRW out
value-next = subst (λ x → K.readRW x ≼ K.readRW out) point-form (follow≤ 22 out)

```
