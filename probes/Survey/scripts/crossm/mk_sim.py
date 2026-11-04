# 从 LadderOrdCross 改写 CrossMSim: 左边也是 HtB. 只改模块头与链行.
A='/Users/alsg/Agentic/agda-googology/probes/OCF/Align/'
t=open(A+'LadderOrdCross.lagda.md',encoding='utf-8').read()
body=t.split('```agda\n',1)[1]
old_head=body.split('open import Data.Nat using (ℕ; zero; suc)',1)[0]
new_head='''{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
import OCF.Align.CrossMSimEq as CE
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
module OCF.Align.CrossMSim (𝕊 : HtB) (𝔹 : HtB) (e : HtB.Ht 𝕊 → HtB.Ht 𝔹) (ε : ∀ {n m} → HtB._<ᴸ_ 𝕊 n m → HtB._<ᴸ_ 𝔹 (e n) (e m))
  (tri-self : ∀ a → HtB.tri 𝔹 a a ≡ teq refl) (rowq : ∀ m → CE.RowEq 𝕊 𝔹 e ε m (HtB.view 𝕊 m)) where

'''
body=body.replace(old_head,new_head,1)
body=body.replace('import OCF.Align.LadderInfTree\nimport OCF.Align.LadderInfRel\nimport OCF.Align.LadderOrdTree\nimport OCF.Align.LadderOrdRel\n','import OCF.Align.LadderOrdTree\nimport OCF.Align.LadderOrdRel\n')
body=body.replace('module N = OCF.Align.LadderInfTree 𝕊','module N = OCF.Align.LadderOrdTree 𝕊').replace('module NR = OCF.Align.LadderInfRel 𝕊','module NR = OCF.Align.LadderOrdRel 𝕊')
assert 'LadderInf' not in body
i=body.index('R-rowL : ∀ {m} F'); j=body.index('R-row : ∀ m →')
body=body[:i]+'''R-rowL : ∀ {m} F (qs₁ : ∀ i → F i N.<ᴸ m) (r₁ : ∀ i → e (F i) I.<ᴸ e m) → (∀ {n} → n N.<ᴸ m → XRΩ n) → ∀ i →
         Rq m zero zero (N.rowL F qs₁ (λ i₁ → N.ΩI m (qs₁ i₁)) i) (I.rowL (λ i₁ → e (F i₁)) r₁ (λ i₁ → I.ΩI (e m) (r₁ i₁)) i)
R-rowL F qs₁ r₁ I₁ zero = R-𝟏L
R-rowL {m} F qs₁ r₁ I₁ (suc i) = subst₂ (λ X Y → Rq m zero zero (N.stepL (qs₁ i) X) (I.stepL (r₁ i) Y)) (sym (N.ΩI≡ (qs₁ i))) (sym (I.ΩI≡ (r₁ i)))
  (subst (λ r → Rq m zero zero (N.stepL (qs₁ i) (N.Ω̇ (F i))) (I.stepL r (I.Ω̇ (e (F i))))) (I.<-prop (ε (qs₁ i)) (r₁ i)) (R-stepL (qs₁ i) (I₁ (qs₁ i))))

'''+body[j:]
old='''R-row m I₁ (chain F qs₁) rq = subst (Rq m zero zero (N.ql (N.rowL F qs₁ (λ i → N.ΩI m (qs₁ i))))) (sym (cong (I.rowV (e m) (I.ΩI (e m))) rq))
  (rl (R-rowL F qs₁ I₁))'''
assert old in body
body=body.replace(old,'''R-row m I₁ (chain F qs₁) (r₁ , rq) = subst (Rq m zero zero (N.ql (N.rowL F qs₁ (λ i → N.ΩI m (qs₁ i))))) (sym (cong (I.rowV (e m) (I.ΩI (e m))) rq))
  (rl (R-rowL F qs₁ r₁ I₁))''')
head='''# 跨段: 两个 `HtB` 世界之间的模拟

> **判决: HOLDS (对结构参数, 编译过; 条件是下面三个参数).** 入口 [CrossM](CrossM.lagda.md). 由 [LadderOrdCross](LadderOrdCross.lagda.md) 机械改写, 差别只有两处: (1) 左边的世界从 `LadderInfTree 𝕊` (`HtS`) 换成 `LadderOrdTree 𝕊` (`HtB`); (2) `RowEq` 的链行不再要求 `view` 右边的证明字面是 `ε ∘ qs`, 只要有某个 `r`, 比较时逐点用 `<-prop` (函数之间的相等要函数外延, 这里没有). 参数: 保序映射 `e`, `ε`; 右边 `tri` 在对角线上是 `teq refl`; 第 0 行的写法对齐 (`rowq`). **`bridge m α α′ d : N.Tᵠ m α ≈ᴿ I.Tᵠ (e m) α′`**.

```agda
'''
open(A+'CrossMSim.lagda.md','w',encoding='utf-8').write(head+body)
eq='''# 跨段: 第 0 行对齐

> **判决: HOLDS (只有声明).** 入口 [CrossM](CrossM.lagda.md). `RowEq` 说右边第 0 行的写法与左边一致. 仿 [LadderOrdCrossEq](LadderOrdCrossEq.lagda.md); 链行的证明项不要求字面相同.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
module OCF.Align.CrossMSimEq (𝕊 : HtB) (𝔹 : HtB) (e : HtB.Ht 𝕊 → HtB.Ht 𝔹) (ε : ∀ {n m} → HtB._<ᴸ_ 𝕊 n m → HtB._<ᴸ_ 𝔹 (e n) (e m)) where

open import Data.Product using (Σ)
open import Relation.Binary.PropositionalEquality using (_≡_)
import OCF.Align.LadderOrdTree
module N = OCF.Align.LadderOrdTree 𝕊
module I = OCF.Align.LadderOrdTree 𝔹

RowEq : ∀ m → View N._<ᴸ_ N.h₀ m → Set
RowEq m base = I.rowV (e m) (I.ΩI (e m)) (I.view (e m)) ≡ I.rowB {e m}
RowEq m (clos q) = I.view (e m) ≡ clos (ε q)
RowEq m (chain F qs) = Σ (∀ i → e (F i) I.<ᴸ e m) λ r → I.view (e m) ≡ chain (λ i → e (F i)) r
```
'''
open(A+'CrossMSimEq.lagda.md','w',encoding='utf-8').write(eq)
