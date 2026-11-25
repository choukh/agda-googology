# YiXVFiniteUp
> 验收文件。档位：编译定理。原生有限层节点在 up 后的正规形合法性；完整 Ω₁+Ω₁ 模型已填。
> 接 YiXVSourceSem、SourceAffine*、Finite*，有限搬运比较参照 YiXVCan2Embed；未交完整外层链或原 Goal。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXVFiniteUp where
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (subst)
import Data.Fin as F
import OCF.Align.Level as L
import OCF.Lean.YiXVFiniteIndex as I
import OCF.Lean.YiXVFiniteFamily as A
import OCF.Lean.YiXVFiniteBasics as B
import OCF.Lean.YiXVFiniteCoerce as C
import OCF.Lean.YiXVFiniteInputs as In
import OCF.Lean.YiXVFiniteAdd as Add

module Raise (n : ℕ) where
  module S = A.Layer n (A.GoFam n) (A.LeFam n)
  module D = A.Layer (suc n) (A.GoFam (suc n)) (A.LeFam (suc n))
  module At {i} (q : i L.<ᴵ L.natᴵ (suc n)) where
    c = In.change n (suc n) q (L.suc q)
    good : ∀ u → D.GU (L.suc q) u → S.GU q u
    good u gu = subst (S.GU q) (C.coe-id q u) (In.Change.good c u gu)
    floor : ∀ u → D.Floor (L.suc q) u → S.Floor q u
    floor u o = subst (S.Floor q) (C.coe-id q u) (In.Change.floor c u o)
    rel : ∀ u v → D.RU (L.suc q) u v → S.RU q u v
    rel u v r = subst (λ z → S.RU q z v) (C.coe-id q u)
      (subst (S.RU q (In.Change.pull c u)) (C.coe-id q v) (In.Change.rel c u v r))
  normal : ∀ {i} {q : i L.<ᴵ L.natᴵ (suc n)} {f : L.U i (L.<→◃ q) → I.T (suc n)} →
    S.Gd (L.limᵢ q f) → D.Gd (L.limᵢ (L.suc q) (λ u → L.up L.zero (f u)))
  normal (S.gn {q = q} {f = f} law gb) = D.gn (D.sc
    (λ u v gu gv o r → D.u≤ (gb u (G.good u gu) (G.floor u o))
      (B.right (suc n) F.zero (S.SC.mo law u v (G.good u gu) (G.good v gv) (G.floor u o) (G.rel u v r)))
      (S.SC.mo law u v (G.good u gu) (G.good v gv) (G.floor u o) (G.rel u v r)))
    (λ u gu o → D.trans (D.upS≤ (gb u (G.good u gu) (G.floor u o))
      (S.gs (gb u (G.good u gu) (G.floor u o))))
      (D.u≤ (S.gs (gb u (G.good u gu) (G.floor u o)))
        (S.right (S.SC.db law u (G.good u gu) (G.floor u o)))
        (S.SC.db law u (G.good u gu) (G.floor u o))))
    (D.trans (D.trans (D.s≤ (D.z≤ (D.gu S.gz))) (D.upS≤ S.gz (S.gs S.gz)))
      (D.u≤ (S.gs S.gz) (S.right (S.SC.po law)) (S.SC.po law))))
    (λ u gu o → D.gu (gb u (G.good u gu) (G.floor u o)))
    where module G = At q

model-good : A.Gd 2 (L.limᵢ (L.suc L.zero) (λ u → L.up L.zero (L.add (L.Ω (L.natᴵ 1)) (λ q → L.suc q) u)))
model-good = Raise.normal 0 (Add.plus-good 1 {X = L.Ω (L.natᴵ 1)} {Y = L.Ω (L.natᴵ 1)} (B.actual 1) (B.actual 1))
```
