# Ψ 的末端记号条件链
验收文件；assemble 保留 TreeBound 和 NΨ 两个未填前提，里程碑仍有条件。
树侧对象接到 YiE4 默认实例；小例出口调用 YiTBFam.sΩ-LF，不把它外推到 Ω 形层号。
来源：零层值序桥直接按构造递归；实际链点下界只调用作者验收的 YiM2Chain.i。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTVAccept where
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTVPsi as Q
import OCF.Lean.YiTVActual as A
import OCF.Lean.YiSLStart as S
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiAZLocal as AL
import OCF.Lean.YiAZStart as AZ
import OCF.Lean.YiM2Chain as M2
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiE4Default as Df
import OCF.Align.Level as L
import OCF.Align.Value as W

open import OCF.Lean.YiTVRead

NΨ : Set
NΨ = V.val K.two (proj₁ (O.Ωt K.two)) V.≼ A.v₁ →
  (h : SI.E.HC (AL.S 2)) → SI.E.tree h W.≼ readV (Q.Ψ (B.tw 2) (P.Ok-tw 2) A.v₁ A.hv₁)

-- perf: C-9，函数在变量 n 上接线；具体链点只经等式搬运。
source-feed : ∀ n → S.Step.feed n ≡ FR.Step.feed n
source-feed n = refl
source-out : ∀ n → S.Step.out n ≡ FR.Step.out n
source-out n = refl
source-chain : ∀ n q → S.Step.chain n q ≡ FR.Step.chain n q
source-chain n q = cong (λ f → O.iter f B.zero q) (source-feed n)

c-wire : A.c₁ ≡ AZ.D.c₁
c-wire = trans A.c₁-eq (trans (source-chain 2 1) (sym M2.c₁-old))
input-low : V.val K.two (proj₁ (O.Ωt K.two)) V.≼ A.v₁
input-low = subst (λ c → V.val K.two (proj₁ (O.Ωt K.two)) V.≼ V.val (B.tw 2) c)
  (sym c-wire) M2.i

output-wire : A.output ≡ AZ.D.output
output-wire = trans A.output-eq (trans (cong (λ f → f A.c₁) (trans (A.out-eq 2) (source-out 2)))
  (trans (cong (FR.Step.out 2) (trans c-wire M2.c₁-old)) (sym Df.output-old)))

assemble-at : (a : V.V B.zero) (out : O.Tr⁺ B.zero) →
  a V.≼ V.val B.zero (proj₁ out) →
  ((h : SI.E.HC (AL.S 2)) → SI.E.tree h W.≼ readV a) →
  (h : SI.E.HC (AL.S 2)) → SI.E.tree h W.≼ K.readRW (proj₁ out)
assemble-at a out tree low h = W.≼-trans (low h)
  (W.≼-trans (readV-mono tree) (W.≅→≼ (read-val (proj₁ out))))

assemble : A.TreeBound → NΨ →
  (h : SI.E.HC (AL.S 2)) → SI.E.tree h W.≼ K.readRW (proj₁ AZ.D.output)
assemble tree nψ h = subst (λ out → SI.E.tree h W.≼ K.readRW (proj₁ out)) output-wire
  (assemble-at (Q.Ψ (B.tw 2) (P.Ok-tw 2) A.v₁ A.hv₁) A.output tree (nψ input-low) h)
```
