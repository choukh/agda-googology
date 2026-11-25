# 干净对象接线与第 0 项条件链
验收文件；ChildBound 与 NΨ 均未实填，first-row 是条件定理，不宣称得到第 0 项。
TreeBound 到整行的值界不足以给有限部分和见证；first-row 使用更具体的 ChildBound。
来源：YiTVAccept 的 readV 桥、YiS2Low 的语义反射；公共对象只接线，不改定义。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiTMAccept where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiTMInner as I
import OCF.Lean.YiTMObjects as A
import OCF.Lean.YiE4Inner as J
import OCF.Lean.YiE4Base as C
import OCF.Lean.YiUTTwo as U
import OCF.Lean.YiUTTwoLocal as UL
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiTVPsi as Q
open import OCF.Lean.YiTVRead
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiKCSem as CS
import OCF.Lean.YiAbsSimInst as SI
import OCF.Lean.YiExInst as XI
import OCF.Lean.YiAZLocal as AL
import OCF.Align.EboLeanDef as E
import OCF.Align.Level as L
import OCF.Align.Value as W

-- perf: C-9，整函数接线先在变量形状上证明。
module Wire (k : B.L) (a : B.Tr k → B.L) (o : P.Ok (B.nd (B.sΩ k) a))
  (r : TB.Rb (B.nd (B.sΩ k) a)) (bs : F.Base (B.nd (B.sΩ k) a)) (β : O.Tr⁺ B.zero) where
  module X = I.Inner k a o r bs β
  module Y = J.Inner k a o r bs β
  opaque
    unfolding X.g X.feed X.out Y.g Y.feed Y.out
    feed-wire : X.feed ≡ Y.feed
    feed-wire = refl
    out-wire : X.out ≡ Y.out
    out-wire = refl
  chain-wire : ∀ n → X.chain n ≡ Y.chain n
  chain-wire n = cong (λ f → O.iter f B.zero n) feed-wire
  line-wire : ∀ n → X.out (X.chain n) ≡ Y.out (Y.chain n)
  line-wire n = trans (cong (λ f → f (X.chain n)) out-wire) (cong Y.out (chain-wire n))

collapse-wire : ∀ h o r bs β → I.collapse h o r bs β ≡ C.collapse (h , o , r , bs) β
collapse-wire h o r bs β = trans (I.collapse-eq h o r bs β) (sym (C.collapse-eq h o r bs β))
output-wire : A.output ≡ U.output
output-wire = trans (collapse-wire U.ℓ₂ U.o₂ (MT.rbᶻ U.ℓ₂) (F.B₀ U.ℓ₂) (O.Ωt B.zero)) (sym U.output-eq)
module Actual = Wire A.one U.a U.o₂ (MT.rbᶻ U.ℓ₂) (F.B₀ U.ℓ₂) (O.Ωt B.zero)

cum-cong : (f g : ℕ → B.Tr B.zero) → (∀ n → f n ≡ g n) → ∀ n → O.cum f n ≡ O.cum g n
cum-cong f g eq zero = eq zero
cum-cong f g eq (suc n) = cong₂ O._+_ (cum-cong f g eq n) (eq (suc n))
P₁ : B.Tr B.zero
P₁ = O.cum (λ n → proj₁ (A.Inner.out (A.Inner.chain n))) 1
cum-wire : P₁ ≡ UL.P 1
cum-wire = cum-cong _ _ (λ n → cong proj₁ (Actual.line-wire n)) 1

target : E.T
target = E.fsn (AL.S 2) 0
target-hc : E.HC target
target-hc = XI.back (AL.hc-S 1)
NΨ : Set
NΨ = V.val A.one (proj₁ (O.Ωt A.one)) V.≼ A.v₁ →
  (h : SI.E.HC target) → SI.E.tree h W.≼ readV (Q.Ψ A.one A.o-one A.v₁ A.hv₁)

reflect-at : ∀ {t} (h : E.HC t) (v : V.V B.zero) (x : B.Tr B.zero) →
  v V.≼ V.val B.zero x →
  ((e : SI.E.HC t) → SI.E.tree e W.≼ readV v) → K.M⁰ t x
reflect-at h v x tree low = CS.sem→M⁰ h x
  (W.≼-trans (SI.toL-tree h) (W.≼-trans (low (SI.conv h))
    (W.≼-trans (readV-mono tree) (W.≅→≼ (read-val x)))))
first-row : A.ChildBound → NΨ → UL.FirstRow
first-row child nψ = 1 , subst (K.M⁰ target) cum-wire
  (reflect-at target-hc (Q.Ψ A.one A.o-one A.v₁ A.hv₁) P₁
    (V.≼-trans child (A.Inner.point-cum 1)) (nψ A.input-low))
whole-value : A.TreeBound → NΨ → (h : SI.E.HC target) → SI.E.tree h W.≼ K.readRW (proj₁ U.output)
whole-value tree nψ h = subst (λ out → SI.E.tree h W.≼ K.readRW (proj₁ out)) output-wire
  (W.≼-trans (nψ A.input-low h)
    (W.≼-trans (readV-mono tree) (W.≅→≼ (read-val (proj₁ A.output)))))
```
