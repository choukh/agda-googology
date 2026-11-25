# 实际第 3 站链点的 Ω₂ 下界
验收文件；编译定理：实际 c₁ 的原生树侧值不低于 Ω₂，另给同一对象的 R 关系。
来源：底下界复用 YiTBFam.ψ-⊵，关系复用 YiNLTop2.leaf-tw2；不把 R 与原生值等同。
本件不证明零层折叠保持，不增加 ψ₀ 值强度；实际内层输入见 YiM2Local。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiM2Chain where
open import Data.Sum using (inj₁)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiVWVal as V
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiFRStep as FR
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiE4Default as Df
import OCF.Lean.YiAZStart as A
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiNLTop2 as N
import OCF.Lean.YiLLCheck as LL
import OCF.Lean.YiGTGen as GT
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiKCStep using (⊴-trans)

zero-left : ∀ {ℓ} (v : V.V ℓ) → v V.≼ (V.zero V.⊹ v)
zero-left V.zero = V.z≼
zero-left (V.suc v) = V.s≼s (zero-left v)
zero-left (V.lim f) = V.l≼ (λ n → V.≼l n (zero-left (f n)))
zero-left (V.Ω p g) = V.Ω≼ (λ z → V.≼Ω z (zero-left (g z)))

child-value : ∀ s (h : B.Ch s → B.L) c (y : O.Tr⁺ (h c)) →
  V.val (h c) (proj₁ y) V.≼ V.val (B.nd s h) (proj₁ (O.upz {s = s} {h = h} c y))
child-value s h c y = V.≼-trans (V.≼-emb (B.nd s h) c (V.val (h c) (proj₁ y)))
  (zero-left (V.emb (B.nd s h) c (V.val (h c) (proj₁ y))))

Ω₂≤tw1 : V.val K.two (proj₁ (O.Ωt K.two)) V.≼ V.val (B.tw 1) (proj₁ (O.Ωt (B.tw 1)))
Ω₂≤tw1 = V.≼Ω (B.suc (B.suc B.zero))
  (child-value (B.sΩ B.zero) (λ c → B.zero B.⊕ B.↑ B.zero c) (B.suc (B.suc B.zero)) (O.Ωt K.two))

Ωtw1≤tw2 : V.val (B.tw 1) (proj₁ (O.Ωt (B.tw 1))) V.≼ V.val (B.tw 2) (proj₁ (O.Ωt (B.tw 2)))
Ωtw1≤tw2 = V.≼Ω B.zero (child-value (B.sΩ (B.tw 1)) (FR.Step.child 1) B.zero (O.Ωt (B.tw 1)))

slot : proj₁ (O.Ωt (B.tw 2)) K.⊴ proj₁ (GI.baseᴱ 3 (B.tw 2) (P.ink P.self))
slot = TF.ψ-⊵ B.Λ P.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) (B.tw 2) (P.inc 3 (P.ink P.self)) (O.Ωt (B.tw 2)) (GI.pre 3)

above : proj₁ (O.Ωt (B.tw 2)) K.⊴ FR.Step.chain 2 1
above = ⊴-trans slot (TF.ψ-⊵ (B.tw 3) (P.Ok-tw 3) (MT.rbᶻ (B.tw 3)) (GI.baseᴱ 3)
  (B.tw 2) (P.ink P.self) (GI.baseᴱ 3 (B.tw 2) (P.ink P.self)) (FR.Step.g 2 B.zero))

from⊴ : ∀ {ℓ} {x y : B.Tr ℓ} → x K.⊴ y → V.val ℓ x V.≼ V.val ℓ y
from⊴ K.⊴r = V.≼-refl _
from⊴ {ℓ} (K.⊴◃ d) = V.◁→≼ (V.val-mono ℓ d)

c₁-old : A.D.c₁ ≡ FR.Step.chain 2 1
c₁-old = trans A.D.c₁-eq (Df.chain-eq 2 1)

i : V.val K.two (proj₁ (O.Ωt K.two)) V.≼ V.val (B.tw 2) A.D.c₁
i = subst (λ c → V.val K.two (proj₁ (O.Ωt K.two)) V.≼ V.val (B.tw 2) c) (sym c₁-old)
  (V.≼-trans Ω₂≤tw1 (V.≼-trans Ωtw1≤tw2 (from⊴ above)))

rd₂ : GR.Rd (B.tw 2) (E.natT 2)
rd₂ = GR.rd-child (B.sΩ (B.tw 1)) (FR.Step.child 1) B.zero
  (GR.cc (inj₁ (E.hd< (E.lv< E.[]<))) LL.rdΩ)

ir : GR.R (B.tw 2) (E.Ωt (E.natT 2)) A.D.c₁
ir = subst (GR.R (B.tw 2) (E.Ωt (E.natT 2))) (sym c₁-old)
  (GT.weakenᴿ (B.tw 2) (N.leaf-tw2 rd₂) above)
```
