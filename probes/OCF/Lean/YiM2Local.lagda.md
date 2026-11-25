# 同一实际实例上的里程碑输入
验收文件；编译定理：全 HC 参照实例、实际孩子的 Leaf、继承底下界与内链 γ 参数关系。
实际 P₁ 仅接好目标基本列第 0 项；未证明 S(2) 的零层值界，未达里程碑。
来源：YiM2Chain、YiNLRaise、YiE4ParamInner、YiTBFam.ψ-⊵、YiAZLocal.S1-low。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiM2Local where
open import Data.Nat using (ℕ; suc)
open import Data.List using ([]; _∷_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
import OCF.Lean.YiM2Chain as C
import OCF.Lean.YiAZStart as A
import OCF.Lean.YiAZLocal as Z
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiNLTop2 as N
import OCF.Lean.YiNLRaise as NR
import OCF.Lean.YiNLCtx as NC
import OCF.Lean.YiAbsSimInst as SI
import OCF.Align.EboLeanDef as E
open import OCF.Align.Value using (_≼_; ≼-trans)
import OCF.Lean.YiE4Default as Df
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiGIInst as GI
import OCF.Lean.YiTBFam as TF
import OCF.Lean.YiGTGen as GT
import OCF.Lean.YiLLCheck as LL
import OCF.Lean.YiHCRel as H
import OCF.Align.EboLeanView as EV
open import Data.Sum using (inj₁)
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
import OCF.Lean.YiLBInv as LB
import OCF.Lean.YiRefTw2 as RT
import OCF.Lean.YiExInst as XI

opaque
  target : E.T
  target = Z.S 2
  target-eq : target ≡ Z.S 2
  target-eq = refl
  hc : SI.E.HC target
  hc = Z.hc-S 2
  partial : ℕ → B.Tr B.zero
  partial = A.P
  partial-eq : partial ≡ A.P
  partial-eq = refl

Bound : ℕ → Set
Bound m = (h : SI.E.HC target) → SI.E.tree h ≼ K.readRW (partial m)

child-input : GR.R (A.D.Step.child 2 A.D.c₁) (E.Ωt (E.Ωt (E.natT 2)))
  (proj₁ (O.Ωt (A.D.Step.child 2 A.D.c₁)))
child-input = NR.raiseR (B.tw 2) (NC.prefix (B.tw 2)) [] (GR.c0 refl)
  (N.leaf-tw2 (GR.c0 refl)) C.ir

shaped-input : GR.R A.N.h (E.Ωt (E.Ωt (E.natT 2))) (proj₁ (O.Ωt A.N.h))
shaped-input = subst (λ h → GR.R h (E.Ωt (E.Ωt (E.natT 2))) (proj₁ (O.Ωt h))) A.N.h-eq child-input

BaseFloor : ∀ ℓ → F.Base ℓ → Set
BaseFloor ℓ bs = ∀ i (u : i P.≤ ℓ) → proj₁ (O.Ωt i) K.⊴ proj₁ (bs i u)

shift-floor : ∀ h h′ (eq : h ≡ h′) (bs : F.Base h) → BaseFloor h bs → BaseFloor h′ (subst F.Base eq bs)
shift-floor h .h refl bs floor = floor

inherited-floor : BaseFloor (A.D.Step.child 2 A.D.c₁) (A.D.restricted A.D.c₁)
inherited-floor i u = subst (λ bs → proj₁ (O.Ωt i) K.⊴ proj₁ (bs i u))
  (sym (A.D.restricted-eq A.D.c₁))
  (subst (λ bs → proj₁ (O.Ωt i) K.⊴ proj₁ (bs i (P.inc A.D.c₁ u))) (sym (Df.base-eq 3))
    (TF.ψ-⊵ B.Λ P.Ok-Λ (MT.rbᶻ B.Λ) (F.B₀ B.Λ) i (P.inc 3 (P.inc A.D.c₁ u)) (O.Ωt i) (GI.pre 3)))

shaped-floor : BaseFloor A.N.h A.N.base₁
shaped-floor = subst (BaseFloor A.N.h) (sym A.N.base₁-eq)
  (shift-floor (A.D.Step.child 2 A.D.c₁) A.N.h A.N.h-eq (A.D.restricted A.D.c₁) inherited-floor)

Ω₂-tw1 : GR.R (B.tw 1) (E.Ωt (E.natT 2)) (proj₁ (O.Ωt (B.tw 1)))
Ω₂-tw1 = LL.rdown (B.tw 1) (inj₁ (E.hd< (E.lv< (E.hd< (E.lv< E.[]<))))) LL.leafΩ

arg : E.T
arg = E.Ωt (E.Ωt (E.natT 2))
ν : E.T
ν = E.natT 1
w : EV.VΩ arg ν
w = EV.ωl refl (EV.ωr refl)
γ : ℕ → E.T
γ = E.γT arg ν
γ-bound : ∀ n → γ n ≤ᵀ E.Ωt (E.natT 2)
γ-bound n = subst (λ t → t ≤ᵀ E.Ωt (E.natT 2)) (sym (EV.γ-eq w n)) (inj₁ (EV.γ< w n))

slot-r : GR.R (B.tw 1) (E.Ωt (E.natT 2)) (proj₁ (A.N.base₁ (B.tw 1) (P.ink P.self)))
slot-r = GT.weakenᴿ (B.tw 1) Ω₂-tw1 (shaped-floor (B.tw 1) (P.ink P.self))

feed-r : ∀ d → GR.R (B.tw 1) (E.Ωt (E.natT 2)) (A.N.Inner.feed d)
feed-r d = subst (λ f → GR.R (B.tw 1) (E.Ωt (E.natT 2)) (f d)) (sym A.N.Inner.feed-eq)
  (GT.weakenᴿ (B.tw 1) slot-r
    (TF.ψ-⊵ A.N.h A.N.o A.N.rr A.N.base₁ (B.tw 1) (P.ink P.self)
      (A.N.base₁ (B.tw 1) (P.ink P.self)) (A.N.Inner.g d)))

inner-chain-r : ∀ q n → GR.R (B.tw 1) (γ n) (A.N.Inner.chain (suc q))
inner-chain-r q n = H.mc (γ-bound n) (feed-r (A.N.Inner.chain q))

branch-r : ∀ d → GR.R (B.tw 2) (E.Ωt (E.natT 2)) (A.N.branch d)
branch-r d = subst (λ f → GR.R (B.tw 2) (E.Ωt (E.natT 2)) (f d)) (sym A.N.branch-eq)
  (GT.weakenᴿ (B.tw 2)
    (GT.weakenᴿ (B.tw 2) (N.leaf-tw2 C.rd₂)
      (subst (λ bs → proj₁ (O.Ωt (B.tw 2)) K.⊴ proj₁ (bs (B.tw 2) (P.ink P.self)))
        (sym (Df.base-eq 3)) C.slot))
    (TF.ψ-⊵ (B.tw 2) (P.Ok-tw 2) (A.D.Step.child-table 2 B.zero) A.N.base₀ (B.tw 2) P.self
      (A.D.baseᴱ 3 (B.tw 2) (P.ink P.self)) (A.D.Step.g 1 d)))

inner-input : ∀ d → GR.R (A.N.a d) arg (proj₁ (O.Ωt (A.N.a d)))
inner-input d = NR.raiseR (B.tw 2) (NC.prefix (B.tw 2)) [] (GR.c0 refl)
  (N.leaf-tw2 (GR.c0 refl)) (branch-r d)

fsn-form : ∀ n → E.fsn (Z.S 2) n ≡ E.ψ [] (E.Ωt (γ n)) ∷ []
fsn-form n = refl

fsn-zero : E.fsn (Z.S 2) 0 ≡ Z.S 1
fsn-zero = refl

partial-step : ∀ m → K.readRW (A.P m) ≼ K.readRW (A.P (suc m))
partial-step m = LB.from⊴ (K.+⊴ (A.P m) (proj₁ (A.G (suc m))))

zero-row : (h : SI.E.HC (E.fsn (Z.S 2) 0)) → SI.E.tree h ≼ K.readRW (partial 1)
zero-row = subst (λ t → (h : SI.E.HC t) → SI.E.tree h ≼ K.readRW (partial 1)) (sym fsn-zero)
  (λ h → subst (λ f → SI.E.tree h ≼ K.readRW (f 1)) (sym partial-eq)
    (≼-trans (Z.S1-low h) (partial-step 0)))

opaque
  hc-row : ∀ n → SI.E.HC (E.fsn (Z.S 2) n)
  hc-row n = SI.conv (RT.hω-inv (XI.back (Z.hc-S 2)) refl n)

first-row-form : E.fsn (Z.S 2) 1 ≡ E.ψ [] (E.Ωt (E.ψ (E.natT 1) (E.Ωt (E.Ωt (E.natT 1))) ∷ [])) ∷ []
first-row-form = refl
```
