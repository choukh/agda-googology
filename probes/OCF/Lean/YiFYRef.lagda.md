# EBOᶻ 的参数加 ω 下界
验收文件；编译定理 target-low、all-hc-low：实际终点不低于 ψ₀(Ω_Ω + ψ₁(Ω_ω) + ω)，hc-target 给非空参照实例。
方法是外层累计前缀的任意有限 next 放大后取极限；不依赖内层 out(feed d) 支配 next(out d) 的未证强式。
树、折叠、表、底、合法性均未改；未证第3站全部下界，亦未证 ψ₀(Ω_Ω + ψ₁(Ω_ω)·2)。
来源：YiFYPrefix；种子用 YiOLBoost.m-base/beta-eq，基本列复制用 YiCLPhi.rep1，参照正规形用 YiVTANLim.gω/nωᴮ。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFYRef where
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; trans)
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanBase as EB
import OCF.Align.EboLeanTree as ET
import OCF.Lean.YiVTANLim as VT
import OCF.Lean.YiMENote as MN
import OCF.Lean.YiCLPhi as CP
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiOLBoost as OL
import OCF.Lean.YiFYPrefix as PFX
import OCF.Lean.YiRefTw2 as RT
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiExInst as XI
import OCF.Lean.YiAbsSimInst as SI
open import OCF.Align.Value using (_≼_; ≼-trans; ≼-refl; l≼)
param : ℕ → E.T
param n = VT.argω ++ E.natT n
ref : ℕ → E.T
ref n = E.ψ [] (param n) ∷ []
cof-nat : ∀ n → E.cof (E.natT (suc n)) ≡ E.c1
cof-nat zero = refl
cof-nat (suc n) = cof-nat n
pred-nat : ∀ n → E.pred (E.natT (suc n)) ≡ E.natT n
pred-nat zero = refl
pred-nat (suc n) = cong (E.𝟏 ∷_) (pred-nat n)
cof-param : ∀ n → E.cof (param (suc n)) ≡ E.c1
cof-param n = MN.cof++1 VT.argω (E.natT (suc n)) (cof-nat n)
pred-param : ∀ n → E.pred (param (suc n)) ≡ param n
pred-param n = trans (MN.pred++ VT.argω (E.natT (suc n)) (cof-nat n)) (cong (VT.argω ++_) (pred-nat n))
cof-ref : ∀ n → E.cof (ref (suc n)) ≡ E.cω
cof-ref n = MN.cofψ1 [] (param (suc n)) (cof-param n)
fsn-ref : ∀ n m → E.fsn (ref (suc n)) m ≡ replicate m (E.ψ [] (param n))
fsn-ref n m = trans (MN.fsnψ1 [] (param (suc n)) m (cof-param n))
  (cong (λ a → replicate m (E.ψ [] a)) (pred-param n))
seed-M : K.M⁰ (ref 0) (proj₁ (PFX.prefix 2))
seed-M = subst (λ b → K.M⁰ (ref 0) (proj₁ b)) (trans OL.beta-eq (sym PFX.prefix-beta)) OL.m-base
finite-M : ∀ n → K.M⁰ (ref n) (proj₁ (O.iter O.next⁺ (PFX.prefix 2) n))
finite-M zero = seed-M
finite-M (suc n) = K.G⁰.m-next {t = ref (suc n)} {p = E.ψ [] (param n)}
  (O.iter O.next⁺ (PFX.prefix 2) n) (cof-ref n) (fsn-ref n) (finite-M n)
finite-low : ∀ n (h : E.HC (ref n)) → RT.Rt h ≼ K.readRW MT.EBOᶻ
finite-low n h = ≼-trans (K.lower⁰ (finite-M n) h)
  (≼-trans (PFX.iterate-bound n) (PFX.prefix-upper (PFX.index n)))
target-arg : E.T
target-arg = VT.argω ++ VT.ω′
target : E.T
target = E.ψ [] target-arg ∷ []
fsn-target : ∀ n → E.fsn target n ≡ ref n
fsn-target n = cong (λ t → E.ψ [] (VT.argω ++ t) ∷ []) (CP.rep1 n)
arg-less : VT.argω E.<ᵀ target-arg
arg-less = E.tl< (E.tl< E.[]<)
gb-tail : EB.GB [] VT.ω′ target-arg
gb-tail (EB.gp (EB.gh _)) = E.hd< (E.lv< E.[]<)
gb-tail (EB.gp (EB.gw _ ()))
gb-tail (EB.gp (EB.gc _ (EB.gp (EB.gh _)))) = E.[]<
gb-tail (EB.gp (EB.gc _ (EB.gp (EB.gw _ ()))))
gb-tail (EB.gp (EB.gc _ (EB.gp (EB.gc _ ()))))
gb-tail (EB.gp (EB.gc _ (EB.gtl ())))
gb-tail (EB.gtl ())
gb-target : EB.GB [] target-arg target-arg
gb-target (EB.gp p) = EB.<ᵀ-trans (VT.gω (EB.gp p)) arg-less
gb-target (EB.gtl (EB.gp p)) = EB.<ᵀ-trans (VT.gω (EB.gtl (EB.gp p))) arg-less
gb-target (EB.gtl (EB.gtl p)) = gb-tail p
nf-arg : EB.NF target-arg
nf-arg = EB.n∷ (EB.nf-hd n) (EB.nf-le n)
  (EB.n∷ (EB.nf-hd (EB.nf-tl n)) (inj₁ (E.lv< E.[]<)) VT.nω′ᴮ)
  where n = EB.nfp-a (EB.nf-hd VT.nωᴮ)
nf-target : EB.NF target
nf-target = EB.nf-ψ EB.n[] nf-arg gb-target
opaque
  hc-target : E.HC target
  hc-target = ET.hc nf-target (EB.c∷ EB.c[])
target-low : (h : E.HC target) → RT.Rt h ≼ K.readRW MT.EBOᶻ
target-low (E.h0 ())
target-low (E.h1 () _)
target-low (E.hω _ hs) = l≼ (λ n → ≼-trans
  (RT.tree-≼ (fsn-target n) (hs n) (subst E.HC (fsn-target n) (hs n)))
  (finite-low n (subst E.HC (fsn-target n) (hs n))))
instance-low : RT.Rt hc-target ≼ K.readRW MT.EBOᶻ
instance-low = target-low hc-target
all-hc-low : (h : SI.E.HC target) → SI.E.tree h ≼ K.readRW MT.EBOᶻ
all-hc-low h = ≼-trans (XI.tree-back h) (target-low (XI.back h))
```
