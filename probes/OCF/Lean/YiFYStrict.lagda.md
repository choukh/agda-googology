# 新极限下界超过既有字面参照
验收文件；编译定理 strict-reference：新参照至少为 YiOLBoost.big 参照的后继；strict-over-FZ：新参照至少为旧基准树的第3个后继；no-FZ-back 排除反向值界。
新下界仍是 YiFYRef.target-low 的 ψ₀(Ω_Ω + ψ₁(Ω_ω) + ω) 整棵参照，不把严格性证据另报成参数内加1。
FZ 的字面旧基准是 suc(suc(Rt hΩω))；其与参数内 +2 的相等未证，本文件不作该替换。
来源：YiNFO.mono<、YiFZClimb.rep-advance、YiOLBoost.two-strict；正规形尾部与可见参数桥显式核对。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFYStrict where
open import Data.Nat using (ℕ; suc)
open import Data.List using ([]; _∷_)
open import Data.Sum using (inj₁)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Data.Product using (proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
import OCF.Align.EboLeanDef as E
import OCF.Align.EboLeanBase as EB
import OCF.Align.StandardOmega as SO
import OCF.Align.Standard as ST
import OCF.Align.Level as L
import OCF.Lean.YiVTANLim as VT
import OCF.Lean.YiNFO as NF
import OCF.Lean.YiRefTw2 as RT
import OCF.Lean.YiOLBoost as OL
import OCF.Lean.YiFYRef as R
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiFZClimb as FZ
import OCF.Lean.YiKVRel as K
open import OCF.Align.Value using (_≼_; ≼-trans; s≼s)
visible-G : ∀ {u z t} → SO.Vis₁ u z t → EB.InG u z t
visible-G (SO.vh h) = EB.gp (EB.gh h)
visible-G (SO.vd h v) = EB.gp (EB.gc h (visible-G v))
visible-G (SO.vs h v) = EB.gp (EB.gw h (visible-G v))
visible-G (SO.vt v) = EB.gtl (visible-G v)
nf-arg₁ : SO.NF₁ R.target-arg
nf-arg₁ = SO.n∷ SO.nfβ
  (SO.n∷ (SO.nψ SO.nf1 (SO.sC (ST.c∷ ST.c[])) VT.nΩω₁ VT.bndΩω)
    VT.nfω′ (inj₁ refl)) (inj₁ refl)
nf-target₁ : SO.NF₁ R.target
nf-target₁ = SO.n∷ (SO.nψ SO.n[] (SO.sC ST.c[]) nf-arg₁ (λ v → R.gb-target (visible-G v))) SO.n[] tt
nf-old₁ : SO.NF₁ OL.big
nf-old₁ = subst SO.NF₁ (sym (NF.fsn≡ R.target 1)) (SO.NF₁-fsn nf-target₁ refl 1)
old<target : OL.big E.<ᵀ R.target
old<target = E.hd< (E.ar< (E.tl< (E.tl< (E.hd< (E.ar< E.[]<)))))
strict-reference : (h : E.HC OL.big) (h′ : E.HC R.target) → L.suc (RT.Rt h) ≼ RT.Rt h′
strict-reference h h′ = NF.mono< nf-old₁ nf-target₁ h h′ old<target
strict-old-ebo : L.suc (RT.Rt OL.big-hc) ≼ K.readRW MT.EBOᶻ
strict-old-ebo = ≼-trans (strict-reference OL.big-hc R.hc-target) R.instance-low

old-two-below-big : L.suc (L.suc (RT.Rt VT.hΩω)) ≼ RT.Rt OL.big-hc
old-two-below-big = ≼-trans
  (≼-trans (s≼s (OL.two-strict VT.argω VT.nω₁ VT.hΩω (OL.rep-hc 2))) (FZ.rep-advance 1))
  (≼-trans (RT.tree-≼ refl (OL.rep-hc 3) (RT.hω-inv OL.big-hc refl 3)) (RT.fs≼ OL.big-hc refl 3))
strict-over-FZ : L.suc (L.suc (L.suc (RT.Rt VT.hΩω))) ≼ RT.Rt R.hc-target
strict-over-FZ = ≼-trans (s≼s old-two-below-big) (strict-reference OL.big-hc R.hc-target)

no-old-back : (h : E.HC OL.big) (h′ : E.HC R.target) → ¬ (RT.Rt h′ ≼ RT.Rt h)
no-old-back h h′ = NF.mono<-strict nf-old₁ nf-target₁ h h′ old<target
no-FZ-back : ¬ (RT.Rt R.hc-target ≼ L.suc (L.suc (RT.Rt VT.hΩω)))
no-FZ-back low = no-old-back OL.big-hc R.hc-target (≼-trans low old-two-below-big)
```
