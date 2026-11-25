# 验收: 终点闭项不低于 ψ₀(Ω_Ω+ψ₁(Ω_ω)) 的参照 (带表的 F2 对照块上的副本)

> 验收文件, 不进成品. 来源: 脚本从 `YiANLim` 照搬全部代码, 只把导入的 F2 折叠换成 [YiVTFold](YiVTFold.lagda.md) (依赖换成对应的 `YiVT` 副本); 陈述与证明的文字未改, 手改之处见文内 "改:" 注释.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTANLim where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using ([]; _∷_; replicate)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

import OCF.Lean.YiRefTw2 as R2
import OCF.Align.EboLeanDef as E
open E using (HC; h0; h1; hω; fsn; ψ; 𝟏; natT; _<ᵀ_; []<; hd<; tl<; lv<; ar<)
import OCF.Align.EboLeanBase as B
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Align.Standard using (c[]; c∷)
open import OCF.Align.StandardOmega using (NF₁; n[]; n∷; nψ; sC; Bnd₁; vh; vd; vs; vt; bnd[];
  Flat; flatVis; flatBnd; f1; fΩ; nf1; nfβ; NF₁-fsn)
open import OCF.Lean.YiNFOCase using (ΩΩ; z<; flatG; flatGB; n1ᴮ; nΩΩᴮ)
open import OCF.Lean.YiNFO using (mono<; fsn≡; ↓suc)
import OCF.Align.Level as O
open import OCF.Align.Value using (_≼_; l≼; ≼-trans)
open import OCF.Lean.YiMTTab using (EBOᶻ)   -- 改: 搬到新主线的闭项
open import OCF.Lean.YiBRValue using (readRW)
open import OCF.Lean.YiVTANEnd using (tN; nN₁; hN; tN≼EBOᴿ)

ω′ : E.T
ω′ = ψ [] (𝟏 ∷ []) ∷ []

Ωω : E.PT
Ωω = ψ ω′ []

argω : E.T
argω = ΩΩ ∷ ψ (natT 1) (Ωω ∷ []) ∷ []

tω : E.T
tω = ψ [] argω ∷ []

_ : ∀ n → fsn tω n ≡ ψ [] (ΩΩ ∷ ψ (natT 1) (ψ (replicate n 𝟏) [] ∷ []) ∷ []) ∷ []
_ = λ n → refl

rep< : ∀ n → replicate n 𝟏 <ᵀ natT (suc (suc (suc n)))
rep< zero    = []<
rep< (suc n) = tl< (rep< n)

lt : ∀ n → fsn tω n <ᵀ tN n
lt n = hd< (ar< (tl< (hd< (ar< (hd< (lv< (rep< n)))))))

N<ω : ∀ m → tN m <ᵀ tω
N<ω m = hd< (ar< (tl< (hd< (ar< (hd< (lv< (hd< (ar< []<))))))))

nfω′ : NF₁ ω′
nfω′ = n∷ (nψ n[] (sC c[]) nf1 (flatBnd f1)) n[] tt

nΩω₁ : NF₁ (Ωω ∷ [])
nΩω₁ = n∷ (nψ nfω′ (sC (c∷ c[])) n[] bnd[]) n[] tt

bndΩω : Bnd₁ (natT 1) (Ωω ∷ [])
bndΩω (vh _) = []<
bndΩω (vd _ ())
bndΩω (vs _ (vh (inj₁ ())))
bndΩω (vs _ (vh (inj₂ ())))
bndΩω (vs _ (vd (inj₁ ()) _))
bndΩω (vs _ (vd (inj₂ ()) _))
bndΩω (vs _ (vs (inj₁ ()) _))
bndΩω (vs _ (vs (inj₂ ()) _))
bndΩω (vs _ (vt ()))
bndΩω (vt ())

bndω : Bnd₁ [] argω
bndω (vh _)                      = []<
bndω (vd _ ())
bndω (vs _ v)                    = z< (flatVis fΩ v)
bndω (vt (vh _))                 = hd< (lv< (hd< (lv< []<)))
bndω (vt (vd _ (vh _)))          = []<
bndω (vt (vd _ (vd _ ())))
bndω (vt (vd _ (vs _ (vh _))))   = hd< (lv< []<)
bndω (vt (vd _ (vs _ (vd _ v)))) = z< (flatVis f1 v)
bndω (vt (vd _ (vs _ (vs _ ()))))
bndω (vt (vd _ (vs _ (vt ()))))
bndω (vt (vd _ (vt ())))
bndω (vt (vs _ v))               = z< (flatVis f1 v)
bndω (vt (vt ()))

nω₁ : NF₁ tω
nω₁ = n∷ (nψ n[] (sC c[]) (n∷ nfβ (n∷ (nψ nf1 (sC (c∷ c[])) nΩω₁ bndΩω) n[] tt) (inj₁ refl)) bndω) n[] tt

nfω : ∀ n → NF₁ (fsn tω n)
nfω n = subst NF₁ (sym (fsn≡ tω n)) (NF₁-fsn nω₁ refl n)

nω′ᴮ : B.NF ω′
nω′ᴮ = B.n∷ (B.nψ B.n[] n1ᴮ (flatGB f1)) tt B.n[]

nΩωᴮ : B.NFP Ωω
nΩωᴮ = B.nψ nω′ᴮ B.n[] B.GB[]

gΩω : B.GB (natT 1) (Ωω ∷ []) (Ωω ∷ [])
gΩω (B.gp (B.gh _)) = []<
gΩω (B.gp (B.gw _ (B.gp (B.gh (inj₁ ())))))
gΩω (B.gp (B.gw _ (B.gp (B.gh (inj₂ ())))))
gΩω (B.gp (B.gw _ (B.gp (B.gw (inj₁ ()) _))))
gΩω (B.gp (B.gw _ (B.gp (B.gw (inj₂ ()) _))))
gΩω (B.gp (B.gw _ (B.gp (B.gc (inj₁ ()) _))))
gΩω (B.gp (B.gw _ (B.gp (B.gc (inj₂ ()) _))))
gΩω (B.gp (B.gw _ (B.gtl ())))
gΩω (B.gp (B.gc _ ()))
gΩω (B.gtl ())

gω : B.GB [] argω argω
gω (B.gp (B.gh _))                                           = []<
gω (B.gp (B.gw _ i))                                         = z< (flatG fΩ i)
gω (B.gp (B.gc _ ()))
gω (B.gtl (B.gp (B.gh _)))                                   = hd< (lv< (hd< (lv< []<)))
gω (B.gtl (B.gp (B.gw _ i)))                                 = z< (flatG f1 i)
gω (B.gtl (B.gp (B.gc _ (B.gp (B.gh _)))))                   = []<
gω (B.gtl (B.gp (B.gc _ (B.gp (B.gw _ (B.gp (B.gh _)))))))   = hd< (lv< []<)
gω (B.gtl (B.gp (B.gc _ (B.gp (B.gw _ (B.gp (B.gw _ ())))))))
gω (B.gtl (B.gp (B.gc _ (B.gp (B.gw _ (B.gp (B.gc _ i))))))) = z< (flatG f1 i)
gω (B.gtl (B.gp (B.gc _ (B.gp (B.gw _ (B.gtl ()))))))
gω (B.gtl (B.gp (B.gc _ (B.gp (B.gc _ ())))))
gω (B.gtl (B.gp (B.gc _ (B.gtl ()))))
gω (B.gtl (B.gtl ()))

nωᴮ : B.NF tω
nωᴮ = B.n∷ (B.nψ B.n[] (B.n∷ nΩΩᴮ (inj₁ (lv< (hd< (lv< []<))))
                (B.n∷ (B.nψ n1ᴮ (B.n∷ nΩωᴮ tt B.n[]) gΩω) tt B.n[])) gω) tt B.n[]

opaque
  hΩω : HC tω
  hΩω = hc nωᴮ (B.c∷ B.c[])

N≺ω : ∀ m (h : HC (tN m)) (h′ : HC tω) → O.suc (R2.Rt h) ≼ R2.Rt h′
N≺ω m h h′ = mono< (nN₁ m) nω₁ h h′ (N<ω m)

tω≼EBOᴿ : (h : HC tω) → R2.Rt h ≼ readRW EBOᶻ
tω≼EBOᴿ (h0 ())
tω≼EBOᴿ (h1 () _)
tω≼EBOᴿ (hω e hs) =
  l≼ (λ n → ≼-trans (↓suc (mono< (nfω n) (nN₁ n) (hs n) (hN n) (lt n))) (tN≼EBOᴿ n (hN n)))

instω : R2.Rt hΩω ≼ readRW EBOᶻ
instω = tω≼EBOᴿ hΩω
```
