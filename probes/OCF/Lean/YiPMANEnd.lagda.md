# 按表参数化: ANEnd 的下降部分

参数化（工程），数学内容与 `YiVTANEnd` 的下降部分相同；具体路径与出口另列，验收文件。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPMANEnd where

open import OCF.Lean.YiPMTable using (Table)

module F (tb : Table) where
  open import Data.Nat using (ℕ; zero; suc)
  open import Data.Unit using (⊤; tt)
  open import Data.Sum using (inj₁; inj₂)
  open import Data.Product using (_,_; proj₁; proj₂)
  open import Data.List using ([]; _∷_; _++_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

  open import OCF.Lean.YiLegBlock renaming (L to LF)
  open import OCF.Lean.YiLegOps
  open import OCF.Lean.YiLegPath using (_≤_; self; ins; Ev; Rt; Ev-tw; Rt-tw)
  import OCF.Lean.YiPMFold
  open OCF.Lean.YiPMFold.F tb
  open import OCF.Lean.YiLSRead using (read)
  import OCF.Lean.YiPMLSFold
  open OCF.Lean.YiPMLSFold.F tb using (OKB)
  import OCF.Lean.YiPMLSTw1
  open OCF.Lean.YiPMLSTw1.F tb using (h₁)
  import OCF.Lean.YiPMT2Frame
  open OCF.Lean.YiPMT2Frame.F tb using (ok-dW)
  import OCF.Lean.YiPMEBShape
  open OCF.Lean.YiPMEBShape.F tb using (dB; br; br≼)
  import OCF.Lean.YiPMEVReach
  open OCF.Lean.YiPMEVReach.F tb using (Hi; hi-dW; _⇐_; ⇐r; ⇐s; ⇐l; Ω≽0; Ω≽1)
  import OCF.Lean.YiMEBase as MB
  open import OCF.Lean.YiMWLow using (rd≼; tΩ; sem0)
  import OCF.Lean.YiPMPHEnd
  open OCF.Lean.YiPMPHEnd.F tb using (t₃)
  import OCF.Lean.YiRefTw2 as R2
  import OCF.Align.EboLeanDef as E
  open E using (HC; fsn; ψ; natT; _<ᵀ_; []<; hd<; tl<; lv<; ar<)
  import OCF.Align.EboLeanBase as B
  open import OCF.Align.EboLeanTree using (hc)
  open import OCF.Align.Standard using (Ctbl; c[]; c∷)
  open import OCF.Align.StandardOmega using (NF₁; n[]; n∷; nψ; sC; Bnd₁; vh; vd; vs; vt; bnd[];
    Flat; f[]; f∷; flatVis; flatBnd; f1; fΩ; nf1; nfβ)
  open import OCF.Lean.YiNFOCase using (ΩΩ; tA; nA₁; z<; flatG; flatGB; n1ᴮ; nΩΩᴮ)
  open import OCF.Lean.YiNFO using (mono<)
  import OCF.Align.Level as O
  open import OCF.Align.Value using (_≼_; ≼-trans)
  open import OCF.Lean.YiMTTab using (EBOᶻ)   -- 改: 搬到新主线的闭项
  open import OCF.Lean.YiBRValue using (readRW; up≼)
  import OCF.Lean.YiPMANFam
  open OCF.Lean.YiPMANFam.F tb using (fin; ψᴺ; Ωᴺ)
  import OCF.Lean.YiPMANLv
  open OCF.Lean.YiPMANLv.F tb using (module Lv)
  import OCF.Lean.YiPMANReach
  open OCF.Lean.YiPMANReach.F tb using (module Reach)

  ΩN : ℕ → E.PT
  ΩN n = ψ (natT n) []

  argN : ℕ → E.T
  argN m = ΩΩ ∷ ψ (natT 1) (ΩN (suc (suc (suc m))) ∷ []) ∷ []

  tN : ℕ → E.T
  tN m = ψ [] (argN m) ∷ []

  _ : ∀ m → tN m ≡ ψᴺ 0 (tΩ ++ ψᴺ 1 (Ωᴺ (suc (suc (suc m)))))
  _ = λ m → refl

  _ : tN 0 ≡ t₃
  _ = refl

  flatN : ∀ n → Flat (natT n)
  flatN zero    = f[]
  flatN (suc n) = f∷ f[] (flatN n)

  fΩN : ∀ n → Flat (ΩN n ∷ [])
  fΩN n = f∷ (flatN n) f[]

  natNF₁ : ∀ n → NF₁ (natT n)
  natNF₁ zero          = n[]
  natNF₁ (suc zero)    = nf1
  natNF₁ (suc (suc n)) = n∷ (nψ n[] (sC c[]) n[] bnd[]) (natNF₁ (suc n)) (inj₂ refl)

  ctblN : ∀ n → Ctbl (natT n)
  ctblN zero    = c[]
  ctblN (suc n) = c∷ (ctblN n)

  nΩN₁ : ∀ n → NF₁ (ΩN n ∷ [])
  nΩN₁ n = n∷ (nψ (natNF₁ n) (sC (ctblN n)) n[] bnd[]) n[] tt

  bndN : ∀ m → Bnd₁ [] (argN m)
  bndN m (vh _)        = []<
  bndN m (vd _ ())
  bndN m (vs _ v)      = z< (flatVis fΩ v)
  bndN m (vt (vh _))   = hd< (lv< (hd< (lv< []<)))
  bndN m (vt (vd _ v)) = z< (flatVis (fΩN (suc (suc (suc m)))) v)
  bndN m (vt (vs _ v)) = z< (flatVis f1 v)
  bndN m (vt (vt ()))

  nN₁ : ∀ m → NF₁ (tN m)
  nN₁ m = n∷ (nψ n[] (sC c[])
            (n∷ nfβ (n∷ (nψ nf1 (sC (c∷ c[])) (nΩN₁ (suc (suc (suc m)))) (flatBnd (fΩN (suc (suc (suc m)))))) n[] tt)
              (inj₁ refl))
            (bndN m)) n[] tt

  natB : ∀ n → B.NF (natT n)
  natB zero          = B.n[]
  natB (suc zero)    = n1ᴮ
  natB (suc (suc n)) = B.n∷ (B.nψ B.n[] B.n[] B.GB[]) (inj₂ refl) (natB (suc n))

  nΩNᴮ : ∀ n → B.NFP (ΩN n)
  nΩNᴮ n = B.nψ (natB n) B.n[] B.GB[]

  gN : ∀ m → B.GB [] (argN m) (argN m)
  gN m (B.gp (B.gh _))           = []<
  gN m (B.gp (B.gw _ i))         = z< (flatG fΩ i)
  gN m (B.gp (B.gc _ ()))
  gN m (B.gtl (B.gp (B.gh _)))   = hd< (lv< (hd< (lv< []<)))
  gN m (B.gtl (B.gp (B.gw _ i))) = z< (flatG f1 i)
  gN m (B.gtl (B.gp (B.gc _ i))) = z< (flatG (fΩN (suc (suc (suc m)))) i)
  gN m (B.gtl (B.gtl ()))

  nNᴮ : ∀ m → B.NF (tN m)
  nNᴮ m = B.n∷ (B.nψ B.n[] (B.n∷ nΩΩᴮ (inj₁ (lv< (hd< (lv< []<))))
                  (B.n∷ (B.nψ n1ᴮ (B.n∷ (nΩNᴮ (suc (suc (suc m)))) tt B.n[]) (flatGB (fΩN (suc (suc (suc m)))))) tt B.n[]))
                (gN m)) tt B.n[]

  opaque
    hN : ∀ m → HC (tN m)
    hN m = hc (nNᴮ m) (B.c∷ B.c[])

  nat< : ∀ n → natT n <ᵀ natT (suc n)
  nat< zero    = []<
  nat< (suc n) = tl< (nat< n)

  A<N : ∀ m → tA <ᵀ tN m
  A<N m = hd< (ar< (tl< (hd< (ar< (hd< (lv< (tl< (tl< []<))))))))

  N<N : ∀ m → tN m <ᵀ tN (suc m)
  N<N m = hd< (ar< (tl< (hd< (ar< (hd< (lv< (nat< (suc (suc (suc m))))))))))

  A≺N : ∀ m (h : HC tA) (h′ : HC (tN m)) → O.suc (R2.Rt h) ≼ R2.Rt h′
  A≺N m h h′ = mono< nA₁ (nN₁ m) h h′ (A<N m)

  N≺N : ∀ m (h : HC (tN m)) (h′ : HC (tN (suc m))) → O.suc (R2.Rt h) ≼ R2.Rt h′
  N≺N m h h′ = mono< (nN₁ m) (nN₁ (suc m)) h h′ (N<N m)

  module AtN (m : ℕ) (ε : Ev (fin (suc (suc (suc m))))) (ρ : Rt (fin (suc (suc (suc m)))))
             (B₃ : Base (fin (suc (suc (suc m))))) (ok : OKB (fin (suc (suc (suc m)))) B₃)
             (hi : Hi (fin (suc (suc (suc m)))) B₃) where
    module A = Lv.Anchor tΩ m ε ρ B₃ ok (sem0 (b⊥ B₃) (proj₁ hi)) (λ w → sem0 (bs B₃ zero w) (proj₂ hi w))

    atN : (h : HC (tN m)) → R2.Rt h ≼ read (ψ⊥ (fin (suc (suc (suc m)))) ε ρ B₃ (Ωt (fin (suc (suc (suc m))))))
    atN h = ≼-trans (MB.lower⁰ A.anchor h) (rd≼ _)
```
