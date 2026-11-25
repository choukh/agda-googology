# 验收: 终点闭项不低于 ψ₀(Ω_Ω+ψ₁(Ω₃)) 的参照 (带表的 F2 对照块上的副本)

> 验收文件, 不进成品. 来源: 脚本从 `YiPHEnd` 照搬全部代码, 只把导入的 F2 折叠换成 [YiVTFold](YiVTFold.lagda.md) (依赖换成对应的 `YiVT` 副本); 陈述与证明的文字未改, 手改之处见文内 "改:" 注释.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTPHEnd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; Ev; Rt; Ev-tw; Rt-tw)
open import OCF.Lean.YiVTFold
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiVTLSFold using (OKB; ok-dS; ok-dL)
open import OCF.Lean.YiVTLSTw1 using (h₁)
open import OCF.Lean.YiVTT2Frame using (ok-dW)
open import OCF.Lean.YiVTEBShape using (dB; br; br≼)
open import OCF.Lean.YiVTEVReach
open import OCF.Lean.YiVTEVEnd using (h₂; Br0; ε′; ρ′; ok0; hi1; c₁; B₁)
import OCF.Lean.YiMEBase as MB
open import OCF.Lean.YiVTMEAnchor using (one; two; Mβ₀; ψ₀ᵗ; ψ₁ᵗ; module G¹)
open import OCF.Lean.YiMWLow using (rd≼; tΩ; sem0)
open import OCF.Lean.YiVTPHBase using (three; u₂; Mβ₂; module G²)
open import OCF.Lean.YiVTPHCtx using (module Ctx3)
import OCF.Lean.YiRefTw2 as R2
import OCF.Align.EboLeanDef as E
open E using (HC; fsn; ψ; natT; _<ᵀ_; []<; hd<; tl<; lv<; ar<)
import OCF.Align.EboLeanBase as B
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Align.Standard using (c[]; c∷)
open import OCF.Align.StandardOmega using (NF₁; n[]; n∷; nψ; sC; Bnd₁; vh; vd; vs; vt; bnd[];
  Flat; f[]; f∷; flatVis; flatBnd; f1; fΩ; nf1; nfβ)
open import OCF.Lean.YiNFOCase using (ΩΩ; tA; tB; nA₁; nfB; z<; f2; nf2₁; flatG; flatGB; n1ᴮ; n2ᴮ; nΩΩᴮ)
open import OCF.Lean.YiNFO using (mono<)
import OCF.Align.Level as O
open import OCF.Align.Value using (_≼_; ≼-trans)
open import OCF.Lean.YiMTTab using (EBOᶻ)   -- 改: 搬到新主线的闭项
open import OCF.Lean.YiVTTw using (EBOᶻ-R)
open import OCF.Lean.YiBRValue using (readRW; up≼)

Ω₃ : E.PT
Ω₃ = ψ (natT 3) []

ψ₁Ω₃ : E.PT
ψ₁Ω₃ = ψ (natT 1) (Ω₃ ∷ [])

arg₃ : E.T
arg₃ = ΩΩ ∷ ψ₁Ω₃ ∷ []

t₃ : E.T
t₃ = ψ [] arg₃ ∷ []

_ : t₃ ≡ ψ₀ᵗ (tΩ ++ ψ₁ᵗ (E.Ωs u₂))
_ = refl

_ : ∀ n → fsn t₃ n ≡ ψ₀ᵗ (tΩ ++ ψ₁ᵗ (E.γT (E.Ωs u₂) u₂ n))
_ = λ n → refl

f3 : Flat (natT 3)
f3 = f∷ f[] f2

fΩ₃ : Flat (Ω₃ ∷ [])
fΩ₃ = f∷ f3 f[]

nf3₁ : NF₁ (natT 3)
nf3₁ = n∷ (nψ n[] (sC c[]) n[] bnd[]) nf2₁ (inj₂ refl)

nΩ₃₁ : NF₁ (Ω₃ ∷ [])
nΩ₃₁ = n∷ (nψ nf3₁ (sC (c∷ (c∷ (c∷ c[])))) n[] bnd[]) n[] tt

bnd₃ : Bnd₁ [] arg₃
bnd₃ (vh _)        = []<
bnd₃ (vd _ ())
bnd₃ (vs _ v)      = z< (flatVis fΩ v)
bnd₃ (vt (vh _))   = hd< (lv< (hd< (lv< []<)))
bnd₃ (vt (vd _ v)) = z< (flatVis fΩ₃ v)
bnd₃ (vt (vs _ v)) = z< (flatVis f1 v)
bnd₃ (vt (vt ()))

n₃₁ : NF₁ t₃
n₃₁ = n∷ (nψ n[] (sC c[]) (n∷ nfβ (n∷ (nψ nf1 (sC (c∷ c[])) nΩ₃₁ (flatBnd fΩ₃)) n[] tt) (inj₁ refl)) bnd₃) n[] tt

n3ᴮ : B.NF (natT 3)
n3ᴮ = B.n∷ (B.nψ B.n[] B.n[] B.GB[]) (inj₂ refl) n2ᴮ

nΩ₃ᴮ : B.NFP Ω₃
nΩ₃ᴮ = B.nψ n3ᴮ B.n[] B.GB[]

g₃ : B.GB [] arg₃ arg₃
g₃ (B.gp (B.gh _))           = []<
g₃ (B.gp (B.gw _ i))         = z< (flatG fΩ i)
g₃ (B.gp (B.gc _ ()))
g₃ (B.gtl (B.gp (B.gh _)))   = hd< (lv< (hd< (lv< []<)))
g₃ (B.gtl (B.gp (B.gw _ i))) = z< (flatG f1 i)
g₃ (B.gtl (B.gp (B.gc _ i))) = z< (flatG fΩ₃ i)
g₃ (B.gtl (B.gtl ()))

n₃ᴮ : B.NF t₃
n₃ᴮ = B.n∷ (B.nψ B.n[] (B.n∷ nΩΩᴮ (inj₁ (lv< (hd< (lv< []<))))
                         (B.n∷ (B.nψ n1ᴮ (B.n∷ nΩ₃ᴮ tt B.n[]) (flatGB fΩ₃)) tt B.n[])) g₃) tt B.n[]

opaque
  h₃ : HC t₃
  h₃ = hc n₃ᴮ (B.c∷ B.c[])

A<3 : tA <ᵀ t₃
A<3 = hd< (ar< (tl< (hd< (ar< (hd< (lv< (tl< (tl< []<))))))))

3<B1 : t₃ <ᵀ fsn tB 1
3<B1 = hd< (ar< (tl< (hd< (ar< (hd< (lv< (hd< (lv< []<))))))))

A≺3 : (h : HC tA) (h′ : HC t₃) → O.suc (R2.Rt h) ≼ R2.Rt h′
A≺3 h h′ = mono< nA₁ n₃₁ h h′ A<3

3≺B1 : (h : HC t₃) (h′ : HC (fsn tB 1)) → O.suc (R2.Rt h) ≼ R2.Rt h′
3≺B1 h h′ = mono< n₃₁ (nfB 1) h h′ 3<B1

Lo³ : (ℓ : LF) → Ev ℓ → Rt ℓ → Base ℓ → Set
Lo³ ℓ ε ρ B = (h : HC t₃) → R2.Rt h ≼ read (ψ⊥ ℓ ε ρ B (Ωt ℓ))

module AtThree (B₃ : Base three) (ok : OKB three B₃) (hi : Hi three B₃) where
  module C = Ctx3 B₃ (G².m⊴ Mβ₂ (cv⊴ (proj₂ ok two (ins self)))) (cv⊴ (proj₂ ok two (ins self)))
    (G¹.m⊴ Mβ₀ (cv⊴ (proj₂ ok one (ins (ins self))))) tΩ
    (sem0 (bs B₃ zero (ins (ins (ins self)))) (proj₂ hi (ins (ins (ins self))))) (sem0 (b⊥ B₃) (proj₁ hi))

  atThree : Lo³ three tt tt B₃
  atThree h = ≼-trans (MB.lower⁰ C.anchor³ h) (rd≼ _)

reach³ : ∀ {ℓ} → three ⇐ ℓ → (ε : Ev ℓ) (ρ : Rt ℓ) (B : Base ℓ) → OKB ℓ B → Hi ℓ B → Lo³ ℓ ε ρ B
reach³ ⇐r ε ρ B ok hi = AtThree.atThree B ok hi
reach³ (⇐s {a} p) ε ρ B ok hi h =
  ≼-trans (reach³ p ε ρ (dS a ε ρ B zero) (ok-dS ε ρ B ok zero) (hi-dS a ε ρ B hi zero) h) (suc≽ a ε ρ B ok)
reach³ (⇐l {g} n p) ε ρ B ok hi h =
  ≼-trans (reach³ p (ε n) (proj₁ ρ n) (dL g ε ρ B n (preΩ g n)) (ok-dL g ε ρ B ok n (preΩ g n)) (hi-dL g ε ρ B hi n (preΩ g n)) h)
    (lim≽ g ε ρ B n)
reach³ (⇐w {k} {h = f} p) ε ρ B ok hi h =
  ≼-trans (reach³ p (proj₂ (proj₂ ε zero)) (proj₂ ρ zero) (dW k f ε ρ B zero zero) (ok-dW k f ε ρ B ok zero zero) (hi-dW k f ε ρ B hi zero zero) h)
    (Ω≽0 k f ε ρ B)

path₃ : three ⇐ h₁ c₁
-- 改: 带表时链的起点是 `next 1`, 它的第 2 个孩子的层号是 3 (原来是后继下 ℕ 极限的第 1 个孩子)
path₃ = ⇐l 0 (⇐l 0 (⇐l 0 (⇐l 2 ⇐r)))

low3 : Lo³ (h₁ c₁) (proj₂ (proj₂ ε′ c₁)) (proj₂ ρ′ c₁) B₁
low3 = reach³ path₃ (proj₂ (proj₂ ε′ c₁)) (proj₂ ρ′ c₁) B₁
  (ok-dW zero h₁ ε′ ρ′ Br0 ok0 c₁ zero) hi1 {- 改: 原为 hi-dW 作用在全路径的 Hi 上 -}

t₃≼br2 : (h : HC t₃) → R2.Rt h ≼ read (br 2)
t₃≼br2 h = ≼-trans (low3 h) (≼-trans (Ω≽1 zero h₁ ε′ ρ′ Br0) (Ω≽0 (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (dB 2)))

t₃≼EBO : (h : HC t₃) → R2.Rt h ≼ read EBOᶜ
t₃≼EBO h = ≼-trans (t₃≼br2 h) (br≼ 2)

t₃≼EBOᴿ : (h : HC t₃) → R2.Rt h ≼ readRW EBOᶻ
t₃≼EBOᴿ h = up≼ EBOᶻ-R (t₃≼EBO h)

inst₃ : R2.Rt h₃ ≼ readRW EBOᶻ
inst₃ = t₃≼EBOᴿ h₃

tA≺EBOᴿ′ : (h : HC tA) → O.suc (R2.Rt h) ≼ readRW EBOᶻ
tA≺EBOᴿ′ h = ≼-trans (A≺3 h h₃) inst₃
```
