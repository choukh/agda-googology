# 验收: 对一切 m, 终点闭项不低于 ψ₀(Ω_Ω+ψ₁(Ω_{m+3})) 的参照 (带表的 F2 对照块上的副本)

> 验收文件, 不进成品. 来源: 脚本从 `YiANEnd` 照搬全部代码, 只把导入的 F2 折叠换成 [YiVTFold](YiVTFold.lagda.md) (依赖换成对应的 `YiVT` 副本); 陈述与证明的文字未改, 手改之处见文内 "改:" 注释.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTANEnd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; Ev; Rt; Ev-tw; Rt-tw)
open import OCF.Lean.YiVTFold
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiVTLSFold using (OKB)
open import OCF.Lean.YiVTLSTw1 using (h₁)
open import OCF.Lean.YiVTT2Frame using (ok-dW)
open import OCF.Lean.YiVTEBShape using (dB; br; br≼)
open import OCF.Lean.YiVTEVReach using (Hi; hi-dW; _⇐_; ⇐r; ⇐s; ⇐l; Ω≽0; Ω≽1)
open import OCF.Lean.YiVTEVEnd using (h₂; Br0; ε′; ρ′; ok0; hi1; c₁; B₁)
import OCF.Lean.YiMEBase as MB
open import OCF.Lean.YiMWLow using (rd≼; tΩ; sem0)
open import OCF.Lean.YiVTPHEnd using (t₃)
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
open import OCF.Lean.YiVTTw using (EBOᶻ-R)
open import OCF.Lean.YiBRValue using (readRW; up≼)
open import OCF.Lean.YiVTANFam using (fin; ψᴺ; Ωᴺ)
open import OCF.Lean.YiVTANLv using (module Lv)
open import OCF.Lean.YiVTANReach using (module Reach)

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

kid : LF → ℕ → LF
kid (lim g) n = g n
kid x       _ = x

pre : LF → LF
pre (suc a) = a
pre x       = x

G : ℕ → LF
-- 改: 带表时链的起点是 `next 1`, 前三步之后直接是 ℕ 极限层号, 第 k 个孩子是 `fin (k+1)`
G k = kid (kid (kid (kid (h₁ c₁) 0) 0) 0) k

one : Tr zero
one = suc zero

num : ℕ → Tr zero
num zero    = zero
num (suc j) = suc (num j)

shape : ∀ k → G k ≡ zero ⊕ ↑ zero (iter (one +_) one k)
shape k = refl

one+ : ∀ j → one + num j ≡ num (suc j)
one+ zero    = refl
one+ (suc j) = cong suc (one+ j)

I≡ : ∀ k → iter (one +_) one k ≡ num (suc k)
I≡ zero    = refl
I≡ (suc k) = trans (cong (one +_) (I≡ k)) (one+ (suc k))

ι-num : ∀ j → ι zero (num j) ≡ num j
ι-num zero    = refl
ι-num (suc j) = cong suc (ι-num j)

↑num : ∀ j → ↑ zero (num j) ≡ fin j
↑num zero    = refl
↑num (suc j) = cong suc (↑num j)

0⊕ : ∀ j → zero ⊕ fin j ≡ fin j
0⊕ zero    = refl
0⊕ (suc j) = cong suc (0⊕ j)

gk : ∀ k → G k ≡ fin (suc k)
gk k = trans (shape k)
  (trans (cong (λ x → zero ⊕ ↑ zero x) (I≡ k))
    (trans (cong (zero ⊕_) (↑num (suc k))) (0⊕ (suc k))))

pathN : ∀ m → fin (suc (suc (suc m))) ⇐ h₁ c₁
pathN m = ⇐l 0 (⇐l 0 (⇐l 0 (⇐l (suc (suc m)) (subst (fin (suc (suc (suc m))) ⇐_) (sym (gk (suc (suc m)))) ⇐r))))

module _ (m : ℕ) where
  open Reach (fin (suc (suc (suc m)))) (tN m)

  lowN : LoG (h₁ c₁) (proj₂ (proj₂ ε′ c₁)) (proj₂ ρ′ c₁) B₁
  lowN = reachG (AtN.atN m) (pathN m) (proj₂ (proj₂ ε′ c₁)) (proj₂ ρ′ c₁) B₁
    (ok-dW zero h₁ ε′ ρ′ Br0 ok0 c₁ zero) hi1 {- 改: 原为 hi-dW 作用在全路径的 Hi 上 -}

  tN≼br2 : (h : HC (tN m)) → R2.Rt h ≼ read (br 2)
  tN≼br2 h = ≼-trans (lowN h) (≼-trans (Ω≽1 zero h₁ ε′ ρ′ Br0) (Ω≽0 (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (dB 2)))

  tN≼EBO : (h : HC (tN m)) → R2.Rt h ≼ read EBOᶜ
  tN≼EBO h = ≼-trans (tN≼br2 h) (br≼ 2)

  tN≼EBOᴿ : (h : HC (tN m)) → R2.Rt h ≼ readRW EBOᶻ
  tN≼EBOᴿ h = up≼ EBOᶻ-R (tN≼EBO h)

  instN : R2.Rt (hN m) ≼ readRW EBOᶻ
  instN = tN≼EBOᴿ (hN m)
```
