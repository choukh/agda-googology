# 验收: 对一切 m, 终点闭项不低于 ψ₀(Ω_Ω+ψ₁(Ω_{m+3})) 的参照

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提, 对一切 m. `tN≼EBOᴿ : ∀ m (h : HC (tN m)) → R2.Rt h ≼ readRW RW.EBOᶜ` (主线精简块), `tN m` 是记号项 ψ₀(Ω_Ω+ψ₁(Ω_{m+3})); 推导 `hN m : HC (tN m)` 对一切 m 存在.
> 做法: [YiANLv](YiANLv.lagda.md) 的 `Lv.Anchor.anchor` 代入满足 `OKB` 与 `Hi` 的底与前缀 Ω_Ω (`AtN.atN`); 下降用 [YiANReach](YiANReach.lagda.md) 的 `reachG`; 路径在层号 `h₁ c₁` 里末一步取孩子 m+1, 它是 `fin (m+3)` (`gk`).
> 项序: tA < tN m < tN (m+1) (`A≺N`, `N≺N`, 对任意推导). 不涉及上界; 极限项 ψ₀(Ω_Ω+ψ₁(Ω_ω)) 见 [YiANLim](YiANLim.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiANEnd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; Ev; Rt; Ev-tw; Rt-tw)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiLSFold using (OKB)
open import OCF.Lean.YiLSTw1 using (h₁)
open import OCF.Lean.YiT2Frame using (ok-dW)
open import OCF.Lean.YiEBShape using (dB; br; br≼)
open import OCF.Lean.YiEVReach using (Hi; hi-dW; _⇐_; ⇐r; ⇐s; ⇐l; Ω≽0; Ω≽1)
open import OCF.Lean.YiEVEnd using (h₂; Br0; ε′; ρ′; ok0; hi0; c₁; B₁)
import OCF.Lean.YiMEBase as MB
open import OCF.Lean.YiMWLow using (rd≼; tΩ; sem0)
open import OCF.Lean.YiPHEnd using (t₃)
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
import OCF.Lean.YiRWFold as RW
open import OCF.Lean.YiBRTw using (EBOᶜ-R)
open import OCF.Lean.YiBRValue using (readRW; up≼)
open import OCF.Lean.YiANFam using (fin; ψᴺ; Ωᴺ)
open import OCF.Lean.YiANLv using (module Lv)
open import OCF.Lean.YiANReach using (module Reach)
```

## 记号项 ψ₀(Ω_Ω+ψ₁(Ω_{m+3})), 对一切 m

两种标准形证明与 `YiPHEnd` 的 t₃ 同法, 层号 `natT n` 的部分对 n 归纳. `tN 0` 就是 t₃.

```agda
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
```

项序: tA < tN m < tN (m+1); 由 `YiNFO.mono<` 得参照的严格序.

```agda
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
```

## 层号 `fin (m+3)` 处: 锚点对一般底

`OKB` 给出各分量在 Ω 树之上; `Hi` 经 `sem0` 给出第 0 层分量与 `b⊥` 对着 ψ₀(Ω_Ω).

```agda
module AtN (m : ℕ) (ε : Ev (fin (suc (suc (suc m))))) (ρ : Rt (fin (suc (suc (suc m)))))
           (B₃ : Base (fin (suc (suc (suc m))))) (ok : OKB (fin (suc (suc (suc m)))) B₃)
           (hi : Hi (fin (suc (suc (suc m)))) B₃) where
  module A = Lv.Anchor tΩ m ε ρ B₃ ok (sem0 (b⊥ B₃) (proj₁ hi)) (λ w → sem0 (bs B₃ zero w) (proj₂ hi w))

  atN : (h : HC (tN m)) → R2.Rt h ≼ read (ψ⊥ (fin (suc (suc (suc m)))) ε ρ B₃ (Ωt (fin (suc (suc (suc m))))))
  atN h = ≼-trans (MB.lower⁰ A.anchor h) (rd≼ _)
```

## 路径: 层号 `h₁ c₁` 里的 ℕ 极限层号, 第 k 个孩子是 `fin (k+2)`

`G k` 是沿 `YiPHEnd.path₃` 的前四步 (孩子 0, 0, 0, 后继) 之后那个 ℕ 极限层号的第 k 个孩子. 它是 1 + ι(1·(k+1)) 抬成的层号 (`shape`, `refl`), 对 k 归纳算出 (`gk`).

```agda
kid : LF → ℕ → LF
kid (lim g) n = g n
kid x       _ = x

pre : LF → LF
pre (suc a) = a
pre x       = x

G : ℕ → LF
G k = kid (pre (kid (kid (kid (h₁ c₁) 0) 0) 0)) k

one : Tr zero
one = suc zero

num : ℕ → Tr zero
num zero    = zero
num (suc j) = suc (num j)

shape : ∀ k → G k ≡ zero ⊕ ↑ zero (one + ι zero (iter (one +_) one k))
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

gk : ∀ k → G k ≡ fin (suc (suc k))
gk k = trans (shape k)
  (trans (cong (λ x → zero ⊕ ↑ zero (one + ι zero x)) (I≡ k))
    (trans (cong (λ x → zero ⊕ ↑ zero (one + x)) (ι-num (suc k)))
      (trans (cong (λ x → zero ⊕ ↑ zero x) (one+ (suc k)))
        (trans (cong (zero ⊕_) (↑num (suc (suc k)))) (0⊕ (suc (suc k)))))))

pathN : ∀ m → fin (suc (suc (suc m))) ⇐ h₁ c₁
pathN m = ⇐l 0 (⇐l 0 (⇐l 0 (⇐s (⇐l (suc m) (subst (fin (suc (suc (suc m))) ⇐_) (sym (gk (suc m))) ⇐r)))))
```

## 终点

```agda
module _ (m : ℕ) where
  open Reach (fin (suc (suc (suc m)))) (tN m)

  lowN : LoG (h₁ c₁) (proj₂ (proj₂ ε′ c₁)) (proj₂ ρ′ c₁) B₁
  lowN = reachG (AtN.atN m) (pathN m) (proj₂ (proj₂ ε′ c₁)) (proj₂ ρ′ c₁) B₁
    (ok-dW zero h₁ ε′ ρ′ Br0 ok0 c₁ zero) (hi-dW zero h₁ ε′ ρ′ Br0 hi0 c₁ zero)

  tN≼br2 : (h : HC (tN m)) → R2.Rt h ≼ read (br 2)
  tN≼br2 h = ≼-trans (lowN h) (≼-trans (Ω≽1 zero h₁ ε′ ρ′ Br0) (Ω≽0 (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (dB 2)))

  tN≼EBO : (h : HC (tN m)) → R2.Rt h ≼ read EBOᶜ
  tN≼EBO h = ≼-trans (tN≼br2 h) (br≼ 2)

  tN≼EBOᴿ : (h : HC (tN m)) → R2.Rt h ≼ readRW RW.EBOᶜ
  tN≼EBOᴿ h = up≼ EBOᶜ-R (tN≼EBO h)

  instN : R2.Rt (hN m) ≼ readRW RW.EBOᶜ
  instN = tN≼EBOᴿ (hN m)
```
