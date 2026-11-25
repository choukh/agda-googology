# 主线候选的值: 终点不低于 ψ₀(Ω_Ω+ψ₁(Ω_ω)) 的参照

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 编译定理, 无前提: 原主线终点上的值定理都搬到兄弟孩子的终点 `EBOˢ`: `tA≼EBOˢ`, `t₃≼EBOˢ`, `tN≼EBOˢ` (对一切 m), `tω≼EBOˢ` (ψ₀(Ω_Ω+ψ₁(Ω_ω))), 严格的 `tA≺EBOˢ`, `btbo≺EBOˢ`; 推导的实例在文末.
> 做法: 第 2 支与 F2 上手造的底 `B₂ᶠ` 的 `Fn 2 B₂ᶠ` 相关 (`br2-R`; 经孩子 c 的分量照新的一行写, 其余照原行); `B₂ᶠ` 满足 `OKB`, 收窄到孩子 0 后满足 `Hi` (`hi0ᶠ`), 再照 `YiEVEnd`, `YiPHEnd`, `YiANEnd`, `YiANLim` 的下降, 只换路径: 新的链点 `c₁ˢ` 比原来多一层前缀, 路径多五步 (`path₂ˢ`, `path₃ˢ`, `pathNˢ`, 由类型检查确认).
> 不是 "新终点 ≥ 原终点"; 不涉及上界. 塔各项与第 1 支在 [YiSMValue](YiSMValue.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSMEnd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; sym; subst)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiSMFold
open import OCF.Lean.YiSMRel using (ψ⁰; A; S; cL)
open import OCF.Lean.YiSMValue using (ψ₀⁰-R; Fᴧ; brˢ; brˢ≼; B1ˢ; β1ˢ; Bᶠ; rB1; β1-R; br1-R; okᶠ; stᶠ; chE; y-R)
import OCF.Lean.YiLegBlock as F
import OCF.Lean.YiLegOps as F
import OCF.Lean.YiLegPath as F
import OCF.Lean.YiLegFold as F
open import OCF.Lean.YiBRRel
open import OCF.Lean.YiBRLem using (E→L)
open import OCF.Lean.YiBROps using (Ωt-R; Ωn-R; +-R; +m-R; ι-R; ιm-R; cumΩ-R)
open import OCF.Lean.YiBRFold using (B₀-R; W→L)
open import OCF.Lean.YiBRTw using (tw-L; tw-E; Λ-L; Λ-E)
open import OCF.Lean.YiBRValue using (readRW; up≼)
open import OCF.Lean.YiLSRead using (read; _⊢_⊴_; ⊴r; ⊴◃; ⊴-◃; ⊴-trans; plus≽)
open import OCF.Lean.YiLSFold using (OKB; ψs-⊵; ψ⊥-⊵; ok-dL; ok-B₀)
open import OCF.Lean.YiT2Frame using (ok-dW)
import OCF.Lean.YiLSTw1 as T1
open import OCF.Lean.YiLSBtbo using (btbo-tw1)
open import OCF.Lean.YiEBBtbo using (module Btbo)
open import OCF.Lean.YiEBShape using (Fn)
import OCF.Lean.YiEVReach as V
import OCF.Lean.YiEVEnd as EV
import OCF.Lean.YiMEAnchor as ME
import OCF.Lean.YiPHBase as PB
import OCF.Lean.YiPHEnd as PH
import OCF.Lean.YiANEnd as AN
import OCF.Lean.YiANLim as AL
import OCF.Lean.YiANReach as AR
import OCF.Lean.YiANFam as AF
open import OCF.Lean.YiNFO using (mono<; ↓suc)
import OCF.Lean.YiRefTw2 as R2
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiNFOCase using (tA; hA; btbo≺A)
open import OCF.Align.EboLeanTree using (hc-tower)
import OCF.Lean.YiDropRow as DR
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; ≅→≼; s≼s; l≼)
open import OCF.Align.YiBtValBT using (module D)
```

## 第 2 支的内层底 (Λ 沿孩子 2 折 `cum Fᴧ 0`)

经孩子 c 的分量是孩子 c 的 Ω 树从 Ω 折下来再加一棵第 0 层的树; 其余分量与 F2 原来的底 `dL … 2 …` 相同.

```agda
B2ᵐ : Base (tw 2)
B2ᵐ j u = ψ Λ Ok-Λ rb-Λ (B₀ Λ) j (inc 2 u) (Ωt j) (cum Fᴧ 0)

Y₁′ : F.Tr (F.tw 1)
Y₁′ = F.up F.zero F.zero (F.suc F.zero) F.◃s

Y₁-R : RelT (tw 1) (F.tw 1) (up zero zero (suc zero) ◃s) Y₁′
Y₁-R = iu (iz , (iz , y-R , ds))

V₁′ : F.Tr F.zero
V₁′ = F.ψ₀ (F.tw 1) (F.Ev-tw 1) (F.Rt-tw 1) Y₁′

nV₁′ : F._⊢_◃_ F.zero F.zero V₁′
nV₁′ = F.nz⊥ (F.tw 1) (F.Ev-tw 1) (F.Rt-tw 1) (F.B₀ (F.tw 1)) Y₁′

h₂′ : F.Tr (F.tw 1) → F.L
h₂′ c = F.tw 1 F.⊕ F.↑ (F.tw 1) c

ε₂ : (c : F.Tr (F.tw 1)) → F.Ev (h₂′ c)
ε₂ c = proj₂ (proj₂ (F.Ev-tw 2) c)

ρ₂ : (c : F.Tr (F.tw 1)) → F.Rt (h₂′ c)
ρ₂ c = proj₂ (F.Rt-tw 2) c

dΛ2 : F.Base (F.tw 2)
dΛ2 = F.dL F.tw F.Ev-Λ F.Rt-Λ (F.B₀ F.Λ) 2 (F.cumΩ F.tw 0)

Pm : (c : F.Tr (F.tw 1)) (j : F.L) → F._≤_ j (h₂′ c) → F.Tr j
Pm c j v = F.ψs (h₂′ c) (ε₂ c) (ρ₂ c) (F.B₀ (h₂′ c)) j v (F.Ωt j) (F.Ωt-nz j) (F.Ωt (h₂′ c))

bsᵐ : (j : F.L) → F._≤_ j (F.tw 2) → F.Tr j
bsᵐ j (F.inb c v) = Pm c j v F.+ F.ι j V₁′
bsᵐ j F.self      = F.bs dΛ2 j F.self
bsᵐ j (F.ink v)   = F.bs dΛ2 j (F.ink v)
bsᵐ j (F.inu vs)  = F.bs dΛ2 j (F.inu vs)

nsᵐ : (j : F.L) (w : F._≤_ j (F.tw 2)) → F._⊢_◃_ j F.zero (bsᵐ j w)
nsᵐ j (F.inb c v) =
  F.◃t (F.nzs (h₂′ c) (ε₂ c) (ρ₂ c) (F.B₀ (h₂′ c)) j v (F.Ωt j) (F.Ωt-nz j) (F.Ωt (h₂′ c))) (F.+-mono (Pm c j v) (F.ι-mono j nV₁′))
nsᵐ j F.self      = F.ns dΛ2 j F.self
nsᵐ j (F.ink v)   = F.ns dΛ2 j (F.ink v)
nsᵐ j (F.inu vs)  = F.ns dΛ2 j (F.inu vs)

Bᵐᶠ : F.Base (F.tw 2)
Bᵐᶠ = F.base (F.b⊥ dΛ2) (F.n⊥ dΛ2) bsᵐ nsᵐ

cΛ2 : RelBase (tw 2) (F.tw 2) (λ i w → ψ⁰ Λ Ok-Λ (B₀ Λ) i (inc 2 w) (B₀ Λ i (inc 2 w)) (cum Fᴧ 0)) dΛ2
cΛ2 = cL Λ-E (B₀ Λ) (F.B₀ F.Λ) (B₀-R Λ-L) (cumΩ-R Λ-L 0) 2

rBᵐ : RelBase (tw 2) (F.tw 2) B2ᵐ Bᵐᶠ
rBᵐ j j′ w w′ rw@wself      = cΛ2 j j′ w w′ rw
rBᵐ j j′ w w′ rw@(winuΩ _)  = cΛ2 j j′ w w′ rw
rBᵐ j j′ w w′ rw@(wink _)   = cΛ2 j j′ w w′ rw
rBᵐ j j′ w w′ (wincΩ {c = c} {c′ = c′} rcc rv) =
  let rec = chE (tw-E 2) c c′ rcc
      rlj = W→L (E→L rec) rv
      s₁  = S rec (B₀ _) (F.B₀ _) (B₀-R (E→L rec)) rv (Ωt j) (Ωt-R rlj) (Ωn-R rlj) (Ωt-R (E→L rec))
      a₂  = A (tw-E 1) (B₀ (tw 1)) (F.B₀ (F.tw 1)) (B₀-R (tw-L 1)) (Ωt zero) (Ωt-R lz) (Ωn-R lz) Y₁-R
  in +-R (proj₁ s₁) (ι-R (proj₁ a₂)) , dt (proj₂ s₁ , +m-R (proj₁ s₁) (ιm-R (proj₂ a₂)))
```

## 第 2 支的底与第 2 支

```agda
B2ˢ : Base (tw 2)
B2ˢ j u = ψ Λ Ok-Λ rb-Λ (B₀ Λ) j (inc 2 u) (Ωt j) (cum Fᴧ 1)

β2ˢ : Tr⁺ zero
β2ˢ = ψ Λ Ok-Λ rb-Λ (B₀ Λ) zero (z≤ Λ) (Ωt zero) (cum Fᴧ 1)

br2-form : brˢ 2 ≡ proj₁ (ψ⁰ (tw 2) (Ok-tw 2) B2ˢ zero (z≤ (tw 2)) β2ˢ (proj₁ (Ωt (tw 2))))
br2-form = refl

nar : (c : F.Tr (F.tw 1)) → F.Base (h₂′ c)
nar c = F.chB Bᵐᶠ (λ u → F.inb c u) (F.b⊥ Bᵐᶠ) (F.n⊥ Bᵐᶠ) (λ j w β n → β) (λ j w β n → n)

Q2 : (c : F.Tr (F.tw 1)) (j : F.L) → F._≤_ j (h₂′ c) → F.Tr j
Q2 c j v = F.ψs (h₂′ c) (ε₂ c) (ρ₂ c) (nar c) j v (bsᵐ j (F.inb c v)) (nsᵐ j (F.inb c v)) (F.Ωt (h₂′ c))

Y₂′ : F.Tr (F.tw 2)
Y₂′ = F.up F.zero F.zero (F.Ωt (F.tw 1)) (F.Ωt-nz (F.tw 1))

T1′ : F.Tr F.zero
T1′ = F.twᶜ 1

nT1′ : F._⊢_◃_ F.zero F.zero T1′
nT1′ = F.nz⊥ (F.tw 1) (F.Ev-tw 1) (F.Rt-tw 1) (F.B₀ (F.tw 1)) (F.Ωt (F.tw 1))

bs₂ : (j : F.L) → F._≤_ j (F.tw 2) → F.Tr j
bs₂ j (F.inb c v) = Q2 c j v F.+ F.ι j T1′
bs₂ j F.self      = F.ψs (F.tw 2) (F.Ev-tw 2) (F.Rt-tw 2) Bᵐᶠ j F.self (bsᵐ j F.self) (nsᵐ j F.self) Y₂′
bs₂ j (F.ink v)   = F.ψs (F.tw 2) (F.Ev-tw 2) (F.Rt-tw 2) Bᵐᶠ j (F.ink v) (bsᵐ j (F.ink v)) (nsᵐ j (F.ink v)) Y₂′
bs₂ j (F.inu vs)  = F.ψs (F.tw 2) (F.Ev-tw 2) (F.Rt-tw 2) Bᵐᶠ j (F.inu vs) (bsᵐ j (F.inu vs)) (nsᵐ j (F.inu vs)) Y₂′

ns₂ : (j : F.L) (w : F._≤_ j (F.tw 2)) → F._⊢_◃_ j F.zero (bs₂ j w)
ns₂ j (F.inb c v) =
  F.◃t (F.nzs (h₂′ c) (ε₂ c) (ρ₂ c) (nar c) j v (bsᵐ j (F.inb c v)) (nsᵐ j (F.inb c v)) (F.Ωt (h₂′ c)))
       (F.+-mono (Q2 c j v) (F.ι-mono j nT1′))
ns₂ j F.self      = F.nzs (F.tw 2) (F.Ev-tw 2) (F.Rt-tw 2) Bᵐᶠ j F.self (bsᵐ j F.self) (nsᵐ j F.self) Y₂′
ns₂ j (F.ink v)   = F.nzs (F.tw 2) (F.Ev-tw 2) (F.Rt-tw 2) Bᵐᶠ j (F.ink v) (bsᵐ j (F.ink v)) (nsᵐ j (F.ink v)) Y₂′
ns₂ j (F.inu vs)  = F.nzs (F.tw 2) (F.Ev-tw 2) (F.Rt-tw 2) Bᵐᶠ j (F.inu vs) (bsᵐ j (F.inu vs)) (nsᵐ j (F.inu vs)) Y₂′

B₂ᶠ : F.Base (F.tw 2)
B₂ᶠ = F.base (Fn 1 Bᶠ) (F.nz⊥ (F.tw 1) (F.Ev-tw 1) (F.Rt-tw 1) Bᶠ (F.Ωt (F.tw 1))) bs₂ ns₂

Y₂-R : RelT (tw 2) (F.tw 2) (up zero zero (proj₁ (Ωt (tw 1))) (proj₂ (Ωt (tw 1)))) Y₂′
Y₂-R = iu (iz , (iz , Ωt-R (tw-L 1) , Ωn-R (tw-L 1)))

rB2 : RelBase (tw 2) (F.tw 2) B2ˢ B₂ᶠ
rB2 j j′ w w′ rw@wself     = S (tw-E 2) B2ᵐ Bᵐᶠ rBᵐ rw (B2ᵐ j w) (proj₁ (rBᵐ j j′ w w′ rw)) (proj₂ (rBᵐ j j′ w w′ rw)) Y₂-R
rB2 j j′ w w′ rw@(winuΩ _) = S (tw-E 2) B2ᵐ Bᵐᶠ rBᵐ rw (B2ᵐ j w) (proj₁ (rBᵐ j j′ w w′ rw)) (proj₂ (rBᵐ j j′ w w′ rw)) Y₂-R
rB2 j j′ w w′ rw@(wink _)  = S (tw-E 2) B2ᵐ Bᵐᶠ rBᵐ rw (B2ᵐ j w) (proj₁ (rBᵐ j j′ w w′ rw)) (proj₂ (rBᵐ j j′ w w′ rw)) Y₂-R
rB2 j j′ w w′ (wincΩ {c = c} {c′ = c′} {v = v} {v′ = v′} rcc rv) =
  let rec = chE (tw-E 2) c c′ rcc
      rn  : RelBase _ _ (λ i u → B2ᵐ i (inc c u)) (nar c′)
      rn  = λ i i′ u u′ ru → rBᵐ i i′ (inc c u) (F.inb c′ u′) (wincΩ rcc ru)
      rb  = rBᵐ j j′ (inc c v) (F.inb c′ v′) (wincΩ rcc rv)
      s₁  = S rec (λ i u → B2ᵐ i (inc c u)) (nar c′) rn rv (B2ᵐ j (inc c v)) (proj₁ rb) (proj₂ rb) (Ωt-R (E→L rec))
      a₂  = A (tw-E 1) (B₀ (tw 1)) (F.B₀ (F.tw 1)) (B₀-R (tw-L 1)) (Ωt zero) (Ωt-R lz) (Ωn-R lz) (Ωt-R (tw-L 1))
  in +-R (proj₁ s₁) (ι-R (proj₁ a₂)) , dt (proj₂ s₁ , +m-R (proj₁ s₁) (ιm-R (proj₂ a₂)))

β2-R : RelD zero F.zero (proj₂ β2ˢ) (F.n⊥ B₂ᶠ)
β2-R = proj₂ (A (tw-E 1) B1ˢ Bᶠ rB1 β1ˢ (proj₁ β1-R) (proj₂ β1-R) (Ωt-R (tw-L 1)))

br2-R : RelT zero F.zero (brˢ 2) (Fn 2 B₂ᶠ)
br2-R = proj₁ (A (tw-E 2) B2ˢ B₂ᶠ rB2 β2ˢ br1-R β2-R (Ωt-R (tw-L 2)))
```

## `OKB`, 孩子 0 的底与 `Hi`, 链点

```agda
okΛ2 : OKB (F.tw 2) dΛ2
okΛ2 = ok-dL F.tw F.Ev-Λ F.Rt-Λ (F.B₀ F.Λ) (ok-B₀ F.Λ) 2 (F.cumΩ F.tw 0)

okᵐ : OKB (F.tw 2) Bᵐᶠ
okᵐ = proj₁ okΛ2 , okb
  where
  okb : (j : F.L) (w : F._≤_ j (F.tw 2)) → j ⊢ F.Ωt j ⊴ bsᵐ j w
  okb j (F.inb c v) =
    ⊴◃ (⊴-◃ (ψs-⊵ (h₂′ c) (ε₂ c) (ρ₂ c) (F.B₀ (h₂′ c)) j v (F.Ωt j) (F.Ωt-nz j) (F.Ωt (h₂′ c)))
             (F.+-mono (Pm c j v) (F.ι-mono j nV₁′)))
  okb j F.self     = proj₂ okΛ2 j F.self
  okb j (F.ink v)  = proj₂ okΛ2 j (F.ink v)
  okb j (F.inu vs) = proj₂ okΛ2 j (F.inu vs)

ok₂ : OKB (F.tw 2) B₂ᶠ
ok₂ = ⊴-trans (proj₁ okᶠ) (ψ⊥-⊵ (F.tw 1) (F.Ev-tw 1) (F.Rt-tw 1) Bᶠ (F.Ωt (F.tw 1))) , okb
  where
  okb : (j : F.L) (w : F._≤_ j (F.tw 2)) → j ⊢ F.Ωt j ⊴ bs₂ j w
  okb j (F.inb c v) =
    ⊴◃ (⊴-◃ (⊴-trans (proj₂ okᵐ j (F.inb c v))
                       (ψs-⊵ (h₂′ c) (ε₂ c) (ρ₂ c) (nar c) j v (bsᵐ j (F.inb c v)) (nsᵐ j (F.inb c v)) (F.Ωt (h₂′ c))))
             (F.+-mono (Q2 c j v) (F.ι-mono j nT1′)))
  okb j F.self     = ⊴-trans (proj₂ okᵐ j F.self) (ψs-⊵ (F.tw 2) (F.Ev-tw 2) (F.Rt-tw 2) Bᵐᶠ j F.self (bsᵐ j F.self) (nsᵐ j F.self) Y₂′)
  okb j (F.ink v)  = ⊴-trans (proj₂ okᵐ j (F.ink v)) (ψs-⊵ (F.tw 2) (F.Ev-tw 2) (F.Rt-tw 2) Bᵐᶠ j (F.ink v) (bsᵐ j (F.ink v)) (nsᵐ j (F.ink v)) Y₂′)
  okb j (F.inu vs) = ⊴-trans (proj₂ okᵐ j (F.inu vs)) (ψs-⊵ (F.tw 2) (F.Ev-tw 2) (F.Rt-tw 2) Bᵐᶠ j (F.inu vs) (bsᵐ j (F.inu vs)) (nsᵐ j (F.inu vs)) Y₂′)

Br0ᶠ : F.Base (F.tw 1)
Br0ᶠ = F.dW (F.tw 1) EV.h₂ (F.Ev-tw 2) (F.Rt-tw 2) B₂ᶠ F.zero F.zero

ok0ᶠ : OKB (F.tw 1) Br0ᶠ
ok0ᶠ = ok-dW (F.tw 1) EV.h₂ (F.Ev-tw 2) (F.Rt-tw 2) B₂ᶠ ok₂ F.zero F.zero

hi0ᶠ : V.Hi (F.tw 1) Br0ᶠ
hi0ᶠ = Btbo.btbo-B Bᶠ okᶠ stᶠ
     , λ w → ≼-trans btbo-tw1 (plus≽ _ (F.ι F.zero (F.twᶜ 1)) (≅→≼ (L.≅-sym (DR.ι₀≅ (F.twᶜ 1)))))

c₁ˢ : F.Tr F.zero
c₁ˢ = V.c1Ω F.zero T1.h₁ EV.ε′ EV.ρ′ Br0ᶠ

B₁ˢ : F.Base (T1.h₁ c₁ˢ)
B₁ˢ = F.dW F.zero T1.h₁ EV.ε′ EV.ρ′ Br0ᶠ c₁ˢ F.zero

path₂ˢ : ME.two V.⇐ T1.h₁ c₁ˢ
path₂ˢ = V.⇐l 0 (V.⇐l 0 (V.⇐l 0 (V.⇐s (V.⇐l 0 (V.⇐l 0 (V.⇐l 0 (V.⇐s (V.⇐l 0 (V.⇐l 1 V.⇐r)))))))))
```

## 终点

```agda
up2 : ∀ {X : L.Ordᶜ L.zero}
    → X ≼ read (F.ψ⊥ (T1.h₁ c₁ˢ) (proj₂ (proj₂ EV.ε′ c₁ˢ)) (proj₂ EV.ρ′ c₁ˢ) B₁ˢ (F.Ωt (T1.h₁ c₁ˢ)))
    → X ≼ readRW EBOˢ
up2 q = ≼-trans (up≼ br2-R (≼-trans q (≼-trans (V.Ω≽1 F.zero T1.h₁ EV.ε′ EV.ρ′ Br0ᶠ)
                                               (V.Ω≽0 (F.tw 1) EV.h₂ (F.Ev-tw 2) (F.Rt-tw 2) B₂ᶠ))))
                (brˢ≼ 2)

ok₁ˢ : OKB (T1.h₁ c₁ˢ) B₁ˢ
ok₁ˢ = ok-dW F.zero T1.h₁ EV.ε′ EV.ρ′ Br0ᶠ ok0ᶠ c₁ˢ F.zero

hi₁ˢ : V.Hi (T1.h₁ c₁ˢ) B₁ˢ
hi₁ˢ = V.hi-dW F.zero T1.h₁ EV.ε′ EV.ρ′ Br0ᶠ hi0ᶠ c₁ˢ F.zero

tA≼EBOˢ : (h : E.HC tA) → R2.Rt h ≼ readRW EBOˢ
tA≼EBOˢ h = up2 (V.reach path₂ˢ (proj₂ (proj₂ EV.ε′ c₁ˢ)) (proj₂ EV.ρ′ c₁ˢ) B₁ˢ ok₁ˢ hi₁ˢ h)

path₃ˢ : PB.three V.⇐ T1.h₁ c₁ˢ
path₃ˢ = V.⇐l 0 (V.⇐l 0 (V.⇐l 0 (V.⇐s (V.⇐l 0 (V.⇐l 0 (V.⇐l 0 (V.⇐s (V.⇐l 0 (V.⇐l 2 V.⇐r)))))))))

t₃≼EBOˢ : (h : E.HC PH.t₃) → R2.Rt h ≼ readRW EBOˢ
t₃≼EBOˢ h = up2 (PH.reach³ path₃ˢ (proj₂ (proj₂ EV.ε′ c₁ˢ)) (proj₂ EV.ρ′ c₁ˢ) B₁ˢ ok₁ˢ hi₁ˢ h)

tA≺EBOˢ : (h : E.HC tA) → L.suc (R2.Rt h) ≼ readRW EBOˢ
tA≺EBOˢ h = ≼-trans (PH.A≺3 h PH.h₃) (t₃≼EBOˢ PH.h₃)

btbo≺EBOˢ : L.suc D.BTBOᴵ ≼ readRW EBOˢ
btbo≺EBOˢ = ≼-trans (s≼s EV.btbo≼row₂) (≼-trans (btbo≺A (hc-tower 2) hA) (tA≼EBOˢ hA))
```

## 对一切 m, 与 ω 处的极限

末一个 ℕ 极限层号的第 k 个孩子是 `fin (k+1)` (`shapeˢ`, `gkˢ`).

```agda
Gs : ℕ → F.L
Gs k = AN.kid (AN.kid (AN.pre (AN.kid (AN.kid (AN.kid (AN.pre (AN.kid (AN.kid (AN.kid (T1.h₁ c₁ˢ) 0) 0) 0)) 0) 0) 0)) 0) k

shapeˢ : ∀ k → Gs k ≡ F.zero F.⊕ F.↑ F.zero (F.iter (AN.one F.+_) AN.one k)
shapeˢ k = refl

gkˢ : ∀ k → Gs k ≡ AF.fin (suc k)
gkˢ k = trans (shapeˢ k)
  (trans (cong (λ x → F.zero F.⊕ F.↑ F.zero x) (AN.I≡ k))
    (trans (cong (F.zero F.⊕_) (AN.↑num (suc k))) (AN.0⊕ (suc k))))

pathNˢ : ∀ m → AF.fin (suc (suc (suc m))) V.⇐ T1.h₁ c₁ˢ
pathNˢ m = V.⇐l 0 (V.⇐l 0 (V.⇐l 0 (V.⇐s (V.⇐l 0 (V.⇐l 0 (V.⇐l 0 (V.⇐s (V.⇐l 0
  (V.⇐l (suc (suc m)) (subst (AF.fin (suc (suc (suc m))) V.⇐_) (sym (gkˢ (suc (suc m)))) V.⇐r))))))))))

module _ (m : ℕ) where
  open AR.Reach (AF.fin (suc (suc (suc m)))) (AN.tN m)

  tN≼EBOˢ : (h : E.HC (AN.tN m)) → R2.Rt h ≼ readRW EBOˢ
  tN≼EBOˢ h = up2 (reachG (AN.AtN.atN m) (pathNˢ m) (proj₂ (proj₂ EV.ε′ c₁ˢ)) (proj₂ EV.ρ′ c₁ˢ) B₁ˢ ok₁ˢ hi₁ˢ h)

tω≼EBOˢ : (h : E.HC AL.tω) → R2.Rt h ≼ readRW EBOˢ
tω≼EBOˢ (E.h0 ())
tω≼EBOˢ (E.h1 () _)
tω≼EBOˢ (E.hω e hs) =
  l≼ (λ n → ≼-trans (↓suc (mono< (AL.nfω n) (AN.nN₁ n) (hs n) (AN.hN n) (AL.lt n))) (tN≼EBOˢ n (AN.hN n)))

instω : R2.Rt AL.hΩω ≼ readRW EBOˢ
instω = tω≼EBOˢ AL.hΩω

inst₃ : R2.Rt PH.h₃ ≼ readRW EBOˢ
inst₃ = t₃≼EBOˢ PH.h₃

instA : R2.Rt hA ≼ readRW EBOˢ
instA = tA≼EBOˢ hA

instN : ∀ m → R2.Rt (AN.hN m) ≼ readRW EBOˢ
instN m = tN≼EBOˢ m (AN.hN m)
```
