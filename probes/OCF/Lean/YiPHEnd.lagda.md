# 验收: 终点闭项不低于 ψ₀(Ω_Ω+ψ₁(Ω₃)) 的参照

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. `t₃≼EBOᴿ : (h : HC t₃) → R2.Rt h ≼ readRW RW.EBOᶜ` (主线精简块), t₃ 是记号项 ψ₀(Ω_Ω+ψ₁(Ω₃)); F2 上是 `t₃≼EBO`. 推导 `h₃ : HC t₃` 存在.
> 做法: [YiPHCtx](YiPHCtx.lagda.md) 的 `Ctx3.anchor³` 代入满足 `OKB` 与 `Hi` 的底与前缀 Ω_Ω (`atThree`); 下降 `reach³` 与 `YiEVReach.reach` 同文, 终点换成层号 3; 路径在 `YiEVEnd` 的层号 `h₁ c₁` 里末一步取孩子 1 (`path₃`).
> 项序上 tA < t₃ < tB 的第 1 项 (`A≺3`, `3≺B1`, 对任意推导). 不涉及上界; 第一目标 (tB 的第 1 项) 没有证出, 也没有否定.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPHEnd where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock renaming (L to LF)
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; Ev; Rt; Ev-tw; Rt-tw)
open import OCF.Lean.YiLegFold
open import OCF.Lean.YiLSRead using (read)
open import OCF.Lean.YiLSFold using (OKB; ok-dS; ok-dL)
open import OCF.Lean.YiLSTw1 using (h₁)
open import OCF.Lean.YiT2Frame using (ok-dW)
open import OCF.Lean.YiEBShape using (dB; br; br≼)
open import OCF.Lean.YiEVReach
open import OCF.Lean.YiEVEnd using (h₂; Br0; ε′; ρ′; ok0; hi0; c₁; B₁)
import OCF.Lean.YiMEBase as MB
open import OCF.Lean.YiMEAnchor using (one; two; Mβ₀; ψ₀ᵗ; ψ₁ᵗ; module G¹)
open import OCF.Lean.YiMWLow using (rd≼; tΩ; sem0)
open import OCF.Lean.YiPHBase using (three; u₂; Mβ₂; module G²)
open import OCF.Lean.YiPHCtx using (module Ctx3)
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
import OCF.Lean.YiRWFold as RW
open import OCF.Lean.YiBRTw using (EBOᶜ-R)
open import OCF.Lean.YiBRValue using (readRW; up≼)
```

## 记号项 ψ₀(Ω_Ω+ψ₁(Ω₃))

基本列的第 n 项是 ψ₀(Ω_Ω+ψ₁(γ³ₙ)), γ³₀ = Ω₂, γ³ₙ₊₁ = ψ₂(γ³ₙ) (`refl`). 两种标准形证明与 `YiNFOCase` 的 tA 同法.

```agda
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
```

项序上的位置: tA < t₃ < tB 的第 1 项 ψ₀(Ω_Ω+ψ₁(Ω_Ω+Ω₁)); 由 `YiNFO.mono<` 得参照的严格序.

```agda
A<3 : tA <ᵀ t₃
A<3 = hd< (ar< (tl< (hd< (ar< (hd< (lv< (tl< (tl< []<))))))))

3<B1 : t₃ <ᵀ fsn tB 1
3<B1 = hd< (ar< (tl< (hd< (ar< (hd< (lv< (hd< (lv< []<))))))))

A≺3 : (h : HC tA) (h′ : HC t₃) → O.suc (R2.Rt h) ≼ R2.Rt h′
A≺3 h h′ = mono< nA₁ n₃₁ h h′ A<3

3≺B1 : (h : HC t₃) (h′ : HC (fsn tB 1)) → O.suc (R2.Rt h) ≼ R2.Rt h′
3≺B1 h h′ = mono< n₃₁ (nfB 1) h h′ 3<B1
```

## 层号 3: `Ctx3` 对一般底

`OKB` 给出第 2 层分量在 Ω₂ 之上, 第 1 层分量在 Ω₁ 之上; `Hi` 经 `sem0` 给出第 0 层分量与 `b⊥` 对着 ψ₀(Ω_Ω).

```agda
Lo³ : (ℓ : LF) → Ev ℓ → Rt ℓ → Base ℓ → Set
Lo³ ℓ ε ρ B = (h : HC t₃) → R2.Rt h ≼ read (ψ⊥ ℓ ε ρ B (Ωt ℓ))

module AtThree (B₃ : Base three) (ok : OKB three B₃) (hi : Hi three B₃) where
  module C = Ctx3 B₃ (G².m⊴ Mβ₂ (cv⊴ (proj₂ ok two (ins self)))) (cv⊴ (proj₂ ok two (ins self)))
    (G¹.m⊴ Mβ₀ (cv⊴ (proj₂ ok one (ins (ins self))))) tΩ
    (sem0 (bs B₃ zero (ins (ins (ins self)))) (proj₂ hi (ins (ins (ins self))))) (sem0 (b⊥ B₃) (proj₁ hi))

  atThree : Lo³ three tt tt B₃
  atThree h = ≼-trans (MB.lower⁰ C.anchor³ h) (rd≼ _)
```

## 下降到层号 3

```agda
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
```

## 终点

层号 `h₁ c₁` 沿 ℕ 极限的孩子 0, 0, 0, 后继, 孩子 1 走到 3 (`path₃`, 由类型检查确认; 末一个 ℕ 极限层号的孩子是 2, 3, 4, …, 只在临时目录里算过前三项).

```agda
path₃ : three ⇐ h₁ c₁
path₃ = ⇐l 0 (⇐l 0 (⇐l 0 (⇐s (⇐l 1 ⇐r))))

low3 : Lo³ (h₁ c₁) (proj₂ (proj₂ ε′ c₁)) (proj₂ ρ′ c₁) B₁
low3 = reach³ path₃ (proj₂ (proj₂ ε′ c₁)) (proj₂ ρ′ c₁) B₁
  (ok-dW zero h₁ ε′ ρ′ Br0 ok0 c₁ zero) (hi-dW zero h₁ ε′ ρ′ Br0 hi0 c₁ zero)

t₃≼br2 : (h : HC t₃) → R2.Rt h ≼ read (br 2)
t₃≼br2 h = ≼-trans (low3 h) (≼-trans (Ω≽1 zero h₁ ε′ ρ′ Br0) (Ω≽0 (tw 1) h₂ (Ev-tw 2) (Rt-tw 2) (dB 2)))

t₃≼EBO : (h : HC t₃) → R2.Rt h ≼ read EBOᶜ
t₃≼EBO h = ≼-trans (t₃≼br2 h) (br≼ 2)

t₃≼EBOᴿ : (h : HC t₃) → R2.Rt h ≼ readRW RW.EBOᶜ
t₃≼EBOᴿ h = up≼ EBOᶜ-R (t₃≼EBO h)
```

实例 (前提可满足), 与推论: 终点闭项严格高于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照 (另一条证法, 不经 `YiTWEnd`).

```agda
inst₃ : R2.Rt h₃ ≼ readRW RW.EBOᶜ
inst₃ = t₃≼EBOᴿ h₃

tA≺EBOᴿ′ : (h : HC tA) → O.suc (R2.Rt h) ≼ readRW RW.EBOᶜ
tA≺EBOᴿ′ h = ≼-trans (A≺3 h h₃) inst₃
```
