# 验收: 最小见证的值不低于 ψ₀(Ω_Ω+ψ₁(Ω₂)) 的参照 (V124 的一部分)

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. `tA≼Vᴿ : (h : HC tA) → R2.Rt h ≼ readRW Vᴿ`, tA 是记号项 ψ₀(Ω_Ω+ψ₁(Ω₂)), `Vᴿ` 是主线精简块上最小见证 `up β two (Ωt 2)` 的折叠; F2 上是 `tA≼V`.
> 做法: [YiMWPre](YiMWPre.lagda.md) 的 `Pre` 代入见证的底 `BW` 与前缀 Ω_Ω; 前缀的两条前提由 `sem→M⁰` 从 BTBO 的参照得到.
> 不给出什么: V124 (`Rt hB ≼ readRW Vᴿ`) 没有证出, 也没有否定; 不涉及上界.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMWLow where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins)
open import OCF.Lean.YiLegFold
import OCF.Align.EboLeanDef as E
open E using (HC; fsn)
open import OCF.Align.EboLeanTree using (hc-tower)
import OCF.Align.Level as O
import OCF.Lean.YiRefTw2 as R2
open import OCF.Align.YiBtValBT using (module D)
open import OCF.Align.Value using (_≼_; z≼; s≼s; ≼l; l≼; ≼-trans)
open import OCF.Lean.YiMEBase
open import OCF.Lean.YiMEAnchor
open import OCF.Lean.YiMWPre
import OCF.Lean.YiLSRead as S
open import OCF.Lean.YiLSTw1 using (G)
open import OCF.Lean.YiLSBtbo using (btbo-tw1)
open import OCF.Lean.YiInv using (BW)
import OCF.Lean.YiDropRow as DR
open import OCF.Lean.YiDropRW using (Vᴿ; V-R)
open import OCF.Lean.YiBRValue using (readRW; up≼)
open import OCF.Lean.YiEXRow using (row₂-btbo)
open import OCF.Lean.YiNFOCase using (tA; tB; ΩΩ; hA; nA₁; nfB)
open import OCF.Lean.YiNFO using (mono<)
open E using (_<ᵀ_; []<; hd<; tl<; lv<; ar<)
```

两个读回 (`YiMEBase.read` 与 `YiLSRead.read`) 逐点同形.

```agda
rd≼ : (x : Tr zero) → read x ≼ S.read x
rd≼ zero          = z≼
rd≼ (suc x)       = s≼s (rd≼ x)
rd≼ (lim f a)     = l≼ (λ n → ≼l n (rd≼ (f n)))
rd≼ (Ω () _)
rd≼ (up _ () _ _)

rd≽ : (x : Tr zero) → S.read x ≼ read x
rd≽ zero          = z≼
rd≽ (suc x)       = s≼s (rd≽ x)
rd≽ (lim f a)     = l≼ (λ n → ≼l n (rd≽ (f n)))
rd≽ (Ω () _)
rd≽ (up _ () _ _)
```

## 最小见证的底

见证的折叠就是第 2 层上以 `BW` 为底的折叠 (`V-form`, `refl`). `BW` 的第 1 层分量是结点, 第一分支在 Ω₁ 之上 (`hβᵂ`); 第 0 层分量与 `b⊥` 不低于 BTBO 的参照, 记号树 ψ₀(Ω_Ω) 与它同标签 (`YiEXRow.row₂-btbo`), 所以对着 ψ₀(Ω_Ω) (`h0ᵂ`, `h⊥ᵂ`). `semR` 对推导一般地陈述再代入 `hc-tower 2`: 两个 `Rt` 在具体推导上直接比较会展开良基证明 (实测 8G 堆耗尽).

```agda
V-form : DR.V ≡ ψ⊥ two tt tt BW (Ωt two)
V-form = refl

tΩ : E.T
tΩ = ΩΩ ∷ []

_ : ψ₀ᵗ tΩ ≡ E.EBOψ 2
_ = refl

hβᵂ : M¹ Ω₁ᵗ (bs BW one (ins self))
hβᵂ = mw (G¹.m⊴ Mβ₀ (+⊴ (Ωt one) (ι one (G zero)))) (◃w {p = inj₁ tt} {g = λ c → Ωt one + ι one (G c)})

semR : ∀ {t} (h : HC t) (x : Tr zero) {Y : O.Ordᶜ O.zero} → R2.Rt h ≼ Y → Y ≼ S.read x → M⁰ t x
semR h x p q = sem→M⁰ h x (≼-trans p (≼-trans q (rd≽ x)))

sem0 : (x : Tr zero) → D.BTBOᴵ ≼ S.read x → M⁰ (ψ₀ᵗ tΩ) x
sem0 x q = semR (hc-tower 2) x row₂-btbo q

h0ᵂ : M⁰ (ψ₀ᵗ tΩ) (bs BW zero (ins (ins self)))
h0ᵂ = sem0 (bs BW zero (ins (ins self))) DR.btbo≼E₀

h⊥ᵂ : M⁰ (ψ₀ᵗ tΩ) (b⊥ BW)
h⊥ᵂ = sem0 (b⊥ BW) btbo-tw1

module PW = Pre BW hβᵂ tΩ h0ᵂ h⊥ᵂ
```

## ψ₀(Ω_Ω+ψ₁(Ω₂)) 的下界

tA 的第 n 个基本列项是 ψ₀(Ω_Ω+ψ₁(γₙ)) (`refl`), 对着见证折叠的第 n+2 行.

```agda
tA-fs : ∀ n → fsn tA n ≡ ψ₀ᵗ (tΩ ++ ψ₁ᵗ (PW.γ n))
tA-fs n = refl

tA-M : M⁰ tA DR.V
tA-M = mL refl PW.rowp

tA≼V : (h : HC tA) → R2.Rt h ≼ S.read DR.V
tA≼V h = ≼-trans (lower⁰ tA-M h) (rd≼ DR.V)

tA≼Vᴿ : (h : HC tA) → R2.Rt h ≼ readRW Vᴿ
tA≼Vᴿ h = up≼ V-R (tA≼V h)
```

实例 (前提可满足): `YiNFOCase.hA` 是 tA 的一个推导.

```agda
inst-A : R2.Rt hA ≼ readRW Vᴿ
inst-A = tA≼Vᴿ hA
```

## tB 的基本列上的位置

tB = ψ₀(Ω_Ω+Ω₂) 的第 0 项是 ψ₀(Ω_Ω+Ω₁), 第 1 项是 ψ₀(Ω_Ω+ψ₁(Ω_Ω+Ω₁)) (`refl`); 项序上 tA 夹在两者之间 (`B0<A`, `A<B1`). 所以第 0 项的参照严格低于见证值 (`B0≺Vᴿ`); 第 1 项没有证出.

```agda
_ : fsn tB 0 ≡ ψ₀ᵗ (tΩ ++ Ω₁ᵗ)
_ = refl

_ : fsn tB 1 ≡ ψ₀ᵗ (tΩ ++ ψ₁ᵗ (tΩ ++ Ω₁ᵗ))
_ = refl

B0<A : fsn tB 0 <ᵀ tA
B0<A = hd< (ar< (tl< (hd< (ar< []<))))

A<B1 : tA <ᵀ fsn tB 1
A<B1 = hd< (ar< (tl< (hd< (ar< (hd< (lv< (hd< (lv< []<))))))))

B0≺Vᴿ : (h : HC (fsn tB 0)) → O.suc (R2.Rt h) ≼ readRW Vᴿ
B0≺Vᴿ h = ≼-trans (mono< (nfB 0) nA₁ h hA B0<A) inst-A
```
