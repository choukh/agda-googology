# 验收一侧: 遗传封闭的族与已有关系的联系, 孩子取 ω 的判据, 出口条件可满足的一例

> 验收文件 (读记号), 不进成品; 树、折叠、合法性一行不改. 判决: 编译定理, 无前提. `of⁰`: 第 0 层未封闭的推导是封闭族的推导, 且出口条件自动成立 (`ex-of⁰`); `ofM̂`: 在封闭族外面再包一层 `YiMHRel.M̂` 不增加什么.
> `critω`: 兄弟孩子写法在孩子 `ωᶜ` 处的那一支对着 ψ₂(Ω_ω), 由 `leafω` 经 `LFω` 一步给出 (不经 Σ 形的逐项陈述). `exit-ωᴴ`: 用到 `mc` 与 `mL` 的推导上 `Exᴴ` 成立的一例.
> 不给出什么: 高层未封闭族 (`YiCLFam.M (suc n)`) 到封闭族的映射没有 (封闭使 `mΩ` 的前提变强); `crit₊`, `critω` 折到第 0 层后的推导上 `Exᴴ` 是否成立没有查.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiHCCheck where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiRBSib
open import OCF.Lean.YiRBCrit using (two; gˢ)
open import OCF.Lean.YiRLCrit using (oˢ; at-nat; le3)
import OCF.Lean.YiKVRel as K
open K using (readRW)
open import OCF.Lean.YiHCRel
import OCF.Align.EboLeanDef as E
open E using (HC; natT)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; NF)
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Lean.YiANFam using (ψᴺ)
open import OCF.Lean.YiANEnd using (natB)
open import OCF.Lean.YiCLFam using (fn)
open import OCF.Lean.YiCLLow using (s0)
open import OCF.Lean.YiCLPhi using (ωᵀ; rep1)
open import OCF.Lean.YiCLCrit using (ωᶜ; ωᶜ-M)
open import OCF.Lean.YiDCRel using (nat≤)
open import OCF.Lean.YiMHRel using (M̂; ĉ; l̂)
open import OCF.Lean.YiMHLean using (ctN)
open import OCF.Lean.YiHCFam using (M; mcJ; mLJ)
open import OCF.Lean.YiHCLim using (hβ₂; atω)
open import OCF.Lean.YiHCPlus using (module Wᶜ; module Tᶜ; le-sh)
```

## 与已有关系的联系

```agda
of⁰ : ∀ {s x} → K.M⁰ s x → M⁰ s x
of⁰ K.mz                   = mz
of⁰ (K.m1 e r)             = m1 e (of⁰ r)
of⁰ (K.mL e h)             = mL e (λ n → of⁰ (h n))
of⁰ (K.mΩ {p = ()} _ _ _)
of⁰ (K.mU {c = ()} _ _)
of⁰ (K.mw m d)             = mw (of⁰ m) d

ex-of⁰ : ∀ {s x} (m : K.M⁰ s x) → Exᴴ (of⁰ m)
ex-of⁰ K.mz                   = tt
ex-of⁰ (K.m1 e r)             = ex-of⁰ r
ex-of⁰ (K.mL e h)             = λ n → ex-of⁰ (h n)
ex-of⁰ (K.mΩ {p = ()} _ _ _)
ex-of⁰ (K.mU {c = ()} _ _)
ex-of⁰ (K.mw m d)             = ex-of⁰ m

ofM̂ : ∀ n {s x} → M̂ (M n) s x → M n s x
ofM̂ n (ĉ le m) = mcJ n le m
ofM̂ n (l̂ e h)  = mLJ n e (λ k → ofM̂ n (h k))
```

## 孩子取 ω 的判据

```agda
critω : M 2 (ψᴺ 2 (E.Ωt ωᵀ)) (proj₁ (gˢ ωᶜ))
critω = atω ωᶜ (Wᶜ.Fold.LFω (proj₂ (oˢ ωᶜ)) (rb-no _) (B₀ Wᶜ.Lω) [] Wᶜ.gbω₀ {n = 0} {j = 2} self s0 refl (Ωt two) hβ₂
                 (Tᶜ.leafω le-sh))
```

## 出口条件可满足的一例

ω 对着第 0 层的树 `ωᶜ`, 第 k 项用 `mc` 换成 k + 3 (与 `YiMHLean.ω̂` 相同的错位).

```agda
ωᴴ : M⁰ ωᵀ ωᶜ
ωᴴ = mL refl (λ k → mc (subst (λ t → t ≤ᵀ natT (suc (suc (suc k)))) (sym (rep1 k)) (nat≤ (le3 k)))
                       (of⁰ (at-nat ωᶜ-M (suc (suc (suc k))))))

ex-ωᴴ : Exᴴ ωᴴ
ex-ωᴴ k = subst NF (sym (rep1 k)) (natB k) , natB (suc (suc (suc k))) , ctN (suc (suc (suc k)))
        , ex-of⁰ (at-nat ωᶜ-M (suc (suc (suc k))))

exit-ωᴴ : (h : HC ωᵀ) → Rt h ≼ readRW ωᶜ
exit-ωᴴ = exitᴴ ωᴴ ex-ωᴴ
```
