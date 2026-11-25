# 读回域 `Dom` 与域上的 Leaf、Lift

> 验收文件 (读记号)。编译定理: `dom-top` (读回域上的 Leaf, 对一切层号形状), `dom-rd`, `liftᴰ`; 有限层号、龙骨、链点孩子、颈结点层号都在域内; `YiLLLeafNeg` 的反例不在域内。
> 做法: 域是带证据的层号与读法的对, 由空读法、沿上下文读回 (`YiNLRaise.raiseR`)、Ω 形状、向下封闭生成; 与 `YiAbsGIface` 的关系是把 `Graded.Rd` 换成 `Dom` 的实例化, 不是新律。
> 不给出 LowKeep; 不否定什么。来源: 四条生成规则分别引用 `YiNLCanonical.one-top`、`YiNLRaise.raiseR`、`YiLLCheck.leafΩ` 的写法、`YiLLCheck.rdown`。LowKeep 一侧见 [YiGLFrame](YiGLFrame.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGLDom where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock hiding (R)
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiLLCheck as LL
import OCF.Lean.YiLLLeafNeg as N
import OCF.Lean.YiBVSmall as S
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Align.EboLean3Base using (Ωt-mono)
open import OCF.Align.JiaAuditClosure using (cof-regular; fs-regular)
open import OCF.Lean.YiCNDomain using (Ωc)
open import OCF.Lean.YiCLFam using (fn; nat)
open import OCF.Lean.YiCLCrit using (natM)
open import OCF.Lean.YiHCCheck using (of⁰)
open import OCF.Lean.YiNLCtx
open import OCF.Lean.YiNLRead using (readR)
open import OCF.Lean.YiNLRaise using (raiseR; ΩΩ; fsΩΩ)
open import OCF.Lean.YiNLCanonical using (one-top; κ)
open import OCF.Lean.YiNLKeel using (kt-upper)
open import OCF.Lean.YiAbsGIface
open import OCF.Lean.YiExSuff using (module ExSuff)
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; keelᴱ)
open ExSuff gradedᵍ domsᵍ using (Keel⁻)
```

## 域

`Dom a ν`: 层号 a 带一份把它读作 ν 的证据。`dz`: 空读法; `dC`: 上下文 F 下把第 ℓ 层的树 y 连同它的关系证据读成层号; `dN`: Ω 形状, 每个带关系证据的孩子都在域内 (对一切孩子一致, 不指定孩子); `dc`: 向下封闭。
域里没有 "经 Ω 形状的某个指定孩子读" 这一条, `YiGIRel.Rd` 有 (`rd-child`), 反例正是用它。

```agda
data Dom : L → E.T → Set where
  dz : ∀ a → Dom a []
  dC : ∀ F ℓ {t ν y} → Dom (run F zero) t → GR.R ℓ ν y → Dom (run F (↑ ℓ y)) (t ++ ν)
  dN : ∀ {k κ ν} (h : Tr k → L) → Dom k κ → E.cof ν ≡ E.cΩ κ
     → (∀ η c → GR.R k η c → Dom (h c) (E.fsT ν η)) → Dom (nd (sΩ k) h) ν
  dc : ∀ {a ν μ} → ν ≤ᵀ μ → Dom a μ → Dom a ν

dom-rd : ∀ {a ν} → Dom a ν → GR.Rd a ν
dom-rd (dz a) = GR.c0 refl
dom-rd (dC F ℓ {y = y} D r) = rd-ctx F (↑ ℓ y) (dom-rd D) (readR ℓ r)
dom-rd (dN {κ = κ} h D e f) = GR.ca (inj₂ (κ , e , dom-rd D , λ η c r → dom-rd (f η c r)))
dom-rd (dc le D) = GR.cc le (dom-rd D)

dom-top : ∀ {a ν} → Dom a ν → Top a ν
dom-top (dz a) = one-top a
dom-top (dC F ℓ {t = t} D r) = raiseR ℓ F t (dom-rd D) (dom-top D) r
dom-top (dN {k} {ν = ν} h D e f) = H.mΩ (ΩΩ ν e) (dom-rd D)
  (λ η c r → subst (λ t → GR.R (nd (sΩ k) h) t (proj₁ (O.upz c (O.Ωt (h c)))))
    (sym (fsΩΩ ν η e)) (H.mU H.mz (dom-top (f η c r))))
dom-top (dc {a} le D) = LL.rdown a (Ωt-mono le) (dom-top D)
```

## 与抽象接口的关系

`Laws.Leaf` 的陈述是 `Rd ℓ ν → R ℓ (Ωr ν) (Ωt ℓ)`, 量化域由 `Graded.Rd` 定。把 `gradedᵍ` 的 `Rd` 换成 `Dom`, Leaf 与 Lift 都对整个实例成立; `Lift` 对一切树成立 (不用 `Gl`)。

```agda
gradedᴰ : Graded _ _ _ _ _
gradedᴰ = record gradedᵍ { Rd = Dom }

open Laws gradedᴰ domsᵍ using (Leaf; Lift)

leafᴰ : Leaf
leafᴰ = dom-top

liftᴰ : Lift
liftᴰ {k} _ r = dC identity k (dz zero) r
```

## 域内的实例

规范 Ω 层号, 塔与龙骨读法, 有限层号, 最小实例的链点孩子与颈结点层号 (`YiBVSmall.child`, `layer`)。

```agda
dom-Ωc : ∀ {k μ} → Dom k μ → Dom (Ωc k) (E.Ωs μ)
dom-Ωc {k} {μ} D = dN (λ c → k ⊕ ↑ k c) D (cof-regular μ)
  (λ η c r → subst (Dom (k ⊕ ↑ k c)) (sym (fs-regular μ η)) (dC (prefix k) k (dz k) r))

dom-tw : ∀ n → Dom (tw n) (κ n)
dom-tw zero = dz zero
dom-tw (suc n) = dom-Ωc (dom-tw n)

dom-keel : ∀ n → Dom (tw n) (Keel⁻.kt keelᴱ n)
dom-keel n = dc (kt-upper n) (dom-tw n)

dom-fin : ∀ n → Dom (fn n) (E.natT n)
dom-fin n = dC (prefix zero) zero (dz zero) (of⁰ (natM n))

dom-child : ∀ {η d} → GR.R zero η d → Dom (S.child d) η
dom-child r = dC (prefix K.two) zero (dz K.two) (H.mw r ◃s)

dom-neck : Dom S.layer (E.Ωs [])
dom-neck = dN S.child (dz zero) (cof-regular [])
  (λ η d r → subst (Dom (S.child d)) (sym (fs-regular [] η)) (dom-child r))
```

## 反例不在域内

`YiLLLeafNeg` 的层号 `ℓ` 有读法 `Rd ℓ 1` (经 Ω 形状的孩子 1), 但没有 `Dom ℓ 1`; 所以 `Rd` 不含于 `Dom`。

```agda
not-in : Dom N.ℓ (E.natT 1) → ⊥
not-in D = N.not-leaf-instance (dom-top D)

rd-not-dom : (∀ {a ν} → GR.Rd a ν → Dom a ν) → ⊥
rd-not-dom f = not-in (f N.rd)
```
