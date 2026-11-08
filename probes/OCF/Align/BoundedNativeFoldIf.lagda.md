# 原生 P 动态跨底折叠接口

源保持原 Source 树，不把所有分量固定在一个 Safe B 类型中。
指标分支使用已有 I₁：sh B e=B⊞leg e，进入后界为 sh B e+1；
分量节点不改界。路径证书逐分支进入新界。目标 Native0 是 step S⊥。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.BoundedNativeFoldIf where
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import OCF.Lean.CRwBase
open import OCF.Lean.CRw using (I₁)
open import OCF.Lean.CRwIf using (CRwIf)
import OCF.Lean.CRwFold as C
open import OCF.Align.BoundedDescentValueBridge using (Native; Source)

module Old = C I₁
open Old using (Po; PS; PH; poΩ; poF)
open Old.Po
open CRwIf I₁ public using (Adm₀; sh₀; nxt₀; adm-sh; nx-up; lg-nx)

policy : (κ : K Source) → Po (E Source κ)
policy (inj₁ _ , inj₁ ())
policy (inj₁ _ , inj₂ _) = poΩ
policy (inj₂ c , κ) = poF

Paths : PS Source
Paths = record
  { Ev = Ev ; Ad = λ B κ → pAd (policy κ) B
  ; nx = λ B κ → pnx (policy κ) B
  ; ev↑ = ev-up ; ad↓ = λ q {κ} a → pad↓ (policy κ) q a
  ; nx↑ = λ {B} {κ} {e} a → pnx↑ (policy κ) a }
  where
  Ev : Cd → K Source → Set
  Ev B (inj₁ _ , κ) = ⊤
  Ev B (inj₂ c , κ) = c ⊲ B
  ev-up : ∀ {B B′} → B ⊲ B′ → ∀ {κ} → Ev B κ → Ev B′ κ
  ev-up p {inj₁ _ , κ} q = tt
  ev-up p {inj₂ c , κ} q = ⊲ᴮ-tr q p

Path : Cd → HB Source → Set
Path = PH Paths

record NativeFold : Set₁ where
  field
    fold : ∀ B → LgB B → ∀ t → t ⊲ B →
      (h : HB Source) → Path B h → HB (Native t)
```

接口不宣称任意输入合法或下降保值。实际分量的 c⊲B 证据直指当前共同界；
保留下来的指标种类会把路径证书转入动态新界，不能拿旧界证书代用。
