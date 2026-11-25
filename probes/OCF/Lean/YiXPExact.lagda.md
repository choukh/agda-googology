# 精确标签上的 LowKeep: 不含 Ω 形状的层号

> 验收文件 (读记号)。编译定理, 无前提: `YiGLExact.LowKeepAtˣ ℓ` 对一切不含 Ω 形状的层号有居民 (`lowKeepAt-noΩ`); `YiGLExact.LowKeepˣ` 有居民 (`lowKeepˣ`), 但 `Lbl` 的 Ω 一条是 ⊥, 所以它只覆盖不含 Ω 形状的层号, 对塔 `tw (suc n)` 与 Λ 什么也没说。
> 做法: `Rˣ` 与参数化关系 `YiXPRel Lbl` 的 `R` 互相给出 (`to`, `of`, 经 `YiFMMap.mapᴴ`), 再用 `YiXPFrame.pres-noΩ`; 嵌入、上折、自身三行的 `Rˣ` 形式是 `upˣ`, `selfˣ`。
> 不否定什么; Ω 形状层号的 `Lbl` 与第 0 层的分支前提不在这里。实例见 [YiXPSmall](YiXPSmall.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiXPExact where
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (Rb; ψ)
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiFMMap using (mapᴴ)
open import OCF.Lean.YiGLFrame using (Lbl)
open import OCF.Lean.YiGLExact using (Rˣ; Lowˣ; Low⁼ˣ; LowKeepAtˣ; LowKeepˣ)
import OCF.Lean.YiXPRel as XR
import OCF.Lean.YiXPRows as XW
open import OCF.Lean.YiXPFrame using (NoΩ; lbl-noΩ; frame; index-all; pres-noΩ)
module X = XR Lbl
module Y = XW Lbl
```

## 两个关系族互相给出

分支关系出现在 `mΩ` 的前提里 (逆变), 所以两个方向互递归; 递归穿过分支关系时层号严格下降。

```agda
mutual
  to : ∀ ℓ {t x} → Rˣ ℓ t x → X.R ℓ t x
  to zero m = m
  to (nd s h) m = mapᴴ (lowOf (nd s h)) (λ c → to (h c)) (λ p q → q) m

  of : ∀ ℓ {t x} → X.R ℓ t x → Rˣ ℓ t x
  of zero m = m
  of (nd s h) m = mapᴴ (lowTo (nd s h)) (λ c → of (h c)) (λ p q → q) m

  lowTo : ∀ ℓ p {η c} → Lowˣ ℓ p η c → X.Low ℓ p η c
  lowTo (nd s h) (inj₂ (c , t)) = lowTo⁼ (h c) t
  lowTo (nd (sΩ k) h) (inj₁ t) = lowTo⁼ k t

  lowTo⁼ : ∀ a t {η c} → Low⁼ˣ a t η c → X.Low⁼ a t η c
  lowTo⁼ a (inj₁ _) = to a
  lowTo⁼ a (inj₂ p) = lowTo a p

  lowOf : ∀ ℓ p {η c} → X.Low ℓ p η c → Lowˣ ℓ p η c
  lowOf (nd s h) (inj₂ (c , t)) = lowOf⁼ (h c) t
  lowOf (nd (sΩ k) h) (inj₁ t) = lowOf⁼ k t

  lowOf⁼ : ∀ a t {η c} → X.Low⁼ a t η c → Low⁼ˣ a t η c
  lowOf⁼ a (inj₁ _) = of a
  lowOf⁼ a (inj₂ p) = lowOf a p
```

## LowKeep

```agda
lowKeepAt-noΩ : ∀ ℓ → NoΩ ℓ → LowKeepAtˣ ℓ
lowKeepAt-noΩ ℓ nω {j} o r B w β ν t lν gb pref mb m =
  of j (pres-noΩ ℓ nω o r B gb t (λ p κ l → to (at ℓ p) (pref p κ l))
    j w ν (index-all ℓ nω o r w lν) β (to j mb) (to ℓ m))

lowKeepˣ : LowKeepˣ
lowKeepˣ ℓ lℓ = lowKeepAt-noΩ ℓ (lbl-noΩ ℓ lℓ)
```

## 上折与自身两行的 `Rˣ` 形式

```agda
upˣ : ∀ j {ℓ} ν (d : Dn ℓ j) → Y.UpFrame ν j d
  → (t : E.T) (β : Tr⁺ ℓ) → Rˣ ℓ (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → Rˣ j a x
  → Rˣ ℓ (E.ψ ν (t ++ a) ∷ []) (proj₁ (Up j d β x))
upˣ j {ℓ} ν d fr t β mb m = of ℓ (Y.up-pres j ν d fr t β (to ℓ mb) (to j m))

selfˣ : ∀ ℓ → NoΩ ℓ → (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → ∀ {ν} → Lbl ℓ ν → (t : E.T)
  → (β : Tr⁺ ℓ) → Rˣ ℓ (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → Rˣ ℓ a x
  → Rˣ ℓ (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B ℓ self β x))
selfˣ ℓ nω o r B {ν} lν t β mb m = of ℓ (Y.self-pres ℓ o r B ν t
  (λ p κ lκ → frame ℓ nω o p self lν lκ) β (to ℓ mb) (to ℓ m))
```
