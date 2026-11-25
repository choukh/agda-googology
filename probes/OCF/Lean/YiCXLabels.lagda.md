# 统一派发的唯一性与 Ω 分支标签的量化域
验收文件，读记号；编译定理：同层任意两个标签都可作顶槽位/目标的走链阈值，当且仅当标签唯一。
`successor-unique` 从后继源的统一 `KeepSpec` 提取该必要条件；复用 `gt→≤` 与 `YiGLFrame.uniq` 的既有证明。
`no-exact-lower-branches` 否定保留 `M⁰` 下界分支域、却要求每支取得该读法的唯一精确标签；见 `shared-zero/one`。
只否定写出的量化域，不证明 Ω 形状必须取空，不否定其他标签设计或 LowKeep；局部反例见 `YiCXWindow`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiCXLabels where
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (kp)
open import OCF.Lean.YiGTNode using (KeepSpec)
open import OCF.Lean.YiGLFrame using (Lbl; uniq; <→gt; lbl-fin)
open import OCF.Lean.YiCLFam using (fn; okf)
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (gt→≤; <ᵀ-asym)
open import OCF.Align.EBO using (<-sucT)

Unique : (L → E.T → Set) → Set
Unique Lab = ∀ a {κ ν} → Lab a κ → Lab a ν → κ ≡ ν

DropStable : (L → E.T → Set) → Set
DropStable Lab = ∀ a {κ ν} → Lab a κ → Lab a ν → E.cmpᵀ (E.sucT κ) ν ≡ E.gt

cut-unique-at : ∀ (A : E.T → Set)
  → (∀ {κ ν} → A κ → A ν → E.cmpᵀ (E.sucT κ) ν ≡ E.gt)
  → ∀ {κ ν} → A κ → A ν → κ ≡ ν
cut-unique-at A cut {κ} {ν} lκ lν with gt→≤ κ ν (cut lκ lν) | gt→≤ ν κ (cut lν lκ)
... | inj₁ v<k | inj₁ k<v = ⊥-elim (<ᵀ-asym v<k k<v)
... | inj₁ v<k | inj₂ eq = eq
... | inj₂ eq | _ = sym eq

cut-unique : ∀ Lab → DropStable Lab → Unique Lab
cut-unique Lab cut a = cut-unique-at (Lab a) (cut a)

unique-cut : ∀ Lab → Unique Lab → DropStable Lab
unique-cut Lab un a {κ} {ν} lκ lν =
  subst (λ v → E.cmpᵀ (E.sucT κ) v ≡ E.gt) (un a lκ lν) (<→gt (<-sucT κ))

lbl-cut : DropStable Lbl
lbl-cut = unique-cut Lbl uniq

FrameFor : (L → E.T → Set) → ∀ ℓ → Ok ℓ → ∀ j → j ≤ ℓ → E.T → Set
FrameFor Lab ℓ o j w ν = ∀ p κ → Lab (at ℓ p) κ
  → KeepSpec ℓ j ν p κ (kp ℓ o p w)

successor-cut : ∀ Lab a (oa : Ok a)
  → (∀ {ν} → Lab a ν → FrameFor Lab (nd sS (λ _ → a)) (tt , λ _ → oa) a (inc tt self) ν)
  → ∀ {κ ν} → Lab a κ → Lab a ν → E.cmpᵀ (E.sucT κ) ν ≡ E.gt
successor-cut Lab a oa fr lκ lν = fr lν (inj₂ (tt , inj₁ tt)) _ lκ

successor-unique : ∀ Lab a (oa : Ok a)
  → (∀ {ν} → Lab a ν → FrameFor Lab (nd sS (λ _ → a)) (tt , λ _ → oa) a (inc tt self) ν)
  → ∀ {κ ν} → Lab a κ → Lab a ν → κ ≡ ν
successor-unique Lab a oa fr = cut-unique-at (Lab a) (successor-cut Lab a oa fr)

frame-one : FrameFor Lbl (fn 2) (okf 2) (fn 1) (inc tt self) (E.natT 1)
frame-one (inj₂ (tt , inj₁ tt)) κ lκ = lbl-cut (fn 1) lκ (lbl-fin 1)
frame-one (inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))) .[] refl =
  inj₂ refl , GR.c0 refl , λ η c r → r

successor-instance : ∀ {ν} → Lbl (fn 1) ν
  → FrameFor Lbl (fn 2) (okf 2) (fn 1) (inc tt self) ν
successor-instance lν = subst (FrameFor Lbl (fn 2) (okf 2) (fn 1) (inc tt self))
  (uniq (fn 1) (lbl-fin 1) lν) frame-one

BranchExact : (L → E.T → Set) → (Tr zero → L) → Set
BranchExact Lab h = ∀ η c → H.M⁰ η c → Lab (h c) (E.fsT (E.Ωs []) η)

shared-zero : H.M⁰ [] (suc zero)
shared-zero = H.mz
shared-one : H.M⁰ (E.natT 1) (suc zero)
shared-one = H.m1 refl H.mz

no-exact-lower-branches : ∀ Lab → Unique Lab → ∀ h → BranchExact Lab h → ⊥
no-exact-lower-branches Lab un h branches with
  un (h (suc zero)) (branches [] (suc zero) shared-zero) (branches (E.natT 1) (suc zero) shared-one)
... | ()

no-lbl-lower-branches : ∀ h → BranchExact Lbl h → ⊥
no-lbl-lower-branches = no-exact-lower-branches Lbl uniq
```
