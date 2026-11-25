# 最小实例的窄桥与尚未填入的出口
验收文件；编译条件接线：Narrow 实填后得到原名 MinimalGoal；Narrow 未构造。
Narrow 的输出固定为实际 child-out d，参照固定为 ψ₁(Ω_index)，并带原始 M⁰ η d。
不把 Level 的 lower 当作 M 关系；对 η 为零、有限自然数和 ω 的桥实例复用既有 Need。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGCBridge where
open import Data.Nat using (ℕ)
open import Data.Product using (proj₁; proj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (refl; sym; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiBVDomain as D
import OCF.Lean.YiGCRel as R
import OCF.Lean.YiGCChosen as C
import OCF.Lean.YiQLRead as Q
import OCF.Lean.YiSQNat as N
import OCF.Lean.YiSQOmega as W
import OCF.Lean.YiCLPhi as Phi
import OCF.Align.EboLeanDef as E

At : E.T → B.Tr B.zero → Set
At η d = H.M 1 (Q.Target η) (proj₁ (S.Small.child-out d))
Narrow : Set
Narrow = ∀ η d → K.M⁰ η d → R.Rel K.one (C.Reference d) (proj₁ (S.Small.child-out d)) → At η d
from-narrow : Narrow → S.MinimalGoal
from-narrow bridge = subst (H.M 1 D.slot) (sym (S.Small.kept-row S.small-keep))
  (K.mΩ refl refl
    (λ η d m → bridge η d m (C.minimal-lower d)))
use-need : ∀ η d → Q.Need η d → At η d
use-need η d need = need (proj₂ S.okay d) (proj₂ (D.Input.table S.minimal) d)
  (S.Small.child-base d) (O.Ωt K.one) (λ i u → K.⊴r) (H.Mβ 0)
zero : ∀ d → At [] d
zero d = use-need [] d (Q.zero d)
nat : ∀ n d → K.M⁰ (E.natT n) d → At (E.natT n) d
nat n d m = use-need (E.natT n) d (N.nat-all n m)
omega : ∀ d → K.M⁰ Phi.ωᵀ d → At Phi.ωᵀ d
omega d m = use-need Phi.ωᵀ d (W.omega-all m)
next-reference : R.Rel K.one (C.Reference (B.suc W.ω)) (proj₁ (S.Small.child-out (B.suc W.ω)))
next-reference = C.minimal-lower (B.suc W.ω)
FirstBridge : Set
FirstBridge = At (E.sucT Phi.ωᵀ) (B.suc W.ω)
next-read : K.M⁰ (E.sucT Phi.ωᵀ) (B.suc W.ω)
next-read = K.m1 refl W.read-ω
first-from-narrow : Narrow → FirstBridge
first-from-narrow bridge = bridge (E.sucT Phi.ωᵀ) (B.suc W.ω) next-read next-reference
```
