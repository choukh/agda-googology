# 任意底上的颈结点弱链反例
验收文件；编译否定：`badB` 满足 `OKB` 与空前缀 `Prefixᵐ`，但第一迭代没有任何 `Ex⁰`，故任意 `r t a` 上弱链为空。
机制：第一迭代的第 0 个孩子是 `next⁺ slow`，再取第 0 个孩子得到已有的无标签树 `YiELZero.slow`。
前提实例为 `bad-ok`、`bad-prefix`；复用 `YiELZero.no-lbl-slow`，没有更换折叠或合法性。
只否定任意底域上的链；`badB` 不是标准底，不否定标准底的 `FirstExact` 或颈结点的值保持。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNCBadBase where
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock hiding (R)
import OCF.Lean.YiRWOps as O
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (Rb)
open import OCF.Lean.YiRBFam using (OKB)
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiMGNeck as N
import OCF.Lean.YiLKIface as I
import OCF.Lean.YiMGRel as MG
import OCF.Lean.YiMGFrame as MF
import OCF.Lean.YiELZero as Z
open import OCF.Lean.YiELOmega using (Lblᵒ)
import OCF.Align.EboLeanDef as E

bad⁺ : (j : L) → O.Tr⁺ j
bad⁺ zero = Z.slow , ◃l 0
bad⁺ (nd s h) = O.Ωt (nd s h)

badB : Base S.layer
badB j u = bad⁺ j

one◃slow : zero ⊢ suc zero ◃ Z.slow
one◃slow = ◃t (◃l 1) (◃l 1)

bad-ok : OKB badB
bad-ok zero u = K.⊴◃ one◃slow
bad-ok (nd s h) u = K.⊴r

bad-top : ∀ j {κ} → Lblᵒ j κ → MG.Rᵐ j (E.Ωt κ) (proj₁ (bad⁺ j))
bad-top zero refl = H.mw (H.m1 refl H.mz) one◃slow
bad-top (nd s h) l = MG.topᵐ (nd s h) l

bad-prefix : MF.Prefixᵐ badB []
bad-prefix p κ l = bad-top (at S.layer p) l

no-next : ∀ μ → Z.Ex⁰ μ (proj₁ (O.next⁺ (bad⁺ zero))) → ⊥
no-next μ (e , nf , la , k) = Z.no-lbl-slow _ (proj₁ (proj₂ (k 0)))

no-first : ∀ (r : Rb S.layer) μ → Z.Ex⁰ μ (O.iter (I.feed S.layer S.okay r badB N.neck N.gL) zero 1) → ⊥
no-first r μ (e , nf , la , k) = no-next _ (proj₁ (proj₂ (k 0)))

no-chain : ∀ r t a → N.NeckLabChain r badB t a → ⊥
no-chain r t a c = no-first r (proj₁ (c 0)) (proj₁ (proj₂ (c 0)))
```
