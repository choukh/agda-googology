# 合成出口的第 0 片叶子与下一条缺口
> 验收文件（读记号），编译定理：`First.first-exit` 给出 `YiMHLean.low0` 第 0 片叶子的值出口；`example` 实填全部参数。
> 本文件声明的 `LowMove`、`FirstMissing` 已由 `YiNXFull.lowMove/firstMissing` 实填；完整无 `Ex` 出口见其 `Out.exit-low0`。
> 叶子的基础推导取自 `YiMHLean.low0`、`YiRBFam.LF` 与 `YiRLCrit.ω̃ˢ`；局部出口用 `YiNXExit.exitNX`。`¬shift₄` 只否定写明的平移等式。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNXLow where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiRBSib using (Rb; rb-no; ψ)
open import OCF.Lean.YiRBFam using (Tp; tc; tp; LF; OKB; mkGB)
open import OCF.Lean.YiRBCrit using (gˢ)
open import OCF.Lean.YiRLCrit using (Can; canω; ω̃ˢ; le3; fsnω)
open import OCF.Lean.YiKVRel using (M⁰; readRW; lower⁰; ⊴r)
open import OCF.Lean.YiCLFam using (fn; okf)
open import OCF.Lean.YiCLLow using (pth; ΩJ; ss; s0)
open import OCF.Lean.YiCLPhi using (ωᵀ)
open import OCF.Lean.YiCLCrit using (ωᶜ; ωᶜ-M)

open import OCF.Align.EboLeanDef using (HC; cof; cω; fsn; natT; hd<; ar<)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (NF; n[]; nf-ψ; GB; gp; gh; gw; gc; gtl; _≤ᵀ_; ≤-<; c∷; c[])
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Align.StandardOmega using (f∷; f[])
open import OCF.Align.Value using (_≼_)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiANEnd using (natB; flatN)
open import OCF.Lean.YiNFOCase using (flatG; z<)
open import OCF.Lean.YiDCExit using (nfΩ; gbΩ)
open import OCF.Lean.YiDCRel using (app≤; Ω≤)
open import OCF.Lean.YiRefTw2 using (Rt)
open import OCF.Lean.YiNXNote using (W; N; hW)
open import OCF.Lean.YiNXExit using (exitNX)
open import OCF.Lean.YiMHRel using (ĉ)
open import OCF.Lean.YiMENote using (fsnψω)

A Wit : ℕ → E.T
A n = ψᴺ 0 (ψᴺ 2 (Ωᴺ n))
Wit n = A (suc (suc (suc n)))

lowTerm : E.T
lowTerm = ψᴺ 0 (ψᴺ 2 (E.Ωt ωᵀ))

fsLow : ∀ n → fsn lowTerm n ≡ A n
fsLow n = trans (fsnψω [] (ψᴺ 2 (E.Ωt ωᵀ)) n refl) (cong (ψᴺ 0) (fsnω n))

nf-small : ∀ m → m ≤ⁿ 2 → NF (A m)
nf-small m l = nf-ψ n[] (nf-ψ (natB 2) (nfΩ m) (gbΩ [] m)) g
  where
  g : GB [] (ψᴺ 2 (Ωᴺ m)) (ψᴺ 2 (Ωᴺ m))
  g (gp (gh _)) = ≤-< (Ω≤ l) (hd< (ar< E.[]<))
  g (gp (gw _ i)) = z< (flatG (flatN 2) i)
  g (gp (gc _ i)) = z< (flatG (f∷ (flatN m) f[]) i)
  g (gtl ())

opaque
  hA₀ : HC (A 0)
  hA₀ = hc (nf-small 0 z≤n) (c∷ c[])

  hA₁ : HC (A 1)
  hA₁ = hc (nf-small 1 (s≤s z≤n)) (c∷ c[])

leAB : ∀ n → A n ≤ᵀ Wit n
leAB n = app≤ 0 [] (app≤ 2 [] (Ω≤ (le3 n)))

module First (o : Ok (fn 2)) (r : Rb (fn 2)) (s : Tp 1 0) (b : Base (fn 2)) (ok : OKB b)
             (β : Tr⁺ (fn 0)) (hβ : M⁰ (Ωᴺ 0) (proj₁ β)) {c : Tr zero} (cc : Can c) (l : M⁰ ωᵀ c) where
  opaque
    first-base : M⁰ (W 2) (proj₁ (ψ (fn 2) o r b (fn 0) (tp s) β (proj₁ (gˢ c))))
    first-base = LF o r s [] b
      (mkGB (λ {i} si → ok (fn i) (inc tt (pth si)))
            (λ {i} si → ΩJ i (b (fn i) (inc tt (pth si))) (ok (fn i) (inc tt (pth si)))))
      β hβ (proj₂ (proj₂ (ω̃ˢ cc l 0)))

  first-exit : (h : HC (A 0)) → Rt h ≼ readRW (proj₁ (ψ (fn 2) o r b (fn 0) (tp s) β (proj₁ (gˢ c))))
  first-exit = exitNX readRW lower⁰ (ĉ (leAB 0) first-base) (inj₂ (2 , nf-small 0 z≤n , refl))

module Example = First (okf 2) (rb-no (fn 2)) (tc (ss s0)) (B₀ (fn 2)) (λ i u → ⊴r)
                       (Ωt (fn 0)) (ΩJ 0 (Ωt (fn 0)) ⊴r) canω ωᶜ-M

example : Rt hA₀ ≼ readRW (proj₁ (ψ (fn 2) (okf 2) (rb-no (fn 2)) (B₀ (fn 2))
                          (fn 0) (tp (tc (ss s0))) (Ωt (fn 0)) (proj₁ (gˢ ωᶜ))))
example = Example.first-exit hA₀
```

`LowMove` 是全部叶子的值比较陈述；本文件填第 0 项，`YiNXFull` 已填全部项。
`FirstMissing` 保留首次切点的类型，现已由该文件的 `firstMissing` 构造；不再是未证前提。

```agda
LowMove : Set
LowMove = ∀ n → Σ (HC (Wit n)) λ h′ → (h : HC (A n)) → Rt h ≼ Rt h′

at-zero : Σ (HC (Wit 0)) λ h′ → (h : HC (A 0)) → Rt h ≼ Rt h′
at-zero = hW 2 , λ h → OCF.Lean.YiNXNote.monoW 2 (nf-small 0 z≤n) (leAB 0) h (hW 2)

FirstMissing : Set
FirstMissing = Σ (HC (Wit 1)) λ h′ → Rt hA₁ ≼ Rt h′

cofB₁ : cof (Wit 1) ≡ cω
cofB₁ = refl

firstB₁ : fsn (Wit 1) 0 ≡ W 2
firstB₁ = refl

¬shift₄ : fsn (Wit 1) 0 ≡ fsn (N 3) 1 → ⊥
¬shift₄ ()
```
