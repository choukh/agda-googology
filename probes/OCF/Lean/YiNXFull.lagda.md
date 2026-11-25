# 合成出口的全部叶子：沿第 0 支比较非标准形参照
> 验收文件（读记号），编译定理：`lowMove`、`firstMissing` 填出 `YiNXLow` 留下的两条陈述；`Out.exit-low0` 给完整合成推导的出口，无 `Ex` 或标准形前提。
> `fromM` 从第 0 层基础关系构造 `HC`；`fsA0` 对所有 n 证明 `A (n+1)[0] = A n`，`move` 沿三次第 0 支比较值；`hLow` 与 `full-example` 给闭合实例。
> 见证关系沿用 `YiMHLean.low0` 的 `LF/ω̃ˢ` 构造；复用 `YiKSRead.fs-sup` 与 `YiRefTw2` 的值工具。不改树、折叠、合法性；不声称任意非标准形上的项序单调。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNXFull where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.Unit using (tt)
open import Data.Product using (proj₁; proj₂; _,_)
open import Data.List using ([])
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; trans; cong)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiRBSib using (Rb; rb-no; ψ)
open import OCF.Lean.YiRBFam using (Tp; tc; tp; LF; OKB; mkGB)
open import OCF.Lean.YiRBCrit using (gˢ)
open import OCF.Lean.YiRLCrit using (Can; canω; ω̃ˢ)
open import OCF.Lean.YiKVRel using (M⁰; mz; m1; mL; mΩ; mU; mw; ⊴r; readRW; lower⁰)
open import OCF.Lean.YiCLFam using (fn; okf)
open import OCF.Lean.YiCLLow using (pth; ΩJ; ss; s0)
open import OCF.Lean.YiCLPhi using (ωᵀ)
open import OCF.Lean.YiCLCrit using (ωᶜ; ωᶜ-M)
open import OCF.Lean.YiANFam using (Ωᴺ; ψᴺ; cofΩ; cmp-gt; fsTΩ)
open import OCF.Lean.YiMENote using (fsnψω)
open import OCF.Align.EboLeanDef using (HC; h0; h1; hω; cof; cω; fsn; natT)
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiNXLow using (A; Wit; lowTerm; fsLow; nf-small; hA₀; hA₁; LowMove; FirstMissing)
open import OCF.Align.EboLeanBase using (c∷; c[])
open import OCF.Align.EboLeanTree using (hc)
open import OCF.Align.Value using (_≼_; ≼-trans)
open import OCF.Lean.YiRefTw2 using (Rt; hω-inv; tree-≼; fs≼)
open import OCF.Lean.YiKSRead using (fs-sup)

opaque
  fromM : ∀ {t x} → M⁰ t x → HC t
  fromM mz = h0 refl
  fromM (m1 e m) = h1 e (fromM m)
  fromM (mL e f) = hω e (λ n → fromM (f n))
  fromM (mΩ {p = ()} _ _ _)
  fromM (mU {c = ()} _ _)
  fromM (mw m _) = fromM m
module Leaves (o : Ok (fn 2)) (r : Rb (fn 2)) (s : Tp 1 0) (b : Base (fn 2)) (ok : OKB b)
              (β : Tr⁺ (fn 0)) (hβ : M⁰ (Ωᴺ 0) (proj₁ β)) {c : Tr zero} (cc : Can c) (l : M⁰ ωᵀ c) where
  opaque
    leaf-base : ∀ n → M⁰ (Wit n) (proj₁ (ψ (fn 2) o r b (fn 0) (tp s) β (proj₁ (gˢ c))))
    leaf-base n = LF o r s [] b
      (mkGB (λ {i} si → ok (fn i) (inc tt (pth si)))
            (λ {i} si → ΩJ i (b (fn i) (inc tt (pth si))) (ok (fn i) (inc tt (pth si)))))
      β hβ (proj₂ (proj₂ (ω̃ˢ cc l n)))

  hWit : ∀ n → HC (Wit n)
  hWit n = fromM (leaf-base n)

module Closed = Leaves (okf 2) (rb-no (fn 2)) (tc (ss s0)) (B₀ (fn 2)) (λ i u → ⊴r)
                       (Ωt (fn 0)) (ΩJ 0 (Ωt (fn 0)) ⊴r) {c = ωᶜ} canω ωᶜ-M

opaque
  hWit-all : ∀ n → HC (Wit n)
  hWit-all = Closed.hWit

cofA : ∀ n → cof (A n) ≡ cω
cofA zero = refl
cofA (suc zero) = refl
cofA (suc (suc zero)) = refl
cofA (suc (suc (suc n))) rewrite cofΩ (suc (suc n)) | cmp-gt {b = 2} {a = suc (suc n)} (s≤s (s≤s z≤n)) = refl

cofAbove : ∀ n → cof (ψᴺ 2 (Ωᴺ (suc (suc (suc n))))) ≡ cω
cofAbove n rewrite cofΩ (suc (suc n)) | cmp-gt {b = 2} {a = suc (suc n)} (s≤s (s≤s z≤n)) = refl

fsAbove0 : ∀ n → fsn (ψᴺ 2 (Ωᴺ (suc (suc (suc n))))) 0 ≡ ψᴺ 2 (Ωᴺ (suc (suc n)))
fsAbove0 n rewrite cofΩ (suc (suc n)) | cmp-gt {b = 2} {a = suc (suc n)} (s≤s (s≤s z≤n)) = cong (ψᴺ 2) (fsTΩ (suc (suc n)) (Ωᴺ (suc (suc n))))

fsA0 : ∀ n → fsn (A (suc n)) 0 ≡ A n
fsA0 zero = refl
fsA0 (suc zero) = refl
fsA0 (suc (suc n)) = trans (fsnψω (natT 0) (ψᴺ 2 (Ωᴺ (suc (suc (suc n))))) 0 (cofAbove n)) (cong (ψᴺ 0) (fsAbove0 n))

hcDown : ∀ n → HC (A (suc n)) → HC (A n)
hcDown n h = subst HC (fsA0 n) (hω-inv h (cofA (suc n)) 0)

opaque
  hA-all : ∀ n → HC (A n)
  hA-all n = hcDown n (hcDown (suc n) (hcDown (suc (suc n)) (hWit-all n)))

opaque
  hLow : HC lowTerm
  hLow = hω refl (λ n → subst HC (sym (fsLow n)) (hA-all n))

upA : ∀ n (h : HC (A n)) (h′ : HC (A (suc n))) → Rt h ≼ Rt h′
upA n h h′ = ≼-trans (tree-≼ (sym (fsA0 n)) h (hω-inv h′ (cofA (suc n)) 0)) (fs≼ h′ (cofA (suc n)) 0)

move : ∀ n (h : HC (A n)) (h′ : HC (Wit n)) → Rt h ≼ Rt h′
move n h h′ = ≼-trans (upA n h (hA-all (suc n)))
  (≼-trans (upA (suc n) (hA-all (suc n)) (hA-all (suc (suc n))))
           (upA (suc (suc n)) (hA-all (suc (suc n))) h′))

lowMove : LowMove
lowMove n = hWit-all n , λ h → move n h (hWit-all n)

firstMissing : FirstMissing
firstMissing = hWit-all 1 , move 1 hA₁ (hWit-all 1)

module Out (o : Ok (fn 2)) (r : Rb (fn 2)) (s : Tp 1 0) (b : Base (fn 2)) (ok : OKB b)
           (β : Tr⁺ (fn 0)) (hβ : M⁰ (Ωᴺ 0) (proj₁ β)) {c : Tr zero} (cc : Can c) (l : M⁰ ωᵀ c) where
  module Lf = Leaves o r s b ok β hβ {c = c} cc l

  exit-low0 : (h : HC lowTerm) → Rt h ≼ readRW (proj₁ (ψ (fn 2) o r b (fn 0) (tp s) β (proj₁ (gˢ c))))
  exit-low0 h = fs-sup h refl (λ n →
    ≼-trans (tree-≼ (fsLow n) (hω-inv h refl n) (hA-all n))
      (≼-trans (move n (hA-all n) (Lf.hWit n)) (lower⁰ (Lf.leaf-base n) (Lf.hWit n))))

module ClosedOut = Out (okf 2) (rb-no (fn 2)) (tc (ss s0)) (B₀ (fn 2)) (λ i u → ⊴r)
                       (Ωt (fn 0)) (ΩJ 0 (Ωt (fn 0)) ⊴r) {c = ωᶜ} canω ωᶜ-M

full-example : Rt hLow ≼ readRW (proj₁ (ψ (fn 2) (okf 2) (rb-no (fn 2)) (B₀ (fn 2))
                               (fn 0) (tp (tc (ss s0))) (Ωt (fn 0)) (proj₁ (gˢ ωᶜ))))
full-example = ClosedOut.exit-low0 hLow
```
