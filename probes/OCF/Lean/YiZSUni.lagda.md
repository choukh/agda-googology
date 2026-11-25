# 合并: Ω 树的折叠沿层号上行 (一条对折叠的四条律陈述的定理)

> 判决: 编译定理, 无前提, 不读记号. `YiSVMono.Mono.liftS`, `liftL` 与 `YiLTLift.upS`, `upL` 合成一条: 折叠满足 `FoldLaws` (起点在下 `f⊵`, 单调 `fm`, 一致路径上嵌入一行进孩子 `fu`, 后继层号的 Ω 树在某个嵌入之上 `fs`), 则 "Ω 树的折叠落在 Q" 从孩子层号传到后继层号与 ℕ 极限层号 (`Lift.genS`, `genL`).
> 实例: 换基核的折叠 `YiRBSib.ψ` (`lawsᴿ`); `liftS′`, `liftL′` 的陈述与 `YiSVMono` 的两条逐字相同, 由 `genS`, `genL` 推出. 比较表折叠的实例与 `upS`, `upL` 见 [YiZSUniT](YiZSUniT.lagda.md).
> 不给出什么: 原文件没有改, 原引理仍在; 含 Ω 形状的层号没有做.
> 来源: `genS`, `genL` 的步骤取自 `YiSVMono.Mono.liftS`, `liftL″`.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiZSUni where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
import OCF.Lean.YiRBSib as R
open import OCF.Lean.YiSVMono
```

## 律

`x ⊑⁺ y`: 从 x 经若干步 `◃` 与左加到 y. 对 `◃` 向上封闭且对左加封闭的谓词沿它上行.

```agda
infix 4 _⊑⁺_
data _⊑⁺_ {ℓ : L} (x : Tr ℓ) : Tr ℓ → Set where
  rfl : x ⊑⁺ x
  stp : ∀ {y z} → x ⊑⁺ y → ℓ ⊢ y ◃ z → x ⊑⁺ z
  add : ∀ {y} (a : Tr ℓ) → x ⊑⁺ y → x ⊑⁺ (a + y)

record FoldLaws (RbT : L → Set) (rc : ∀ {s h} → RbT (nd s h) → (c : Ch s) → RbT (h c))
                (F : (ℓ : L) → Ok ℓ → RbT ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j) : Set₁ where
  field
    f⊵ : ∀ ℓ o r B j w β x → proj₁ β ⊴ proj₁ (F ℓ o r B j w β x)
    fm : ∀ ℓ o r B j w β {x y} → ℓ ⊢ x ◃ y → j ⊢ proj₁ (F ℓ o r B j w β x) ◃ proj₁ (F ℓ o r B j w β y)
    fu : ∀ {s h} (o : Ok (nd s h)) (r : RbT (nd s h)) (B : Base (nd s h)) j (ws : (c : Ch s) → j ≤ h c) β x c y e
       → F (nd s h) o r B j (inu ws) β (up x c y e)
       ≡ F (h c) (proj₂ o c) (rc r c) (λ i u → F (nd s h) o r B i (inc c u) (B i (inc c u)) x) j (ws c)
           (F (nd s h) o r B j (inu ws) β x) y
    fs : ∀ {h : ⊤ → L} (o : Ok (nd sS h)) (r : RbT (nd sS h)) (B : Base (nd sS h)) j (ws : (c : ⊤) → j ≤ h c) β → OKB B
       → Σ (Tr (h tt)) λ z → (proj₁ (Ωt (h tt)) ⊴ z)
           × (proj₁ (F (nd sS h) o r B j (inu ws) β (up zero tt (suc z) (z◃ z ◃s)))
              ⊑⁺ proj₁ (F (nd sS h) o r B j (inu ws) β (proj₁ (Ωt (nd sS h)))))
```

## 定理

```agda
module Lift {RbT : L → Set} {rc : ∀ {s h} → RbT (nd s h) → (c : Ch s) → RbT (h c)}
            {F : (ℓ : L) → Ok ℓ → RbT ℓ → Base ℓ → (j : L) → j ≤ ℓ → Tr⁺ j → Tr ℓ → Tr⁺ j}
            (W : FoldLaws RbT rc F) (j : L) (P Q : Tr j → Set)
            (P↑ : ∀ {x y} → P x → j ⊢ x ◃ y → P y)
            (Q↑ : ∀ {x y} → Q x → j ⊢ x ◃ y → Q y)
            (Q+ : ∀ (a : Tr j) {y} → Q y → Q (a + y)) where
  open FoldLaws W

  P⊴ : ∀ {x y} → P x → x ⊴ y → P y
  P⊴ p ⊴r     = p
  P⊴ p (⊴◃ d) = P↑ p d

  Q⊴ : ∀ {x y} → Q x → x ⊴ y → Q y
  Q⊴ p ⊴r     = p
  Q⊴ p (⊴◃ d) = Q↑ p d

  Q⁺ : ∀ {x y} → Q x → x ⊑⁺ y → Q y
  Q⁺ q rfl       = q
  Q⁺ q (stp v d) = Q↑ (Q⁺ q v) d
  Q⁺ q (add a v) = Q+ a (Q⁺ q v)

  SΩ : (ℓ : L) → Ok ℓ → RbT ℓ → j ≤ ℓ → Set
  SΩ ℓ o r v = (B : Base ℓ) → OKB B → (β : Tr⁺ j) → P (proj₁ β) → Q (proj₁ (F ℓ o r B j v β (proj₁ (Ωt ℓ))))

  F⊴ : ∀ ℓ o r B w β {x y} → x ⊴ y → proj₁ (F ℓ o r B j w β x) ⊴ proj₁ (F ℓ o r B j w β y)
  F⊴ ℓ o r B w β ⊴r     = ⊴r
  F⊴ ℓ o r B w β (⊴◃ d) = ⊴◃ (fm ℓ o r B j w β d)

  kid : ∀ {s h} (o : Ok (nd s h)) (r : RbT (nd s h)) (B : Base (nd s h)) (ws : (c : Ch s) → j ≤ h c) (c : Ch s)
      → SΩ (h c) (proj₂ o c) (rc r c) (ws c) → OKB B → (β : Tr⁺ j) → P (proj₁ β)
      → (x : Tr (nd s h)) (y : Tr (h c)) (e : h c ⊢ zero ◃ y) → proj₁ (Ωt (h c)) ⊴ y
      → Q (proj₁ (F (nd s h) o r B j (inu ws) β (up x c y e)))
  kid {s} {h} o r B ws c q ok β hβ x y e d =
    subst (λ Z → Q (proj₁ Z)) (sym (fu o r B j ws β x c y e))
      (Q⊴ (q (λ i u → F (nd s h) o r B i (inc c u) (B i (inc c u)) x)
             (λ i u → ⊴-trans (ok i (inc c u)) (f⊵ (nd s h) o r B i (inc c u) (B i (inc c u)) x))
             (F (nd s h) o r B j (inu ws) β x)
             (P⊴ hβ (f⊵ (nd s h) o r B j (inu ws) β x)))
          (F⊴ (h c) (proj₂ o c) (rc r c) _ (ws c) _ d))

  genS : ∀ {h : ⊤ → L} (o : Ok (nd sS h)) (r : RbT (nd sS h)) (ws : (c : ⊤) → j ≤ h c)
       → SΩ (h tt) (proj₂ o tt) (rc r tt) (ws tt) → SΩ (nd sS h) o r (inu ws)
  genS o r ws q B ok β hβ with fs o r B j ws β ok
  ... | z , d , dom = Q⁺ (kid o r B ws tt q ok β hβ zero (suc z) (z◃ z ◃s) (⊴◃ (⊴-◃ d ◃s))) dom

  genL : ∀ {g : ℕ → L} (o : Ok (nd sL g)) (r : RbT (nd sL g)) (ws : (n : ℕ) → j ≤ g n) (n : ℕ)
       → SΩ (g n) (proj₂ o n) (rc r n) (ws n) → SΩ (nd sL g) o r (inu ws)
  genL {g} o r ws zero q B ok β hβ =
    Q↑ (kid o r B ws zero q ok β hβ zero (proj₁ (Ωt (g zero))) (proj₂ (Ωt (g zero))) ⊴r)
       (fm (nd sL g) o r B j (inu ws) β (◃l zero))
  genL {g} o r ws (suc m) q B ok β hβ =
    Q↑ (kid o r B ws (suc m) q ok β hβ (cum (λ k → proj₁ (upz {sL} {g} k (Ωt (g k)))) m)
            (proj₁ (Ωt (g (suc m)))) (proj₂ (Ωt (g (suc m)))) ⊴r)
       (fm (nd sL g) o r B j (inu ws) β (◃l (suc m)))
```

## 实例: 换基核的折叠; `YiSVMono` 的两条由定理推出

```agda
lawsᴿ : FoldLaws R.Rb (λ r c → proj₂ r c) R.ψ
lawsᴿ = record
  { f⊵ = ψ-⊵
  ; fm = λ ℓ o r B j w β d → R.mono ℓ o r B j w β d
  ; fu = λ o r B j ws β x c y e → refl
  ; fs = λ {h} o r B j ws β ok →
      proj₁ (next⁺ (B (h tt) (inc tt self))) , ⊴◃ (⊴-◃ (ok (h tt) (inc tt self)) (◃l zero)) , stp (add _ rfl) (◃l 1)
  }

module MonoU (j : L) (oj : Ok j) (P Q : Tr j → Set)
  (P↑ : ∀ {x y} → P x → j ⊢ x ◃ y → P y)
  (Q↑ : ∀ {x y} → Q x → j ⊢ x ◃ y → Q y)
  (Q+ : ∀ (a : Tr j) {y} → Q y → Q (a + y)) where
  module M = Mono j oj P Q P↑ Q↑ Q+
  module U = Lift lawsᴿ j P Q P↑ Q↑ Q+

  liftS′ : (h : ⊤ → L) → M.Car (h tt) → M.Car (nd sS h)
  liftS′ h car ob r B β ok hβ =
    U.genS (Ok⊕ j (nd sS h) oj ob) r (λ c → lift j (h c))
      (λ B′ ok′ β′ hβ′ → car (proj₂ ob tt) (proj₂ r tt) B′ β′ ok′ hβ′) B ok β hβ

  liftL′ : (g : ℕ → L) (n : ℕ) → M.Car (g n) → M.Car (nd sL g)
  liftL′ g n car ob r B β ok hβ =
    U.genL (Ok⊕ j (nd sL g) oj ob) r (λ k → lift j (g k)) n
      (λ B′ ok′ β′ hβ′ → car (proj₂ ob n) (proj₂ r n) B′ β′ ok′ hβ′) B ok β hβ
```
