# 任意目标下标的上折保持
验收文件（读记号）；来源为 `YiHCFam.Pu` 的推导归纳，改用一般层关系与一般目标下标。
`UpFrame` 只含槽位的参照比较与全分支搬运；后继、极限、嵌入不作额外假设。
不声称所有层号和读法满足此框架；零源层有无条件实例。
入口：`up-pres`、`down-frame`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGTUp where
open import Data.Nat using (zero)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (subst)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiKVRel using (++[])
open import OCF.Lean.YiANFam using (Pen)
open import OCF.Lean.YiGTGen
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

UpFrame : ∀ {ℓ} → E.T → (j : L) → Dn ℓ j → Set
UpFrame {ℓ} ν j d = (p : Pos j) (κ : E.T) → GR.Nu j p κ
  → Pen (E.cmpᵀ (E.sucT κ) ν) × GR.Nu ℓ (mv d p) κ
    × (∀ η c → GR.Low ℓ (mv d p) η c → GR.Low j p η (mvBr d p c))

down-frame : ∀ {ℓ} ν s h (d : Dn ℓ (nd s h)) → UpFrame ν (nd s h) d
  → (c : Ch s) → UpFrame ν (h c) (down d c)
down-frame ν s h d fr c p κ nu = fr (inj₂ (c , inj₂ p)) κ nu

zero-frame : ∀ {ℓ} ν (d : Dn ℓ zero) → UpFrame ν zero d
zero-frame ν d ()

up-zero : ∀ {ℓ} ν (d : Dn ℓ zero) t (β : Tr⁺ ℓ)
  → GR.R ℓ (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R zero a x
  → GR.R ℓ (E.ψ ν (t ++ a) ∷ []) (proj₁ (Up zero d β x))
up-zero {ℓ} ν d t β mb (H.mz {x = x}) =
  ++[] (λ z → GR.R ℓ (E.ψ ν z ∷ []) (proj₁ (Up zero d β x))) t
    (zlᴿ ℓ (λ y → proj₁ (Up zero d β y)) (Upm zero d β) mb x)
up-zero {ℓ} ν d t β mb (H.m1 {t = a} {x = x} e m) =
  nextψ ℓ ν t a e (Up zero d β x) (up-zero ν d t β mb m)
up-zero {ℓ} ν d t β mb (H.mL {t = a} {x = x} e m) =
  limψ ℓ ν t a e (proj₁ (Up zero d β x)) (λ n → up-zero ν d t β mb (m n))
up-zero ν d t β mb (H.mΩ {p = ()} _ _ _)
up-zero ν d t β mb (H.mU {c = ()} _ _)
up-zero {ℓ} ν d t β mb (H.mw m q) = weakᴿ ℓ (up-zero ν d t β mb m) (Upm zero d β q)
up-zero {ℓ} ν d t β mb (H.mc le m) = closeᴿ ℓ (app≤ν ν t le) (up-zero ν d t β mb m)

UpAt : L → Set
UpAt j = ∀ {ℓ} ν (d : Dn ℓ j) → UpFrame ν j d
  → (t : E.T) (β : Tr⁺ ℓ) → GR.R ℓ (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R j a x
  → GR.R ℓ (E.ψ ν (t ++ a) ∷ []) (proj₁ (Up j d β x))

fold-up : ∀ s h → ((c : Ch s) → UpAt (h c)) → UpAt (nd s h)
fold-up s h child {ℓ} ν d fr t β mb (H.mz {x = x}) =
  ++[] (λ z → GR.R ℓ (E.ψ ν z ∷ []) (proj₁ (Up (nd s h) d β x))) t
    (zlᴿ ℓ (λ y → proj₁ (Up (nd s h) d β y)) (Upm (nd s h) d β) mb x)
fold-up s h child {ℓ} ν d fr t β mb (H.m1 {t = a} {x = x} e m) =
  nextψ ℓ ν t a e (Up (nd s h) d β x) (fold-up s h child ν d fr t β mb m)
fold-up s h child {ℓ} ν d fr t β mb (H.mL {t = a} {x = x} e m) =
  limψ ℓ ν t a e (proj₁ (Up (nd s h) d β x))
    (λ n → fold-up s h child ν d fr t β mb (m n))
fold-up s h child {ℓ} ν d fr t β mb (H.mΩ {t = a} {ν = κ} {p = p} {g = g} e nu m) =
  nodeψ ℓ ν t a (mv d p) e (proj₁ (fr p κ nu)) (proj₁ (proj₂ (fr p κ nu)))
    (λ η c lc → fold-up s h child ν d fr t β mb
      (m η (mvBr d p c) (proj₂ (proj₂ (fr p κ nu)) η c lc)))
fold-up s h child {ℓ} ν d fr t β mb (H.mU {t = a} {s = b} {x = x} {c = c} {y = y} m ch) =
  subst (λ z → GR.R ℓ (E.ψ ν z ∷ [])
    (proj₁ (Up (h c) (down d c) (Up (nd s h) d β x) y))) (++-assoc t a b)
    (child c ν (down d c) (down-frame ν s h d fr c) (t ++ a)
      (Up (nd s h) d β x) (fold-up s h child ν d fr t β mb m) ch)
fold-up s h child {ℓ} ν d fr t β mb (H.mw m q) =
  weakᴿ ℓ (fold-up s h child ν d fr t β mb m) (Upm (nd s h) d β q)
fold-up s h child {ℓ} ν d fr t β mb (H.mc le m) =
  closeᴿ ℓ (app≤ν ν t le) (fold-up s h child ν d fr t β mb m)

up-pres : ∀ j → UpAt j
up-pres zero ν d fr = up-zero ν d
up-pres (nd s h) = fold-up s h (λ c → up-pres (h c))
```
