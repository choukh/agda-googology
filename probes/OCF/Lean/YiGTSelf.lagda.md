# 一般下标的自身折叠保持
验收文件（读记号）；推导归纳据 `YiTBFam.Self.PF`，上折改用 `YiGTUp.up-pres`。
只需自身路径的 `NodeFrame`，不用 Leaf、PrefixU、StepU′ 或 SlotPres。
不主张 `Rd ℓ ν` 自动给出此框架；零层与最小非零层实例另交。
入口：`self-pres`、`zero-self`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGTSelf where
open import Data.Nat using (zero)
open import Data.Product using (proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (subst)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (Rb; ψ; mono)
open import OCF.Lean.YiKVRel using (++[])
open import OCF.Lean.YiGTGen
open import OCF.Lean.YiGTNode using (NodeFrame)
open import OCF.Lean.YiGTUp using (up-pres)
open import OCF.Lean.YiGTEmb using (self-child)
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

zero-self : (o : Ok zero) (r : Rb zero) (B : Base zero) (t ν : E.T) (β : Tr⁺ zero)
  → GR.R zero (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R zero a x
  → GR.R zero (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ zero o r B zero self β x))
zero-self o r B t ν β mb (H.mz {x = x}) =
  ++[] (λ z → GR.R zero (E.ψ ν z ∷ []) (proj₁ (ψ zero o r B zero self β x))) t
    (zlᴿ zero (λ y → proj₁ (ψ zero o r B zero self β y)) (mono zero o r B zero self β) mb x)
zero-self o r B t ν β mb (H.m1 {t = a} {x = x} e m) =
  nextψ zero ν t a e (ψ zero o r B zero self β x) (zero-self o r B t ν β mb m)
zero-self o r B t ν β mb (H.mL {t = a} {x = x} e m) =
  limψ zero ν t a e (proj₁ (ψ zero o r B zero self β x))
    (λ n → zero-self o r B t ν β mb (m n))
zero-self o r B t ν β mb (H.mΩ {p = ()} _ _ _)
zero-self o r B t ν β mb (H.mU {c = ()} _ _)
zero-self o r B t ν β mb (H.mw m d) =
  weakᴿ zero (zero-self o r B t ν β mb m) (mono zero o r B zero self β d)
zero-self o r B t ν β mb (H.mc le m) =
  closeᴿ zero (app≤ν ν t le) (zero-self o r B t ν β mb m)

module Self (s : Sh) (h : Ch s → L) (o : Ok (nd s h)) (r : Rb (nd s h))
  (B : Base (nd s h)) (ν t : E.T) (fr : NodeFrame (nd s h) o (nd s h) self ν)
  (β : Tr⁺ (nd s h)) (mb : GR.R (nd s h) (E.ψ ν t ∷ []) (proj₁ β)) where
  F : Tr (nd s h) → Tr⁺ (nd s h)
  F x = ψ (nd s h) o r B (nd s h) self β x

  LF : ∀ {a x} → GR.R (nd s h) a x → GR.R (nd s h) (E.ψ ν (t ++ a) ∷ []) (proj₁ (F x))
  LF (H.mz {x = x}) = ++[] (λ z → GR.R (nd s h) (E.ψ ν z ∷ []) (proj₁ (F x))) t
    (zlᴿ (nd s h) (λ y → proj₁ (F y)) (mono (nd s h) o r B (nd s h) self β) mb x)
  LF (H.m1 {t = a} {x = x} e m) = nextψ (nd s h) ν t a e (F x) (LF m)
  LF (H.mL {t = a} {x = x} e m) = limψ (nd s h) ν t a e (proj₁ (F x)) (λ n → LF (m n))
  LF (H.mΩ {t = a} {ν = κ} {p = p} {g = g} e nu m) =
    nodeψ (nd s h) ν t a p e (proj₁ (fr p κ nu)) nu (λ η c lc → LF (m η c lc))
  LF (H.mU {t = a} {s = b} {x = x} {c = c} {y = y} m ch) =
    subst (λ z → GR.R (nd s h) (E.ψ ν z ∷ [])
      (proj₁ (Up (h c) (down {s = s} {h = h} stop c) (F x) y))) (++-assoc t a b)
      (up-pres (h c) ν (down {s = s} {h = h} stop c) (self-child s h o ν fr c)
        (t ++ a) (F x) (LF m) ch)
  LF (H.mw m d) = weakᴿ (nd s h) (LF m) (mono (nd s h) o r B (nd s h) self β d)
  LF (H.mc le m) = closeᴿ (nd s h) (app≤ν ν t le) (LF m)

self-pres : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) ν t → NodeFrame ℓ o ℓ self ν
  → (β : Tr⁺ ℓ) → GR.R ℓ (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R ℓ a x
  → GR.R ℓ (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B ℓ self β x))
self-pres zero o r B ν t fr = zero-self o r B t ν
self-pres (nd s h) o r B ν t fr = Self.LF s h o r B ν t fr
```
