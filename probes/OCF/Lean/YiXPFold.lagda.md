# 槽位标签作参数: 统一保持、同步生成与槽位步进的组装

> 验收文件 (读记号)。编译定理 (条件): `YiGTFold.pres` (由 `Kit`), `YiGTDirect.direct` (由 `IndexTree`), `YiGTSlot.kit` (由 `IndexTree` 给 `Kit`) 对任意槽位标签 `Lab` 成立。
> 来源: 逐行搬自这三个文件, 关系与各行换成 [YiXPRel](YiXPRel.lagda.md), [YiXPRows](YiXPRows.lagda.md) 的参数化版本; 证明不用 `Lab` 的性质。
> 不否定什么; `IndexTree` 在精确标签下的居民见 [YiXPFrame](YiXPFrame.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Lean.YiRWBlock using (L)
import OCF.Align.EboLeanDef as E
module OCF.Lean.YiXPFold (Lab : L → E.T → Set) where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (Rb; ψ; mono)
open import OCF.Lean.YiKVRel using (++[])
open import OCF.Lean.YiLKIface using (OK; feed)
open import OCF.Lean.YiMWPre using (fsT++)
open import OCF.Lean.YiGTGen using (app≤ν)
import OCF.Lean.YiHCRel as H
open import OCF.Lean.YiXPRel Lab
open import OCF.Lean.YiXPRows Lab
```

## 统一保持 (来源 `YiGTFold`)

```agda
pres-zero : PresAt zero
pres-zero o r B gb t pref .zero self ν idx = zero-self o r B t ν

module Fold (s : Sh) (h : Ch s → L) (child : (c : Ch s) → PresAt (h c))
  (sp : SlotPres (nd s h)) (st : StepU′ (nd s h))
  (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) (gb : OK B)
  (t : E.T) (pref : PrefixU B t) where

  F : ∀ j → j ≤ nd s h → Tr⁺ j → Tr (nd s h) → Tr⁺ j
  F j w β x = ψ (nd s h) o r B j w β x

  LF : ∀ j (w : j ≤ nd s h) ν → IndexOK (nd s h) o r j w ν
    → (β : Tr⁺ j) → R j (E.ψ ν t ∷ []) (proj₁ β)
    → ∀ {a x} → R (nd s h) a x
    → R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (F j w β x))
  LF j w ν idx β mb (H.mz {x = x}) =
    ++[] (λ z → R j (E.ψ ν z ∷ []) (proj₁ (F j w β x))) t
      (zlᴿ j (λ y → proj₁ (F j w β y)) (mono (nd s h) o r B j w β) mb x)
  LF j w ν idx β mb (H.m1 {t = a} {x = x} e m) =
    nextψ j ν t a e (F j w β x) (LF j w ν idx β mb m)
  LF j w ν idx β mb (H.mL {t = a} {x = x} e m) =
    limψ j ν t a e (proj₁ (F j w β x)) (λ n → LF j w ν idx β mb (m n))
  LF j w ν idx β mb (H.mΩ {t = a} {ν = κ} {p = p} {g = g} e nu m) =
    Row.node-row (nd s h) j o r B w ν t gb pref st β (proj₁ idx)
      p g e nu m (λ η c lc → LF j w ν idx β mb (m η c lc))
  LF j w ν idx β mb (H.mU {t = a} {s = b} {x = x} {c = c} {y = y} {e = ey} m ch) =
    subst (λ z → R j (E.ψ ν z ∷ []) (proj₁ (F j w β (up x c y ey)))) (++-assoc t a b)
      (emb-row s h child o r B gb t pref j w ν idx β c y ey m
        (shift-prefix s h sp o r B gb t pref m) (LF j w ν idx β mb m) ch)
  LF j w ν idx β mb (H.mw m d) = weakᴿ j (LF j w ν idx β mb m) (mono (nd s h) o r B j w β d)
  LF j w ν idx β mb (H.mc le m) = closeᴿ j (app≤ν ν t le) (LF j w ν idx β mb m)

pres : ∀ ℓ → Kit ℓ → PresAt ℓ
pres zero k = pres-zero
pres (nd s h) (sp , st , ks) o r B gb t pref =
  Fold.LF s h (λ c → pres (h c) (ks c)) sp st o r B gb t pref
```

## 同步生成 (来源 `YiGTDirect`)

```agda
SlotIndex : ∀ ℓ → Ok ℓ → Rb ℓ → Set
SlotIndex ℓ o r = (p : Pos ℓ) (ν : E.T) → Lab (at ℓ p) ν
  → IndexOK ℓ o r (at ℓ p) (posW ℓ p) ν

IndexTree : L → Set
IndexTree zero = ⊤
IndexTree (nd s h) = ((o : Ok (nd s h)) (r : Rb (nd s h)) → SlotIndex (nd s h) o r)
  × ((c : Ch s) → IndexTree (h c))

slot-index : ∀ ℓ → IndexTree ℓ → (o : Ok ℓ) (r : Rb ℓ) → SlotIndex ℓ o r
slot-index zero it o r ()
slot-index (nd s h) it = proj₁ it

module Direct (s : Sh) (h : Ch s → L) (child : (c : Ch s) → PresAt (h c))
  (o : Ok (nd s h)) (r : Rb (nd s h)) (slots : SlotIndex (nd s h) o r)
  (B : Base (nd s h)) (gb : OK B)
  (t : E.T) (pref : PrefixU B t) where

  F : ∀ j → j ≤ nd s h → Tr⁺ j → Tr (nd s h) → Tr⁺ j
  F j w β x = ψ (nd s h) o r B j w β x

  mutual
    LF : ∀ j (w : j ≤ nd s h) ν → IndexOK (nd s h) o r j w ν
      → (β : Tr⁺ j) → R j (E.ψ ν t ∷ []) (proj₁ β)
      → ∀ {a x} → R (nd s h) a x
      → R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (F j w β x))
    LF j w ν idx β mb (H.mz {x = x}) =
      ++[] (λ z → R j (E.ψ ν z ∷ []) (proj₁ (F j w β x))) t
        (zlᴿ j (λ y → proj₁ (F j w β y)) (mono (nd s h) o r B j w β) mb x)
    LF j w ν idx β mb (H.m1 {t = a} {x = x} e m) =
      nextψ j ν t a e (F j w β x) (LF j w ν idx β mb m)
    LF j w ν idx β mb (H.mL {t = a} {x = x} e m) =
      limψ j ν t a e (proj₁ (F j w β x)) (λ n → LF j w ν idx β mb (m n))
    LF j w ν idx β mb (H.mΩ {t = a} {ν = κ} {p = p} {g = g} e nu m) =
      Core.node-row (nd s h) j o r B w ν t β (proj₁ idx) p g e nu m
        (λ η c lc → LF j w ν idx β mb (m η c lc)) (chain a p κ nu e g m)
    LF j w ν idx β mb (H.mU {t = a} {s = b} {x = x} {c = c} {y = y} {e = ey} m ch) =
      subst (λ z → R j (E.ψ ν z ∷ []) (proj₁ (F j w β (up x c y ey)))) (++-assoc t a b)
        (emb-row s h child o r B gb t pref j w ν idx β c y ey m
          (update m) (LF j w ν idx β mb m) ch)
    LF j w ν idx β mb (H.mw m d) = weakᴿ j (LF j w ν idx β mb m) (mono (nd s h) o r B j w β d)
    LF j w ν idx β mb (H.mc le m) = closeᴿ j (app≤ν ν t le) (LF j w ν idx β mb m)

    update : ∀ {a x} → R (nd s h) a x → (c : Ch s)
      → PrefixU (Top.cb s h child o r B gb t pref x c) (t ++ a)
    update m c p ν nu = LF _ (posW (nd s h) (inj₂ (c , inj₂ p))) ν
      (slots (inj₂ (c , inj₂ p)) ν nu)
      (B _ (posW (nd s h) (inj₂ (c , inj₂ p)))) (pref (inj₂ (c , inj₂ p)) ν nu) m

    chain : ∀ a (p : Pos (nd s h)) κ → Lab (at (nd s h) p) κ → E.cof a ≡ E.cΩ κ
      → (g : Br (nd s h) p → Tr (nd s h))
      → (∀ η c → Low (nd s h) p η c → R (nd s h) (E.fsT a η) (g c))
      → ChainAt (nd s h) o r B t a p κ g
    chain a p κ nu e g m zero = start-prefix (nd s h) o r B t pref p κ nu g
    chain a p κ nu e g m (suc n) = low-from (nd s h) p
      (subst (λ z → R (at (nd s h) p) (E.ψ κ z ∷ [])
        (proj₁ (F (at (nd s h) p) (posW (nd s h) p) (B (at (nd s h) p) (posW (nd s h) p))
          (g (iter (feed (nd s h) o r B p g) (fromBr (nd s h) p zero) (suc n))))))
        (sym (fsT++ t a (E.γT (t ++ a) κ n) e))
        (LF (at (nd s h) p) (posW (nd s h) p) κ (slots p κ nu)
          (B (at (nd s h) p) (posW (nd s h) p)) (pref p κ nu)
          (m (E.γT (t ++ a) κ n) _ (chain a p κ nu e g m n))))

direct : ∀ ℓ → IndexTree ℓ → PresAt ℓ
direct zero it = pres-zero
direct (nd s h) (slots , its) o r B gb t pref =
  Direct.LF s h (λ c → direct (h c) (its c)) o r (slots o r) B gb t pref
```

## 槽位步进与 Kit (来源 `YiGTSlot`)

```agda
slot-pres : ∀ ℓ → IndexTree ℓ → SlotPres ℓ
slot-pres ℓ it o r B gb t pref p ν nu m = direct ℓ it o r B gb t pref
  (at ℓ p) (posW ℓ p) ν (slot-index ℓ it o r p ν nu)
  (B (at ℓ p) (posW ℓ p)) (pref p ν nu) m

step-from-slot : ∀ ℓ → SlotPres ℓ → StepU′ ℓ
step-from-slot ℓ sp o r B gb t pref a p ν nu e g n c lc m = low-from ℓ p
  (subst (λ z → R (at ℓ p) (E.ψ ν z ∷ [])
    (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g c))))
    (sym (fsT++ t a (E.γT (t ++ a) ν n) e)) (sp o r B gb t pref p ν nu m))

step′ : ∀ ℓ → IndexTree ℓ → StepU′ ℓ
step′ ℓ it = step-from-slot ℓ (slot-pres ℓ it)

kit : ∀ ℓ → IndexTree ℓ → Kit ℓ
kit zero it = tt
kit (nd s h) it = slot-pres (nd s h) it , step′ (nd s h) it , λ c → kit (h c) (proj₂ it c)
```
