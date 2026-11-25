# 同步生成一般保持、更新前缀与槽位链
验收文件（读记号）；据 `YiSPRel.Fold.LF¹/chain` 的互递归，把源关系推导作为下降参数。
`IndexTree/LayerIndex` 只供槽位路径证据，后者固定本层比较表；不假定 SlotPres 或 StepU′。
实例和证据域的限制另交，不声称所有合法层号都有 IndexTree。
入口：`direct`、`Direct.LF`、`Direct.chain`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGTDirect where
open import Data.Nat using (zero; suc)
open import Data.Unit using (⊤)
open import Data.Sum using (inj₂)
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
open import OCF.Lean.YiLKSlot using (low-from)
open import OCF.Lean.YiSUIface using (PrefixU)
open import OCF.Lean.YiMWPre using (fsT++)
open import OCF.Lean.YiGTGen
open import OCF.Lean.YiGTNode using (ChainAt; start-prefix; module Core)
open import OCF.Lean.YiGTIndex
open import OCF.Lean.YiGTFold using (pres-zero)
import OCF.Lean.YiGTEmb as Emb
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

SlotIndex : ∀ ℓ → Ok ℓ → Rb ℓ → Set
SlotIndex ℓ o r = (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
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
      → (β : Tr⁺ j) → GR.R j (E.ψ ν t ∷ []) (proj₁ β)
      → ∀ {a x} → GR.R (nd s h) a x
      → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (F j w β x))
    LF j w ν idx β mb (H.mz {x = x}) =
      ++[] (λ z → GR.R j (E.ψ ν z ∷ []) (proj₁ (F j w β x))) t
        (zlᴿ j (λ y → proj₁ (F j w β y)) (mono (nd s h) o r B j w β) mb x)
    LF j w ν idx β mb (H.m1 {t = a} {x = x} e m) =
      nextψ j ν t a e (F j w β x) (LF j w ν idx β mb m)
    LF j w ν idx β mb (H.mL {t = a} {x = x} e m) =
      limψ j ν t a e (proj₁ (F j w β x)) (λ n → LF j w ν idx β mb (m n))
    LF j w ν idx β mb (H.mΩ {t = a} {ν = κ} {p = p} {g = g} e nu m) =
      Core.node-row (nd s h) j o r B w ν t β (proj₁ idx) p g e nu m
        (λ η c lc → LF j w ν idx β mb (m η c lc)) (chain a p κ nu e g m)
    LF j w ν idx β mb (H.mU {t = a} {s = b} {x = x} {c = c} {y = y} {e = ey} m ch) =
      subst (λ z → GR.R j (E.ψ ν z ∷ []) (proj₁ (F j w β (up x c y ey)))) (++-assoc t a b)
        (Emb.emb-row s h child o r B gb t pref j w ν idx β c y ey m
          (update m) (LF j w ν idx β mb m) ch)
    LF j w ν idx β mb (H.mw m d) = weakᴿ j (LF j w ν idx β mb m) (mono (nd s h) o r B j w β d)
    LF j w ν idx β mb (H.mc le m) = closeᴿ j (app≤ν ν t le) (LF j w ν idx β mb m)

    update : ∀ {a x} → GR.R (nd s h) a x → (c : Ch s)
      → PrefixU (Emb.Top.cb s h child o r B gb t pref x c) (t ++ a)
    update m c p ν nu = LF _ (posW (nd s h) (inj₂ (c , inj₂ p))) ν
      (slots (inj₂ (c , inj₂ p)) ν nu)
      (B _ (posW (nd s h) (inj₂ (c , inj₂ p)))) (pref (inj₂ (c , inj₂ p)) ν nu) m

    chain : ∀ a (p : Pos (nd s h)) κ → GR.Nu (nd s h) p κ → E.cof a ≡ E.cΩ κ
      → (g : Br (nd s h) p → Tr (nd s h))
      → (∀ η c → GR.Low (nd s h) p η c → GR.R (nd s h) (E.fsT a η) (g c))
      → ChainAt (nd s h) o r B t a p κ g
    chain a p κ nu e g m zero = start-prefix (nd s h) o r B t pref p κ nu g
    chain a p κ nu e g m (suc n) = low-from (nd s h) p
      (subst (λ z → GR.R (at (nd s h) p) (E.ψ κ z ∷ [])
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

LayerIndex : ∀ ℓ → Ok ℓ → Rb ℓ → Set
LayerIndex zero o r = ⊤
LayerIndex (nd s h) o r = SlotIndex (nd s h) o r × ((c : Ch s) → IndexTree (h c))

layer-at : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) → LayerIndex ℓ o r
  → (B : Base ℓ) → OK B → (t : E.T) → PrefixU B t
  → (j : L) (w : j ≤ ℓ) (ν : E.T) → IndexOK ℓ o r j w ν
  → (β : Tr⁺ j) → GR.R j (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R ℓ a x
  → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B j w β x))
layer-at zero o r li = pres-zero o r
layer-at (nd s h) o r (si , its) =
  Direct.LF s h (λ c → direct (h c) (its c)) o r si
```
