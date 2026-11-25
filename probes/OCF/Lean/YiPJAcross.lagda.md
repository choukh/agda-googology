# 跨有限孩子的任意路径分派
验收文件；编译定理。比较表两支中的嵌入后槽位分派，对两条实际有限路径均不加规范形前提。
由 YiPJCase.cases 与 YiPJEmb.slotJ 合成；记号下标的 gt/keep 包装只用既有 gtJ。
来源：YiHCBridge.kcaseB/kcaseB₂ 的效果，不改树、折叠或合法性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPJAcross where
open import Data.Nat using (ℕ; zero; suc) renaming (_≤_ to _≤ⁿ_)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Keep; kp⁼; mapK)
open import OCF.Lean.YiCLFam using (fn)
open import OCF.Lean.YiCLLow using (gtJ)
open import OCF.Lean.YiHCBridge using (LwB)
open import OCF.Lean.YiHCFam using (LwP)
open import OCF.Lean.YiPJCase using (cases; levB; levPB)
open import OCF.Lean.YiPJEmb using (slotJ)
import OCF.Align.EboLeanDef as E
open E using (cmpᵀ; sucT; natT; gt)

across : ∀ A ℓ (e : ℓ ≡ fn A) B ℓ′ (e′ : ℓ′ ≡ fn B) j j′ (e″ : j′ ≡ fn j)
  (o : Ok ℓ′) (u : ℓ ≤ ℓ′) (t : Pos⁼ ℓ) (v : j′ ≤ ℓ′) (Q : Keep j′ (Br⁼ ℓ t) (bz⁼ ℓ t) → Set)
  → (j ≤ⁿ levB A ℓ e t → Q nothing)
  → ((q : Pos j′) (cv : Br j′ q → Br⁼ ℓ t) (eq : cv (fromBr j′ q zero) ≡ bz⁼ ℓ t)
    → levPB j j′ e″ q ≡ levB A ℓ e t
    → (∀ η c → LwB j′ e″ (inj₂ q) η c → LwB ℓ e t η (cv c)) → Q (just (q , cv , eq)))
  → Q (mapK (pshBr u t) (pshFirst u t) (kp⁼ ℓ′ o (psh u t) v))
across A ℓ e B ℓ′ e′ j j′ e″ o u t v Q dr kc =
  cases B ℓ′ e′ j j′ e″ o (psh u t) v (λ K → Q (mapK (pshBr u t) (pshFirst u t) K))
    (λ le → dr (subst (j ≤ⁿ_) (proj₁ (slotJ B ℓ′ e′ A ℓ e u t)) le))
    (λ q cv eq lq lw → kc q (λ c → pshBr u t (cv c)) (trans (cong (pshBr u t) eq) (pshFirst u t))
      (trans lq (proj₁ (slotJ B ℓ′ e′ A ℓ e u t)))
      (λ η c l → proj₂ (slotJ B ℓ′ e′ A ℓ e u t) η (cv c) (lw η c l)))

caseK : ∀ A ℓ (e : ℓ ≡ fn A) j (o : Ok ℓ) (t : Pos⁼ ℓ) (v : fn j ≤ ℓ) {ν}
  → ν ≡ natT (levB A ℓ e t) → (Q : Keep (fn j) (Br⁼ ℓ t) (bz⁼ ℓ t) → Set)
  → (cmpᵀ (sucT ν) (natT j) ≡ gt → Q nothing)
  → ((q : Pos (fn j)) (cv : Br (fn j) q → Br⁼ ℓ t) (eq : cv (fromBr (fn j) q zero) ≡ bz⁼ ℓ t)
    → ν ≡ natT (levPB j (fn j) refl q)
    → (∀ η c → LwP j q η c → LwB ℓ e t η (cv c)) → Q (just (q , cv , eq)))
  → Q (kp⁼ ℓ o t v)
caseK A ℓ e j o t v nu Q dr kc = cases A ℓ e j (fn j) refl o t v Q
  (λ le → dr (gtJ le nu)) (λ q cv eq lq lw → kc q cv eq (trans nu (cong natT (sym lq))) lw)

acrossK : ∀ A ℓ (e : ℓ ≡ fn A) B ℓ′ (e′ : ℓ′ ≡ fn B) j (o : Ok ℓ′)
  (u : ℓ ≤ ℓ′) (t : Pos⁼ ℓ) (v : fn j ≤ ℓ′) {ν} → ν ≡ natT (levB A ℓ e t)
  → (Q : Keep (fn j) (Br⁼ ℓ t) (bz⁼ ℓ t) → Set)
  → (cmpᵀ (sucT ν) (natT j) ≡ gt → Q nothing)
  → ((q : Pos (fn j)) (cv : Br (fn j) q → Br⁼ ℓ t) (eq : cv (fromBr (fn j) q zero) ≡ bz⁼ ℓ t)
    → ν ≡ natT (levPB j (fn j) refl q)
    → (∀ η c → LwP j q η c → LwB ℓ e t η (cv c)) → Q (just (q , cv , eq)))
  → Q (mapK (pshBr u t) (pshFirst u t) (kp⁼ ℓ′ o (psh u t) v))
acrossK A ℓ e B ℓ′ e′ j o u t v nu Q dr kc = across A ℓ e B ℓ′ e′ j (fn j) refl o u t v Q
  (λ le → dr (gtJ le nu)) (λ q cv eq lq lw → kc q cv eq (trans nu (cong natT (sym lq))) lw)
```
