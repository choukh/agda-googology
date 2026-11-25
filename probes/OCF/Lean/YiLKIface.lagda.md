# 全层零目标保持的孩子与槽位接口
验收文件；编译定理的接口与零层实例，不改树、折叠或合法性。
`KidU` 含孩子的标准零路径保持及槽位回灌的起点、步进；不是已经实填的全层律。
来源：孩子行据 `YiSPRel.LFU`，路径检查据 `YiGIBlock.dnᵍ`；零层复用 `YiGICheck.low-zero`。
入口：`Reduction`、`kid-zero`、`self-zero`、`up-inc`、`up-inu`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLKIface where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiRBFam public using () renaming (OKB to OK)
open import OCF.Lean.YiKCStep using (⊴-trans)
open import OCF.Lean.YiHCRel using (M⁰)
open import OCF.Lean.YiGIBlock using (Bsᵍ; ψᵍ)
open import OCF.Lean.YiGIInst using (Bdᵍ; Wlᵍ; wz)
open import OCF.Lean.YiGICheck using (low-zero)
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiMTTab as MT
import OCF.Align.EboLeanDef as E

PresU : L → Set
PresU ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t : E.T) (β : Tr⁺ zero) → M⁰ (E.ψ [] t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R ℓ a x
  → M⁰ (E.ψ [] (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B zero (z≤ ℓ) β x))

ChildU : L → Set
ChildU zero = ⊤
ChildU (nd s h) = (c : Ch s) → PresU (h c)

feed : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (p : Pos ℓ)
  → (Br ℓ p → Tr ℓ) → Br ℓ p → Br ℓ p
feed ℓ o r B p g c = fromBr ℓ p
  (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) (g c)))

StartU : L → Set
StartU ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ)
  → GR.Low ℓ p (E.γT (t ++ a) ν zero)
      (feed ℓ o r B p g (fromBr ℓ p zero))

StepU : L → Set
StepU ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ) (n : ℕ) (c : Br ℓ p)
  → GR.Low ℓ p (E.γT (t ++ a) ν n) c
  → GR.R ℓ (E.fsT a (E.γT (t ++ a) ν n)) (g c)
  → GR.Low ℓ p (E.γT (t ++ a) ν (suc n)) (feed ℓ o r B p g c)


record SlotU (ℓ : L) : Set where
  field
    start : StartU ℓ
    step : StepU ℓ

record KidU (ℓ : L) : Set where
  field
    child : ChildU ℓ
    slot : SlotU ℓ

LowAt : L → Set
LowAt ℓ = ∀ {j} (b : Bsᵍ ℓ) (w : j ≤ ℓ) (β : Tr⁺ j) (t : E.T)
  → proj₁ (proj₂ b) ≡ MT.rbᶻ ℓ → Wlᵍ w → Bdᵍ b w β t
  → ∀ {a x} → x ≡ proj₁ (Ωt ℓ) → GR.R ℓ a x
  → GR.R j (E.ψ [] (t ++ a) ∷ []) (proj₁ (ψᵍ ℓ b j w β x))

Reduction : Set
Reduction = ∀ ℓ → KidU ℓ → LowAt ℓ

kid-zero : KidU zero
kid-zero = record { child = tt ; slot = record { start = λ o r B gb t a () ; step = λ o r B gb t a () } }

self-zero : PresU zero
self-zero o r B gb t β mb = low-zero (o , r , B) β t (mb , gb)

low-zero-instance : LowAt zero
low-zero-instance b .self β t rb wz bd gx m = low-zero b β t bd m

updated-ok : ∀ s h (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) → OK B
  → (x : Tr (nd s h)) (c : Ch s)
  → OK (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x)
updated-ok s h o r B gb x c i u = ⊴-trans (gb i (inc c u))
  (ψ-⊵ (nd s h) o r B i (inc c u) (B i (inc c u)) x)

up-inu : ∀ s h → ChildU (nd s h)
  → (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) → OK B
  → (t a b : E.T) (β : Tr⁺ zero) (x : Tr (nd s h)) (c : Ch s)
  → (y : Tr (h c)) (e : h c ⊢ zero ◃ y)
  → M⁰ (E.ψ [] (t ++ a) ∷ []) (proj₁ (ψ (nd s h) o r B zero (inu (λ c → z≤ (h c))) β x))
  → GR.R (h c) b y
  → M⁰ (E.ψ [] ((t ++ a) ++ b) ∷ [])
      (proj₁ (ψ (nd s h) o r B zero (inu (λ c → z≤ (h c))) β (up x c y e)))
up-inu s h child o r B gb t a b β x c y e mx my =
  child c (proj₂ o c) (proj₂ r c) _ (updated-ok s h o r B gb x c) (t ++ a) _ mx my

up-inc : ∀ h → ChildU (nd sS h)
  → (o : Ok (nd sS h)) (r : Rb (nd sS h)) (B : Base (nd sS h)) → OK B
  → (t a b : E.T) (β : Tr⁺ zero) (x : Tr (nd sS h))
  → (y : Tr (h tt)) (e : h tt ⊢ zero ◃ y)
  → M⁰ (E.ψ [] (t ++ a) ∷ []) (proj₁ (ψ (nd sS h) o r B zero (inc tt (z≤ (h tt))) β x))
  → GR.R (h tt) b y
  → M⁰ (E.ψ [] ((t ++ a) ++ b) ∷ [])
      (proj₁ (ψ (nd sS h) o r B zero (inc tt (z≤ (h tt))) β (up x tt y e)))
up-inc h child o r B gb t a b β x y e mx my =
  child tt (proj₂ o tt) (proj₂ r tt) _ (updated-ok sS h o r B gb x tt) (t ++ a) _ mx my

```
