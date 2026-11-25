# 总域上的限域接口与条件归约
验收文件；编译定理：`Presᴰ`、`Startᴰ`、`Stepᴰ` 分别与原全域律互推，没有缩小前提。
接口据 `YiLKIface` 加域证据；归约直接复用 `YiLKFold`、`YiLKSlot`，不重证折叠归纳。
`steps→lowKeepᴰ` 仍带全域 Leaf；其前提已有否定，本文件不作为强度成果。
入口：`pres-fromᴰ`、`step-fromᴰ`、`pres→lowKeepᴰ`、`slots→lowKeepᴰ`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPFReduce where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiRWBlock hiding (D; R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiHCRel using (M⁰)
open import OCF.Lean.YiPFDom
open import OCF.Lean.YiLKIface using (OK; PresU; StartU; StepU; self-zero)
open import OCF.Lean.YiLKFold using (slots→lowKeep)
open import OCF.Lean.YiLKSlot using (steps→lowKeep)
open import OCF.Lean.YiGIInst using (gradedᵍ; domsᵍ; wz)
open import OCF.Lean.YiAbsGIface using (module Laws)
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

Presᴰ : L → Set
Presᴰ ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t : E.T) (β : Tr⁺ zero) → M⁰ (E.ψ [] t ∷ []) (proj₁ β)
  → ∀ {a x} → D ℓ x → GR.R ℓ a x
  → M⁰ (E.ψ [] (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B zero (z≤ ℓ) β x))

Startᴰ : L → Set
Startᴰ ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ) → D ℓ (Ω p g)
  → GR.Low ℓ p (E.γT (t ++ a) ν zero)
      (feedᴰ ℓ o r B p g (fromBr ℓ p zero))

Stepᴰ : L → Set
Stepᴰ ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t a : E.T) (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → E.cof a ≡ E.cΩ ν → (g : Br ℓ p → Tr ℓ) → D ℓ (Ω p g)
  → (n : ℕ) (c : Br ℓ p)
  → GR.Low ℓ p (E.γT (t ++ a) ν n) c
  → GR.R ℓ (E.fsT a (E.γT (t ++ a) ν n)) (g c)
  → GR.Low ℓ p (E.γT (t ++ a) ν (suc n)) (feedᴰ ℓ o r B p g c)

pres-toᴰ : ∀ ℓ → PresU ℓ → Presᴰ ℓ
pres-toᴰ ℓ pr o r B gb t β mb d m = pr o r B gb t β mb m

pres-fromᴰ : ∀ ℓ → Presᴰ ℓ → PresU ℓ
pres-fromᴰ ℓ pr o r B gb t β mb {a} {x} m = pr o r B gb t β mb (all-in ℓ x) m

start-toᴰ : ∀ ℓ → StartU ℓ → Startᴰ ℓ
start-toᴰ ℓ st o r B gb t a p ν nu e g d = st o r B gb t a p ν nu e g

start-fromᴰ : ∀ ℓ → Startᴰ ℓ → StartU ℓ
start-fromᴰ ℓ st o r B gb t a p ν nu e g = st o r B gb t a p ν nu e g (all-in ℓ (Ω p g))

step-toᴰ : ∀ ℓ → StepU ℓ → Stepᴰ ℓ
step-toᴰ ℓ st o r B gb t a p ν nu e g d = st o r B gb t a p ν nu e g

step-fromᴰ : ∀ ℓ → Stepᴰ ℓ → StepU ℓ
step-fromᴰ ℓ st o r B gb t a p ν nu e g = st o r B gb t a p ν nu e g (all-in ℓ (Ω p g))

pres-zero : Presᴰ zero
pres-zero = pres-toᴰ zero self-zero

start-zero : Startᴰ zero
start-zero o r B gb t a ()

step-zero : Stepᴰ zero
step-zero o r B gb t a ()

gx-in : ∀ {ℓ x} → x ≡ proj₁ (Ωt ℓ) → D ℓ x
gx-in {ℓ} refl = root ℓ

pres→lowKeepᴰ : (∀ ℓ → Presᴰ ℓ) → Laws.LowKeep gradedᵍ domsᵍ
pres→lowKeepᴰ pr {ℓ} (o , r , B) .(z≤ ℓ) β t rb wz (mb , gb) gx m =
  pr ℓ o r B gb t β mb (gx-in gx) m

slots→lowKeepᴰ : (∀ ℓ → Startᴰ ℓ) → (∀ ℓ → Stepᴰ ℓ) → Laws.LowKeep gradedᵍ domsᵍ
slots→lowKeepᴰ st sp = slots→lowKeep (λ ℓ → record
  { start = start-fromᴰ ℓ (st ℓ) ; step = step-fromᴰ ℓ (sp ℓ) })

steps→lowKeepᴰ : Laws.Leaf gradedᵍ domsᵍ → (∀ ℓ → Stepᴰ ℓ) → Laws.LowKeep gradedᵍ domsᵍ
steps→lowKeepᴰ lf sp = steps→lowKeep lf (λ ℓ → step-fromᴰ ℓ (sp ℓ))
```
