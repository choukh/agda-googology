# 一般目标的路径证据与前缀更新
验收文件（读记号）；路径证据逐条对应现有折叠，比较表缺项的指定孩子路径不在本证据域。
`IndexOK` 只含槽位比较、关系搬运与孩子的同类证据，不含折叠值的保持结论。
`SlotPres` 是尚待构造的槽位目标保持；它给出递归更新底的 `PrefixU`，不由 OK 推出。
入口：`index-zero`、`index-tw1-slot`、`shift-prefix`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGTIndex where
open import Data.Nat using (zero)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; Keep)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiLKIface using (OK)
open import OCF.Lean.YiSUIface using (PrefixU; StepU′)
open import OCF.Lean.YiGTNode using (KeepSpec; NodeFrame)
open import OCF.Lean.YiTSNote using (gt0)
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

CWReq : ∀ {A B : Set} → A ⊎ B → (A → Set) → (B → Set) → Set
CWReq (inj₁ a) F G = F a
CWReq (inj₂ b) F G = G b

DWReq : ∀ {A B : Set} → Maybe (A ⊎ B) → (A → Set) → (B → Set) → Set
DWReq (just w) F G = CWReq w F G
DWReq nothing F G = ⊥

mutual
  IndexOK : ∀ ℓ → Ok ℓ → Rb ℓ → ∀ j → j ≤ ℓ → E.T → Set
  IndexOK ℓ o r j w ν = NodeFrame ℓ o j w ν × RouteOK ℓ o r j w ν

  RouteOK : ∀ ℓ → Ok ℓ → Rb ℓ → ∀ j → j ≤ ℓ → E.T → Set
  RouteOK ℓ o r .ℓ self ν = ⊤
  RouteOK (nd s h) o r j (inu ws) ν = (c : Ch s) → IndexOK (h c) (proj₂ o c) (proj₂ r c) j (ws c) ν
  RouteOK (nd (sΩ k) h) o r j (ink v) ν = (c : Tr k) →
    IndexOK (h c) (proj₂ o c) (proj₂ r c) j (v ∙ proj₂ (proj₁ o) c) ν
  RouteOK (nd sS h) o r j (inc c′ v) ν = IndexOK (h c′) (proj₂ o c′) (proj₂ r c′) j v ν
  RouteOK (nd sL h) o r j (inc n v) ν = (m : Ch sL) → CWReq (way h (proj₁ o) m n)
    (λ u → IndexOK (h n) (proj₂ o n) (proj₂ r n) j v ν)
    (λ u → IndexOK (h m) (proj₂ o m) (proj₂ r m) j (v ∙ u) ν)
  RouteOK (nd (sΩ k) h) o r j (inc c′ v) ν = (c : Tr k) → DWReq (proj₁ r c c′)
    (λ u → IndexOK (h c) (proj₂ o c) (proj₂ r c) j (v ∙ u) ν)
    (λ u → IndexOK (h c′) (proj₂ o c′) (proj₂ r c′) j v ν)

zero-spec : ∀ ℓ (p : Pos ℓ) κ (K : Keep zero (Br ℓ p) (fromBr ℓ p zero)) → KeepSpec ℓ zero [] p κ K
zero-spec ℓ p κ nothing = gt0 κ
zero-spec ℓ p κ (just (() , _))

zero-frame : ∀ ℓ (o : Ok ℓ) (w : zero ≤ ℓ) → NodeFrame ℓ o zero w []
zero-frame ℓ o w p κ nu = zero-spec ℓ p κ _

index-zero : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) → IndexOK ℓ o r zero (z≤ ℓ) []
index-zero zero o r = zero-frame zero o self , tt
index-zero (nd s h) o r = zero-frame (nd s h) o (z≤ (nd s h))
  , λ c → index-zero (h c) (proj₂ o c) (proj₂ r c)

index-lift : ∀ a (o : Ok (zero ⊕ a)) (r : Rb (zero ⊕ a))
  → IndexOK (zero ⊕ a) o r zero (self ∙ lift zero a) []
index-lift zero o r = zero-frame zero o self , tt
index-lift (nd s h) o r = zero-frame (zero ⊕ nd s h) o (self ∙ lift zero (nd s h))
  , λ c → index-lift (h c) (proj₂ o c) (proj₂ r c)

index-tw1-slot : (r : Rb (tw 1)) → IndexOK (tw 1) (Ok-tw 1) r zero (ink self) []
index-tw1-slot r = zero-frame (tw 1) (Ok-tw 1) (ink self)
  , λ c → index-lift (↑ zero c) (proj₂ (Ok-tw 1) c) (proj₂ r c)

SlotPres : L → Set
SlotPres ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t : E.T) → PrefixU B t → (p : Pos ℓ) (ν : E.T) → GR.Nu ℓ p ν
  → ∀ {a x} → GR.R ℓ a x
  → GR.R (at ℓ p) (E.ψ ν (t ++ a) ∷ [])
      (proj₁ (ψ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p)) x))

shift-prefix : ∀ s h → SlotPres (nd s h)
  → (o : Ok (nd s h)) (r : Rb (nd s h)) (B : Base (nd s h)) → OK B
  → (t : E.T) → PrefixU B t → ∀ {a x} → GR.R (nd s h) a x → (c : Ch s)
  → PrefixU (λ i u → ψ (nd s h) o r B i (inc c u) (B i (inc c u)) x) (t ++ a)
shift-prefix s h sp o r B gb t pref m c p ν nu = sp o r B gb t pref (inj₂ (c , inj₂ p)) ν nu m

PresAt : L → Set
PresAt ℓ = (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t : E.T) → PrefixU B t → (j : L) (w : j ≤ ℓ) (ν : E.T) → IndexOK ℓ o r j w ν
  → (β : Tr⁺ j) → GR.R j (E.ψ ν t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R ℓ a x
  → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (ψ ℓ o r B j w β x))

Kit : L → Set
Kit zero = ⊤
Kit (nd s h) = SlotPres (nd s h) × StepU′ (nd s h) × ((c : Ch s) → Kit (h c))
```
