# ω+1 结点分支的精确标签前提
验收文件，读记号；编译定理：实际 Tp、Mβ 有居民，标准底的精确标签版 GB 无居民。
来源：YiLRLow.Lim 的关系与底接口，YiLRNeg.NegLim 的否定机制；接到实际 S.child ω 与 YiTBRow。
不否定 SecondMissing、StepMissing 或其他可数验收关系；按第 0 步的前提失败停止。
入口：actual-Tp、Mβ、no-initial-GB、no-chain-zero；LFNode 仅是接口陈述，未构造居民。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiOPCountable where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiRWFold as F
import OCF.Lean.YiTBRow as TB
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiCLFam as H
import OCF.Lean.YiCLLow as L
import OCF.Lean.YiRBCrit as RC
import OCF.Lean.YiLRBridge as RB
import OCF.Lean.YiLRLow as RL
import OCF.Lean.YiLRNeg as Neg
import OCF.Lean.YiSQOmega as Ω
import OCF.Lean.YiBVSmall as S
import OCF.Lean.YiCLPhi as Phi
import OCF.Align.EboLeanDef as E
import OCF.Lean.YiQLRead as Q
import OCF.Lean.YiVRRel as VR
open import Data.Maybe using (nothing)
G : ℕ → B.L
G n = K.two B.⊕ B.↑ B.zero (H.nat n)
eG : ∀ n → G n ≡ H.fn (RC.sh n)
eG zero = refl
eG (suc n) = cong RB.Sᶜ (eG n)
route : ∀ n → P._≤_ (G n) (G (suc n))
route n = P.inc tt P.self
canonical-step : ∀ {a n} (e : a ≡ H.fn n)
  → RB.τ₂ {ℓ = a} {ℓ′ = RB.Sᶜ a} {A = n} {B = suc n} e (cong RB.Sᶜ e) (P.inc tt P.self) ≡ P.inc tt P.self
canonical-step refl = refl
canR : ∀ n → Σ (L.Sb (RC.sh (suc n)) (RC.sh n)) λ s
  → RB.τ₂ (eG n) (eG (suc n)) (route n) ≡ L.pth s
canR n = L.ss L.s0 , canonical-step (eG n)
module W = RL.Lim G RC.sh eG route canR
module N = Neg.NegLim G RC.sh eG route canR
source : B.L
source = B.nd B.sS (λ _ → W.Lω)
source-eq : S.child Ω.ω ≡ source
source-eq = refl
v : ∀ n → P._≤_ K.one (G n)
v n = P.inc tt P.self P.∙ P.lift K.two (B.↑ B.zero (H.nat n))
data Pt : ∀ {a} → P._≤_ K.one a → Set where
  anchor : Pt (P.inc {s = B.sS} {h = λ _ → K.one} tt P.self)
  next : ∀ {a} {w : P._≤_ K.one a} → Pt w → Pt (P.inu {s = B.sS} {h = λ _ → a} (λ _ → w))
  limit : ∀ {h : ℕ → B.L} {w : ∀ n → P._≤_ K.one (h n)} → (∀ n → Pt (w n)) → Pt (P.inu w)
finite-path : ∀ n → Pt (v n)
finite-path zero = anchor
finite-path (suc n) = next (finite-path n)
Tp : Set
Tp = Pt (S.lower Ω.ω)
actual-Tp : Tp
actual-Tp = next (limit finite-path)
Low : (p : B.Pos source) → E.T → B.Br source p → Set
Low (inj₁ ())
Low (inj₂ (tt , inj₁ tt)) = W.Mω
Low (inj₂ (tt , inj₂ p)) = W.Lowω p
Nu : B.Pos source → E.T → Set
Nu (inj₁ ())
Nu (inj₂ (tt , inj₁ tt)) ν = ν ≡ Phi.ωᵀ
Nu (inj₂ (tt , inj₂ p)) = W.Nuω p
M : E.T → B.Tr source → Set
M = K.Mᴰ (B.Sig source) Low (λ _ → W.Mω) Nu
Mβ : M (E.Ωt (E.sucT Phi.ωᵀ)) (proj₁ (O.Ωt source))
Mβ = K.mΩ refl refl (λ η c l → K.mU K.mz (K.mw l B.◃s))
record GB (base : F.Base source) (prefix : E.T) : Set where
  constructor gb
  field
    finite : W.GBω (λ i u → base i (P.inc tt u)) prefix
    omega-upper : proj₁ (O.Ωt W.Lω) K.⊴ proj₁ (base W.Lω (P.inc tt P.self))
    omega-rel : W.Mω (E.ψ Phi.ωᵀ prefix ∷ []) (proj₁ (base W.Lω (P.inc tt P.self)))
finite-GB : W.GBω (F.B₀ W.Lω) []
finite-GB = W.gbω₀
NZG : ∀ n → Neg.NZ (G n)
NZG zero = tt
NZG (suc n) = tt
QG : ∀ n → Neg.Q (G n) (proj₁ (O.Ωt (G n)))
QG zero = Neg.QΩS (λ _ → K.one) tt
QG (suc n) = Neg.QΩS (λ _ → G n) (NZG n)
no-omega-seed : W.Mω (E.Ωt Phi.ωᵀ) (proj₁ (O.Ωt W.Lω)) → ⊥
no-omega-seed m = N.noωω m refl (Neg.QΩL G QG)
no-initial-GB : GB (F.B₀ source) [] → ⊥
no-initial-GB b = no-omega-seed (GB.omega-rel b)

source-countable : VR.NoΩ source
source-countable = λ n → noG n
  where
  noG : ∀ n → VR.NoΩ (G n)
  noG zero = tt
  noG (suc n) = noG n
read-check : K.M⁰ Phi.ωᵀ Ω.ω
read-check = Ω.read-ω
need-check : Q.Need Phi.ωᵀ Ω.ω
need-check = Ω.need-ω
need-next-check : Q.Need (E.pred (E.sucT Phi.ωᵀ)) Ω.ω
need-next-check = Ω.need-next-input
first-check : H.M 1 (Q.Target Phi.ωᵀ) (proj₁ (Ω.Actual.part 1))
first-check = Ω.first-row
omega-upper : proj₁ (O.Ωt W.Lω) K.⊴ proj₁ (F.B₀ source W.Lω (P.inc tt P.self))
omega-upper = K.⊴r
p : B.Pos source
p = inj₂ (tt , inj₁ tt)
keep-none : ∀ (o : P.Ok source) → F.kp source o p (S.lower Ω.ω) ≡ nothing
keep-none o = refl
feed-zero : ∀ (o : P.Ok source) (r : TB.Rb source)
  → TB.ψ source o r (F.B₀ source) W.Lω (P.inc tt P.self) (O.Ωt W.Lω)
      (B.up B.zero tt (B.suc B.zero) (O.z◃ B.zero B.◃s))
    ≡ O.next⁺ (O.Ωt W.Lω)
feed-zero o r = refl
no-feed-seed : W.Mω (E.Ωt Phi.ωᵀ) (proj₁ (O.next⁺ (O.Ωt W.Lω))) → ⊥
no-feed-seed m = N.noωω m refl (Neg.Qnext W.Lω (O.Ωt W.Lω) (Neg.QΩL G QG))
no-chain-zero : ∀ (o : P.Ok source) (r : TB.Rb source) prefix
  → W.Mω (E.γT prefix Phi.ωᵀ 0)
      (proj₁ (TB.ψ source o r (F.B₀ source) W.Lω (P.inc tt P.self) (O.Ωt W.Lω)
        (B.up B.zero tt (B.suc B.zero) (O.z◃ B.zero B.◃s)))) → ⊥
no-chain-zero o r prefix m = no-feed-seed (subst (λ z → W.Mω (E.Ωt Phi.ωᵀ) (proj₁ z)) (feed-zero o r) m)
LFNode : Set
LFNode = (o : P.Ok source) (r : TB.Rb source) (prefix : E.T) (base : F.Base source)
  → GB base prefix → (beta : O.Tr⁺ K.one)
  → H.M 1 (E.ψ (E.natT 1) prefix ∷ []) (proj₁ beta)
  → ∀ {a ν} {g : B.Tr W.Lω → B.Tr source}
  → E.cof a ≡ E.cΩ ν → ν ≡ Phi.ωᵀ
  → (∀ η c → W.Mω η c → M (E.fsT a η) (g c))
  → H.M 1 (E.ψ (E.natT 1) (prefix ++ a) ∷ [])
      (proj₁ (TB.ψ source o r base K.one (S.lower Ω.ω) beta (B.Ω p g)))
no-GB-from-need : (Q.Need Phi.ωᵀ Ω.ω → GB (F.B₀ source) []) → ⊥
no-GB-from-need f = no-initial-GB (f need-check)
```
