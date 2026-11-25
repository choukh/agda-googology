# 一般目标的 Ω 行：保留与走链
验收文件（读记号）；保留支据 `YiTBFam.LFΩ`，走链支据 `YiLKFold.Fold.chain/LF`。
目标为任意 j、参照下标为任意 ν；`NodeFrame` 只记录实际 `kp` 分支的比较与槽位搬运。
链起点直接用 `PrefixU`；可交 YiSU 的 `StepU′` 或显式链给互递归，不假定 Leaf。
入口：`node-row`、`chain′`；各层框架是否满足仍须另证。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGTNode where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; Keep; kp; node⁺)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiLKIface using (OK; feed)
open import OCF.Lean.YiLKSlot using (low-from)
open import OCF.Lean.YiSUIface using (PrefixU; StepU′)
open import OCF.Lean.YiANFam using (Pen; cofG; fsnG)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiGTGen
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

KeepSpec : ∀ ℓ j ν (p : Pos ℓ) κ → Keep j (Br ℓ p) (fromBr ℓ p zero) → Set
KeepSpec ℓ j ν p κ nothing = E.cmpᵀ (E.sucT κ) ν ≡ E.gt
KeepSpec ℓ j ν p κ (just (q , cv , eq)) =
  Pen (E.cmpᵀ (E.sucT κ) ν) × GR.Nu j q κ
  × (∀ η c → GR.Low j q η c → GR.Low ℓ p η (cv c))

NodeFrame : ∀ ℓ → Ok ℓ → ∀ j → j ≤ ℓ → E.T → Set
NodeFrame ℓ o j w ν = (p : Pos ℓ) (κ : E.T) → GR.Nu ℓ p κ
  → KeepSpec ℓ j ν p κ (kp ℓ o p w)

start-prefix : ∀ ℓ (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) t → PrefixU B t
  → (p : Pos ℓ) (κ : E.T) → GR.Nu ℓ p κ → (g : Br ℓ p → Tr ℓ)
  → GR.Low ℓ p (E.Ωt κ) (feed ℓ o r B p g (fromBr ℓ p zero))
start-prefix ℓ o r B t pref p κ nu g = low-from ℓ p
  (weakenᴿ (at ℓ p) (closeᴿ (at ℓ p) (Ω≤ψ κ t) (pref p κ nu))
    (ψ-⊵ ℓ o r B (at ℓ p) (posW ℓ p) (B (at ℓ p) (posW ℓ p))
      (g (fromBr ℓ p zero))))

chain′ : ∀ ℓ → StepU′ ℓ → (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) → OK B
  → (t : E.T) → PrefixU B t → ∀ a (p : Pos ℓ) κ → GR.Nu ℓ p κ → E.cof a ≡ E.cΩ κ
  → (g : Br ℓ p → Tr ℓ)
  → (∀ η c → GR.Low ℓ p η c → GR.R ℓ (E.fsT a η) (g c))
  → ∀ n → GR.Low ℓ p (E.γT (t ++ a) κ n)
    (iter (feed ℓ o r B p g) (fromBr ℓ p zero) (suc n))
chain′ ℓ st o r B gb t pref a p κ nu e g hg zero = start-prefix ℓ o r B t pref p κ nu g
chain′ ℓ st o r B gb t pref a p κ nu e g hg (suc n) =
  st o r B gb t pref a p κ nu e g n
    (iter (feed ℓ o r B p g) (fromBr ℓ p zero) (suc n))
    (chain′ ℓ st o r B gb t pref a p κ nu e g hg n)
    (hg (E.γT (t ++ a) κ n) _ (chain′ ℓ st o r B gb t pref a p κ nu e g hg n))

ChainAt : ∀ ℓ → Ok ℓ → Rb ℓ → Base ℓ → E.T → E.T → (p : Pos ℓ) → E.T → (Br ℓ p → Tr ℓ) → Set
ChainAt ℓ o r B t a p κ g = ∀ n → GR.Low ℓ p (E.γT (t ++ a) κ n)
  (iter (feed ℓ o r B p g) (fromBr ℓ p zero) (suc n))

module Core (ℓ j : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (w : j ≤ ℓ)
  (ν t : E.T) (β : Tr⁺ j) where
  F : Tr ℓ → Tr⁺ j
  F x = ψ ℓ o r B j w β x

  node-at : ∀ (p : Pos ℓ) {a κ} (g : Br ℓ p → Tr ℓ) → E.cof a ≡ E.cΩ κ → GR.Nu ℓ p κ
    → (∀ η c → GR.Low ℓ p η c → GR.R ℓ (E.fsT a η) (g c))
    → (∀ η c → GR.Low ℓ p η c → GR.R j (E.ψ ν (t ++ E.fsT a η) ∷ []) (proj₁ (F (g c))))
    → ChainAt ℓ o r B t a p κ g
    → (K : Keep j (Br ℓ p) (fromBr ℓ p zero)) → KeepSpec ℓ j ν p κ K
    → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (node⁺ K (λ c → F (g c)) (feed ℓ o r B p g)))
  node-at p {a} {κ} g e nu hg bh hc (just (q , cv , eq)) (pen , nuq , low) =
    nodeψ j ν t a q e pen nuq (λ η c lc → bh η (cv c) (low η c lc))
  node-at p {a} {κ} g e nu hg bh hc nothing gt =
    limᴿ j (cofG ν (t ++ a) gt (cof++Ω t a e))
      (λ n → subst (λ z → GR.R j z
        (proj₁ (limc⁺ (λ k → F (g (iter (feed ℓ o r B p g) (fromBr ℓ p zero) k))))))
        (sym (trans (fsnG ν (t ++ a) n gt (cof++Ω t a e))
          (cong (λ z → E.ψ ν z ∷ []) (fsT++ t a (E.γT (t ++ a) κ n) e))))
        (cumᴿ j (λ k → F (g (iter (feed ℓ o r B p g) (fromBr ℓ p zero) k))) (suc n)
          (bh (E.γT (t ++ a) κ n) _ (hc n))))

  node-row : NodeFrame ℓ o j w ν
    → ∀ (p : Pos ℓ) {a κ} (g : Br ℓ p → Tr ℓ) → E.cof a ≡ E.cΩ κ → GR.Nu ℓ p κ
    → (∀ η c → GR.Low ℓ p η c → GR.R ℓ (E.fsT a η) (g c))
    → (∀ η c → GR.Low ℓ p η c → GR.R j (E.ψ ν (t ++ E.fsT a η) ∷ []) (proj₁ (F (g c))))
    → ChainAt ℓ o r B t a p κ g
    → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (F (Ω p g)))
  node-row frame p {κ = κ} g e nu hg bh hc = node-at p g e nu hg bh hc (kp ℓ o p w) (frame p κ nu)

module Row (ℓ j : L) (o : Ok ℓ) (r : Rb ℓ) (B : Base ℓ) (w : j ≤ ℓ)
  (ν t : E.T) (gb : OK B) (pref : PrefixU B t) (st : StepU′ ℓ) (β : Tr⁺ j) where
  open Core ℓ j o r B w ν t β using (F)

  node-row : NodeFrame ℓ o j w ν
    → ∀ (p : Pos ℓ) {a κ} (g : Br ℓ p → Tr ℓ) → E.cof a ≡ E.cΩ κ → GR.Nu ℓ p κ
    → (∀ η c → GR.Low ℓ p η c → GR.R ℓ (E.fsT a η) (g c))
    → (∀ η c → GR.Low ℓ p η c → GR.R j (E.ψ ν (t ++ E.fsT a η) ∷ []) (proj₁ (F (g c))))
    → GR.R j (E.ψ ν (t ++ a) ∷ []) (proj₁ (F (Ω p g)))
  node-row fr p {a} {κ} g e nu hg bh = Core.node-row ℓ j o r B w ν t β fr p g e nu hg bh
    (chain′ ℓ st o r B gb t pref a p κ nu e g hg)
```
