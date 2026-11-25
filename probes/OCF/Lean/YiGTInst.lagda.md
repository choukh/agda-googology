# 零层、最小层与实际 tw 1 的路径实例
验收文件（读记号）；零与最小非零层的路径、前缀及保持条件有闭实例。
`slot-one` 来源于 `YiSUMin.step′-one` 中的有限层保持应用，不把原 StepU 当成已成立。
实际 tw 1 这里只交目标零层的槽位路径证据，不称整个 tw 1 已有 IndexTree。
入口：`it-one`、`kit-one`、`self-one`、`tw1-index`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiGTInst where
open import Data.Nat using (zero)
open import Data.Unit using (tt)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (refl)
open import OCF.Lean.YiRWBlock hiding (R)
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀)
open import OCF.Lean.YiTBRow using (Rb; ψ)
open import OCF.Lean.YiCLFam using (fn; okf)
open import OCF.Lean.YiCLLow using (s0)
open import OCF.Lean.YiRBFam using (tc)
open import OCF.Lean.YiHCFold using (mkGB)
open import OCF.Lean.YiLTFold using (LF)
open import OCF.Lean.YiSUIface using (PrefixU)
open import OCF.Lean.YiSUMin using (rd-zero; to-one; step′-one; prefix-zero)
open import OCF.Lean.YiSUBridge using (Bnext; ok-next; prefix-next)
open import OCF.Lean.YiGTNode using (NodeFrame)
open import OCF.Lean.YiGTIndex
open import OCF.Lean.YiGTFold using (pres)
open import OCF.Lean.YiGTDirect using (IndexTree; SlotIndex)
open import OCF.Lean.YiGTSelf using (self-pres)
open import OCF.Lean.YiGTLow using (low-when-prefix)
import OCF.Lean.YiMTTab as MT
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E

slot-one : SlotPres (fn 1)
slot-one o r B gb t pref (inj₂ (tt , inj₁ tt)) ν nu m with rd-zero nu
... | refl = LF o r (tc s0) t B
  (mkGB (λ { s0 → gb zero (inc tt self) })
    (λ { s0 → pref (inj₂ (tt , inj₁ tt)) [] (GR.c0 refl) }))
  (B zero (inc tt self)) (pref (inj₂ (tt , inj₁ tt)) [] (GR.c0 refl)) (to-one m)
slot-one o r B gb t pref (inj₂ (tt , inj₂ ())) ν nu m

kit-one : Kit (fn 1)
kit-one = slot-one , step′-one , λ _ → tt

pres-one : PresAt (fn 1)
pres-one = pres (fn 1) kit-one

slot-index-one : (o : Ok (fn 1)) (r : Rb (fn 1)) → SlotIndex (fn 1) o r
slot-index-one o r (inj₂ (tt , inj₁ tt)) ν nu with rd-zero nu
... | refl = zero-frame (fn 1) o (inc tt self) , index-zero zero (proj₂ o tt) (proj₂ r tt)
slot-index-one o r (inj₂ (tt , inj₂ ())) ν nu

it-one : IndexTree (fn 1)
it-one = slot-index-one , λ _ → tt

one-frame : (o : Ok (fn 1)) → NodeFrame (fn 1) o (fn 1) self (E.natT 1)
one-frame o (inj₂ (tt , inj₁ tt)) κ nu with rd-zero nu
... | refl = inj₂ refl , nu , λ η c lc → lc
one-frame o (inj₂ (tt , inj₂ ())) κ nu

self-one : (o : Ok (fn 1)) (r : Rb (fn 1)) (B : Base (fn 1)) (t : E.T) (β : Tr⁺ (fn 1))
  → GR.R (fn 1) (E.ψ (E.natT 1) t ∷ []) (proj₁ β)
  → ∀ {a x} → GR.R (fn 1) a x
  → GR.R (fn 1) (E.ψ (E.natT 1) (t ++ a) ∷ [])
      (proj₁ (ψ (fn 1) o r B (fn 1) self β x))
self-one o r B t = self-pres (fn 1) o r B (E.natT 1) t (one-frame o)

tw1-index : (r : Rb (tw 1)) → IndexOK (tw 1) (Ok-tw 1) r zero (ink self) []
tw1-index = index-tw1-slot

one-leaf : GR.R (fn 1) (E.Ωs []) (proj₁ (Ωt (fn 1)))
one-leaf = H.mΩ refl (GR.c0 refl) (λ η c lc → H.mU H.mz (H.mw lc ◃s))

one-prefix : PrefixU (B₀ (fn 1)) []
one-prefix = prefix-zero

rd-one : GR.Rd (fn 1) (E.natT 1)
rd-one = GR.ca (inj₂ (refl , GR.c0 refl))

prefix-one : PrefixU Bnext (E.natT 1)
prefix-one = prefix-next

beta-one : GR.R zero (E.ψ [] (E.natT 1) ∷ []) (proj₁ (next⁺ (Ωt zero)))
beta-one = H.G⁰.m-next (Ωt zero) refl (λ n → refl) (H.m1 refl H.mz)

low-one-next : ∀ {a x} → GR.R (fn 1) a x
  → GR.R zero (E.ψ [] (E.natT 1 ++ a) ∷ [])
      (proj₁ (ψ (fn 1) (okf 1) (MT.rbᶻ (fn 1)) Bnext zero (z≤ (fn 1)) (next⁺ (Ωt zero)) x))
low-one-next = low-when-prefix (fn 1) it-one (okf 1 , MT.rbᶻ (fn 1) , Bnext)
  (next⁺ (Ωt zero)) (E.natT 1) (beta-one , ok-next) prefix-one
```
