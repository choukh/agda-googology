# 修改后的槽位步进在最小层号实填
验收文件；编译定理：`StepU′ (fn 1)`，底与前缀的联系不空真，规范底在空前缀下满足它。
来源：`to-one` 只把 `Rd zero` 化成零；步进直接复用 `YiLTFold.LF` 与 `YiMWPre.fsT++`。
不推出全层 `StepU′`，也没有由原 `Bdᵍ` 推出 `PrefixU`。
入口：`step′-one`、`prefix-zero`。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSUMin where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (B₀)
open import OCF.Lean.YiTBRow using (ψ)
open import OCF.Lean.YiCLFam using (fn)
open import OCF.Lean.YiCLLow using (s0)
open import OCF.Lean.YiRBFam using (tc)
open import OCF.Lean.YiHCFold using (mkGB)
open import OCF.Lean.YiLTFold using (LF)
open import OCF.Lean.YiMWPre using (fsT++)
open import OCF.Lean.YiSUBound using (fsn-nat)
open import OCF.Lean.YiSUIface
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiHCFam as F
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanView using (cof0; ne)

rd-zero : ∀ {ν} → GR.Rd zero ν → ν ≡ []
rd-zero (GR.c0 {ν = []} e) = refl
rd-zero (GR.c0 {ν = x ∷ xs} e) = ⊥-elim (cof0 (x ∷ xs) ne e)
rd-zero (GR.ca ())
rd-zero (GR.cL e h) = ⊥-elim (bad (subst (E.natT 1 E.<ᵀ_) (rd-zero (h 2)) (fsn-nat e 1)))
  where
  bad : E.natT 1 E.<ᵀ [] → ⊥
  bad ()
rd-zero (GR.cc le r) with rd-zero r
... | refl with le
... | inj₂ refl = refl

to-one : ∀ {a x} → GR.R (fn 1) a x → F.M 1 a x
to-one H.mz = H.mz
to-one (H.m1 e m) = H.m1 e (to-one m)
to-one (H.mL e m) = H.mL e (λ n → to-one (m n))
to-one (H.mΩ {p = inj₂ (tt , inj₁ tt)} e nu m) = H.mΩ e (rd-zero nu) (λ η c l → to-one (m η c l))
to-one (H.mΩ {p = inj₂ (tt , inj₂ ())} e nu m)
to-one (H.mU m ch) = H.mU (to-one m) ch
to-one (H.mw m d) = H.mw (to-one m) d
to-one (H.mc le m) = H.mc le (to-one m)

step′-one : StepU′ (fn 1)
step′-one o r B gb t pref a (inj₂ (tt , inj₁ tt)) ν nu e g n c low m with rd-zero nu
... | refl = subst (λ η → H.M⁰ η
    (proj₁ (ψ (fn 1) o r B zero (inc tt self) (B zero (inc tt self)) (g c))))
  (cong (λ z → E.ψ [] z ∷ []) (sym (fsT++ t a (E.γT (t ++ a) [] n) e)))
  (LF o r (tc s0) t B
    (mkGB (λ { s0 → gb zero (inc tt self) }) (λ { s0 → pref (inj₂ (tt , inj₁ tt)) [] (GR.c0 refl) }))
    (B zero (inc tt self)) (pref (inj₂ (tt , inj₁ tt)) [] (GR.c0 refl)) (to-one m))
step′-one o r B gb t pref a (inj₂ (tt , inj₂ ())) ν nu e g n c low m

prefix-zero : PrefixU (B₀ (fn 1)) []
prefix-zero (inj₂ (tt , inj₁ tt)) ν nu with rd-zero nu
... | refl = H.m1 refl H.mz
prefix-zero (inj₂ (tt , inj₂ ())) ν nu
```
