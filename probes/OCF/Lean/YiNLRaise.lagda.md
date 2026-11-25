# R 推导在相容上下文中的 Leaf
验收文件；`raiseR` 从底上的读法与 Leaf，构造上抬层号上的 Leaf。
上下文取 `YiNLCtx`；极限与基本列算式引用 `YiKVInst`、`YiMENote`、`YiMWPre`。
不把任意 Rd 推导转成 Leaf；入口 `raiseR`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNLRaise where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiLLCheck as LL
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Align.EboLeanView using (cof0; ne)
open import OCF.Align.EboLean3Base using (Ωt-mono)
open import OCF.Align.EBO using (<-sucT)
open import OCF.Lean.YiMENote using (cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiKVInst using (Ωω; fsnΩω)
open import OCF.Lean.YiGICheck using (limᵍ)
open import OCF.Lean.YiNLRead
open import OCF.Lean.YiNLCtx

extend : ∀ F b {t} → GR.Rd (run F zero) t → Top (run F zero) t → Top (run F b) t
extend F zero qa lf = lf
extend F (nd sS h) {t} qa lf = packTop F sS h
  (LL.rdown (nd sS _) (Ωt-mono (inj₁ (<-sucT t))) (LL.succ-upper (λ _ → run F (h tt)) (rd-floor F (h tt) qa)))
extend F (nd sL h) qa lf = packTop F sL h
  (LL.G.m-cum sL (λ n → run F (h n)) (λ n → O.upz n (O.Ωt (run F (h n)))) 0
    (H.mU H.mz (extend F (h 0) qa lf)))
extend F (nd (sΩ k) h) qa lf = packTop F (sΩ k) h (H.mw (H.mU H.mz (extend F (h zero) qa lf)) ◃w)

weak-top : ∀ F ℓ {x y t} → ℓ ⊢ x ◃ y → GR.Rd (run F (↑ ℓ x)) t → Top (run F (↑ ℓ x)) t → Top (run F (↑ ℓ y)) t
weak-top F ℓ {t = t} ◃s qa lf = packTop F sS _
  (LL.rdown (nd sS _) (Ωt-mono (inj₁ (<-sucT t))) (LL.succ-upper _ qa))
weak-top F ℓ (◃l {f} n) qa lf = packTop F sL (λ n → ↑ ℓ (f n))
  (LL.G.m-cum sL (λ n → run F (↑ ℓ (f n))) (λ n → O.upz n (O.Ωt (run F (↑ ℓ (f n))))) n (H.mU H.mz lf))
weak-top F ℓ (◃w {p} {g}) qa lf = packTop F (sΩ (at ℓ p)) (λ c → ↑ ℓ (g (fromBr ℓ p c))) (H.mw (H.mU H.mz lf) ◃w)
weak-top F (nd s h) (◃u x c y e) qa lf = extend (compose F (prefix (↑ (nd s h) x))) (↑ (h c) y) qa lf
weak-top F (nd s h) (◃c x c d) qa lf = weak-top (compose F (prefix (↑ (nd s h) x))) (h c) d qa lf
weak-top F ℓ (◃t d e) qa lf = weak-top F ℓ e (rd-mono F (P.◃→⊑ ℓ d) qa) (weak-top F ℓ d qa lf)

ΩΩ : ∀ ν {κ} → E.cof ν ≡ E.cΩ κ → E.cof (E.Ωt ν) ≡ E.cΩ κ
ΩΩ [] ()
ΩΩ ν@(_ ∷ _) e = cong (E.cofψ0 ν) e

fsΩΩ : ∀ ν {κ} η → E.cof ν ≡ E.cΩ κ → E.fsT (E.Ωt ν) η ≡ E.Ωt (E.fsT ν η)
fsΩΩ [] η ()
fsΩΩ ν@(_ ∷ _) η e = cong (λ c → E.fsT0 ν c η) e

RaiseAt : L → Set
RaiseAt ℓ = ∀ F t → GR.Rd (run F zero) t → Top (run F zero) t →
  ∀ {ν y} → GR.R ℓ ν y → Top (run F (↑ ℓ y)) (t ++ ν)

module NodeRaise (s : Sh) (h : Ch s → L) (child : ∀ c → RaiseAt (h c)) where
  raiseN : RaiseAt (nd s h)
  raiseN F t qa lf (H.mz {x}) = subst (Top (run F (↑ (nd s h) x))) (sym (++-identityʳ t)) (extend F (↑ (nd s h) x) qa lf)
  raiseN F t qa lf (H.m1 {t = ν} {x} e r) = packTop F sS (λ _ → ↑ (nd s h) x)
    (LL.succ-exact (λ _ → run F (↑ (nd s h) x)) (cof++1 t ν e)
      (subst (GR.Rd (run F (↑ (nd s h) x))) (sym (pred++ t ν e)) (rd-ctx F (↑ (nd s h) x) qa (readR (nd s h) r))))
  raiseN F t qa lf (H.mL {t = ν} {x} e ds) = limᵍ {ℓ = run F (↑ (nd s h) x)} (Ωω (t ++ ν) (cof++ω t ν e))
    (λ n → subst (λ z → GR.R (run F (↑ (nd s h) x)) z (proj₁ (O.Ωt (run F (↑ (nd s h) x)))))
      (sym (trans (fsnΩω (t ++ ν) n (cof++ω t ν e)) (cong E.Ωt (fsn++ t ν n e)))) (raiseN F t qa lf (ds n)))
  raiseN F t qa lf (H.mΩ {t = ν} {ν = κ} {p} {g} e q ds) = packTop F (sΩ (at (nd s h) p)) (λ c → ↑ (nd s h) (g (fromBr (nd s h) p c)))
    (H.mΩ (ΩΩ (t ++ ν) (cof++Ω t ν e)) (nu-to (nd s h) p q)
      (λ η c r → subst (λ z → GR.R (nd (sΩ (at (nd s h) p)) (λ c → run F (↑ (nd s h) (g (fromBr (nd s h) p c))))) z _)
        (sym (trans (fsΩΩ (t ++ ν) η (cof++Ω t ν e)) (cong E.Ωt (fsT++ t ν η e))))
        (H.mU H.mz (raiseN F t qa lf (ds η (fromBr (nd s h) p c) (low-from (nd s h) p r))))))

  raiseN F t qa lf (H.mU {t = u} {s = v} {x} {c} {y} r q) =
    subst (Top (run F (↑ (nd s h) x ⊕ ↑ (h c) y))) (++-assoc t u v)
      (child c (compose F (prefix (↑ (nd s h) x))) (t ++ u) (rd-ctx F (↑ (nd s h) x) qa (readR (nd s h) r)) (raiseN F t qa lf r) q)
  raiseN F t qa lf (H.mw {x} r d) = weak-top F (nd s h) d (rd-ctx F (↑ (nd s h) x) qa (readR (nd s h) r)) (raiseN F t qa lf r)
  raiseN F t qa lf (H.mc le r) = LL.rdown _ (Ωt-mono (app≤ t le)) (raiseN F t qa lf r)

raise0 : RaiseAt zero
raise0 F t qa lf (H.mz {x}) = subst (Top (run F (↑ zero x))) (sym (++-identityʳ t)) (extend F (↑ zero x) qa lf)
raise0 F t qa lf (H.m1 {t = ν} {x} e r) = packTop F sS (λ _ → ↑ zero x)
  (LL.succ-exact (λ _ → run F (↑ zero x)) (cof++1 t ν e)
    (subst (GR.Rd (run F (↑ zero x))) (sym (pred++ t ν e)) (rd-ctx F (↑ zero x) qa (readR zero r))))
raise0 F t qa lf (H.mL {t = ν} {x} e ds) = limᵍ {ℓ = run F (↑ zero x)} (Ωω (t ++ ν) (cof++ω t ν e))
  (λ n → subst (λ z → GR.R (run F (↑ zero x)) z (proj₁ (O.Ωt (run F (↑ zero x)))))
    (sym (trans (fsnΩω (t ++ ν) n (cof++ω t ν e)) (cong E.Ωt (fsn++ t ν n e)))) (raise0 F t qa lf (ds n)))
raise0 F t qa lf (H.mΩ {p = ()} e q ds)
raise0 F t qa lf (H.mU {c = ()} r q)
raise0 F t qa lf (H.mw {x} r d) = weak-top F zero d (rd-ctx F (↑ zero x) qa (readR zero r)) (raise0 F t qa lf r)
raise0 F t qa lf (H.mc le r) = LL.rdown _ (Ωt-mono (app≤ t le)) (raise0 F t qa lf r)

raiseR : ∀ ℓ → RaiseAt ℓ
raiseR zero = raise0
raiseR (nd s h) = NodeRaise.raiseN s h (λ c → raiseR (h c))
```
