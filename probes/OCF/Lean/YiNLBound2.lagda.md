# 第二塔项全部读法的上界
验收文件；编译定理 `upper₂`：`tw 2` 的任意读法不高于 Ω_{Ω+1}。
来源：孩子严格上界取 `YiNLCeiling`，Ω 根用 `YiCNTw1.leaf-tw1` 供给探针。
这里仅比较记号项序；完整 Leaf 见 `YiNLTop2`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNLBound2 where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiGIRel as GR
import OCF.Lean.YiLLCheck as LL
import OCF.Lean.YiLLLeafNeg as N
import OCF.Lean.YiCNTw1 as T1
open import OCF.Lean.YiGICheck using (succᵍ)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_; ≤-<; ≤-trans′; <ᵀ-trans; <sucT)
open import OCF.Align.EboLean3Base using (hd<Ω; Ωt-mono)
open import OCF.Align.EBO using (<-sucT; pred-suc)
open import OCF.Align.EboLeanView using (Vω; ws; wl; w4; w5; w6; vω; fω; fω-eq; VΩ; ωs; ωr; ωl; ωp; vΩ; fΩ; fΩ-eq; fΩ-pos; γ; cof0; ne)
open import OCF.Lean.YiNLCeiling

Upper₂ : Set
Upper₂ = ∀ {ν} → GR.Rd (tw 2) ν → ν ≤ᵀ κ₂

level-head : E.T → E.T
level-head [] = []
level-head (E.ψ u b ∷ xs) = u

no-fω-succΩ₁ : ∀ {ν} (v : Vω ν) → fω v 2 ≡ E.sucT T1.Ω₁ → ⊥
no-fω-succΩ₁ (ws v) eq = N.conflict (N.fω-big v) (inj₂ (cong T1.tail eq))
no-fω-succΩ₁ (wl e v) eq = T1.nonempty (sym (cong T1.tail eq))
no-fω-succΩ₁ (w4 {u = u} {b = b} e) eq = T1.nonempty (trans (sym head) tail-level)
  where
  head : u ≡ E.natT 1
  head = cong level-head eq
  tail-level : u ≡ []
  tail-level = cong (λ t → level-head (T1.tail t)) eq
no-fω-succΩ₁ (w5 e v) eq = T1.nonempty (sym (cong T1.tail eq))
no-fω-succΩ₁ (w6 e cmp v) eq = T1.nonempty (sym (cong T1.tail eq))

no-fω-cap : ∀ {ν} (v : Vω ν) → fω v 2 ≡ κ₂ → ⊥
no-fω-cap (ws v) eq = T1.no-emptyω v (cong T1.tail eq)
no-fω-cap (wl e v) eq = no-fω-succΩ₁ v (cong level-head eq)
no-fω-cap (w4 e) eq = T1.nonempty (cong T1.tail eq)
no-fω-cap (w5 e v) eq = T1.no-emptyω v (cong T1.arg eq)
no-fω-cap (w6 e cmp v) eq = bad (subst ([] E.<ᵀ_) (cong T1.arg eq) (fΩ-pos v E.[]<))
  where
  bad : [] E.<ᵀ [] → ⊥
  bad ()

fω-cap≤ : ∀ {ν} (v : Vω ν) → fω v 2 ≤ᵀ κ₂ → ν E.<ᵀ κ₂
fω-cap≤ v (inj₁ p) = fω-ceil₂ v p
fω-cap≤ v (inj₂ eq) = ⊥-elim (no-fω-cap v eq)

fΩ-cap≤ : ∀ {ν μ} (v : VΩ ν μ) → μ ≤ᵀ T1.Ω₁ → fΩ v (probe μ) E.<ᵀ κ₂ → ν ≤ᵀ κ₂
fΩ-cap≤ (ωs {x = E.ψ u b} v) pm p = inj₁ (E.hd< (E.lv< (hd<Ω p)))
fΩ-cap≤ (ωr {u} e) (inj₁ pm) p = inj₁ (fΩ-ceil₂ (ωr e) pm p)
fΩ-cap≤ (ωr {u} e) (inj₂ eq) p = inj₂ (cong E.Ωt (trans (sym (pred-suc u e)) (cong E.sucT eq)))
fΩ-cap≤ (ωl e v) pm p = inj₁ (≤-< (Ωt-mono (fΩ-small v (<sucT T1.Ω₁ (hd<Ω p)))) (E.hd< (E.lv< (<-sucT T1.Ω₁))))
fΩ-cap≤ (ωp {u} e pen v) pm p = inj₁ (E.hd< (E.lv< (hd<Ω p)))

upper₂ : Upper₂
upper₂ (GR.c0 {ν = []} e) = inj₁ E.[]<
upper₂ (GR.c0 {ν = _ ∷ _} e) = ⊥-elim (cof0 _ ne e)
upper₂ (GR.ca (inj₁ (c , q))) = inj₁ (child-bound₂ c q)
upper₂ {ν} (GR.ca (inj₂ (μ , e , qk , qh))) = fΩ-cap≤ (vΩ ν e) (T1.rd1-bound qk)
  (subst (E._<ᵀ κ₂) (fΩ-eq (vΩ ν e) (probe μ))
    (child-bound₂ (suc (proj₁ (O.Ωt (tw 1))))
      (qh (probe μ) (suc (proj₁ (O.Ωt (tw 1)))) (succᵍ {ℓ = tw 1} refl (T1.leaf-tw1 qk)))))
upper₂ {ν} (GR.cL e ds) = inj₁ (fω-cap≤ (vω ν e) (subst (_≤ᵀ κ₂) (fω-eq (vω ν e) 2) (upper₂ (ds 2))))
upper₂ (GR.cc le q) = ≤-trans′ le (upper₂ q)
```
