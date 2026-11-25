# 新旧有限关系的首层对接与余尾读法的首个差别
> 验收文件（读记号）。首层双向及第二层旧到新成立；`Rd (fn 1) []` 不满足旧槽位的指定读法。
> 来源：两层转换共用 `YiFMMap.mapᴴ`，Ω 实例调用 `YiHCFam.Mβ`。
> `rd-zero` 用 `EboLeanView.Vω` 排除零层读法中的 ℕ 极限；不据余尾字段差别否定关系族等价。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiFMFin where
open import Data.Nat using (zero; suc)
open import Data.Unit using (tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_; ≤[])
open import OCF.Align.EboLeanView using (Vω; ws; wl; w4; w5; w6; vω; fω; fω-eq; cof0; ne)
open import OCF.Lean.YiRWBlock
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiHCFam as F
import OCF.Lean.YiGIRel as G
open import OCF.Lean.YiCLFam using (fn; Nw)
open import OCF.Lean.YiFMMap using (mapᴴ)

fω₁≢[] : ∀ {t} (v : Vω t) → fω v 1 ≡ [] → ⊥
fω₁≢[] (ws v) ()
fω₁≢[] (wl e v) ()
fω₁≢[] (w4 e) ()
fω₁≢[] (w5 e v) ()
fω₁≢[] (w6 e q v) ()

rd-zero : ∀ {ν} → G.Rd zero ν → ν ≡ []
rd-zero {ν = []} (G.c0 e) = refl
rd-zero {ν = _ ∷ _} (G.c0 e) = ⊥-elim (cof0 _ ne e)
rd-zero (G.ca ())
rd-zero {ν} (G.cL e h) = ⊥-elim (fω₁≢[] (vω ν e) (trans (sym (fω-eq (vω ν e) 1)) (rd-zero (h 1))))
rd-zero {ν} (G.cc le r) = ≤[] (subst (λ μ → ν ≤ᵀ μ) (rd-zero r) le)

old-new¹ : ∀ {s x} → F.M 1 s x → G.R (fn 1) s x
old-new¹ = mapᴴ
  (λ { (inj₂ (tt , inj₁ tt)) m → m ; (inj₂ (tt , inj₂ ())) })
  (λ _ m → m)
  (λ { (inj₂ (tt , inj₁ tt)) refl → G.c0 refl ; (inj₂ (tt , inj₂ ())) })

new-old¹ : ∀ {s x} → G.R (fn 1) s x → F.M 1 s x
new-old¹ = mapᴴ
  (λ { (inj₂ (tt , inj₁ tt)) m → m ; (inj₂ (tt , inj₂ ())) })
  (λ _ m → m)
  (λ { (inj₂ (tt , inj₁ tt)) m → rd-zero m ; (inj₂ (tt , inj₂ ())) })

old-leaf¹ : F.M 1 (E.Ωt (E.natT 1)) (proj₁ (O.Ωt (fn 1)))
old-leaf¹ = F.Mβ 0

new-leaf¹ : G.R (fn 1) (E.Ωt (E.natT 1)) (proj₁ (O.Ωt (fn 1)))
new-leaf¹ = old-new¹ old-leaf¹

back-leaf¹ : F.M 1 (E.Ωt (E.natT 1)) (proj₁ (O.Ωt (fn 1)))
back-leaf¹ = new-old¹ new-leaf¹

low-back² : ∀ p {η c} → G.Low (fn 2) p η c → F.LwP 2 p η c
low-back² (inj₂ (tt , inj₁ tt)) = new-old¹
low-back² (inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))) m = m
low-back² (inj₂ (tt , inj₂ (inj₂ (tt , inj₂ ()))))

nu-forward² : ∀ p {ν} → Nw 1 p ν → G.Nu (fn 2) p ν
nu-forward² (inj₂ (tt , inj₁ tt)) refl = G.ca (inj₂ (refl , G.c0 refl))
nu-forward² (inj₂ (tt , inj₂ (inj₂ (tt , inj₁ tt)))) refl = G.c0 refl
nu-forward² (inj₂ (tt , inj₂ (inj₂ (tt , inj₂ ()))))

old-new² : ∀ {s x} → F.M 2 s x → G.R (fn 2) s x
old-new² = mapᴴ low-back² (λ _ → old-new¹) nu-forward²

p² : Pos (fn 2)
p² = inj₂ (tt , inj₁ tt)

rd-one-zero : G.Rd (fn 1) []
rd-one-zero = G.cc {μ = E.natT 1} (inj₁ E.[]<)
  (G.ca (inj₂ (refl , G.c0 {ν = []} refl)))

nu-new² : G.Nu (fn 2) p² []
nu-new² = rd-one-zero

nu-old²-empty : Nw 1 p² [] → ⊥
nu-old²-empty ()

no-direct-nu-back² : (∀ {ν} → G.Nu (fn 2) p² ν → Nw 1 p² ν) → ⊥
no-direct-nu-back² f = nu-old²-empty (f nu-new²)
```
