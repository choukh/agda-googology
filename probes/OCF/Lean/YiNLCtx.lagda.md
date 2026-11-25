# 读法的构造子相容上下文
验收文件；上下文逐字保留结点形状，复合律不使用函数外延。
编译定理：`rd-ctx` 合并两侧读法，`rd-mono` 沿非下标侧路径保持读法。
来源：沿用 `YiGIRel.rd-add` 的形状，拼接算式引用 `YiMENote`、`YiMWPre`。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNLCtx where
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)
open import OCF.Lean.YiRWBlock
import OCF.Lean.YiRWOps as O
import OCF.Lean.YiRWPath as P
import OCF.Lean.YiGIRel as GR
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_)
open import OCF.Align.EboLeanView using (cof0; ne)
open import OCF.Align.Standard using (++-mono)
open import OCF.Lean.YiMENote using (cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)

app≤ : ∀ t {ν μ} → ν ≤ᵀ μ → (t ++ ν) ≤ᵀ (t ++ μ)
app≤ t (inj₁ p) = inj₁ (++-mono t p)
app≤ t (inj₂ refl) = inj₂ refl

record Ctx : Set where
  field
    run : L → L
    row : ∀ s h → run (nd s h) ≡ nd s (λ c → run (h c))
open Ctx public

prefix : L → Ctx
prefix a = record { run = a ⊕_ ; row = λ s h → refl }

compose : Ctx → Ctx → Ctx
compose F G = record { run = λ b → run F (run G b) ; row = λ s h →
  trans (cong (run F) (row G s h)) (row F s (λ c → run G (h c))) }

Top : L → E.T → Set
Top a ν = GR.R a (E.Ωt ν) (proj₁ (O.Ωt a))

packRd : ∀ F s h {ν} → GR.Rd (nd s (λ c → run F (h c))) ν → GR.Rd (run F (nd s h)) ν
packRd F s h = subst (λ a → GR.Rd a _) (sym (row F s h))

packTop : ∀ F s h {ν} → Top (nd s (λ c → run F (h c))) ν → Top (run F (nd s h)) ν
packTop F s h = subst (λ a → Top a _) (sym (row F s h))

rd-floor : ∀ F b {ν} → GR.Rd (run F zero) ν → GR.Rd (run F b) ν
rd-floor F zero q = q
rd-floor F (nd s h) q = packRd F s h (GR.rd-child s _ (O.c₀ s) (rd-floor F (h (O.c₀ s)) q))

rd-mono : ∀ F {a b ν} → a P.⊑ b → GR.Rd (run F a) ν → GR.Rd (run F b) ν
rd-mono F P.self q = q
rd-mono F {b = nd s h} (P.inc c p) q = packRd F s h (GR.rd-child s _ c (rd-mono F p q))
rd-mono F {b = nd s h} (P.inu ps) q = packRd F s h (GR.rd-child s _ (O.c₀ s) (rd-mono F (ps (O.c₀ s)) q))

mutual
  rd-ctx : ∀ F b {t ν} → GR.Rd (run F zero) t → GR.Rd b ν → GR.Rd (run F b) (t ++ ν)
  rd-ctx F b {t} qa (GR.c0 {ν = []} e) = subst (GR.Rd (run F b)) (sym (++-identityʳ t)) (rd-floor F b qa)
  rd-ctx F b qa (GR.c0 {ν = _ ∷ _} e) = ⊥-elim (cof0 _ ne e)
  rd-ctx F zero qa (GR.ca ())
  rd-ctx F (nd s h) qa (GR.ca d) = packRd F s h (GR.ca (hd-ctx F s h qa d))
  rd-ctx F b {t} qa (GR.cL {ν} e ds) = GR.cL (cof++ω t ν e)
    (λ n → subst (GR.Rd (run F b)) (sym (fsn++ t ν n e)) (rd-ctx F b qa (ds n)))
  rd-ctx F b {t} qa (GR.cc le q) = GR.cc (app≤ t le) (rd-ctx F b qa q)

  hd-ctx : ∀ F s h {t ν} → GR.Rd (run F zero) t → GR.Hd (nd s h) ν → GR.Hd (nd s (λ c → run F (h c))) (t ++ ν)
  hd-ctx F s h qa (inj₁ (c , q)) = inj₁ (c , rd-ctx F (h c) qa q)
  hd-ctx F sS h {t} {ν} qa (inj₂ (e , q)) = inj₂ (cof++1 t ν e ,
    subst (GR.Rd (run F (h tt))) (sym (pred++ t ν e)) (rd-ctx F (h tt) qa q))
  hd-ctx F sL h qa (inj₂ ())
  hd-ctx F (sΩ k) h {t} {ν} qa (inj₂ (κ , e , qk , qh)) = inj₂
    (κ , cof++Ω t ν e , qk , λ η c r → subst (GR.Rd (run F (h c))) (sym (fsT++ t ν η e))
      (rd-ctx F (h c) qa (qh η c r)))

identity : Ctx
identity = record { run = λ a → a ; row = λ s h → refl }
```
