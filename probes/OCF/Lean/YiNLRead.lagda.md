# 任意 R 推导读回上抬层号
验收文件；编译定理 `readR` 无前提，对全部层号与 R 推导成立。
来源：零层调用 `YiLLCheck.read0`，路径调用 `YiRWPath.◃→⊑`，拼接统一调用 `YiNLCtx.rd-ctx`。
不要求 Leaf；不改树、折叠、合法性。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiNLRead where
open import Data.Nat using (ℕ)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
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
open import OCF.Align.Standard using (++-mono)
open import OCF.Lean.YiMENote using (cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiNLCtx

mutual
  low-from : ∀ ℓ p {η c} → GR.R (at ℓ p) η c → GR.Low ℓ p η (fromBr ℓ p c)
  low-from (nd s h) (inj₂ (d , q)) r = low-from⁼ (h d) q r
  low-from (nd (sΩ k) h) (inj₁ q) r = low-from⁼ k q r

  low-from⁼ : ∀ a q {η c} → GR.R (proj₁ (sl⁼ a q)) η c → GR.Low⁼ a q η (proj₂ (sl⁼ a q) c)
  low-from⁼ a (inj₁ _) r = r
  low-from⁼ a (inj₂ p) r = low-from a p r

mutual
  nu-to : ∀ ℓ p {ν} → GR.Nu ℓ p ν → GR.Rd (at ℓ p) ν
  nu-to (nd s h) (inj₂ (c , q)) r = nu-to⁼ (h c) q r
  nu-to (nd (sΩ k) h) (inj₁ q) r = nu-to⁼ k q r

  nu-to⁼ : ∀ a q {ν} → GR.Nu⁼ a q ν → GR.Rd (proj₁ (sl⁼ a q)) ν
  nu-to⁼ a (inj₁ _) r = r
  nu-to⁼ a (inj₂ p) r = nu-to a p r

module Node (s : Sh) (h : Ch s → L)
  (rec : ∀ c {ν y} → GR.R (h c) ν y → GR.Rd (↑ (h c) y) ν) where
  readN : ∀ {ν c} → GR.R (nd s h) ν c → GR.Rd (↑ (nd s h) c) ν
  readN H.mz = GR.c0 refl
  readN (H.m1 e r) = GR.ca (inj₂ (e , readN r))
  readN (H.mL e ds) = GR.cL e (λ n → readN (ds n))
  readN (H.mΩ {ν = κ} {p} {g} e q ds) = GR.ca (inj₂ (κ , e , nu-to (nd s h) p q ,
    λ η c r → readN (ds η (fromBr (nd s h) p c) (low-from (nd s h) p r))))
  readN (H.mU {x} {c} {y} r q) = rd-ctx (prefix (↑ (nd s h) x)) (↑ (h c) y) (readN r) (rec c q)
  readN (H.mw r d) = rd-mono identity (P.◃→⊑ (nd s h) d) (readN r)
  readN (H.mc le r) = GR.cc le (readN r)

readR : ∀ ℓ {ν c} → GR.R ℓ ν c → GR.Rd (↑ ℓ c) ν
readR zero = LL.read0
readR (nd s h) = Node.readN s h (λ c → readR (h c))
```
