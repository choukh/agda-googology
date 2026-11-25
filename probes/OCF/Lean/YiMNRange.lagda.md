# 精确读回给原下界关系的项序上界
验收文件，读记号；编译定理：Ex⁰ ν x 与 H.M⁰ t x 推出 t ≤ᵀ ν，不要求 t 正规。
ex-down 给每个第一位置前驱的精确标签；ex-bound 的极限行复用 YiELLim.lim-gen。
这是 η 范围的接线工具，不消去 mc，不给第 1 层折叠的关系或新值下界。
入口：YiMNAssemble.eta-range；后继项序单调复用 YiELZero.suc-mono。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMNRange where
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (refl; subst; subst₂)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiELZero as Z
import OCF.Lean.YiGLFrame as L
import OCF.Align.EboLeanDef as E
open import OCF.Align.EboLeanBase using (_≤ᵀ_; ≤-trans′; <ᵀ-trans; dec≤)
open import OCF.Align.EBO using (pred-suc; <-sucT)
open import OCF.Lean.YiELLim using (lim-gen)
ex-down : ∀ {x y ν} → B._⊢_◃_ B.zero x y → Z.Ex⁰ ν y
  → Σ E.T λ μ → Z.Ex⁰ μ x × (μ E.<ᵀ ν)
ex-down {ν = ν} B.◃s (e , q) = E.pred ν , q , subst (E.pred ν E.<ᵀ_) (pred-suc ν e) (<-sucT (E.pred ν))
ex-down (B.◃l n) (e , nf , la , f) = proj₁ (f n) , proj₁ (proj₂ (f n)) , proj₂ (proj₂ (proj₂ (f n)))
ex-down (B.◃w {p = ()}) q
ex-down (B.◃u _ () _ _) q
ex-down (B.◃c _ () _) q
ex-down (B.◃t d e) q with ex-down e q
... | μ , qμ , le with ex-down d qμ
... | κ , qκ , ld = κ , qκ , <ᵀ-trans ld le
ex-bound : ∀ {t x ν} → H.M⁰ t x → Z.Ex⁰ ν x → t ≤ᵀ ν
ex-bound {ν = []} H.mz q = inj₂ refl
ex-bound {ν = _ ∷ _} H.mz q = inj₁ E.[]<
ex-bound {t = t} {ν = ν} (H.m1 e m) (en , q) = subst₂ _≤ᵀ_ (pred-suc t e) (pred-suc ν en) (Z.suc-mono (ex-bound m q))
ex-bound {t = t} {x = x} {ν = ν} (H.mL e h) q with dec≤ t ν
... | inj₁ le = le
... | inj₂ lt = ⊥-elim (lim-gen t e (Z.lbl-nf (B.↑ B.zero x) q) lt (λ n → ex-bound (h n) q))
ex-bound (H.mΩ {p = ()} _ _ _) q
ex-bound (H.mU {c = ()} _ _) q
ex-bound (H.mw m e) q with ex-down e q
... | μ , qμ , lt = ≤-trans′ (ex-bound m qμ) (inj₁ lt)
ex-bound (H.mc le m) q = ≤-trans′ le (ex-bound m q)
```
