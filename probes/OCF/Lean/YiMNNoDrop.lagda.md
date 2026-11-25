# 任意第 1 层关系的统一去 mc 不成立
验收文件，读记号；编译否定：no-remove-one 排除 ∀ {t x} → Rˣ one t x → M 1 t x。
反例是含非正规项的 mc 推导：其参照共尾度为 Ω，而承载树是由有限后继树组成的 ℕ 极限。
这不否定正规参照或 YiMNAssemble.DropActual；实际折叠输出上的去 mc 仍未走通。
Plain 的前驱保持与 no-cofΩ 在本件证明；自然数余尾及 ω 基本列复用 YiANFam、YiGLOmega。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiMNNoDrop where
open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)
import OCF.Lean.YiRWBlock as B
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiGLExact as R
import OCF.Lean.YiCLFam as F
import OCF.Align.EboLeanDef as E
open import OCF.Lean.YiANFam using (cof-nat; pred-nat)
open import OCF.Lean.YiCLPhi using (ωᵀ)
open import OCF.Lean.YiGLOmega using (fs-ω)
Plain : ∀ {S} → B.T S → Set
Plain B.zero = ⊤
Plain (B.suc x) = Plain x
Plain (B.lim f a) = ∀ n → Plain (f n)
Plain (B.Ω p g) = ⊥
Plain (B.up x c y e) = ⊥
plain-down : ∀ {S x y} → B.Lt S x y → Plain y → Plain x
plain-down B.◃s p = p
plain-down (B.◃l n) p = p n
plain-down B.◃w ()
plain-down (B.◃u _ _ _ _) ()
plain-down (B.◃c _ _ _) ()
plain-down (B.◃t d e) p = plain-down d (plain-down e p)
no-cofΩ : ∀ {S Low Chd Nu t x ν} → K.Mᴰ S Low Chd Nu t x → Plain x → E.cof t ≡ E.cΩ ν → ⊥
no-cofΩ K.mz p ()
no-cofΩ (K.m1 e m) p q with trans (sym e) q
... | ()
no-cofΩ (K.mL e h) p q with trans (sym e) q
... | ()
no-cofΩ (K.mΩ e n h) () q
no-cofΩ (K.mU m ch) () q
no-cofΩ (K.mw m e) p q = no-cofΩ m (plain-down e p) q
nat¹ : ℕ → B.Tr K.one
nat¹ zero = B.zero
nat¹ (suc n) = B.suc (nat¹ n)
nat-plain : ∀ n → Plain (nat¹ n)
nat-plain zero = tt
nat-plain (suc n) = nat-plain n
ω¹ : B.Tr K.one
ω¹ = B.lim nat¹ (λ n → B.◃s)
ω¹-plain : Plain ω¹
ω¹-plain = nat-plain
nat-rel : ∀ n → R.Rˣ K.one (E.natT n) (nat¹ n)
nat-rel zero = H.mz
nat-rel (suc n) = H.m1 (cof-nat n) (subst (λ t → R.Rˣ K.one t (nat¹ n)) (sym (pred-nat n)) (nat-rel n))
ω-rel : R.Rˣ K.one ωᵀ ω¹
ω-rel = H.mL refl (λ n → subst (λ t → R.Rˣ K.one t ω¹) (sym (fs-ω n)) (H.mw (nat-rel n) (B.◃l n)))
bad : E.T
bad = E.𝟏 ∷ E.ψ (E.natT 2) [] ∷ []
bad<ω : bad E.<ᵀ ωᵀ
bad<ω = E.hd< (E.ar< E.[]<)
bad-rel : R.Rˣ K.one bad ω¹
bad-rel = H.mc (inj₁ bad<ω) ω-rel
no-bad : F.M 1 bad ω¹ → ⊥
no-bad m = no-cofΩ m ω¹-plain refl
no-remove-one : (∀ {t x} → R.Rˣ K.one t x → F.M 1 t x) → ⊥
no-remove-one drop = no-bad (drop bad-rel)
```
