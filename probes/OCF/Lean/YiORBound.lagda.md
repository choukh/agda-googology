# 原行审查：封闭关系仍排除原行的全 n 判据
验收文件（读记号）；编译否定：原行每个 n ≥ 2 均不过封闭判据；不涉及序数值上界。
来源：复用 `YiRCNeg` 的 Sm 与结构封闭引理、`YiLLLeafNeg.Fin` 的零与一界；不引用旧判据否定。
入口：`closed-bound`、`original-neg`、`no-all-original`；严格界由 `YiORCut` 处理两条封闭规则。
```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiORBound where
open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (proj₁)
open import Data.List using ([]; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps using (Ωt)
import OCF.Lean.YiKVRel as K
import OCF.Lean.YiHCRel as H
import OCF.Lean.YiLLLeafNeg as N
open import OCF.Lean.YiSUBound using (fsn-nat; suc-bound; nat-ψ)
open import OCF.Lean.YiCLFam using (M; nat; Mβ)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ)
open import OCF.Lean.YiRBCrit using (two; gᴹ)
open import OCF.Lean.YiRCNeg using (Sm; k0; kb; kΩ; ks; kl; dwn; Sm+ι; nz; lt1; belowB)
open import OCF.Lean.YiMHRel using (M̂; ĉ; l̂)
open import OCF.Lean.YiDCRel using (Ω≤; app≤)
open import OCF.Lean.YiORCrit using (CritAtˆ)
open import OCF.Lean.YiORCut
import OCF.Align.EboLeanDef as E
open E using (_<ᵀ_; _<ᴾ_; []<; hd<; tl<; lv<; ar<)
open import OCF.Align.EBO using (pred-suc)
open import OCF.Align.EboLeanBase using (_≤ᵀ_; ≤-trans′; ≤-<; <-≤; <ᵀ-irrefl)
open import OCF.Align.EboLeanView using (VΩ; ωs; ωr; ωl; ωp; vΩ; fΩ; fΩ-eq; fΩ-pos; vω; fω-eq)

pred-two : ∀ {S x} → Lt S x (suc (suc zero)) → (x ≡ zero) ⊎ (x ≡ suc zero)
pred-two ◃s = inj₂ refl
pred-two (◃t d e) with pred-two e
... | inj₁ refl = ⊥-elim (nz d)
... | inj₂ refl = inj₁ (lt1 d)

module Fin {S : Sg} {Low : (p : P S) → E.T → B S p → Set}
           {Chd : (c : C S) → E.T → D S c → Set} {Nu : P S → E.T → Set} where
  private
    Rel = K.Mᴰ S Low Chd Nu
  lift : ∀ {t x} → Rel t x → H.Mᴴ S Low Chd Nu t x
  lift K.mz = H.mz
  lift (K.m1 e r) = H.m1 e (lift r)
  lift (K.mL e h) = H.mL e (λ n → lift (h n))
  lift (K.mΩ e nu h) = H.mΩ e nu (λ η c r → lift (h η c r))
  lift (K.mU m ch) = H.mU (lift m) ch
  lift (K.mw m d) = H.mw (lift m) d

  zero-ref : ∀ {t} → Rel t zero → t ≡ []
  zero-ref m = N.Fin.zero-ref (lift m)
  one-ref : ∀ {t} → Rel t (suc zero) → t ≤ᵀ E.natT 1
  one-ref m = N.Fin.one-ref (lift m)
  two-ref : ∀ {t} → Rel t (suc (suc zero)) → t ≤ᵀ E.natT 2
  two-ref K.mz = inj₁ []<
  two-ref (K.m1 {t = t} e r) = subst (_≤ᵀ E.natT 2) (pred-suc t e) (suc-bound (one-ref r))
  two-ref (K.mL e h) = ⊥-elim (<ᵀ-irrefl (<-≤ (fsn-nat e 2) (two-ref (h 3))))
  two-ref (K.mw m d) with pred-two d
  ... | inj₁ refl = subst (_≤ᵀ E.natT 2) (sym (zero-ref m)) (inj₁ []<)
  ... | inj₂ refl = ≤-trans′ (one-ref m) (inj₁ (tl< []<))

head-one : ∀ {p xs} → (p ∷ xs) ≤ᵀ E.natT 2 → p ≡ E.𝟏
head-one (inj₁ (hd< (lv< ())))
head-one (inj₁ (hd< (ar< ())))
head-one (inj₁ (tl< p)) = refl
head-one (inj₂ refl) = refl

Ω-cap : ∀ {t κ} (v : VΩ t κ) → κ ≡ E.natT 1 → fΩ v (E.natT 1) ≤ᵀ E.natT 2 → t <ᵀ cap
Ω-cap (ωs v) q le with head-one le
... | refl = hd< (lv< []<)
Ω-cap (ωr {u = u} e) q le = subst (λ a → (E.ψ a [] ∷ []) <ᵀ cap)
  (sym (trans (sym (pred-suc u e)) (cong E.sucT q))) (hd< (ar< []<))
Ω-cap (ωl e v) q le = ⊥-elim (<ᵀ-irrefl (<-≤ (nat-leaf 2 (fΩ-pos v []<)) le))
Ω-cap (ωp {u = u} e pen v) q le = ⊥-elim (<ᵀ-irrefl (<-≤ (nat-ψ 2 u (fΩ-pos v []<)) le))

data Tiny : Tr two → Set where
  tz : Tiny zero
  t1 : ∀ {e} → Tiny (up zero tt (suc zero) e)
  t2 : ∀ {e} → Tiny (up zero tt (suc (suc zero)) e)

tiny-down : ∀ {x y} → two ⊢ x ◃ y → Tiny y → Tiny x
tiny-down d tz = ⊥-elim (nz d)
tiny-down d t1 with belowB d
... | refl = tz
tiny-down (◃u _ _ _ _) t2 = tz
tiny-down (◃c _ _ {e′ = e′} r) t2 with pred-two r
... | inj₁ refl = ⊥-elim (nz e′)
... | inj₂ refl = t1
tiny-down (◃t d e) t2 = tiny-down d (tiny-down e t2)

tiny-bound : ∀ {t x} → M 2 t x → Tiny x → t ≤ᵀ E.natT 2
tiny-bound K.mz sm = inj₁ []<
tiny-bound (K.mL e h) sm = ⊥-elim (<ᵀ-irrefl (<-≤ (fsn-nat e 2) (tiny-bound (h 3) sm)))
tiny-bound (K.mU m ch) t1 with Fin.zero-ref m
... | refl = ≤-trans′ (Fin.one-ref ch) (inj₁ (tl< []<))
tiny-bound (K.mU m ch) t2 with Fin.zero-ref m
... | refl = Fin.two-ref ch
tiny-bound (K.mw m d) sm = tiny-bound m (tiny-down d sm)

small-bound : ∀ {t x} → M 2 t x → Sm x → t <ᵀ cap
small-bound K.mz sm = []<
small-bound (K.m1 {t = t} e r) (ks sm) = subst (_<ᵀ cap) (pred-suc t e) (cap-suc (small-bound r sm))
small-bound (K.mL {t = t} e h) sm = ω-cap (vω t e) (λ n → subst (_<ᵀ cap) (fω-eq (vω t e) n) (small-bound (h n) sm))
small-bound (K.mΩ {t = t} e nu h) kΩ = Ω-cap (vΩ t e) nu
  (subst (_≤ᵀ E.natT 2) (fΩ-eq (vΩ t e) (E.natT 1)) (tiny-bound (h (E.natT 1) (suc zero) (K.m1 refl K.mz)) t2))
small-bound (K.mU m ch) kb with Fin.zero-ref m
... | refl = ≤-< (Fin.one-ref ch) (hd< (lv< []<))
small-bound (K.mw m d) sm = small-bound m (dwn sm d)

closed-bound : ∀ {t x} → M̂ (M 2) t x → Sm x → t <ᵀ cap
closed-bound (ĉ le m) sm = ≤-< le (small-bound m sm)
closed-bound (l̂ {s = t} e h) sm = ω-cap (vω t e) (λ n → subst (_<ᵀ cap) (fω-eq (vω t e) n) (closed-bound (h n) sm))

original-neg-2 : CritAtˆ gᴹ 2 → ⊥
original-neg-2 m = <ᵀ-irrefl (closed-bound m (Sm+ι kΩ _))

no-all-original : (∀ n → CritAtˆ gᴹ n) → ⊥
no-all-original all = original-neg-2 (all 2)

base-instance : M̂ (M 2) (Ωᴺ 2) (proj₁ (Ωt two))
base-instance = ĉ (inj₂ refl) (Mβ 1)

base-bound : Ωᴺ 2 <ᵀ cap
base-bound = closed-bound base-instance kΩ

original-shape : ∀ c → Sm (proj₁ (gᴹ c))
original-shape c = Sm+ι kΩ _

original-neg-all : ∀ k c → M̂ (M 2) (ψᴺ 2 (Ωᴺ (suc (suc k)))) (proj₁ (gᴹ c)) → ⊥
original-neg-all k c m = <ᵀ-irrefl (≤-<
  (app≤ 2 [] (Ω≤ {m = 2} {n = suc (suc k)} (s≤s (s≤s z≤n))))
  (closed-bound m (original-shape c)))

original-neg : ∀ k → CritAtˆ gᴹ (suc (suc k)) → ⊥
original-neg k = original-neg-all k (nat (suc (suc k)))
```
