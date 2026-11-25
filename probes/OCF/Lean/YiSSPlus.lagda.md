# ω+1 层的比较表折叠保持
验收文件；表任意，关系和底的前提引用 `YiHCPlus.Plus`。
来源：`YiHCPlus.Fold₊` 搬到 `YiTBRow.ψ`；有限孩子用 `YiLTLim`，自身保持用 `YiSSOmega`。
不改树、折叠、合法性；当前路径经指定有限孩子或经 ω 孩子。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiSSPlus where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; node⁺)
open import OCF.Lean.YiTBRow hiding (nat; fn; h₁)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiRBCrit using (two; sh; gˢ; wˢ)
open import OCF.Lean.YiRLCrit using (ℓˢ; oˢ)
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; ++[])
open import OCF.Lean.YiKCStep using (⊴-trans)
open import OCF.Lean.YiHCRel using (Mᴴ; mz; m1; mL; mΩ; mU; mw; mc)
import OCF.Align.EboLeanDef as E
open E using (cof; cΩ; fsT; γT; natT; sucT; cmpᵀ; gt)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ; cofK; fsTK; cofG; fsnG)
open import OCF.Lean.YiDCRel using (app≤)
open import OCF.Lean.YiCLFam using (fn; levP)
open import OCF.Lean.YiCLLow using (Sb; s0; pth; penJ)
open import OCF.Lean.YiCLPhi using (ωᵀ)
open import OCF.Lean.YiCLCrit using (ωᶜ)
open import OCF.Lean.YiHCFam using (M; LwP; mwN; mcJ; zlJ; nextJ; cumJ; mLJ; mΩP; ΩJ)
open import OCF.Lean.YiLRBridge using (Sᶜ; NwB; τ; τ₂; comp)
open import OCF.Lean.YiHCBridge using (MB; LwB; kcaseB; kcaseB₂; feedB)
open import OCF.Lean.YiLRLow using (cWC; Gᶜ; eᶜ; Rᶜ; canRᶜ)
open import OCF.Lean.YiLTLim using (module LimT)
import OCF.Lean.YiHCPlus as Old
open Old using (gtN; gtS)
open import OCF.Lean.YiSSOmega using (module Omega)
open import OCF.Lean.YiHCOmega using (ψᵘ; appᵘ; gtω-nat; gtω-self; penB; module Tω)

module Plus (G : ℕ → L) (d : ℕ → ℕ) (eG : ∀ n → G n ≡ fn (d n)) (R : (n : ℕ) → G n ≤ G (suc n))
            (canR : ∀ n → Σ (Sb (d (suc n)) (d n)) λ s → τ₂ (eG n) (eG (suc n)) (R n) ≡ pth s)
            (dk : ∀ k → k ≤ⁿ d k) (oc : (k : ℕ) → Ok (G k)) where
  open LimT G d eG R canR
  open Omega G d eG R canR using (ψω; leafω; module Gω; module Self)

  module P = Old.Plus G d eG R canR dk oc
  open P using (ℓ₊; o₊; Low₊; Nu₊; M₊; Mβ₊; GB₊; mkGB₊; fΩ; fM; ωΩ; ωM; gb₊₀) public

  module Fold₊ (r : Rb ℓ₊) (B : Base ℓ₊) (t₀ : E.T) (gb : GB₊ B t₀) where

    Ff : ∀ {n j} → fn j ≤ G n → Tr⁺ (fn j) → Tr ℓ₊ → Tr⁺ (fn j)
    Ff {n} {j} v β x = ψ ℓ₊ o₊ r B (fn j) (inc tt (inc n v)) β x

    Fw : Tr⁺ Lω → Tr ℓ₊ → Tr⁺ Lω
    Fw β x = ψ ℓ₊ o₊ r B Lω (inc tt self) β x

    cb₊ : Tr ℓ₊ → Base Lω
    cb₊ x i u = ψ ℓ₊ o₊ r B i (inc tt u) (B i (inc tt u)) x

    sω : (Tr Lω → Tr ℓ₊) → Tr Lω → Tr Lω
    sω g z = proj₁ (Fw (B Lω (inc tt self)) (g z))

    sf : (m : ℕ) (t : Pos⁼ (G m)) → (Br⁼ (G m) t → Tr ℓ₊) → Br⁼ (G m) t → Br⁼ (G m) t
    sf m t g z = proj₂ (sl⁼ (G m) t)
      (proj₁ (ψ ℓ₊ o₊ r B (proj₁ (sl⁼ (G m) t)) (inc tt (inc m (posW⁼ (G m) t)))
                (B (proj₁ (sl⁼ (G m) t)) (inc tt (inc m (posW⁼ (G m) t)))) (g z)))

    mutual
      LFf : ∀ {n j} (v : fn j ≤ G n) (s : Sb (d n) j) → τ (eG n) v ≡ pth s
          → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
          → ∀ {a x} → M₊ a x → M j (ψᴺ j (t₀ ++ a)) (proj₁ (Ff v β x))
      LFf {n} {j} v s q β hβ (mz {x = x}) =
        ++[] (λ z → M j (ψᴺ j z) (proj₁ (Ff v β x))) t₀
          (zlJ j (λ y → proj₁ (Ff v β y)) (mono ℓ₊ o₊ r B (fn j) (inc tt (inc n v)) β) hβ x)
      LFf {n} {j} v s q β hβ (m1 {t = a} {x = x} e h) =
        nextJ j (Ff v β x) (cofψ1 (natT j) (t₀ ++ a) (cof++1 t₀ a e))
          (λ k → trans (fsnψ1 (natT j) (t₀ ++ a) k (cof++1 t₀ a e)) (cong (λ z → replicate k (E.ψ (natT j) z)) (pred++ t₀ a e)))
          (LFf v s q β hβ h)
      LFf {n} {j} v s q β hβ (mL {t = a} {x = x} e h) =
        mLJ j (cofψω (natT j) (t₀ ++ a) (cof++ω t₀ a e))
          (λ k → subst (λ z → M j z (proj₁ (Ff v β x)))
            (sym (trans (fsnψω (natT j) (t₀ ++ a) k (cof++ω t₀ a e)) (cong (ψᴺ j) (fsn++ t₀ a k e))))
            (LFf v s q β hβ (h k)))
      LFf v s q β hβ (mΩ {p = inj₁ ()} _ _ _)
      LFf v s q β hβ (mΩ {p = inj₂ (tt , inj₁ tt)} e nu h) = LFf-ω v s q β hβ e nu h
      LFf v s q β hβ (mΩ {p = inj₂ (tt , inj₂ (inj₁ ()))} _ _ _)
      LFf v s q β hβ (mΩ {p = inj₂ (tt , inj₂ (inj₂ (m , t)))} e nu h) = LFf-Ω v s q β hβ m t e nu h
      LFf {n} {j} v s q β hβ (mU {t = a} {s = s₁} {x = x} {y = y} h ch) =
        subst (λ z → M j (ψᴺ j z) (proj₁ (ψ Lω (R , oc) (proj₂ r tt) (cb₊ x) (fn j) (inc n v) (Ff v β x) y)))
          (++-assoc t₀ a s₁)
          (Fold.LFω oc (proj₂ r tt) (cb₊ x) (t₀ ++ a) (gbL h) v s q (Ff v β x) (LFf v s q β hβ h) ch)
      LFf {n} {j} v s q β hβ (mw h dd) = mwN j (LFf v s q β hβ h) (mono ℓ₊ o₊ r B (fn j) (inc tt (inc n v)) β dd)
      LFf {n} {j} v s q β hβ (mc le h) = mcJ j (app≤ j t₀ le) (LFf v s q β hβ h)

      gbL : ∀ {a x} → M₊ a x → GBω (cb₊ x) (t₀ ++ a)
      gbL {a} {x} h =
        mkGBω (λ m {i} si u qu → ⊴-trans (fΩ gb m si u qu)
                 (ψ-⊵ ℓ₊ o₊ r B (fn i) (inc tt (inc m u)) (B (fn i) (inc tt (inc m u))) x))
              (λ m {i} si u qu → LFf u si qu (B (fn i) (inc tt (inc m u))) (fM gb m si u qu) h)

      LFf-ω : ∀ {n j} (v : fn j ≤ G n) (s : Sb (d n) j) → τ (eG n) v ≡ pth s
            → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
            → ∀ {a ν} {g : Tr Lω → Tr ℓ₊} → cof a ≡ cΩ ν → ν ≡ ωᵀ → (∀ η c → Mω η c → M₊ (fsT a η) (g c))
            → M j (ψᴺ j (t₀ ++ a)) (proj₁ (limc⁺ (λ k → Ff v β (g (iter (sω g) zero k)))))
      LFf-ω {n} {j} v s q β hβ {a} {ν} {g} e nu h =
        mLJ j (cofG (natT j) (t₀ ++ a) (gtN j nu) (cof++Ω t₀ a e))
          (λ k → subst (λ z → M j z (proj₁ (limc⁺ (λ k′ → Ff v β (g (iter (sω g) zero k′))))))
            (sym (trans (fsnG (natT j) (t₀ ++ a) k (gtN j nu) (cof++Ω t₀ a e)) (cong (ψᴺ j) (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))))
            (cumJ j (λ k′ → Ff v β (g (iter (sω g) zero k′))) (suc k)
              (LFf v s q β hβ (h (γT (t₀ ++ a) ν k) (iter (sω g) zero (suc k)) (chainω e nu h k)))))

      chainω : ∀ {a ν} {g : Tr Lω → Tr ℓ₊} → cof a ≡ cΩ ν → ν ≡ ωᵀ → (∀ η c → Mω η c → M₊ (fsT a η) (g c))
             → ∀ k → Mω (γT (t₀ ++ a) ν k) (iter (sω g) zero (suc k))
      chainω {g = g} e refl h zero =
        Gω.m⊴ (leafω dk) (⊴-trans (ωΩ gb) (ψ-⊵ ℓ₊ o₊ r B Lω (inc tt self) (B Lω (inc tt self)) (g zero)))
      chainω {a} {g = g} e refl h (suc k) =
        subst (λ z → Mω (ψω z) (sω g (iter (sω g) zero (suc k))))
          (sym (fsT++ t₀ a (γT (t₀ ++ a) ωᵀ k) e))
          (LFw (B Lω (inc tt self)) (ωM gb) (h (γT (t₀ ++ a) ωᵀ k) (iter (sω g) zero (suc k)) (chainω e refl h k)))

      LFf-Ω : ∀ {n j} (v : fn j ≤ G n) (s : Sb (d n) j) → τ (eG n) v ≡ pth s
            → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
            → (m : ℕ) (t : Pos⁼ (G m)) → ∀ {a ν} {g : Br⁼ (G m) t → Tr ℓ₊}
            → cof a ≡ cΩ ν → NwB (G m) (eG m) t ν → (∀ η c → LwB (G m) (eG m) t η c → M₊ (fsT a η) (g c))
            → M j (ψᴺ j (t₀ ++ a)) (proj₁ (Ff v β (Ω (inj₂ (tt , inj₂ (inj₂ (m , t)))) g)))
      LFf-Ω {n} {j} v s q β hβ m t {a} {ν} {g} e nu h =
        cWC (λ K → M j (ψᴺ j (t₀ ++ a)) (proj₁ (node⁺ K (λ z → Ff v β (g z)) (sf m t g)))) (way G R m n) (wc m n)
          (λ u c → kcaseB₂ (G m) (G n) (eG m) (eG n) (oc n) u (proj₁ c) (proj₂ c) t v s q nu
                     (λ K → M j (ψᴺ j (t₀ ++ a)) (proj₁ (node⁺ K (λ z → Ff v β (g z)) (sf m t g))))
                     (λ gtq → LFf-lim v s q β hβ m t e nu h gtq)
                     (λ qq cv eq nq lw → LFf-keep v s q β hβ m t e nu h qq cv eq nq lw))
          (λ u c → kcaseB (G m) (eG m) (oc m) t (v ∙ u) (comp (proj₁ c) s) (∙q q u c) nu
                     (λ K → M j (ψᴺ j (t₀ ++ a)) (proj₁ (node⁺ K (λ z → Ff v β (g z)) (sf m t g))))
                     (λ gtq → LFf-lim v s q β hβ m t e nu h gtq)
                     (λ qq cv eq nq lw → LFf-keep v s q β hβ m t e nu h qq cv eq nq lw))

      LFf-lim : ∀ {n j} (v : fn j ≤ G n) (s : Sb (d n) j) → τ (eG n) v ≡ pth s
              → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
              → (m : ℕ) (t : Pos⁼ (G m)) → ∀ {a ν} {g : Br⁼ (G m) t → Tr ℓ₊}
              → cof a ≡ cΩ ν → NwB (G m) (eG m) t ν → (∀ η c → LwB (G m) (eG m) t η c → M₊ (fsT a η) (g c))
              → cmpᵀ (sucT ν) (natT j) ≡ gt
              → M j (ψᴺ j (t₀ ++ a)) (proj₁ (limc⁺ (λ k → Ff v β (g (iter (sf m t g) (bz⁼ (G m) t) k)))))
      LFf-lim {n} {j} v s q β hβ m t {a} {ν} {g} e nu h gtq =
        mLJ j (cofG (natT j) (t₀ ++ a) gtq (cof++Ω t₀ a e))
          (λ k → subst (λ z → M j z (proj₁ (limc⁺ (λ k′ → Ff v β (g (iter (sf m t g) (bz⁼ (G m) t) k′))))))
            (sym (trans (fsnG (natT j) (t₀ ++ a) k gtq (cof++Ω t₀ a e)) (cong (ψᴺ j) (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))))
            (cumJ j (λ k′ → Ff v β (g (iter (sf m t g) (bz⁼ (G m) t) k′))) (suc k)
              (LFf v s q β hβ (h (γT (t₀ ++ a) ν k) (iter (sf m t g) (bz⁼ (G m) t) (suc k)) (chainf m t e nu h k)))))

      LFf-keep : ∀ {n j} (v : fn j ≤ G n) (s : Sb (d n) j) → τ (eG n) v ≡ pth s
               → (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
               → (m : ℕ) (t : Pos⁼ (G m)) → ∀ {a ν} {g : Br⁼ (G m) t → Tr ℓ₊}
               → cof a ≡ cΩ ν → NwB (G m) (eG m) t ν → (∀ η c → LwB (G m) (eG m) t η c → M₊ (fsT a η) (g c))
               → (qq : Pos (fn j)) (cv : Br (fn j) qq → Br⁼ (G m) t) (eq : cv (fromBr (fn j) qq zero) ≡ bz⁼ (G m) t)
               → ν ≡ natT (levP j qq) → (∀ η c → LwP j qq η c → LwB (G m) (eG m) t η (cv c))
               → M j (ψᴺ j (t₀ ++ a)) (Ω qq (λ z → proj₁ (Ff v β (g (cv z)))))
      LFf-keep {n} {j} v s q β hβ m t {a} {ν} {g} e nu h qq cv eq nq lw =
        mΩP j (cofK (natT j) (t₀ ++ a) (penJ j qq nq) (cof++Ω t₀ a e)) nq
          (λ η c l → subst (λ z → M j z (proj₁ (Ff v β (g (cv c)))))
            (sym (trans (fsTK (natT j) (t₀ ++ a) η (penJ j qq nq) (cof++Ω t₀ a e)) (cong (ψᴺ j) (fsT++ t₀ a η e))))
            (LFf v s q β hβ (h η (cv c) (lw η c l))))

      chainf : ∀ m (t : Pos⁼ (G m)) → ∀ {a ν} {g : Br⁼ (G m) t → Tr ℓ₊}
             → cof a ≡ cΩ ν → NwB (G m) (eG m) t ν → (∀ η c → LwB (G m) (eG m) t η c → M₊ (fsT a η) (g c))
             → ∀ k → LwB (G m) (eG m) t (γT (t₀ ++ a) ν k) (iter (sf m t g) (bz⁼ (G m) t) (suc k))
      chainf m t {a} {ν} {g} e nu h zero =
        feedB (G m) (eG m) t nu (γT (t₀ ++ a) ν zero)
          (λ k w → proj₁ (ψ ℓ₊ o₊ r B k (inc tt (inc m w)) (B k (inc tt (inc m w))) (g (bz⁼ (G m) t))))
          (λ {i} si u qu eqν → subst (λ μ → M i (E.Ωt μ) (proj₁ (ψ ℓ₊ o₊ r B (fn i) (inc tt (inc m u)) (B (fn i) (inc tt (inc m u))) (g (bz⁼ (G m) t)))))
             (sym eqν)
             (ΩJ i (ψ ℓ₊ o₊ r B (fn i) (inc tt (inc m u)) (B (fn i) (inc tt (inc m u))) (g (bz⁼ (G m) t)))
                (⊴-trans (fΩ gb m si u qu) (ψ-⊵ ℓ₊ o₊ r B (fn i) (inc tt (inc m u)) (B (fn i) (inc tt (inc m u))) (g (bz⁼ (G m) t))))))
      chainf m t {a} {ν} {g} e nu h (suc k) =
        feedB (G m) (eG m) t nu (γT (t₀ ++ a) ν (suc k))
          (λ k′ w → proj₁ (ψ ℓ₊ o₊ r B k′ (inc tt (inc m w)) (B k′ (inc tt (inc m w))) (g (iter (sf m t g) (bz⁼ (G m) t) (suc k)))))
          (λ {i} si u qu eqν →
             subst (λ μ → M i (E.ψ μ (fsT (t₀ ++ a) (γT (t₀ ++ a) ν k)) ∷ [])
                            (proj₁ (ψ ℓ₊ o₊ r B (fn i) (inc tt (inc m u)) (B (fn i) (inc tt (inc m u))) (g (iter (sf m t g) (bz⁼ (G m) t) (suc k))))))
               (sym eqν)
               (subst (λ z → M i (ψᴺ i z) (proj₁ (ψ ℓ₊ o₊ r B (fn i) (inc tt (inc m u)) (B (fn i) (inc tt (inc m u))) (g (iter (sf m t g) (bz⁼ (G m) t) (suc k))))))
                 (sym (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))
                 (LFf u si qu (B (fn i) (inc tt (inc m u))) (fM gb m si u qu)
                   (h (γT (t₀ ++ a) ν k) (iter (sf m t g) (bz⁼ (G m) t) (suc k)) (chainf m t e nu h k)))))

      LFw : (β : Tr⁺ Lω) → Mω (ψω t₀) (proj₁ β)
          → ∀ {a x} → M₊ a x → Mω (ψω (t₀ ++ a)) (proj₁ (Fw β x))
      LFw β hβ (mz {x = x}) =
        ++[] (λ z → Mω (ψω z) (proj₁ (Fw β x))) t₀
          (Gω.m-zl (λ y → proj₁ (Fw β y)) (mono ℓ₊ o₊ r B Lω (inc tt self) β) hβ x)
      LFw β hβ (m1 {t = a} {x = x} e h) =
        Gω.m-next (Fw β x) (cofψ1 ωᵀ (t₀ ++ a) (cof++1 t₀ a e))
          (λ k → trans (fsnψ1 ωᵀ (t₀ ++ a) k (cof++1 t₀ a e)) (cong (λ z → replicate k (E.ψ ωᵀ z)) (pred++ t₀ a e)))
          (LFw β hβ h)
      LFw β hβ (mL {t = a} {x = x} e h) =
        mL (cofψω ωᵀ (t₀ ++ a) (cof++ω t₀ a e))
          (λ k → subst (λ z → Mω z (proj₁ (Fw β x)))
            (sym (trans (fsnψω ωᵀ (t₀ ++ a) k (cof++ω t₀ a e)) (cong ψω (fsn++ t₀ a k e))))
            (LFw β hβ (h k)))
      LFw β hβ (mΩ {p = inj₁ ()} _ _ _)
      LFw β hβ (mΩ {t = a} {ν = ν} {p = inj₂ (tt , inj₁ tt)} {g = g} e nu h) =
        mL (cofG ωᵀ (t₀ ++ a) (gtS nu) (cof++Ω t₀ a e))
          (λ k → subst (λ z → Mω z (proj₁ (limc⁺ (λ k′ → Fw β (g (iter (sω g) zero k′))))))
            (sym (trans (fsnG ωᵀ (t₀ ++ a) k (gtS nu) (cof++Ω t₀ a e)) (cong ψω (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))))
            (Gω.m-cum (λ k′ → Fw β (g (iter (sω g) zero k′))) (suc k)
              (LFw β hβ (h (γT (t₀ ++ a) ν k) (iter (sω g) zero (suc k)) (chainω e nu h k)))))
      LFw β hβ (mΩ {p = inj₂ (tt , inj₂ (inj₁ ()))} _ _ _)
      LFw β hβ (mΩ {t = a} {p = inj₂ (tt , inj₂ (inj₂ (m , t)))} {g = g} e nu h) =
        mΩ (cofK ωᵀ (t₀ ++ a) (penB (G m) (eG m) t nu) (cof++Ω t₀ a e)) nu
          (λ η c l → subst (λ z → Mω z (proj₁ (Fw β (g c))))
            (sym (trans (fsTK ωᵀ (t₀ ++ a) η (penB (G m) (eG m) t nu) (cof++Ω t₀ a e)) (cong ψω (fsT++ t₀ a η e))))
            (LFw β hβ (h η c l)))
      LFw β hβ (mU {t = a} {s = s₁} {x = x} {y = y} h ch) =
        subst (λ z → Mω (ψω z) (Self.F R oc (proj₂ r tt) (cb₊ x) (Fw β x) y)) (++-assoc t₀ a s₁)
          (Self.PFω R oc (proj₂ r tt) (cb₊ x) (Fw β x) (LFw β hβ h) ch)
      LFw β hβ (mw h dd) = mw (LFw β hβ h) (mono ℓ₊ o₊ r B Lω (inc tt self) β dd)
      LFw β hβ (mc le h) = mc (appᵘ ωᵀ t₀ le) (LFw β hβ h)
```
