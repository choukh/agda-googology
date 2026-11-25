# 有限读回孩子的极限层沿任意路径下折
验收文件；编译定理。Generic 的实际相邻路径、子证据、表以及折到有限层的路径均任意。
LFω/LFu 保持既有 Mω；GBω 是同一既有底条件。没有要求实际路径读成 Sb。
来源：YiLTLim 的 Mω 推导归纳与链，有限保持改接 YiPJAll，槽位改接 YiPJAcross。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiPJLim where
open import Data.Nat using (ℕ; zero; suc; z≤n)
open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong; cong₂)

open import OCF.Lean.YiRWBlock
open import OCF.Lean.YiRWOps
open import OCF.Lean.YiRWPath
open import OCF.Lean.YiRWFold using (Base; B₀; Keep; kp; node⁺)
open import OCF.Lean.YiTBRow hiding (nat; fn; h₁)
open import OCF.Lean.YiTBFam using (ψ-⊵)
open import OCF.Lean.YiRBFam using (Pt; pt)
open import OCF.Lean.YiKVRel using (_⊴_; ⊴r; +⊴; ++[])
open import OCF.Lean.YiHCRel using (Mᴴ; mz; m1; mL; mΩ; mU; mw; mc; M⁰)
open import OCF.Lean.YiKCStep using (⊴-trans)
import OCF.Align.EboLeanDef as E
open E using (cof; cΩ; fsT; γT; natT; sucT; cmpᵀ; gt)
open import OCF.Lean.YiMENote using (cofψ1; fsnψ1; cofψω; fsnψω; cof++1; cof++ω; pred++; fsn++)
open import OCF.Lean.YiMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiANFam using (ψᴺ; Ωᴺ; cofK; fsTK; cofG; fsnG)
open import OCF.Lean.YiDCRel using (app≤)
open import OCF.Lean.YiCLFam using (nat; fn; levP)
open import OCF.Lean.YiCLLow using (Sb; s0; ss; pth; penJ; gtJ)
open import OCF.Lean.YiHCFam using (M; LwP; mwN; m⊴N; mcJ; Mβ; zlJ; nextJ; cumJ; mLJ; mΩP; ΩJ)
open import OCF.Lean.YiLRBridge using (Sᶜ; NwB; τ; τ₂; τ∙; τ₂∙; τ₂self; τ₂S; τ₂SS; comp; ∙pth)
open import OCF.Lean.YiHCBridge hiding (LFA; LFAB)
open import OCF.Lean.YiLRLow using (WC; wf; wb; wayC; cWC)
open import OCF.Lean.YiHCLim using (module Lim)
open import OCF.Lean.YiLTFold using (LFAB; LFPB)


open import OCF.Lean.YiLTLim using (nodeZ; gt0B)
import OCF.Lean.YiPJAll as P
open import OCF.Lean.YiPJEmb using (liftM)
open import OCF.Lean.YiPJAcross using (caseK; acrossK)
open import OCF.Lean.YiPJRef using (module Reference)
open import OCF.Lean.YiPJCase using (levB)

nuRead : ∀ N ℓ (e : ℓ ≡ fn N) (t : Pos⁼ ℓ) {ν} → NwB ℓ e t ν → ν ≡ natT (levB N ℓ e t)
nuRead N _ refl t nu = nu

module Generic (G : ℕ → L) (d : ℕ → ℕ) (eG : ∀ n → G n ≡ fn (d n))
  (R₀ : ∀ n → G n ≤ G (suc n))
  (canR₀ : ∀ n → Σ (Sb (d (suc n)) (d n)) λ s → τ₂ (eG n) (eG (suc n)) (R₀ n) ≡ pth s)
  (R : ∀ n → G n ≤ G (suc n)) where
  open Lim G d eG R₀ canR₀ hiding (module Fold)
  module Fold (oc : (k : ℕ) → Ok (G k)) (r : Rb Lω) (B : Base Lω) (t₀ : E.T) (gb : GBω B t₀) where
    o : Ok Lω
    o = R , oc

    F : ∀ {j} → fn j ≤ Lω → Tr⁺ (fn j) → Tr Lω → Tr⁺ (fn j)
    F {j} w β x = ψ Lω o r B (fn j) w β x

    cb : (m : ℕ) → Tr Lω → Base (G m)
    cb m x i u = ψ Lω o r B i (inc m u) (B i (inc m u)) x

    sf : (m : ℕ) (t : Pos⁼ (G m)) → (Br⁼ (G m) t → Tr Lω) → Br⁼ (G m) t → Br⁼ (G m) t
    sf m t g z = proj₂ (sl⁼ (G m) t)
      (proj₁ (ψ Lω o r B (proj₁ (sl⁼ (G m) t)) (inc m (posW⁼ (G m) t)) (B (proj₁ (sl⁼ (G m) t)) (inc m (posW⁼ (G m) t))) (g z)))

    mutual
      LFω : ∀ {n j} (v : fn j ≤ G n) (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
          → ∀ {a x} → Mω a x → M j (ψᴺ j (t₀ ++ a)) (proj₁ (F (inc n v) β x))
      LFω {n} {j} v β hβ (mz {x = x}) =
        ++[] (λ z → M j (ψᴺ j z) (proj₁ (F (inc n v) β x))) t₀
          (zlJ j (λ y → proj₁ (F (inc n v) β y)) (mono Lω o r B (fn j) (inc n v) β) hβ x)
      LFω {n} {j} v β hβ (m1 {t = a} {x = x} e h) =
        nextJ j (F (inc n v) β x) (cofψ1 (natT j) (t₀ ++ a) (cof++1 t₀ a e))
          (λ k → trans (fsnψ1 (natT j) (t₀ ++ a) k (cof++1 t₀ a e)) (cong (λ z → replicate k (E.ψ (natT j) z)) (pred++ t₀ a e)))
          (LFω v β hβ h)
      LFω {n} {j} v β hβ (mL {t = a} {x = x} e h) =
        mLJ j (cofψω (natT j) (t₀ ++ a) (cof++ω t₀ a e))
          (λ k → subst (λ z → M j z (proj₁ (F (inc n v) β x)))
            (sym (trans (fsnψω (natT j) (t₀ ++ a) k (cof++ω t₀ a e)) (cong (ψᴺ j) (fsn++ t₀ a k e))))
            (LFω v β hβ (h k)))
      LFω v β hβ (mΩ {p = inj₁ ()} _ _ _)
      LFω v β hβ (mΩ {p = inj₂ (m , t)} e nu h) = LFΩ v β hβ m t e nu h
      LFω {n} {j} v β hβ (mU {t = a} {s = s₁} {x = x} {c = m} {y = y} {e = ey} h ch) =
        subst (λ z → M j (ψᴺ j z) (proj₁ (F (inc n v) β (up x m y ey)))) (++-assoc t₀ a s₁)
          (LFU v β hβ m y ey h ch (way G R m n))
      LFω {n} {j} v β hβ (mw h dd) = mwN j (LFω v β hβ h) (mono Lω o r B (fn j) (inc n v) β dd)
      LFω {n} {j} v β hβ (mc le h) = mcJ j (app≤ j t₀ le) (LFω v β hβ h)

      LFU : ∀ {n j} (v : fn j ≤ G n) (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
          → ∀ {a s₁ x} (m : ℕ) (y : Tr (G m)) (ey : G m ⊢ zero ◃ y) → Mω a x → MB (G m) (eG m) s₁ y
          → (W : (G m ≤ G n) ⊎ (G n ≤ G m))
          → M j (ψᴺ j ((t₀ ++ a) ++ s₁)) (proj₁ (cW W
              (λ u → ψ (G n) (oc n) (proj₂ r n) (cb n x) (fn j) v (F (inc n v) β x) (proj₁ (emb (G n) (oc n) u (y , ey))))
              (λ u → ψ (G m) (oc m) (proj₂ r m) (cb m x) (fn j) (v ∙ u) (F (inc n v) β x) y)))
      LFU {n} {j} v β hβ {a} {s₁} {x} m y ey h ch W =
        cW-ind (λ Z → M j (ψᴺ j ((t₀ ++ a) ++ s₁)) (proj₁ Z)) W
          (λ u → P.all (d n) (G n) (eG n) j (fn j) refl v (oc n) (proj₂ r n) (cb n x) (t₀ ++ a) (gbL n h)
              (F (inc n v) β x) (LFω v β hβ h)
              (liftM (d n) (G n) (eG n) (d m) (G m) (eG m) (oc n) u y ey ch))
          (λ u → P.all (d m) (G m) (eG m) j (fn j) refl (v ∙ u) (oc m) (proj₂ r m) (cb m x) (t₀ ++ a) (gbL m h)
              (F (inc n v) β x) (LFω v β hβ h) ch)

      gbL : ∀ m {a x} → Mω a x → GBB (G m) (eG m) (cb m x) (t₀ ++ a)
      gbL m {a} {x} h =
        mkGBB (G m) (eG m) (cb m x) (t₀ ++ a)
          (λ {i} si u qu → ⊴-trans (wΩ gb m si u qu) (ψ-⊵ Lω o r B (fn i) (inc m u) (B (fn i) (inc m u)) x)
                         , LFω u (B (fn i) (inc m u)) (wM gb m si u qu) h)

      LFΩ : ∀ {n j} (v : fn j ≤ G n) (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
          → (m : ℕ) (t : Pos⁼ (G m)) → ∀ {a ν} {g : Br⁼ (G m) t → Tr Lω}
          → cof a ≡ cΩ ν → NwB (G m) (eG m) t ν → (∀ η c → LwB (G m) (eG m) t η c → Mω (fsT a η) (g c))
          → M j (ψᴺ j (t₀ ++ a)) (proj₁ (F (inc n v) β (Ω (inj₂ (m , t)) g)))
      LFΩ {n} {j} v β hβ m t {a} {ν} {g} e nu h =
        cW-ind (λ K → M j (ψᴺ j (t₀ ++ a)) (proj₁ (node⁺ K (λ z → F (inc n v) β (g z)) (sf m t g)))) (way G R m n)
          (λ u → acrossK (d m) (G m) (eG m) (d n) (G n) (eG n) j (oc n) u t v (nuRead (d m) (G m) (eG m) t nu)
                     (λ K → M j (ψᴺ j (t₀ ++ a)) (proj₁ (node⁺ K (λ z → F (inc n v) β (g z)) (sf m t g))))
                     (λ gtq → LFΩ-lim v β hβ m t e nu h gtq)
                     (λ qq cv eq nq lw → LFΩ-keep v β hβ m t e nu h qq cv eq nq lw))
          (λ u → caseK (d m) (G m) (eG m) j (oc m) t (v ∙ u) (nuRead (d m) (G m) (eG m) t nu)
                     (λ K → M j (ψᴺ j (t₀ ++ a)) (proj₁ (node⁺ K (λ z → F (inc n v) β (g z)) (sf m t g))))
                     (λ gtq → LFΩ-lim v β hβ m t e nu h gtq)
                     (λ qq cv eq nq lw → LFΩ-keep v β hβ m t e nu h qq cv eq nq lw))

      LFΩ-lim : ∀ {n j} (v : fn j ≤ G n) (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
              → (m : ℕ) (t : Pos⁼ (G m)) → ∀ {a ν} {g : Br⁼ (G m) t → Tr Lω}
              → cof a ≡ cΩ ν → NwB (G m) (eG m) t ν → (∀ η c → LwB (G m) (eG m) t η c → Mω (fsT a η) (g c))
              → cmpᵀ (sucT ν) (natT j) ≡ gt
              → M j (ψᴺ j (t₀ ++ a)) (proj₁ (limc⁺ (λ k → F (inc n v) β (g (iter (sf m t g) (bz⁼ (G m) t) k)))))
      LFΩ-lim {n} {j} v β hβ m t {a} {ν} {g} e nu h gtq =
        mLJ j (cofG (natT j) (t₀ ++ a) gtq (cof++Ω t₀ a e))
          (λ k → subst (λ z → M j z (proj₁ (limc⁺ (λ k′ → F (inc n v) β (g (iter (sf m t g) (bz⁼ (G m) t) k′))))))
            (sym (trans (fsnG (natT j) (t₀ ++ a) k gtq (cof++Ω t₀ a e)) (cong (ψᴺ j) (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))))
            (cumJ j (λ k′ → F (inc n v) β (g (iter (sf m t g) (bz⁼ (G m) t) k′))) (suc k)
              (LFω v β hβ (h (γT (t₀ ++ a) ν k) (iter (sf m t g) (bz⁼ (G m) t) (suc k)) (chain m t e nu h k)))))

      LFΩ-keep : ∀ {n j} (v : fn j ≤ G n) (β : Tr⁺ (fn j)) → M j (ψᴺ j t₀) (proj₁ β)
               → (m : ℕ) (t : Pos⁼ (G m)) → ∀ {a ν} {g : Br⁼ (G m) t → Tr Lω}
               → cof a ≡ cΩ ν → NwB (G m) (eG m) t ν → (∀ η c → LwB (G m) (eG m) t η c → Mω (fsT a η) (g c))
               → (qq : Pos (fn j)) (cv : Br (fn j) qq → Br⁼ (G m) t) (eq : cv (fromBr (fn j) qq zero) ≡ bz⁼ (G m) t)
               → ν ≡ natT (levP j qq) → (∀ η c → LwP j qq η c → LwB (G m) (eG m) t η (cv c))
               → M j (ψᴺ j (t₀ ++ a)) (Ω qq (λ z → proj₁ (F (inc n v) β (g (cv z)))))
      LFΩ-keep {n} {j} v β hβ m t {a} {ν} {g} e nu h qq cv eq nq lw =
        mΩP j (cofK (natT j) (t₀ ++ a) (penJ j qq nq) (cof++Ω t₀ a e)) nq
          (λ η c l → subst (λ z → M j z (proj₁ (F (inc n v) β (g (cv c)))))
            (sym (trans (fsTK (natT j) (t₀ ++ a) η (penJ j qq nq) (cof++Ω t₀ a e)) (cong (ψᴺ j) (fsT++ t₀ a η e))))
            (LFω v β hβ (h η (cv c) (lw η c l))))

      chain : ∀ m (t : Pos⁼ (G m)) → ∀ {a ν} {g : Br⁼ (G m) t → Tr Lω}
            → cof a ≡ cΩ ν → NwB (G m) (eG m) t ν → (∀ η c → LwB (G m) (eG m) t η c → Mω (fsT a η) (g c))
            → ∀ k → LwB (G m) (eG m) t (γT (t₀ ++ a) ν k) (iter (sf m t g) (bz⁼ (G m) t) (suc k))
      chain m t {a} {ν} {g} e nu h zero =
        feedB (G m) (eG m) t nu (γT (t₀ ++ a) ν zero)
          (λ k w → proj₁ (ψ Lω o r B k (inc m w) (B k (inc m w)) (g (bz⁼ (G m) t))))
          (λ {i} si u qu eqν → subst (λ μ → M i (E.Ωt μ) (proj₁ (ψ Lω o r B (fn i) (inc m u) (B (fn i) (inc m u)) (g (bz⁼ (G m) t)))))
             (sym eqν)
             (ΩJ i (ψ Lω o r B (fn i) (inc m u) (B (fn i) (inc m u)) (g (bz⁼ (G m) t)))
                (⊴-trans (wΩ gb m si u qu) (ψ-⊵ Lω o r B (fn i) (inc m u) (B (fn i) (inc m u)) (g (bz⁼ (G m) t))))))
      chain m t {a} {ν} {g} e nu h (suc k) =
        feedB (G m) (eG m) t nu (γT (t₀ ++ a) ν (suc k))
          (λ k′ w → proj₁ (ψ Lω o r B k′ (inc m w) (B k′ (inc m w)) (g (iter (sf m t g) (bz⁼ (G m) t) (suc k)))))
          (λ {i} si u qu eqν →
             subst (λ μ → M i (E.ψ μ (fsT (t₀ ++ a) (γT (t₀ ++ a) ν k)) ∷ [])
                            (proj₁ (ψ Lω o r B (fn i) (inc m u) (B (fn i) (inc m u)) (g (iter (sf m t g) (bz⁼ (G m) t) (suc k))))))
               (sym eqν)
               (subst (λ z → M i (ψᴺ i z) (proj₁ (ψ Lω o r B (fn i) (inc m u) (B (fn i) (inc m u)) (g (iter (sf m t g) (bz⁼ (G m) t) (suc k))))))
                 (sym (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))
                 (LFω u (B (fn i) (inc m u)) (wM gb m si u qu)
                   (h (γT (t₀ ++ a) ν k) (iter (sf m t g) (bz⁼ (G m) t) (suc k)) (chain m t e nu h k)))))

  module FoldU (oc : (k : ℕ) → Ok (G k)) (r : Rb Lω) (B : Base Lω) (t₀ : E.T) (gb : GBω B t₀)
               (ws : ∀ n → zero ≤ G n) where
    open Fold oc r B t₀ gb

    Fu : Tr⁺ zero → Tr Lω → Tr⁺ zero
    Fu β x = ψ Lω o r B zero (inu ws) β x

    LFu : (β : Tr⁺ zero) → M⁰ (ψᴺ 0 t₀) (proj₁ β)
        → ∀ {a x} → Mω a x → M⁰ (ψᴺ 0 (t₀ ++ a)) (proj₁ (Fu β x))
    LFu β hβ (mz {x = x}) =
      ++[] (λ z → M⁰ (ψᴺ 0 z) (proj₁ (Fu β x))) t₀
        (zlJ 0 (λ y → proj₁ (Fu β y)) (mono Lω o r B zero (inu ws) β) hβ x)
    LFu β hβ (m1 {t = a} {x = x} e h) =
      nextJ 0 (Fu β x) (cofψ1 (natT 0) (t₀ ++ a) (cof++1 t₀ a e))
        (λ k → trans (fsnψ1 (natT 0) (t₀ ++ a) k (cof++1 t₀ a e)) (cong (λ z → replicate k (E.ψ (natT 0) z)) (pred++ t₀ a e)))
        (LFu β hβ h)
    LFu β hβ (mL {t = a} {x = x} e h) =
      mLJ 0 (cofψω (natT 0) (t₀ ++ a) (cof++ω t₀ a e))
        (λ k → subst (λ z → M⁰ z (proj₁ (Fu β x)))
          (sym (trans (fsnψω (natT 0) (t₀ ++ a) k (cof++ω t₀ a e)) (cong (ψᴺ 0) (fsn++ t₀ a k e))))
          (LFu β hβ (h k)))
    LFu β hβ (mΩ {p = inj₁ ()} _ _ _)
    LFu β hβ (mΩ {t = a} {ν = ν} {p = inj₂ (m , t)} {g = g} e nu h) =
      nodeZ (kp Lω o (inj₂ (m , t)) (inu ws)) (λ Z → M⁰ (ψᴺ 0 (t₀ ++ a)) (proj₁ Z)) (λ z → Fu β (g z)) (sf m t g)
        (mLJ 0 (cofG (natT 0) (t₀ ++ a) (gt0B (G m) (eG m) t nu) (cof++Ω t₀ a e))
          (λ k → subst (λ z → M⁰ z (proj₁ (limc⁺ (λ k′ → Fu β (g (iter (sf m t g) (bz⁼ (G m) t) k′))))))
            (sym (trans (fsnG (natT 0) (t₀ ++ a) k (gt0B (G m) (eG m) t nu) (cof++Ω t₀ a e)) (cong (ψᴺ 0) (fsT++ t₀ a (γT (t₀ ++ a) ν k) e))))
            (cumJ 0 (λ k′ → Fu β (g (iter (sf m t g) (bz⁼ (G m) t) k′))) (suc k)
              (LFu β hβ (h (γT (t₀ ++ a) ν k) (iter (sf m t g) (bz⁼ (G m) t) (suc k)) (chain m t e nu h k))))))
    LFu β hβ (mU {t = a} {s = s₁} {x = x} {c = m} {y = y} {e = ey} h ch) =
      subst (λ z → M⁰ (ψᴺ 0 z) (proj₁ (Fu β (up x m y ey)))) (++-assoc t₀ a s₁)
        (P.all (d m) (G m) (eG m) 0 zero refl (ws m) (oc m) (proj₂ r m) (cb m x) (t₀ ++ a) (gbL m h) (Fu β x) (LFu β hβ h) ch)
    LFu β hβ (mw h dd) = mwN 0 (LFu β hβ h) (mono Lω o r B zero (inu ws) β dd)
    LFu β hβ (mc le h) = mcJ 0 (app≤ 0 t₀ le) (LFu β hβ h)

module LimAny (R : ∀ n → fn n ≤ fn (suc n)) = Generic fn (λ n → n) (λ _ → refl) (λ _ → inc tt self) (λ n → ss s0 , refl) R
```
