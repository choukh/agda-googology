# 验收: 有限层号上按槽位的折叠, 保留判定的化简, 上下文, 带前缀项的基本列 (带表的 F2 对照块上的副本)

> 验收文件, 不进成品. 来源: 脚本从 `YiANKp` 照搬全部代码, 只把导入的 F2 折叠换成 [YiVTFold](YiVTFold.lagda.md) (依赖换成对应的 `YiVT` 副本); 陈述与证明的文字未改, 手改之处见文内 "改:" 注释.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTANKp where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; posW; Ev; Rt)
open import OCF.Lean.YiVTFold
open import OCF.Lean.YiVTLSFold using (OKB; ok-dS; ψ⊥-⊵; ψs-⊵)
import OCF.Align.EboLeanDef as E
open E using (cof; c1; cω; cΩ; pred; fsn; fsT; γT; ψ; 𝟏; natT; sucT; cmpᵀ; lt; eq; gt)
open import OCF.Lean.YiMEBase hiding (Rt)
open import OCF.Lean.YiMENote
open import OCF.Lean.YiVTMEAnchor using (M¹; Mβ₀; module G⁰; module G¹)
open import OCF.Lean.YiVTMWPre using (cof++Ω; fsT++; module Pre)
open import OCF.Lean.YiVTEVReach using (cv⊴)
open import OCF.Lean.YiVTPHCtx using (module L1)
open import OCF.Lean.YiVTANFam

≤ⁿ-refl : ∀ a → a ≤ⁿ a
≤ⁿ-refl zero    = z≤n
≤ⁿ-refl (suc a) = s≤s (≤ⁿ-refl a)

≤ⁿ-trans : ∀ {a b c} → a ≤ⁿ b → b ≤ⁿ c → a ≤ⁿ c
≤ⁿ-trans z≤n     _       = z≤n
≤ⁿ-trans (s≤s p) (s≤s q) = s≤s (≤ⁿ-trans p q)

≤ⁿ-step : ∀ {a b} → a ≤ⁿ b → a ≤ⁿ suc b
≤ⁿ-step z≤n     = z≤n
≤ⁿ-step (s≤s l) = s≤s (≤ⁿ-step l)

≤ⁿ-pred : ∀ {a b} → suc a ≤ⁿ b → a ≤ⁿ b
≤ⁿ-pred (s≤s l) = ≤ⁿ-step l

¬s≤ : ∀ {a} → suc a ≤ⁿ a → ⊥
¬s≤ (s≤s l) = ¬s≤ l

cmpℕ : ∀ a b → (suc a ≤ⁿ b) ⊎ (b ≤ⁿ a)
cmpℕ a       zero    = inj₂ z≤n
cmpℕ zero    (suc b) = inj₁ (s≤s z≤n)
cmpℕ (suc a) (suc b) with cmpℕ a b
... | inj₁ l = inj₁ (s≤s l)
... | inj₂ l = inj₂ (s≤s l)

infixl 5 _▸_
data Ctx (m : ℕ) : Set where
  •   : Ctx m
  _▸_ : Ctx m → Tr (fin m) → Ctx m

⟦_⟧ : ∀ {m} → Ctx m → Tr (fin m) → Tr (fin m)
⟦ • ⟧     y = y
⟦ K ▸ X ⟧ y = ⟦ K ⟧ (X + y)

cm : ∀ {m} (K : Ctx m) {x y : Tr (fin m)} → fin m ⊢ x ◃ y → fin m ⊢ ⟦ K ⟧ x ◃ ⟦ K ⟧ y
cm •       d = d
cm (K ▸ X) d = cm K (+-mono X d)

c⊴ : ∀ {m} (K : Ctx m) {x y : Tr (fin m)} → x ⊴ y → ⟦ K ⟧ x ⊴ ⟦ K ⟧ y
c⊴ K ⊴r     = ⊴r
c⊴ K (⊴◃ d) = ⊴◃ (cm K d)

eΩ : ∀ {m} (K : Ctx m) (p : Pos (fin m)) (g : Br (fin m) p → Tr (fin m)) → ⟦ K ⟧ (Ω p g) ≡ Ω p (λ c → ⟦ K ⟧ (g c))
eΩ •       p g = refl
eΩ (K ▸ X) p g = eΩ K p (λ c → X + g c)

eΩt : ∀ {n} (K : Ctx (suc n)) (x₀ : Tr (fin (suc n)))
    → ⟦ K ⟧ (Ω (inj₁ tt) (λ c → up x₀ tt (suc c) (z◃s c))) ≡ Ω (inj₁ tt) (λ c → up (⟦ K ⟧ x₀) tt (suc c) (z◃s c))
eΩt •       x₀ = refl
eΩt (K ▸ X) x₀ = eΩt K (X + x₀)

z⊴ : ∀ {S : Sg} (x : T S) → zero ⊴ x
z⊴ x with zl x
... | inj₁ refl = ⊴r
... | inj₂ d    = ⊴◃ d

atP : (Fam : (i : ℕ) → Tr (fin i) → Set) (n : ℕ) (p : Pos (fin (suc n))) → Tr (at (fin (suc n)) p) → Set
atP Fam n       (inj₁ _) x = Fam n x
atP Fam (suc n) (inj₂ p) x = atP Fam n p x
atP Fam zero    (inj₂ ())

atP-map : ∀ {Fam Fam′ : (i : ℕ) → Tr (fin i) → Set} → (∀ i {x} → Fam i x → Fam′ i x)
        → ∀ n p {x} → atP Fam n p x → atP Fam′ n p x
atP-map f n       (inj₁ _) a = f n a
atP-map f (suc n) (inj₂ p) a = atP-map f n p a
atP-map f zero    (inj₂ ())

atP-up : ∀ {Fam : (i : ℕ) → Tr (fin i) → Set} → (∀ i {x x′} → Fam i x → fin i ⊢ x ◃ x′ → Fam i x′)
       → ∀ n p {x x′} → atP Fam n p x → at (fin (suc n)) p ⊢ x ◃ x′ → atP Fam n p x′
atP-up f n       (inj₁ _) a d = f n a d
atP-up f (suc n) (inj₂ p) a d = atP-up f n p a d
atP-up f zero    (inj₂ ())

atP-cum : ∀ {Fam : (i : ℕ) → Tr (fin i) → Set}
        → (∀ i (Z : ℕ → Tr (fin i)) (nz : ∀ k → fin i ⊢ zero ◃ Z k) k → Fam i (Z k) → Fam i (limc Z nz))
        → ∀ n p (Z : ℕ → Tr (at (fin (suc n)) p)) (nz : ∀ k → at (fin (suc n)) p ⊢ zero ◃ Z k) k
        → atP Fam n p (Z k) → atP Fam n p (limc Z nz)
atP-cum f n       (inj₁ _) Z nz k a = f n Z nz k a
atP-cum f (suc n) (inj₂ p) Z nz k a = atP-cum f n p Z nz k a
atP-cum f zero    (inj₂ ())

toLw : ∀ n p (f : ℕ → E.T) {x} → atP (λ i y → M i (f i) y) n p x → Lw n p (f (slot n p)) (fromBr (fin (suc n)) p x)
toLw n       (inj₁ _) f a = a
toLw (suc n) (inj₂ p) f a = toLw n p f a
toLw zero    (inj₂ ())

module _ (n : ℕ) (ε : Ev (fin (suc n))) (ρ : Rt (fin (suc n))) (D : Base (fin (suc n))) where
  private
    ℓ : L
    ℓ = fin (suc n)

  fo : (p : Pos ℓ) → Tr ℓ → Tr (at ℓ p)
  fo p V = ψs ℓ ε ρ D (at ℓ p) (posW ℓ p) (bs D (at ℓ p) (posW ℓ p)) (ns D (at ℓ p) (posW ℓ p)) V

  fo-nz : (p : Pos ℓ) (V : Tr ℓ) → at ℓ p ⊢ zero ◃ fo p V
  fo-nz p V = nzs ℓ ε ρ D (at ℓ p) (posW ℓ p) (bs D (at ℓ p) (posW ℓ p)) (ns D (at ℓ p) (posW ℓ p)) V

  fo-mono : (p : Pos ℓ) {V V′ : Tr ℓ} → ℓ ⊢ V ◃ V′ → at ℓ p ⊢ fo p V ◃ fo p V′
  fo-mono p = monos ℓ ε ρ D (at ℓ p) (posW ℓ p) (bs D (at ℓ p) (posW ℓ p)) (ns D (at ℓ p) (posW ℓ p))

  fo-⊴ : (p : Pos ℓ) {V V′ : Tr ℓ} → V ⊴ V′ → fo p V ⊴ fo p V′
  fo-⊴ p ⊴r     = ⊴r
  fo-⊴ p (⊴◃ d) = ⊴◃ (fo-mono p d)

  fo⊵ : (p : Pos ℓ) (V : Tr ℓ) → bs D (at ℓ p) (posW ℓ p) ⊴ fo p V
  fo⊵ p V = cv⊴ (ψs-⊵ ℓ ε ρ D (at ℓ p) (posW ℓ p) (bs D (at ℓ p) (posW ℓ p)) (ns D (at ℓ p) (posW ℓ p)) V)

  vch : (p₀ : Pos ℓ) (G : Br ℓ p₀ → Tr ℓ) → ℕ → Br ℓ p₀
  vch p₀ G = iter (λ z → fromBr ℓ p₀ (fo p₀ (G z))) (br0 ℓ p₀)

  ⊥-⊴ : {V V′ : Tr ℓ} → V ⊴ V′ → ψ⊥ ℓ ε ρ D V ⊴ ψ⊥ ℓ ε ρ D V′
  ⊥-⊴ ⊴r     = ⊴r
  ⊥-⊴ (⊴◃ d) = ⊴◃ (mono⊥ ℓ ε ρ D d)

kpDrop : ∀ n (ε : Ev (fin (suc n))) (ρ : Rt (fin (suc n))) (p₀ p : Pos (fin (suc n))) → slot n p ≤ⁿ slot n p₀
       → {X : Set} (K : (q : Pos (at (fin (suc n)) p)) → (Br (at (fin (suc n)) p) q → Br (fin (suc n)) p₀) → X) (d : X)
       → kp (fin (suc n)) ε ρ p₀ (posW (fin (suc n)) p) K d ≡ d
kpDrop n       ε ρ (inj₁ _)  p         le K d = refl
kpDrop (suc n) ε ρ (inj₂ p₀) (inj₁ _)  le K d = ⊥-elim (¬s≤ (≤ⁿ-trans le (slot≤ n p₀)))
kpDrop (suc n) ε ρ (inj₂ p₀) (inj₂ p)  le K d = kpDrop n ε ρ p₀ p le K d
kpDrop zero    ε ρ (inj₂ ()) p         le K d

kpKeep : (FamH : E.T → (i : ℕ) → Tr (fin i) → Set) (Fam : (i : ℕ) → Tr (fin i) → Set) (nB : ℕ) (ν : E.T)
  → (step : ∀ i (q : Pos (fin (suc i))) (Z : Br (fin (suc i)) q → Tr (fin (suc i))) → suc i ≤ⁿ nB → Nw i q ν
          → (∀ η c → Lw i q η c → FamH η (suc i) (Z c)) → Fam (suc i) (Ω q Z))
  → ∀ n (ε : Ev (fin (suc n))) (ρ : Rt (fin (suc n))) (p₀ p : Pos (fin (suc n))) → suc (slot n p₀) ≤ⁿ slot n p → n ≤ⁿ nB
  → Nw n p₀ ν
  → (Zf : Br (fin (suc n)) p₀ → Tr (at (fin (suc n)) p)) (d : Tr (at (fin (suc n)) p))
  → (∀ η c → Lw n p₀ η c → atP (FamH η) n p (Zf c))
  → atP Fam n p (kp (fin (suc n)) ε ρ p₀ (posW (fin (suc n)) p) (λ q cv → Ω q (λ z → Zf (cv z))) d)
kpKeep FamH Fam nB ν step n       ε ρ (inj₁ _)  p        l bd nu Zf d h = ⊥-elim (¬s≤ (≤ⁿ-trans l (slot≤ n p)))
kpKeep FamH Fam nB ν step (suc n) ε ρ (inj₂ p₀) (inj₁ _) l bd nu Zf d h = step n p₀ Zf bd nu h
kpKeep FamH Fam nB ν step (suc n) ε ρ (inj₂ p₀) (inj₂ p) l bd nu Zf d h =
  kpKeep FamH Fam nB ν step n ε ρ p₀ p l (≤ⁿ-pred bd) nu Zf d h
kpKeep FamH Fam nB ν step zero    ε ρ (inj₂ ()) p        l bd nu Zf d h

module Tm (t : E.T) where

  trmS : ℕ → E.T → E.T
  trmS zero    q = ψᴺ 0 (t ++ ψᴺ 1 q)
  trmS (suc i) q = ψᴺ (suc i) q

  trmKS : ℕ → E.T → E.T
  trmKS zero    q = []
  trmKS (suc i) q = ψᴺ (suc i) q

  ĉ : ℕ → E.T → ℕ → E.T
  ĉ i₀ q zero    = Ωᴺ i₀
  ĉ i₀ q (suc k) = trmS i₀ (fsT q (ĉ i₀ q k))

  lCof : ∀ i q → cof q ≡ cω → cof (trmS i q) ≡ cω
  lCof zero    q e = cofψω [] (t ++ ψᴺ 1 q) (cof++ω t (ψᴺ 1 q) (cofψω (natT 1) q e))
  lCof (suc i) q e = cofψω (natT (suc i)) q e

  lFsn : ∀ i q k → cof q ≡ cω → fsn (trmS i q) k ≡ trmS i (fsn q k)
  lFsn zero    q k e =
    trans (fsnψω [] (t ++ ψᴺ 1 q) k (cof++ω t (ψᴺ 1 q) (cofψω (natT 1) q e)))
      (cong (ψᴺ 0) (trans (fsn++ t (ψᴺ 1 q) k (cofψω (natT 1) q e)) (cong (t ++_) (fsnψω (natT 1) q k e))))
  lFsn (suc i) q k e = fsnψω (natT (suc i)) q k e

  γ≡ĉ : ∀ i₀ q k → γT q (natT (suc i₀)) k ≡ ĉ (suc i₀) q k
  γ≡ĉ i₀ q zero    = refl
  γ≡ĉ i₀ q (suc k) = cong (λ z → ψᴺ (suc i₀) (fsT q z)) (γ≡ĉ i₀ q k)

  private
    module Z0 (q : E.T) (e : cof q ≡ cΩ []) where
      B′ : E.T
      B′ = t ++ ψᴺ 1 q

      c1K : cof (ψᴺ 1 q) ≡ cΩ []
      c1K = cofK (natT 1) q (inj₂ refl) e

      cB : cof B′ ≡ cΩ []
      cB = cof++Ω t (ψᴺ 1 q) c1K

      fB : ∀ η → fsT B′ η ≡ t ++ ψᴺ 1 (fsT q η)
      fB η = trans (fsT++ t (ψᴺ 1 q) η c1K) (cong (t ++_) (fsTK (natT 1) q η (inj₂ refl) e))

      γ0 : ∀ k → γT B′ [] k ≡ ĉ 0 q k
      γ0 zero    = refl
      γ0 (suc k) = trans (cong (λ z → ψᴺ 0 (fsT B′ z)) (γ0 k)) (cong (ψᴺ 0) (fB (ĉ 0 q k)))

  gCof : ∀ i i₀ q → i ≤ⁿ i₀ → cof q ≡ cΩ (natT i₀) → cof (trmS i q) ≡ cω
  gCof (suc i) (suc i₀) q le e = cofG (natT (suc i)) q (cmp-gt {b = suc i} {a = suc i₀} le) e
  gCof zero    (suc i₀) q le e =
    cofψω [] (t ++ ψᴺ 1 q) (cof++ω t (ψᴺ 1 q) (cofG (natT 1) q (cmp-gt {b = 1} {a = suc i₀} (s≤s z≤n)) e))
  gCof zero    zero     q le e = cofG [] (Z0.B′ q e) refl (Z0.cB q e)

  gFsn : ∀ i i₀ q k → i ≤ⁿ i₀ → cof q ≡ cΩ (natT i₀) → fsn (trmS i q) k ≡ trmS i (fsT q (ĉ i₀ q k))
  gFsn (suc i) (suc i₀) q k le e =
    trans (fsnG (natT (suc i)) q k (cmp-gt {b = suc i} {a = suc i₀} le) e)
      (cong (λ z → ψᴺ (suc i) (fsT q z)) (γ≡ĉ i₀ q k))
  gFsn zero    (suc i₀) q k le e =
    trans (fsnψω [] (t ++ ψᴺ 1 q) k (cof++ω t (ψᴺ 1 q) cq1))
      (cong (ψᴺ 0) (trans (fsn++ t (ψᴺ 1 q) k cq1)
        (cong (t ++_) (trans (fsnG (natT 1) q k (cmp-gt {b = 1} {a = suc i₀} (s≤s z≤n)) e)
          (cong (λ z → ψᴺ 1 (fsT q z)) (γ≡ĉ i₀ q k))))))
    where
    cq1 : cof (ψᴺ 1 q) ≡ cω
    cq1 = cofG (natT 1) q (cmp-gt {b = 1} {a = suc i₀} (s≤s z≤n)) e
  gFsn zero    zero     q k le e = trans (fsnG [] (Z0.B′ q e) k refl (Z0.cB q e)) (Z0.γ0 q e (suc k))

  record Gd (n : ℕ) (D : Base (fin (suc n))) : Set where
    constructor mkGd
    field
      gok : OKB (fin (suc n)) D
      g⊥  : M⁰ (ψᴺ 0 t) (b⊥ D)
      g0  : (w : zero ≤ fin (suc n)) → M⁰ (ψᴺ 0 t) (bs D zero w)
  open Gd public

  gd-dS : ∀ n (ε : Ev (fin (suc (suc n)))) (ρ : Rt (fin (suc (suc n)))) (D : Base (fin (suc (suc n))))
          → Gd (suc n) D → (x : Tr (fin (suc (suc n)))) → Gd n (dS (fin (suc n)) ε ρ D x)
  gd-dS n ε ρ D g x = mkGd (ok-dS ε ρ D (gok g) x)
    (G⁰.m⊴ (g⊥ g) (cv⊴ (ψ⊥-⊵ (fin (suc (suc n))) ε ρ D x)))
    (λ w → G⁰.m⊴ (g0 g (ins w)) (cv⊴ (ψs-⊵ (fin (suc (suc n))) ε ρ D zero (ins w) (bs D zero (ins w)) (ns D zero (ins w)) x)))

  GF : (i : ℕ) → Tr (fin i) → Set
  GF zero    x = M⁰ (ψᴺ 0 t) x
  GF (suc i) x = M (suc i) (Ωᴺ (suc i)) x × (Ωt (fin (suc i)) ⊴ x)

  gB′ : ∀ {ℓ′} (B′ : Base ℓ′) → OKB ℓ′ B′ → ((w : zero ≤ ℓ′) → M⁰ (ψᴺ 0 t) (bs B′ zero w))
      → ∀ n (ex : ∀ {j} → j ≤ fin (suc n) → j ≤ ℓ′) (p : Pos (fin (suc n)))
      → atP GF n p (bs B′ (at (fin (suc n)) p) (ex (posW (fin (suc n)) p)))
  gB′ B′ ok h0 zero    ex (inj₁ _) = h0 (ex (ins self))
  gB′ B′ ok h0 (suc n) ex (inj₁ _) =
    GM.m⊴ n (Mβ n) (cv⊴ (proj₂ ok (fin (suc n)) (ex (ins self)))) , cv⊴ (proj₂ ok (fin (suc n)) (ex (ins self)))
  gB′ B′ ok h0 (suc n) ex (inj₂ p) = gB′ B′ ok h0 n (λ w → ex (ins w)) p
  gB′ B′ ok h0 zero    ex (inj₂ ())

  gBs : ∀ n (D : Base (fin (suc n))) → Gd n D → (p : Pos (fin (suc n)))
      → atP GF n p (bs D (at (fin (suc n)) p) (posW (fin (suc n)) p))
  gBs n D g p = gB′ D (gok g) (g0 g) n (λ w → w) p

  ΩR : ∀ n p {b x} → atP GF n p b → b ⊴ x → at (fin (suc n)) p ⊢ zero ◃ x
     → Lw n p (Ωᴺ (slot n p)) (fromBr (fin (suc n)) p x)
  ΩR zero    (inj₁ _) {x = x} a le nz = pos⁰ x nz
  ΩR (suc n) (inj₁ _) a le nz = GM.m⊴ n (proj₁ a) le
  ΩR (suc n) (inj₂ p) a le nz = ΩR n p a le nz
  ΩR zero    (inj₂ ())

  module One (ε : Ev (fin 1)) (ρ : Rt (fin 1)) (D : Base (fin 1)) (g : Gd 0 D) where
    private
      module PL = Pre (L1.lift D) (G¹.m⊴ Mβ₀ (cv⊴ (proj₂ (gok g) (fin 1) self))) t (g0 g (ins self)) (g⊥ g)

    QH1 : ∀ {s y} → M 1 s y → M⁰ (ψᴺ 0 (t ++ s)) (fo 0 ε ρ D (inj₁ tt) y)
    QH1 m = PL.QHp (to¹ m)

    VW1 : ∀ {s y} → M 1 s y → M⁰ (ψᴺ 0 (t ++ s)) (ψ⊥ (fin 1) ε ρ D y)
    VW1 m = PL.VWp (to¹ m)

MβC : ∀ n (K : Ctx (suc n)) → M (suc n) (Ωᴺ (suc n)) (⟦ K ⟧ (Ωt (fin (suc n))))
MβC n K = subst (M (suc n) (Ωᴺ (suc n))) (sym (eΩt K zero))
  (mΩ (cofΩ n) refl
    (λ η c l → subst (λ s → M (suc n) s (up (⟦ K ⟧ zero) tt (suc c) (z◃s c))) (sym (fsTΩ n η)) (mU mz (mwN n l ◃s))))
```
