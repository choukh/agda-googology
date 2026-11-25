# 验收: 一切有限层号上折到低层的保持 (遗传的三条结论), 带前缀锚点 (带表的 F2 对照块上的副本)

> 验收文件, 不进成品. 来源: 脚本从 `YiANLv` 照搬全部代码, 只把导入的 F2 折叠换成 [YiVTFold](YiVTFold.lagda.md) (依赖换成对应的 `YiVT` 副本); 陈述与证明的文字未改, 手改之处见文内 "改:" 注释.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiVTANLv where

open import Data.Nat using (ℕ; zero; suc; z≤n; s≤s) renaming (_≤_ to _≤ⁿ_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.List using ([]; _∷_; _++_; replicate)
open import Data.List.Properties using (++-assoc; ++-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans; cong)

open import OCF.Lean.YiLegBlock
open import OCF.Lean.YiLegOps
open import OCF.Lean.YiLegPath using (_≤_; self; ins; posW; Ev; Rt)
open import OCF.Lean.YiVTFold
open import OCF.Lean.YiVTLSFold using (OKB; ψ⊥-⊵; ψs-⊵)
import OCF.Align.EboLeanDef as E
open E using (cof; c1; cω; cΩ; pred; fsn; fsT; γT; ψ; 𝟏; natT)
open import OCF.Lean.YiMEBase hiding (Rt)
open import OCF.Lean.YiMENote
open import OCF.Lean.YiVTMEAnchor using (++[]; module G⁰)
open import OCF.Lean.YiVTMWPre using (cof++Ω; fsT++)
open import OCF.Lean.YiVTEVReach using (cv⊴)
open import OCF.Lean.YiVTPHCtx using (up⊵)
open import OCF.Lean.YiVTANFam
open import OCF.Lean.YiVTANKp

split≤ : ∀ {j m} → j ≤ⁿ m → (j ≡ m) ⊎ (suc j ≤ⁿ m)
split≤ {j = zero}  {m = zero}  z≤n     = inj₁ refl
split≤ {j = zero}  {m = suc m} z≤n     = inj₂ (s≤s z≤n)
split≤ {j = suc j} {m = suc m} (s≤s l) with split≤ l
... | inj₁ refl = inj₁ refl
... | inj₂ l′   = inj₂ (s≤s l′)

module Lv (t : E.T) where
  open Tm t

  Bot : E.T → (i : ℕ) → Tr (fin i) → Set
  Bot q zero    x = M⁰ (trmS 0 q) x
  Bot q (suc i) x = ⊤

  bot-up : ∀ q i {x x′} → Bot q i x → fin i ⊢ x ◃ x′ → Bot q i x′
  bot-up q zero    a d = mw a d
  bot-up q (suc i) a d = tt

  bot-cum : ∀ q i (Z : ℕ → Tr (fin i)) (nz : ∀ k → fin i ⊢ zero ◃ Z k) k → Bot q i (Z k) → Bot q i (limc Z nz)
  bot-cum q zero    Z nz k a = G⁰.m-cum Z nz k a
  bot-cum q (suc i) Z nz k a = tt

  B0 : ∀ n (ε : Ev (fin (suc n))) (ρ : Rt (fin (suc n))) (D : Base (fin (suc n))) → E.T → Tr (fin (suc n)) → Set
  B0 n ε ρ D q V =
    ((p : Pos (fin (suc n))) → atP (Bot q) n p (fo n ε ρ D p V)) × M⁰ (trmS 0 q) (ψ⊥ (fin (suc n)) ε ρ D V)

  B0-up : ∀ n ε ρ D {q V V′} → B0 n ε ρ D q V → V ⊴ V′ → B0 n ε ρ D q V′
  B0-up n ε ρ D     b ⊴r     = b
  B0-up n ε ρ D {q} b (⊴◃ d) =
    (λ p → atP-up {Fam = Bot q} (bot-up q) n p (proj₁ b p) (fo-mono n ε ρ D p d))
    , mw (proj₂ b) (mono⊥ (fin (suc n)) ε ρ D d)

  rootΩ : ∀ n ε ρ D → Gd n D → (K : Ctx (suc n)) (V : Tr (fin (suc n))) → ⟦ K ⟧ (Ωt (fin (suc n))) ⊴ V
        → B0 n ε ρ D [] V
  rootΩ zero ε ρ D g K V le =
    B0-up zero ε ρ D
      ((λ { (inj₁ _) → One.QH1 ε ρ D g (MβC 0 K) ; (inj₂ ()) }) , One.VW1 ε ρ D g (MβC 0 K)) le
  rootΩ (suc m) ε ρ D g K V le =
    B0-up (suc m) ε ρ D (subst (B0 (suc m) ε ρ D []) (sym (eΩt K zero)) bΩ) le
    where
    X₀ : Tr (fin (suc (suc m)))
    X₀ = ⟦ K ⟧ zero

    gL : Tr (fin (suc m)) → Tr (fin (suc (suc m)))
    gL c = up X₀ tt (suc c) (z◃s c)

    D₀ : Base (fin (suc m))
    D₀ = dS (fin (suc m)) ε ρ D X₀

    vc : ℕ → Tr (fin (suc m))
    vc = vch (suc m) ε ρ D (inj₁ tt) gL

    r₀ : B0 m ε ρ D₀ [] (vc 1)
    r₀ = rootΩ m ε ρ D₀ (gd-dS m ε ρ D g X₀) • (vc 1)
      (⊴◃ (⊴-◃ (⊴-trans (proj₂ (gBs (suc m) D g (inj₁ tt))) (fo⊵ (suc m) ε ρ D (inj₁ tt) X₀)) (◃l zero)))

    bΩ : B0 (suc m) ε ρ D [] (Ω (inj₁ tt) gL)
    bΩ = (λ { (inj₁ _)  → tt
            ; (inj₂ p′) → atP-cum {Fam = Bot []} (bot-cum []) m p′
                (λ k → fo (suc m) ε ρ D (inj₂ p′) (gL (vc k))) (λ k → fo-nz (suc m) ε ρ D (inj₂ p′) (gL (vc k))) 1
                (atP-up {Fam = Bot []} (bot-up []) m p′ (proj₁ r₀ p′) (◃l zero)) })
       , G⁰.m-cum (λ k → ψ⊥ (fin (suc (suc m))) ε ρ D (gL (vc k))) (λ k → nz⊥ (fin (suc (suc m))) ε ρ D (gL (vc k))) 1
           (mw (proj₂ r₀) (◃l zero))

  mutual
    Her : (i : ℕ) → E.T → Tr (fin i) → Set
    Her zero          p x = ⊤
    Her (suc zero)    p x = ⊤
    Her (suc (suc j)) p x =
      (ε : Ev (fin (suc (suc j)))) (ρ : Rt (fin (suc (suc j)))) (D : Base (fin (suc (suc j)))) → Gd (suc j) D
      → TC (suc j) ε ρ D p x

    RelP : (n : ℕ) (p : Pos (fin (suc n))) → (ℕ → E.T) → Tr (at (fin (suc n)) p) → Set
    RelP n       (inj₁ _)  f x = M n (f n) x × Her n (f n) x
    RelP (suc n) (inj₂ p)  f x = RelP n p f x
    RelP zero    (inj₂ ()) f x

    Cl : ∀ n (ε : Ev (fin (suc n))) (ρ : Rt (fin (suc n))) (D : Base (fin (suc n))) → E.T → Tr (fin (suc n)) → Set
    Cl n ε ρ D q V =
      ((p : Pos (fin (suc n))) → RelP n p (λ i → trmS i q) (fo n ε ρ D p V))
      × M⁰ (trmS 0 q) (ψ⊥ (fin (suc n)) ε ρ D V)

    Kn : ∀ n (ε : Ev (fin (suc n))) (ρ : Rt (fin (suc n))) (D : Base (fin (suc n))) → Ctx (suc n) → E.T → Set
    Kn n ε ρ D K A₀ =
      ((p : Pos (fin (suc n))) → RelP n p (λ i → trmKS i A₀) (fo n ε ρ D p (⟦ K ⟧ zero)))
      × ((V : Tr (fin (suc n))) → ⟦ K ⟧ zero ⊴ V → B0 n ε ρ D [] V → B0 n ε ρ D A₀ V)

    TC : ∀ n (ε : Ev (fin (suc n))) (ρ : Rt (fin (suc n))) (D : Base (fin (suc n))) → E.T → Tr (fin (suc n)) → Set
    TC n ε ρ D p Y = (K : Ctx (suc n)) (A₀ : E.T) → Kn n ε ρ D K A₀ → Cl n ε ρ D (A₀ ++ p) (⟦ K ⟧ Y)

  toAt : ∀ n p (f : ℕ → E.T) {x} → RelP n p f x → atP (λ i y → M i (f i) y × Her i (f i) y) n p x
  toAt n       (inj₁ _) f r = r
  toAt (suc n) (inj₂ p) f r = toAt n p f r
  toAt zero    (inj₂ ())

  fromAt : ∀ n p (f : ℕ → E.T) {x} → atP (λ i y → M i (f i) y × Her i (f i) y) n p x → RelP n p f x
  fromAt n       (inj₁ _) f r = r
  fromAt (suc n) (inj₂ p) f r = fromAt n p f r
  fromAt zero    (inj₂ ())

  relM : ∀ n p (f : ℕ → E.T) {x} → RelP n p f x → atP (λ i y → M i (f i) y) n p x
  relM n       (inj₁ _) f r = proj₁ r
  relM (suc n) (inj₂ p) f r = relM n p f r
  relM zero    (inj₂ ())

  cl→kn : ∀ n p q {x} → RelP n p (λ i → trmS i q) x → RelP n p (λ i → trmKS i q) x
  cl→kn zero    (inj₁ _) q r = mz , tt
  cl→kn (suc n) (inj₁ _) q r = r
  cl→kn (suc n) (inj₂ p) q r = cl→kn n p q r
  cl→kn zero    (inj₂ ())

  kn→cl : ∀ n p q {x} → RelP n p (λ i → trmKS i q) x → atP (Bot q) n p x → RelP n p (λ i → trmS i q) x
  kn→cl zero    (inj₁ _) q r b = b , tt
  kn→cl (suc n) (inj₁ _) q r b = r
  kn→cl (suc n) (inj₂ p) q r b = kn→cl n p q r b
  kn→cl zero    (inj₂ ())

  relBot : ∀ n p q {x} → RelP n p (λ i → trmS i q) x → atP (Bot q) n p x
  relBot zero    (inj₁ _) q r = proj₁ r
  relBot (suc n) (inj₁ _) q r = tt
  relBot (suc n) (inj₂ p) q r = relBot n p q r
  relBot zero    (inj₂ ())

  record Th (m : ℕ) : Set where
    field
      tcUp   : ∀ ε ρ D → Gd (suc m) D → ∀ {p Y Y′} → TC (suc m) ε ρ D p Y → fin (suc (suc m)) ⊢ Y ◃ Y′
             → TC (suc m) ε ρ D p Y′
      tcLim  : ∀ ε ρ D → Gd (suc m) D → ∀ {b Y} → cof b ≡ cω → (∀ k → TC (suc m) ε ρ D (fsn b k) Y)
             → TC (suc m) ε ρ D b Y
      tcLimc : ∀ ε ρ D → Gd (suc m) D → ∀ {b} (Z : ℕ → Tr (fin (suc (suc m))))
               (nz : ∀ k → fin (suc (suc m)) ⊢ zero ◃ Z k) (κ : ℕ → ℕ) → cof b ≡ cω
             → (∀ k → TC (suc m) ε ρ D (fsn b k) (Z (κ k))) → TC (suc m) ε ρ D b (limc Z nz)
      tcNode : ∀ ε ρ D → Gd (suc m) D → ∀ {b ν} (p₀ : Pos (fin (suc (suc m))))
               (G₀ : Br (fin (suc (suc m))) p₀ → Tr (fin (suc (suc m)))) → cof b ≡ cΩ ν → Nw (suc m) p₀ ν
             → (∀ η c → Lw (suc m) p₀ η c → TC (suc m) ε ρ D (fsT b η) (G₀ c)) → TC (suc m) ε ρ D b (Ω p₀ G₀)
      tcLeaf : ∀ ε ρ D → Gd (suc m) D → TC (suc m) ε ρ D (Ωᴺ (suc (suc m))) (Ωt (fin (suc (suc m))))
      tcMain : ∀ ε ρ D → Gd (suc m) D → ∀ ε₀ ρ₀ D₀ β nβ → Ωt (fin (suc (suc m))) ⊴ β
             → ∀ {P₀} → TC (suc m) ε ρ D (ψᴺ (suc (suc m)) P₀) β
             → ∀ {a x} → M (suc (suc m)) a x
             → TC (suc m) ε ρ D (ψᴺ (suc (suc m)) (P₀ ++ a)) (Self.F (suc m) ε₀ ρ₀ D₀ β nβ x)

  Low : ℕ → Set
  Low m = ∀ j → suc j ≤ⁿ m → Th j

  SubRow : ℕ → Set
  SubRow m = (ε : Ev (fin (suc m))) (ρ : Rt (fin (suc m))) (D₀ : Base (fin (suc m))) → Gd m D₀
    → (A₀ : E.T) (β : Tr (fin (suc m))) (nβ : fin (suc m) ⊢ zero ◃ β)
    → Ωt (fin (suc m)) ⊴ β → M (suc m) (Ωᴺ (suc m)) β
    → M (suc m) (ψᴺ (suc m) A₀) β × Her (suc m) (ψᴺ (suc m) A₀) β
    → Kn m ε ρ D₀ • A₀
    → (∀ k → Σ ℕ λ k′ → Cl m ε ρ D₀ (A₀ ++ Self.gch m ε ρ D₀ β nβ A₀ k) (Self.z m ε ρ D₀ β nβ k′))
    × (∀ k → Her (suc m) (ψᴺ (suc m) (A₀ ++ Self.gch m ε ρ D₀ β nβ A₀ k)) (Self.z m ε ρ D₀ β nβ (suc (suc k))))

  subOf : ∀ m → Low m → SubRow m
  subOf zero low ε ρ D₀ g₀ A₀ β nβ hΩ hΩM hP kn₀ =
    (λ k → suc (suc k)
         , ((λ { (inj₁ _) → One.QH1 ε ρ D₀ g₀ (sγ hΩM (proj₁ hP) (suc k)) , tt ; (inj₂ ()) })
           , One.VW1 ε ρ D₀ g₀ (sγ hΩM (proj₁ hP) (suc k))))
    , (λ k → tt)
    where open Self zero ε ρ D₀ β nβ
  subOf (suc m) low ε ρ D₀ g₀ A₀ β nβ hΩ hΩM hP kn₀ = rows , topHer
    where
    open Self (suc m) ε ρ D₀ β nβ
    th : Th m
    th = low m (≤ⁿ-refl (suc m))

    rows : ∀ k → Σ ℕ λ k′ → Cl (suc m) ε ρ D₀ (A₀ ++ gch A₀ k) (z k′)
    rows zero    = 1 , Th.tcUp th ε ρ D₀ g₀ (Th.tcLeaf th ε ρ D₀ g₀) (⊴-◃ hΩ (◃l zero)) • A₀ kn₀
    rows (suc k) = suc (suc k)
      , Th.tcUp th ε ρ D₀ g₀ (Th.tcMain th ε ρ D₀ g₀ ε ρ D₀ β nβ hΩ (proj₂ hP ε ρ D₀ g₀) (sγ hΩM (proj₁ hP) k))
          (◃l zero) • A₀ kn₀

    topHer : ∀ k → Her (suc (suc m)) (ψᴺ (suc (suc m)) (A₀ ++ gch A₀ k)) (z (suc (suc k)))
    topHer k ε′ ρ′ D′ g′ =
      Th.tcUp th ε′ ρ′ D′ g′
        (Th.tcMain th ε′ ρ′ D′ g′ ε ρ D₀ β nβ hΩ (proj₂ hP ε′ ρ′ D′ g′) (sγ hΩM (proj₁ hP) k)) (◃l zero)

  module Level (m : ℕ) (low : Low m) where
    private
      N : ℕ
      N = suc (suc m)

      ℓ : L
      ℓ = fin N

    herUp : ∀ i → i ≤ⁿ suc m → ∀ {p x x′} → Her i p x → fin i ⊢ x ◃ x′ → Her i p x′
    herUp zero          bd       h d = tt
    herUp (suc zero)    bd       h d = tt
    herUp (suc (suc j)) (s≤s bd) h d = λ ε′ ρ′ D′ g′ → Th.tcUp (low j bd) ε′ ρ′ D′ g′ (h ε′ ρ′ D′ g′) d

    herLim : ∀ i → i ≤ⁿ suc m → ∀ {p x} → cof p ≡ cω → (∀ k → Her i (fsn p k) x) → Her i p x
    herLim zero          bd       e h = tt
    herLim (suc zero)    bd       e h = tt
    herLim (suc (suc j)) (s≤s bd) e h = λ ε′ ρ′ D′ g′ → Th.tcLim (low j bd) ε′ ρ′ D′ g′ e (λ k → h k ε′ ρ′ D′ g′)

    herLimc : ∀ i → i ≤ⁿ suc m → ∀ {p} (Z : ℕ → Tr (fin i)) (nz : ∀ k → fin i ⊢ zero ◃ Z k) (κ : ℕ → ℕ)
            → cof p ≡ cω → (∀ k → Her i (fsn p k) (Z (κ k))) → Her i p (limc Z nz)
    herLimc zero          bd       Z nz κ e h = tt
    herLimc (suc zero)    bd       Z nz κ e h = tt
    herLimc (suc (suc j)) (s≤s bd) Z nz κ e h =
      λ ε′ ρ′ D′ g′ → Th.tcLimc (low j bd) ε′ ρ′ D′ g′ Z nz κ e (λ k → h k ε′ ρ′ D′ g′)

    herNode : ∀ i → suc i ≤ⁿ suc m → ∀ {p ν} (q : Pos (fin (suc i))) (Z : Br (fin (suc i)) q → Tr (fin (suc i)))
            → cof p ≡ cΩ ν → Nw i q ν → (∀ η c → Lw i q η c → Her (suc i) (fsT p η) (Z c)) → Her (suc i) p (Ω q Z)
    herNode zero    bd       q Z e nu h = tt
    herNode (suc j) (s≤s bd) q Z e nu h =
      λ ε′ ρ′ D′ g′ → Th.tcNode (low j bd) ε′ ρ′ D′ g′ q Z e nu (λ η c l → h η c l ε′ ρ′ D′ g′)

    relUp : ∀ n′ → n′ ≤ⁿ suc m → ∀ p f {x x′} → RelP n′ p f x → at (fin (suc n′)) p ⊢ x ◃ x′ → RelP n′ p f x′
    relUp n′       bd (inj₁ _)  f r d = mwN n′ (proj₁ r) d , herUp n′ bd (proj₂ r) d
    relUp (suc n′) bd (inj₂ p)  f r d = relUp n′ (≤ⁿ-pred bd) p f r d
    relUp zero     bd (inj₂ ())

    relUp⊴ : ∀ n′ → n′ ≤ⁿ suc m → ∀ p f {x x′} → RelP n′ p f x → x ⊴ x′ → RelP n′ p f x′
    relUp⊴ n′ bd p f r ⊴r     = r
    relUp⊴ n′ bd p f r (⊴◃ d) = relUp n′ bd p f r d

    relLim : ∀ n′ → n′ ≤ⁿ suc m → ∀ p (f : ℕ → E.T) (fk : ℕ → ℕ → E.T) {x}
           → cof (f (slot n′ p)) ≡ cω → (∀ k → fsn (f (slot n′ p)) k ≡ fk k (slot n′ p))
           → (∀ k → RelP n′ p (fk k) x) → RelP n′ p f x
    relLim n′ bd (inj₁ _) f fk {x} e q h =
      mLN n′ e (λ k → subst (λ r → M n′ r x) (sym (q k)) (proj₁ (h k)))
      , herLim n′ bd e (λ k → subst (λ r → Her n′ r x) (sym (q k)) (proj₂ (h k)))
    relLim (suc n′) bd (inj₂ p) f fk e q h = relLim n′ (≤ⁿ-pred bd) p f fk e q h
    relLim zero     bd (inj₂ ())

    relLimc : ∀ n′ → n′ ≤ⁿ suc m → ∀ p (f : ℕ → E.T) (fk : ℕ → ℕ → E.T)
              (Z : ℕ → Tr (at (fin (suc n′)) p)) (nz : ∀ k → at (fin (suc n′)) p ⊢ zero ◃ Z k) (κ : ℕ → ℕ)
            → cof (f (slot n′ p)) ≡ cω → (∀ k → fsn (f (slot n′ p)) k ≡ fk k (slot n′ p))
            → (∀ k → RelP n′ p (fk k) (Z (κ k))) → RelP n′ p f (limc Z nz)
    relLimc n′ bd (inj₁ _) f fk Z nz κ e q h =
      mLN n′ e (λ k → subst (λ r → M n′ r (limc Z nz)) (sym (q k)) (cumN n′ Z nz (κ k) (proj₁ (h k))))
      , herLimc n′ bd Z nz κ e (λ k → subst (λ r → Her n′ r (Z (κ k))) (sym (q k)) (proj₂ (h k)))
    relLimc (suc n′) bd (inj₂ p) f fk Z nz κ e q h = relLimc n′ (≤ⁿ-pred bd) p f fk Z nz κ e q h
    relLimc zero     bd (inj₂ ())

    rootRel : ∀ {ℓ′} (B′ : Base ℓ′) → OKB ℓ′ B′
            → ∀ n′ → n′ ≤ⁿ suc m → (ex : ∀ {j} → j ≤ fin (suc n′) → j ≤ ℓ′) (p : Pos (fin (suc n′)))
            → RelP n′ p (λ i → trmKS i []) (bs B′ (at (fin (suc n′)) p) (ex (posW (fin (suc n′)) p)))
    rootRel B′ ok zero          bd ex (inj₁ _) = mz , tt
    rootRel B′ ok (suc zero)    bd ex (inj₁ _) =
      GM.m⊴ zero (Mβ zero) (cv⊴ (proj₂ ok (fin 1) (ex (ins self)))) , tt
    rootRel B′ ok (suc (suc j)) (s≤s bd) ex (inj₁ _) =
      GM.m⊴ (suc j) (Mβ (suc j)) (cv⊴ (proj₂ ok (fin (suc (suc j))) (ex (ins self))))
      , (λ ε′ ρ′ D′ g′ → up′ (low j bd) ε′ ρ′ D′ g′ (cv⊴ (proj₂ ok (fin (suc (suc j))) (ex (ins self)))))
      where
      up′ : (th : Th j) → ∀ ε′ ρ′ D′ → Gd (suc j) D′ → ∀ {x} → Ωt (fin (suc (suc j))) ⊴ x
          → TC (suc j) ε′ ρ′ D′ (Ωᴺ (suc (suc j))) x
      up′ th ε′ ρ′ D′ g′ ⊴r     = Th.tcLeaf th ε′ ρ′ D′ g′
      up′ th ε′ ρ′ D′ g′ (⊴◃ d) = Th.tcUp th ε′ ρ′ D′ g′ (Th.tcLeaf th ε′ ρ′ D′ g′) d
    rootRel B′ ok (suc n′) bd ex (inj₂ p) = rootRel B′ ok n′ (≤ⁿ-pred bd) (λ w → ex (ins w)) p
    rootRel B′ ok zero     bd ex (inj₂ ())

    module Bs (ε : Ev ℓ) (ρ : Rt ℓ) (D : Base ℓ) (g : Gd (suc m) D) where

      private
        rf : suc m ≤ⁿ suc m
        rf = ≤ⁿ-refl (suc m)

      ClD : E.T → Tr ℓ → Set
      ClD = Cl (suc m) ε ρ D

      KnD : Ctx N → E.T → Set
      KnD = Kn (suc m) ε ρ D

      TCD : E.T → Tr ℓ → Set
      TCD = TC (suc m) ε ρ D

      fo′ : (p : Pos ℓ) → Tr ℓ → Tr (at ℓ p)
      fo′ = fo (suc m) ε ρ D

      Cl-up◃ : ∀ {q V V′} → ClD q V → ℓ ⊢ V ◃ V′ → ClD q V′
      Cl-up◃ c d = (λ p → relUp (suc m) rf p _ (proj₁ c p) (fo-mono (suc m) ε ρ D p d))
                 , mw (proj₂ c) (mono⊥ ℓ ε ρ D d)

      Cl-up⊴ : ∀ {q V V′} → ClD q V → V ⊴ V′ → ClD q V′
      Cl-up⊴ c ⊴r     = c
      Cl-up⊴ c (⊴◃ d) = Cl-up◃ c d

      Cl-lim : ∀ {q V} → cof q ≡ cω → (∀ k → ClD (fsn q k) V) → ClD q V
      Cl-lim {q} {V} e h =
        (λ p → relLim (suc m) rf p (λ i → trmS i q) (λ k i → trmS i (fsn q k))
                 (lCof (slot (suc m) p) q e) (λ k → lFsn (slot (suc m) p) q k e) (λ k → proj₁ (h k) p))
        , mL (lCof 0 q e) (λ k → subst (λ r → M⁰ r (ψ⊥ ℓ ε ρ D V)) (sym (lFsn 0 q k e)) (proj₂ (h k)))

      tcUp◃ : ∀ {p Y Y′} → TCD p Y → ℓ ⊢ Y ◃ Y′ → TCD p Y′
      tcUp◃ tc d K A₀ kn = Cl-up◃ (tc K A₀ kn) (cm K d)

      tcUp⊴ : ∀ {p Y Y′} → TCD p Y → Y ⊴ Y′ → TCD p Y′
      tcUp⊴ tc ⊴r     = tc
      tcUp⊴ tc (⊴◃ d) = tcUp◃ tc d

      tcLim : ∀ {b Y} → cof b ≡ cω → (∀ k → TCD (fsn b k) Y) → TCD b Y
      tcLim {b} {Y} e h K A₀ kn =
        Cl-lim (cof++ω A₀ b e) (λ k → subst (λ r → ClD r (⟦ K ⟧ Y)) (sym (fsn++ A₀ b k e)) (h k K A₀ kn))

      knRoot : KnD • []
      knRoot = (λ p → rootRel D (gok g) (suc m) rf (λ w → w) p) , (λ V le r → r)

      ext : ∀ {K A₀ p Y} → KnD K A₀ → TCD p Y → KnD (K ▸ Y) (A₀ ++ p)
      ext {K} {A₀} {p} {Y} kn tc =
        (λ p′ → cl→kn (suc m) p′ (A₀ ++ p) (proj₁ c p′))
        , (λ V le r → B0-up (suc m) ε ρ D ((λ p′ → relBot (suc m) p′ (A₀ ++ p) (proj₁ c p′)) , proj₂ c) le)
        where
        c : ClD (A₀ ++ p) (⟦ K ⟧ Y)
        c = tc K A₀ kn

      knJunk : ∀ {K A₀} → KnD K A₀ → (a : Tr ℓ) → KnD (K ▸ a) A₀
      knJunk {K} {A₀} kn a =
        (λ p → relUp⊴ (suc m) rf p _ (proj₁ kn p) (fo-⊴ (suc m) ε ρ D p (c⊴ K (z⊴ a))))
        , (λ V le r → proj₂ kn V (⊴-trans (c⊴ K (z⊴ a)) le) r)

      knCl : ∀ {K A₀} → KnD K A₀ → (V : Tr ℓ) → ⟦ K ⟧ zero ⊴ V → B0 (suc m) ε ρ D [] V → ClD A₀ V
      knCl {K} {A₀} kn V le r =
        (λ p → kn→cl (suc m) p A₀ (relUp⊴ (suc m) rf p _ (proj₁ kn p) (fo-⊴ (suc m) ε ρ D p le)) (proj₁ b p))
        , proj₂ b
        where
        b : B0 (suc m) ε ρ D A₀ V
        b = proj₂ kn V le r

      tcLimc : ∀ {b} (Z : ℕ → Tr ℓ) (nz : ∀ k → ℓ ⊢ zero ◃ Z k) (κ : ℕ → ℕ) → cof b ≡ cω
             → (∀ k → TCD (fsn b k) (Z (κ k))) → TCD b (limc Z nz)
      tcLimc {b} Z nz κ e h K A₀ kn =
        Cl-lim (cof++ω A₀ b e)
          (λ k → subst (λ r → ClD r (⟦ K ⟧ (limc Z nz))) (sym (fsn++ A₀ b k e))
            (Cl-up◃ (atCum (fsn b k) (κ k) (h k)) (cm K (◃l (κ k)))))
        where
        atCum : ∀ p′ j → TCD p′ (Z j) → ClD (A₀ ++ p′) (⟦ K ⟧ (cum Z j))
        atCum p′ zero    tc = tc K A₀ kn
        atCum p′ (suc j) tc = tc (K ▸ cum Z j) A₀ (knJunk kn (cum Z j))

      module Nd (p₀ : Pos ℓ) (s : E.T) (e : cof s ≡ cΩ (natT (slot (suc m) p₀))) (G : Br ℓ p₀ → Tr ℓ) where
        i₀ : ℕ
        i₀ = slot (suc m) p₀

        vc : ℕ → Br ℓ p₀
        vc = vch (suc m) ε ρ D p₀ G

        sk : ℕ → E.T
        sk k = fsT s (ĉ i₀ s k)

        dropP : ∀ p → slot (suc m) p ≤ⁿ i₀ → (κ : ℕ → ℕ)
              → (∀ k → RelP (suc m) p (λ i → trmS i (sk k)) (fo′ p (G (vc (κ k)))))
              → RelP (suc m) p (λ i → trmS i s) (fo′ p (Ω p₀ G))
        dropP p le κ rows =
          subst (RelP (suc m) p (λ i → trmS i s)) (sym (kpDrop (suc m) ε ρ p₀ p le _ _))
            (relLimc (suc m) rf p (λ i → trmS i s) (λ k i → trmS i (sk k))
              (λ k → fo′ p (G (vc k))) (λ k → fo-nz (suc m) ε ρ D p (G (vc k))) κ
              (gCof (slot (suc m) p) i₀ s le e) (λ k → gFsn (slot (suc m) p) i₀ s k le e) rows)

        bot⊥ : (κ : ℕ → ℕ) → (∀ k → M⁰ (trmS 0 (sk k)) (ψ⊥ ℓ ε ρ D (G (vc (κ k)))))
             → M⁰ (trmS 0 s) (ψ⊥ ℓ ε ρ D (Ω p₀ G))
        bot⊥ κ rows =
          mL (gCof 0 i₀ s z≤n e)
            (λ k → subst (λ r → M⁰ r (ψ⊥ ℓ ε ρ D (Ω p₀ G))) (sym (gFsn 0 i₀ s k z≤n e))
              (G⁰.m-cum (λ j → ψ⊥ ℓ ε ρ D (G (vc j))) (λ j → nz⊥ ℓ ε ρ D (G (vc j))) (κ k) (rows k)))

      nodeCl : (p₀ : Pos ℓ) (s : E.T) {ν : E.T} → cof s ≡ cΩ ν → Nw (suc m) p₀ ν → (G : Br ℓ p₀ → Tr ℓ)
             → (∀ η c → Lw (suc m) p₀ η c → ClD (fsT s η) (G c)) → ClD s (Ω p₀ G)
      nodeCl p₀ s e refl G hyp = (λ p → pos p (cmpℕ i₀ (slot (suc m) p))) , bot⊥ suc (λ k → proj₂ (row k))
        where
        open Nd p₀ s e G

        chain : ∀ k → Lw (suc m) p₀ (ĉ i₀ s k) (vc (suc k))
        chain zero    = ΩR (suc m) p₀ (gBs (suc m) D g p₀) (fo⊵ (suc m) ε ρ D p₀ (G (br0 ℓ p₀)))
                          (fo-nz (suc m) ε ρ D p₀ (G (br0 ℓ p₀)))
        chain (suc k) = toLw (suc m) p₀ (λ i → trmS i (sk k))
                          (relM (suc m) p₀ (λ i → trmS i (sk k)) (proj₁ (hyp (ĉ i₀ s k) (vc (suc k)) (chain k)) p₀))

        row : ∀ k → ClD (sk k) (G (vc (suc k)))
        row k = hyp (ĉ i₀ s k) (vc (suc k)) (chain k)

        FamH : E.T → (i : ℕ) → Tr (fin i) → Set
        FamH η i y = M i (trmS i (fsT s η)) y × Her i (trmS i (fsT s η)) y

        Fam : (i : ℕ) → Tr (fin i) → Set
        Fam i y = M i (trmS i s) y × Her i (trmS i s) y

        step : ∀ i (q : Pos (fin (suc i))) (Z : Br (fin (suc i)) q → Tr (fin (suc i))) → suc i ≤ⁿ suc m
             → Nw i q (natT i₀) → (∀ η c → Lw i q η c → FamH η (suc i) (Z c)) → Fam (suc i) (Ω q Z)
        step i q Z bd nuq h =
          mΩ (cofK (natT (suc i)) s (penN i q nuq) e) nuq
            (λ η c l → subst (λ r → M (suc i) r (Z c)) (sym (fsTK (natT (suc i)) s η (penN i q nuq) e)) (proj₁ (h η c l)))
          , herNode i bd q Z (cofK (natT (suc i)) s (penN i q nuq) e) nuq
            (λ η c l → subst (λ r → Her (suc i) r (Z c)) (sym (fsTK (natT (suc i)) s η (penN i q nuq) e)) (proj₂ (h η c l)))

        pos : ∀ p → (suc i₀ ≤ⁿ slot (suc m) p) ⊎ (slot (suc m) p ≤ⁿ i₀)
            → RelP (suc m) p (λ i → trmS i s) (fo′ p (Ω p₀ G))
        pos p (inj₂ le) = dropP p le suc (λ k → proj₁ (row k) p)
        pos p (inj₁ lt) =
          fromAt (suc m) p (λ i → trmS i s)
            (kpKeep FamH Fam (suc m) (natT i₀) step (suc m) ε ρ p₀ p lt rf refl (λ c → fo′ p (G c)) _
              (λ η c l → toAt (suc m) p (λ i → trmS i (fsT s η)) (proj₁ (hyp η c l) p)))

      tcNode : ∀ {b ν} (p₀ : Pos ℓ) (G₀ : Br ℓ p₀ → Tr ℓ) → cof b ≡ cΩ ν → Nw (suc m) p₀ ν
             → (∀ η c → Lw (suc m) p₀ η c → TCD (fsT b η) (G₀ c)) → TCD b (Ω p₀ G₀)
      tcNode {b} p₀ G₀ e nu hyp K A₀ kn =
        subst (ClD (A₀ ++ b)) (sym (eΩ K p₀ G₀))
          (nodeCl p₀ (A₀ ++ b) (cof++Ω A₀ b e) nu (λ c → ⟦ K ⟧ (G₀ c))
            (λ η c l → subst (λ r → ClD r (⟦ K ⟧ (G₀ c))) (sym (fsT++ A₀ b η e)) (hyp η c l K A₀ kn)))

      module Leaf (K : Ctx N) (A₀ : E.T) (kn : KnD K A₀) where
        X₀ : Tr ℓ
        X₀ = ⟦ K ⟧ zero

        gL : Tr (fin (suc m)) → Tr ℓ
        gL c = up X₀ tt (suc c) (z◃s c)

        D₀ : Base (fin (suc m))
        D₀ = dS (fin (suc m)) ε ρ D X₀

        g₀ : Gd m D₀
        g₀ = gd-dS m ε ρ D g X₀

        βX : Tr (fin (suc m))
        βX = fo′ (inj₁ tt) X₀

        nβX : fin (suc m) ⊢ zero ◃ βX
        nβX = fo-nz (suc m) ε ρ D (inj₁ tt) X₀

        open Self m ε ρ D₀ βX nβX

        s : E.T
        s = A₀ ++ Ωᴺ N

        e : cof s ≡ cΩ (natT (suc m))
        e = cof++Ω A₀ (Ωᴺ N) (cofΩ (suc m))

        fs : ∀ η → fsT s η ≡ A₀ ++ η
        fs η = trans (fsT++ A₀ (Ωᴺ N) η (cofΩ (suc m))) (cong (A₀ ++_) (fsTΩ (suc m) η))

        open Nd (inj₁ tt) s e gL

        hΩ : Ωt (fin (suc m)) ⊴ βX
        hΩ = ⊴-trans (proj₂ (gBs (suc m) D g (inj₁ tt))) (fo⊵ (suc m) ε ρ D (inj₁ tt) X₀)

        hΩM : M (suc m) (Ωᴺ (suc m)) βX
        hΩM = GM.m⊴ m (proj₁ (gBs (suc m) D g (inj₁ tt))) (fo⊵ (suc m) ε ρ D (inj₁ tt) X₀)

        hP : M (suc m) (ψᴺ (suc m) A₀) βX × Her (suc m) (ψᴺ (suc m) A₀) βX
        hP = proj₁ kn (inj₁ tt)

        kb₀ : (V′ : Tr (fin (suc m))) → zero ⊴ V′ → B0 m ε ρ D₀ [] V′ → B0 m ε ρ D₀ A₀ V′
        kb₀ V′ le r with zl V′
        ... | inj₁ refl = (λ p′ → proj₁ b (inj₂ p′)) , proj₂ b
          where
          b : B0 (suc m) ε ρ D A₀ X₀
          b = proj₂ kn X₀ ⊴r ((λ { (inj₁ _) → tt ; (inj₂ p′) → proj₁ r p′ }) , proj₂ r)
        ... | inj₂ nzV = (λ p′ → proj₁ b (inj₂ p′)) , proj₂ b
          where
          b : B0 (suc m) ε ρ D A₀ (up X₀ tt V′ nzV)
          b = proj₂ kn (up X₀ tt V′ nzV) (⊴◃ (◃u X₀ tt V′ nzV))
                ((λ { (inj₁ _) → tt ; (inj₂ p′) → proj₁ r p′ }) , proj₂ r)

        kn₀ : Kn m ε ρ D₀ • A₀
        kn₀ = (λ p′ → proj₁ kn (inj₂ p′)) , kb₀

        sub : (∀ k → Σ ℕ λ k′ → Cl m ε ρ D₀ (A₀ ++ gch A₀ k) (z k′))
            × (∀ k → Her (suc m) (ψᴺ (suc m) (A₀ ++ gch A₀ k)) (z (suc (suc k))))
        sub = subOf m low ε ρ D₀ g₀ A₀ βX nβX hΩ hΩM hP kn₀

        ĉ≡ : ∀ k → ĉ (suc m) s k ≡ gch A₀ k
        ĉ≡ zero    = refl
        ĉ≡ (suc k) = cong (ψᴺ (suc m)) (trans (fs (ĉ (suc m) s k)) (cong (A₀ ++_) (ĉ≡ k)))

        skq : ∀ k → sk k ≡ A₀ ++ gch A₀ k
        skq k = trans (fs (ĉ (suc m) s k)) (cong (A₀ ++_) (ĉ≡ k))

        κ : Pos ℓ → ℕ → ℕ
        κ (inj₁ _)  k = suc k
        κ (inj₂ p′) k = proj₁ (proj₁ sub k)

        rows : ∀ p k → RelP (suc m) p (λ i → trmS i (sk k)) (fo′ p (gL (vc (κ p k))))
        rows (inj₁ _)  k =
          subst (λ r → M (suc m) (ψᴺ (suc m) r) (z (suc (suc k))) × Her (suc m) (ψᴺ (suc m) r) (z (suc (suc k))))
            (sym (skq k)) (sγ hΩM (proj₁ hP) (suc k) , proj₂ sub k)
        rows (inj₂ p′) k =
          relUp m (≤ⁿ-step (≤ⁿ-refl m)) p′ (λ i → trmS i (sk k))
            (subst (λ r → RelP m p′ (λ i → trmS i r) (fo m ε ρ D₀ p′ (z (proj₁ (proj₁ sub k))))) (sym (skq k))
              (proj₁ (proj₂ (proj₁ sub k)) p′))
            (◃l zero)

        rows⊥ : ∀ k → M⁰ (trmS 0 (sk k)) (ψ⊥ ℓ ε ρ D (gL (vc (proj₁ (proj₁ sub k)))))
        rows⊥ k =
          mw (subst (λ r → M⁰ (trmS 0 r) (ψ⊥ (fin (suc m)) ε ρ D₀ (z (proj₁ (proj₁ sub k))))) (sym (skq k))
               (proj₂ (proj₂ (proj₁ sub k))))
             (◃l zero)

        leafCl : ClD s (Ω (inj₁ tt) gL)
        leafCl = (λ p → dropP p (slot≤ (suc m) p) (κ p) (rows p)) , bot⊥ (λ k → proj₁ (proj₁ sub k)) rows⊥

      tcLeaf : TCD (Ωᴺ N) (Ωt ℓ)
      tcLeaf K A₀ kn = subst (ClD (A₀ ++ Ωᴺ N)) (sym (eΩt K zero)) (Leaf.leafCl K A₀ kn)

      module Nx (b : E.T) (e : cof b ≡ c1) (Y : Tr ℓ) (nz : ℓ ⊢ zero ◃ Y) (hY : Ωt ℓ ⊴ Y)
                (tc : TCD (ψᴺ N (pred b)) Y) where
        p′ : E.PT
        p′ = ψ (natT N) (pred b)

        stepN : ∀ j K A₀ → KnD K A₀ → ClD (A₀ ++ replicate (suc j) p′) (⟦ K ⟧ (iter (Y +_) Y j))
        stepN zero    K A₀ kn = tc K A₀ kn
        stepN (suc j) K A₀ kn =
          subst (λ r → ClD r (⟦ K ⟧ (Y + iter (Y +_) Y j))) (++-assoc A₀ (p′ ∷ []) (replicate (suc j) p′))
            (stepN j (K ▸ Y) (A₀ ++ ψᴺ N (pred b)) (ext kn tc))

        nextL : TCD (ψᴺ N b) (next Y nz)
        nextL K A₀ kn =
          Cl-lim (cof++ω A₀ (ψᴺ N b) (cofψ1 (natT N) b e))
            (λ k → subst (λ r → ClD r (⟦ K ⟧ (next Y nz)))
              (sym (trans (fsn++ A₀ (ψᴺ N b) k (cofψ1 (natT N) b e)) (cong (A₀ ++_) (fsnψ1 (natT N) b k e))))
              (go k))
          where
          go : ∀ k → ClD (A₀ ++ replicate k p′) (⟦ K ⟧ (next Y nz))
          go zero    = subst (λ r → ClD r (⟦ K ⟧ (next Y nz))) (sym (++-identityʳ A₀))
                         (knCl kn (⟦ K ⟧ (next Y nz)) (c⊴ K (z⊴ (next Y nz)))
                           (rootΩ (suc m) ε ρ D g K (⟦ K ⟧ (next Y nz)) (c⊴ K (⊴◃ (⊴-◃ hY (◃l zero))))))
          go (suc j) = Cl-up◃ (stepN j K A₀ kn) (cm K (◃l j))

      Tu⁰ : (d : FD N zero) (b : Tr ℓ) (nb : ℓ ⊢ zero ◃ b) → Ωt ℓ ⊴ b → ∀ {t′} → TCD (ψᴺ N t′) b
          → ∀ {s y} → M⁰ s y → TCD (ψᴺ N (t′ ++ s)) (Up zero (dn d) b nb y)
      Tu⁰ d b nb hb {t′} tb (mz {x = y}) =
        ++[] (λ r → TCD (ψᴺ N r) (Up zero (dn d) b nb y)) t′ (tcUp⊴ tb (up⊵ zero (dn d) b nb y))
      Tu⁰ d b nb hb {t′} tb (m1 {t = s} {x = y} e r) =
        Nx.nextL (t′ ++ s) (cof++1 t′ s e) (Up zero (dn d) b nb y) (Up-nz zero (dn d) b nb y)
          (⊴-trans hb (up⊵ zero (dn d) b nb y))
          (subst (λ r′ → TCD (ψᴺ N r′) (Up zero (dn d) b nb y)) (sym (pred++ t′ s e)) (Tu⁰ d b nb hb tb r))
      Tu⁰ d b nb hb {t′} tb (mL {t = s} {x = y} e h) =
        tcLim (cofψω (natT N) (t′ ++ s) (cof++ω t′ s e))
          (λ k → subst (λ r′ → TCD r′ (Up zero (dn d) b nb y))
            (sym (trans (fsnψω (natT N) (t′ ++ s) k (cof++ω t′ s e)) (cong (ψᴺ N) (fsn++ t′ s k e))))
            (Tu⁰ d b nb hb tb (h k)))
      Tu⁰ d b nb hb tb (mΩ {p = ()} _ _ _)
      Tu⁰ d b nb hb tb (mU {c = ()} _ _)
      Tu⁰ d b nb hb tb (mw m′ r) = tcUp◃ (Tu⁰ d b nb hb tb m′) (Up-mono zero (dn d) b nb r)

      mutual
        Tu : ∀ j (d : FD N j) (b : Tr ℓ) (nb : ℓ ⊢ zero ◃ b) → Ωt ℓ ⊴ b → ∀ {t′} → TCD (ψᴺ N t′) b
           → ∀ {s y} → M j s y → TCD (ψᴺ N (t′ ++ s)) (Up (fin j) (dn d) b nb y)
        Tu zero    = Tu⁰
        Tu (suc j) = Tuˢ j

        Tuˢ : ∀ j (d : FD N (suc j)) (b : Tr ℓ) (nb : ℓ ⊢ zero ◃ b) → Ωt ℓ ⊴ b → ∀ {t′} → TCD (ψᴺ N t′) b
            → ∀ {s y} → M (suc j) s y → TCD (ψᴺ N (t′ ++ s)) (Up (fin (suc j)) (dn d) b nb y)
        Tuˢ j d b nb hb {t′} tb (mz {x = y}) =
          ++[] (λ r → TCD (ψᴺ N r) (Up (fin (suc j)) (dn d) b nb y)) t′
            (tcUp⊴ tb (up⊵ (fin (suc j)) (dn d) b nb y))
        Tuˢ j d b nb hb {t′} tb (m1 {t = s} {x = y} e r) =
          Nx.nextL (t′ ++ s) (cof++1 t′ s e) (Up (fin (suc j)) (dn d) b nb y) (Up-nz (fin (suc j)) (dn d) b nb y)
            (⊴-trans hb (up⊵ (fin (suc j)) (dn d) b nb y))
            (subst (λ r′ → TCD (ψᴺ N r′) (Up (fin (suc j)) (dn d) b nb y)) (sym (pred++ t′ s e))
              (Tuˢ j d b nb hb tb r))
        Tuˢ j d b nb hb {t′} tb (mL {t = s} {x = y} e h) =
          tcLim (cofψω (natT N) (t′ ++ s) (cof++ω t′ s e))
            (λ k → subst (λ r′ → TCD r′ (Up (fin (suc j)) (dn d) b nb y))
              (sym (trans (fsnψω (natT N) (t′ ++ s) k (cof++ω t′ s e)) (cong (ψᴺ N) (fsn++ t′ s k e))))
              (Tuˢ j d b nb hb tb (h k)))
        Tuˢ j d b nb hb {t′} tb (mΩ {t = s} {p = p} {g = gg} e nu h) =
          tcNode (mv (dn d) p) (λ c → Up (fin (suc j)) (dn d) b nb (gg (mvBr (dn d) p c)))
            (cofK (natT N) (t′ ++ s) (penN (suc m) (mv (dn d) p) (mvN d p nu)) (cof++Ω t′ s e)) (mvN d p nu)
            (λ η c l → subst (λ r′ → TCD r′ (Up (fin (suc j)) (dn d) b nb (gg (mvBr (dn d) p c))))
              (sym (trans (fsTK (natT N) (t′ ++ s) η (penN (suc m) (mv (dn d) p) (mvN d p nu)) (cof++Ω t′ s e))
                     (cong (ψᴺ N) (fsT++ t′ s η e))))
              (Tuˢ j d b nb hb tb (h η (mvBr (dn d) p c) (mvL d p c l))))
        Tuˢ j d b nb hb {t′} tb (mU {t = s₀} {s = s₁} {x = y₀} {y = y₁} m′ ch) =
          subst (λ r′ → TCD (ψᴺ N r′)
              (Up (fin j) (dn (fds d)) (Up (fin (suc j)) (dn d) b nb y₀) (Up-nz (fin (suc j)) (dn d) b nb y₀) y₁))
            (++-assoc t′ s₀ s₁)
            (Tu j (fds d) (Up (fin (suc j)) (dn d) b nb y₀) (Up-nz (fin (suc j)) (dn d) b nb y₀)
              (⊴-trans hb (up⊵ (fin (suc j)) (dn d) b nb y₀)) (Tuˢ j d b nb hb tb m′) ch)
        Tuˢ j d b nb hb tb (mw m′ r) = tcUp◃ (Tuˢ j d b nb hb tb m′) (Up-mono (fin (suc j)) (dn d) b nb r)

      module Mn (ε₀ : Ev ℓ) (ρ₀ : Rt ℓ) (D₀ : Base ℓ) (β : Tr ℓ) (nβ : ℓ ⊢ zero ◃ β) (hβ : Ωt ℓ ⊴ β) where
        open Self (suc m) ε₀ ρ₀ D₀ β nβ

        F⊵ : (x : Tr ℓ) → Ωt ℓ ⊴ F x
        F⊵ x = ⊴-trans hβ (cv⊴ (ψs-⊵ ℓ ε₀ ρ₀ D₀ ℓ self β nβ x))

        main : ∀ {P₀} → TCD (ψᴺ N P₀) β → ∀ {a x} → M N a x → TCD (ψᴺ N (P₀ ++ a)) (F x)
        main {P₀} tb (mz {x = x}) =
          ++[] (λ r → TCD (ψᴺ N r) (F x)) P₀ (tcUp⊴ tb (cv⊴ (ψs-⊵ ℓ ε₀ ρ₀ D₀ ℓ self β nβ x)))
        main {P₀} tb (m1 {t = a} {x = x} e r) =
          Nx.nextL (P₀ ++ a) (cof++1 P₀ a e) (F x) (nzF x) (F⊵ x)
            (subst (λ r′ → TCD (ψᴺ N r′) (F x)) (sym (pred++ P₀ a e)) (main tb r))
        main {P₀} tb (mL {t = a} {x = x} e h) =
          tcLim (cofψω (natT N) (P₀ ++ a) (cof++ω P₀ a e))
            (λ k → subst (λ r′ → TCD r′ (F x))
              (sym (trans (fsnψω (natT N) (P₀ ++ a) k (cof++ω P₀ a e)) (cong (ψᴺ N) (fsn++ P₀ a k e))))
              (main tb (h k)))
        main {P₀} tb (mΩ {t = a} {p = p} {g = gg} e nu h) =
          tcNode p (λ c → F (gg c)) (cofK (natT N) (P₀ ++ a) (penN (suc m) p nu) (cof++Ω P₀ a e)) nu
            (λ η c l → subst (λ r′ → TCD r′ (F (gg c)))
              (sym (trans (fsTK (natT N) (P₀ ++ a) η (penN (suc m) p nu) (cof++Ω P₀ a e))
                     (cong (ψᴺ N) (fsT++ P₀ a η e))))
              (main tb (h η c l)))
        main {P₀} tb (mU {t = s₀} {s = s₁} {x = x} {y = y} m′ ch) =
          subst (λ r′ → TCD (ψᴺ N r′) (Up (fin (suc m)) (dn (fds fd0)) (F x) (nzF x) y)) (++-assoc P₀ s₀ s₁)
            (Tu (suc m) (fds fd0) (F x) (nzF x) (F⊵ x) (main tb m′) ch)
        main tb (mw m′ d) = tcUp◃ (main tb m′) (monoF d)

    mk : Th m
    mk = record
      { tcUp   = λ ε ρ D g → Bs.tcUp◃ ε ρ D g
      ; tcLim  = λ ε ρ D g → Bs.tcLim ε ρ D g
      ; tcLimc = λ ε ρ D g → Bs.tcLimc ε ρ D g
      ; tcNode = λ ε ρ D g → Bs.tcNode ε ρ D g
      ; tcLeaf = λ ε ρ D g → Bs.tcLeaf ε ρ D g
      ; tcMain = λ ε ρ D g ε₀ ρ₀ D₀ β nβ hβ → Bs.Mn.main ε ρ D g ε₀ ρ₀ D₀ β nβ hβ
      }

  thB : ∀ m → Low m
  thB (suc m) j (s≤s le) with split≤ le
  ... | inj₁ refl = Level.mk m (thB m)
  ... | inj₂ lt   = thB m j lt

  th : ∀ m → Th m
  th m = Level.mk m (thB m)

  module Anchor (m : ℕ) (ε : Ev (fin (suc (suc (suc m))))) (ρ : Rt (fin (suc (suc (suc m)))))
                (B′ : Base (fin (suc (suc (suc m))))) (ok : OKB (fin (suc (suc (suc m)))) B′)
                (hp⊥ : M⁰ (ψᴺ 0 t) (b⊥ B′))
                (hp0 : (w : zero ≤ fin (suc (suc (suc m)))) → M⁰ (ψᴺ 0 t) (bs B′ zero w)) where
    private
      N : ℕ
      N = suc (suc m)

      ℓ : L
      ℓ = fin N

    Dᵃ : Base ℓ
    Dᵃ = dS ℓ ε ρ B′ zero

    gᵃ : Gd (suc m) Dᵃ
    gᵃ = gd-dS (suc m) ε ρ B′ (mkGd ok hp⊥ hp0) zero

    β : Tr ℓ
    β = bs B′ ℓ (ins self)

    nβ : ℓ ⊢ zero ◃ β
    nβ = ns B′ ℓ (ins self)

    hβ : Ωt ℓ ⊴ β
    hβ = cv⊴ (proj₂ ok ℓ (ins self))

    open Self (suc m) ε ρ Dᵃ β nβ public
    open Level.Bs m (thB m) ε ρ Dᵃ gᵃ

    W : Tr ℓ → Tr zero
    W x = ψ⊥ ℓ ε ρ Dᵃ x

    nzW : (x : Tr ℓ) → zero ⊢ zero ◃ W x
    nzW x = nz⊥ ℓ ε ρ Dᵃ x

    tcβ : TCD (ψᴺ N []) β
    tcβ = tcUp⊴ tcLeaf hβ

    hΩM : M N (Ωᴺ N) β
    hΩM = GM.m⊴ (suc m) (Mβ (suc m)) hβ

    rowW : ∀ k → M⁰ (ψᴺ 0 (t ++ ψᴺ 1 (gch [] k))) (W (F (z k)))
    rowW zero    = proj₂ (Mn.main ε ρ Dᵃ β nβ hβ tcβ (mz {x = zero}) • [] knRoot)
    rowW (suc k) = proj₂ (Mn.main ε ρ Dᵃ β nβ hβ tcβ (sγ hΩM hΩM k) • [] knRoot)

    form : ψ⊥ (suc ℓ) ε ρ B′ (Ωt (suc ℓ))
         ≡ limc (λ k → next (W (z k)) (nzW (z k))) (λ k → nz⊥ (suc ℓ) ε ρ B′ (up zero tt (suc (z k)) (z◃s (z k))))
    form = refl

    row : ∀ k → M⁰ (ψᴺ 0 (t ++ ψᴺ 1 (gch [] k))) (ψ⊥ (suc ℓ) ε ρ B′ (Ωt (suc ℓ)))
    row k =
      G⁰.m-cum (λ j → next (W (z j)) (nzW (z j))) (λ j → nz⊥ (suc ℓ) ε ρ B′ (up zero tt (suc (z j)) (z◃s (z j))))
        (suc k) (mw (mw (rowW k) (mono⊥ ℓ ε ρ Dᵃ (◃l zero))) (◃l zero))

    γ≡ : ∀ k → γT (Ωᴺ (suc N)) (natT N) k ≡ gch [] k
    γ≡ zero    = refl
    γ≡ (suc k) = cong (ψᴺ N) (trans (fsTΩ N (γT (Ωᴺ (suc N)) (natT N) k)) (γ≡ k))

    cΩ₁ : cof (ψᴺ 1 (Ωᴺ (suc N))) ≡ cω
    cΩ₁ = cofG (natT 1) (Ωᴺ (suc N)) (cmp-gt {b = 1} {a = N} (s≤s z≤n)) (cofΩ N)

    fΩ₁ : ∀ k → fsn (ψᴺ 1 (Ωᴺ (suc N))) k ≡ ψᴺ 1 (gch [] k)
    fΩ₁ k = trans (fsnG (natT 1) (Ωᴺ (suc N)) k (cmp-gt {b = 1} {a = N} (s≤s z≤n)) (cofΩ N))
              (cong (ψᴺ 1) (trans (fsTΩ N (γT (Ωᴺ (suc N)) (natT N) k)) (γ≡ k)))

    anchor : M⁰ (ψᴺ 0 (t ++ ψᴺ 1 (Ωᴺ (suc N)))) (ψ⊥ (suc ℓ) ε ρ B′ (Ωt (suc ℓ)))
    anchor = mL (cofψω [] (t ++ ψᴺ 1 (Ωᴺ (suc N))) (cof++ω t (ψᴺ 1 (Ωᴺ (suc N))) cΩ₁))
      (λ k → subst (λ r → M⁰ r (ψ⊥ (suc ℓ) ε ρ B′ (Ωt (suc ℓ))))
        (sym (trans (fsnψω [] (t ++ ψᴺ 1 (Ωᴺ (suc N))) k (cof++ω t (ψᴺ 1 (Ωᴺ (suc N))) cΩ₁))
               (cong (ψᴺ 0) (trans (fsn++ t (ψᴺ 1 (Ωᴺ (suc N))) k cΩ₁) (cong (t ++_) (fΩ₁ k))))))
        (row k))
```
