# YiBtVal 底座：按 `LF` 层号递归的逐点前序

**验收文件，档位：定义与编译定理 (引理)。** 关系族 `RelF K` 对层号 `K : LF` 递归 (后继层 `LvS`，极限层 `LvL`)，是 [YiLvAllRel](YiLvAllRel.lagda.md) 的 `Rel M` 从 `fin M` 推广到一切 `LF`；
参照一侧的层号与树一侧的层号只要求结构对应 (`Corr`，与 `≅ᴵ` 相容)，结点的起点对一切对应的层号陈述。另有对层间搬运封闭 (`TRC-all`)、
带关系的加法值域 `RA`、起点 `START` 与位置引理 `POS`, `posCorr` (都不需要层号类的前提)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiBtValRel where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
import OCF.Align.RR5IrrCore as B
open B using (module G; LF; Raw; Pre; Low; GdL)
open import OCF.Align.RR5IrrCheck using (cO)
open import OCF.Align.YiLvIf using (lev)
open import OCF.Align.YiLvFoldAdd using (Alg; shS; shL; rawAlg)
open import OCF.Align.YiLvAllRel using (R0; r0; TRC; module Back; TR0)
import OCF.Align.Level as L
open import OCF.Align.Value using (≼-refl)
open L using (_≅ᴵ_; _<ᴵ_)
```

## 1 参照一侧的层号与两种层

```agda
data Corr : L.Ordᴵ → LF → Set where
  cz : Corr L.zero B.zero
  cs : ∀ {a k} → Corr a k → Corr (L.suc a) (B.suc k)
  cl : ∀ {g s f} → (∀ n → Corr (g n) (f n)) → Corr (L.lim g s) (B.lim f)

Corr-≅ : ∀ {a b x} → a ≅ᴵ b → Corr b x → Corr a x
Corr-≅ L.z≅ cz = cz
Corr-≅ (L.s≅ e) (cs c) = cs (Corr-≅ e c)
Corr-≅ (L.l≅ h) (cl c) = cl (λ n → Corr-≅ (h n) (c n))

Corr-uniq : ∀ {a b x} → Corr a x → Corr b x → a ≅ᴵ b
Corr-uniq cz cz = L.z≅
Corr-uniq (cs c) (cs d) = L.s≅ (Corr-uniq c d)
Corr-uniq (cl c) (cl d) = L.l≅ (λ n → Corr-uniq (c n) (d n))

module LvS (k : LF)
  (Prev : ∀ {j} → L.Ordᶜ j → Raw k → Set)
  (PrevL : (r : Pre k) → ∀ {j} → L.Ordᶜ j → Low k r → Set) where

  SL : (s : Pre (B.suc k)) → ∀ {j} → L.Ordᶜ j → Low (B.suc k) s → Set
  SL (inj₁ _) = Prev
  SL (inj₂ r) = PrevL r

  infix 4 _⊴_
  data _⊴_ : ∀ {j} → L.Ordᶜ j → Raw (B.suc k) → Set where
    zr : ∀ {j} {η} → _⊴_ {j} L.zero η
    ssr : ∀ {j} {x : L.Ordᶜ j} {η} → x ⊴ η → L.suc x ⊴ G.suc η
    sr : ∀ {j} {x : L.Ordᶜ j} {η} → x ⊴ η → x ⊴ G.suc η
    lr : ∀ {j} {x : L.Ordᶜ j} {F : ℕ → Raw (B.suc k)} n → x ⊴ F n → x ⊴ G.lim F
    llr : ∀ {j} {F : ℕ → L.Ordᶜ j} {η} → (∀ n → F n ⊴ η) → L.lim F ⊴ η
    br : ∀ {j} {x : L.Ordᶜ j} {s c t}
      {g : (a : Low (B.suc k) s) → .(GdL (B.suc k) s c a) → Raw (B.suc k)} →
      (∀ .(e : GdL (B.suc k) s c c) → x ⊴ g c e) → x ⊴ G.lc s c t g
    ndr : ∀ {s c t} {g : (a : Low (B.suc k) s) → .(GdL (B.suc k) s c a) → Raw (B.suc k)}
      {j K} {q : j <ᴵ K} {f : L.U j (L.<→◃ q) → L.Ordᶜ K} →
      Corr j (lev (B.suc k) s) →
      (∀ {j′} → Corr j′ (lev (B.suc k) s) → SL s (L.Ω j′) c) →
      (∀ (y : L.Ordᶜ j) a .(e : GdL (B.suc k) s c a) → SL s y a →
        f (L.into (L.<→◃ q) y) ⊴ g a e) →
      L.limᵢ q f ⊴ G.lc s c t g
    ntr : ∀ {j K} {q : j <ᴵ K} {f : L.U j (L.<→◃ q) → L.Ordᶜ K} → Corr j k →
      (∀ {j′} → Corr j′ k → Prev (L.Ω j′) (cO k)) →
      (∀ (y : L.Ordᶜ j) a → Prev y a → f (L.into (L.<→◃ q) y) ⊴ G.em tt a) →
      L.limᵢ q f ⊴ G.top
    emr : ∀ {j} {y : L.Ordᶜ j} {a} → Prev y a → y ⊴ G.em tt a
    ur : ∀ {j} {y : L.Ordᶜ j} {η} → y ⊴ η → L.up {k = j} L.zero y ⊴ η
    us : ∀ {f : ℕ → L.Ordᴵ} {s′ : ∀ n → f n L.⊑ᴵ f (suc n)} {n} {y : L.Ordᶜ (f n)} {η} →
      y ⊴ η → L.up (L.self {f = f} {s = s′} n) y ⊴ η

module LvL (f : ℕ → LF)
  (Prev : ∀ n → ∀ {j} → L.Ordᶜ j → Raw (f n) → Set)
  (PrevL : ∀ n (r : Pre (f n)) → ∀ {j} → L.Ordᶜ j → Low (f n) r → Set) where

  SL : (s : Pre (B.lim f)) → ∀ {j} → L.Ordᶜ j → Low (B.lim f) s → Set
  SL (n , r) = PrevL n r

  infix 4 _⊴_
  data _⊴_ : ∀ {j} → L.Ordᶜ j → Raw (B.lim f) → Set where
    zrˡ : ∀ {j} {η} → _⊴_ {j} L.zero η
    ssrˡ : ∀ {j} {x : L.Ordᶜ j} {η} → x ⊴ η → L.suc x ⊴ G.suc η
    srˡ : ∀ {j} {x : L.Ordᶜ j} {η} → x ⊴ η → x ⊴ G.suc η
    lrˡ : ∀ {j} {x : L.Ordᶜ j} {F : ℕ → Raw (B.lim f)} n → x ⊴ F n → x ⊴ G.lim F
    llrˡ : ∀ {j} {F : ℕ → L.Ordᶜ j} {η} → (∀ n → F n ⊴ η) → L.lim F ⊴ η
    brˡ : ∀ {j} {x : L.Ordᶜ j} {s c t}
      {g : (a : Low (B.lim f) s) → .(GdL (B.lim f) s c a) → Raw (B.lim f)} →
      (∀ .(e : GdL (B.lim f) s c c) → x ⊴ g c e) → x ⊴ G.lc s c t g
    ndrˡ : ∀ {s c t} {g : (a : Low (B.lim f) s) → .(GdL (B.lim f) s c a) → Raw (B.lim f)}
      {j K} {q : j <ᴵ K} {h : L.U j (L.<→◃ q) → L.Ordᶜ K} →
      Corr j (lev (B.lim f) s) →
      (∀ {j′} → Corr j′ (lev (B.lim f) s) → SL s (L.Ω j′) c) →
      (∀ (y : L.Ordᶜ j) a .(e : GdL (B.lim f) s c a) → SL s y a →
        h (L.into (L.<→◃ q) y) ⊴ g a e) →
      L.limᵢ q h ⊴ G.lc s c t g
    emrˡ : ∀ {j} {y : L.Ordᶜ j} {n a} → Prev n y a → y ⊴ G.em n a
    tlrˡ : ∀ {j} {y : L.Ordᶜ j} n → Prev n y G.top → y ⊴ G.top
    urˡ : ∀ {j} {y : L.Ordᶜ j} {η} → y ⊴ η → L.up {k = j} L.zero y ⊴ η
    usˡ : ∀ {g : ℕ → L.Ordᴵ} {s′ : ∀ n → g n L.⊑ᴵ g (suc n)} {n} {y : L.Ordᶜ (g n)} {η} →
      y ⊴ η → L.up (L.self {f = g} {s = s′} n) y ⊴ η

open LvS public using (zr; ssr; sr; lr; llr; br; ndr; ntr; emr; ur; us)
open LvL public using (zrˡ; ssrˡ; srˡ; lrˡ; llrˡ; brˡ; ndrˡ; emrˡ; tlrˡ; urˡ; usˡ)

RelF : (K : LF) → ∀ {j} → L.Ordᶜ j → Raw K → Set
RelL : (K : LF) (r : Pre K) → ∀ {j} → L.Ordᶜ j → Low K r → Set
RelF B.zero = R0
RelF (B.suc k) = LvS._⊴_ k (RelF k) (RelL k)
RelF (B.lim f) = LvL._⊴_ f (λ n → RelF (f n)) (λ n → RelL (f n))
RelF (B.lc k c w b t g) y η = ⊥
RelL B.zero ()
RelL (B.suc k) = LvS.SL k (RelF k) (RelL k)
RelL (B.lim f) = LvL.SL f (λ n → RelF (f n)) (λ n → RelL (f n))
RelL (B.lc k c w b t g) r y a = ⊥
```

## 2 对层间搬运封闭

与 `YiLvAllRel.TRS` 同形，多出极限层的 `emrˡ`, `tlrˡ` 与 `up (self n)` 的 `us`。

```agda
module TRS (k : LF) (PT : TRC (RelF k)) (PLT : ∀ r → TRC (RelL k r)) where
  open LvS k (RelF k) (RelL k) using (SL; _⊴_)

  SLT : ∀ s → TRC (SL s)
  SLT (inj₁ _) = PT
  SLT (inj₂ r) = PLT r

  TR⁻ : ∀ {a b} (e : a ≅ᴵ b) {y : L.Ordᶜ b} {η} → y ⊴ η → L.tr⁻ e y ⊴ η
  TR⁺ : ∀ {a b} (e : a ≅ᴵ b) {y : L.Ordᶜ a} {η} → y ⊴ η → L.tr e y ⊴ η

  TR⁻ e zr = zr
  TR⁻ e (ssr r) = ssr (TR⁻ e r)
  TR⁻ e (sr r) = sr (TR⁻ e r)
  TR⁻ e (lr n r) = lr n (TR⁻ e r)
  TR⁻ e (llr h) = llr (λ n → TR⁻ e (h n))
  TR⁻ e (br h) = br (λ e′ → TR⁻ e (h e′))
  TR⁻ e (ndr {s = s} {g = g} {q = q} {f = f} lv base h) =
    ndr (Corr-≅ (L.≅ᴵ-sym (L.Restr.eq (L.res⁻ q e))) lv) base (λ y a e′ r →
      subst (λ w → L.tr⁻ e (f (L.into (L.<→◃ q) (L.Restr.back (L.res⁻ q e) w))) ⊴ g a e′)
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res⁻ q e))) y))
        (TR⁻ e (h (L.Restr.back (L.res⁻ q e) y) a e′ (Back.back⁻ᴿ (SLT s) q e r))))
  TR⁻ e (ntr {q = q} {f = f} lv base h) =
    ntr (Corr-≅ (L.≅ᴵ-sym (L.Restr.eq (L.res⁻ q e))) lv) base (λ y a r →
      subst (λ w → L.tr⁻ e (f (L.into (L.<→◃ q) (L.Restr.back (L.res⁻ q e) w))) ⊴ G.em tt a)
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res⁻ q e))) y))
        (TR⁻ e (h (L.Restr.back (L.res⁻ q e) y) a (Back.back⁻ᴿ PT q e r))))
  TR⁻ e (emr r) = emr (TRC.tr⁻ᴿ PT e r)
  TR⁻ (L.s≅ e) (ur r) = ur (TR⁻ e r)
  TR⁻ (L.l≅ h) (us {n = n} r) = us (TR⁻ (h n) r)

  TR⁺ e zr = zr
  TR⁺ e (ssr r) = ssr (TR⁺ e r)
  TR⁺ e (sr r) = sr (TR⁺ e r)
  TR⁺ e (lr n r) = lr n (TR⁺ e r)
  TR⁺ e (llr h) = llr (λ n → TR⁺ e (h n))
  TR⁺ e (br h) = br (λ e′ → TR⁺ e (h e′))
  TR⁺ e (ndr {s = s} {g = g} {q = q} {f = f} lv base h) =
    ndr (Corr-≅ (L.≅ᴵ-sym (L.Restr.eq (L.res q e))) lv) base (λ y a e′ r →
      subst (λ w → L.tr e (f (L.into (L.<→◃ q) (L.Restr.back (L.res q e) w))) ⊴ g a e′)
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res q e))) y))
        (TR⁺ e (h (L.Restr.back (L.res q e) y) a e′ (Back.backᴿ (SLT s) q e r))))
  TR⁺ e (ntr {q = q} {f = f} lv base h) =
    ntr (Corr-≅ (L.≅ᴵ-sym (L.Restr.eq (L.res q e))) lv) base (λ y a r →
      subst (λ w → L.tr e (f (L.into (L.<→◃ q) (L.Restr.back (L.res q e) w))) ⊴ G.em tt a)
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res q e))) y))
        (TR⁺ e (h (L.Restr.back (L.res q e) y) a (Back.backᴿ PT q e r))))
  TR⁺ e (emr r) = emr (TRC.trᴿ PT e r)
  TR⁺ (L.s≅ e) (ur r) = ur (TR⁺ e r)
  TR⁺ (L.l≅ h) (us {n = n} r) = us (TR⁺ (h n) r)

  trc : TRC (RelF (B.suc k))
  trc = record { tr⁻ᴿ = TR⁻ ; trᴿ = TR⁺ }

module TRL (f : ℕ → LF) (PT : ∀ n → TRC (RelF (f n))) (PLT : ∀ n r → TRC (RelL (f n) r)) where
  open LvL f (λ n → RelF (f n)) (λ n → RelL (f n)) using (SL; _⊴_)

  SLT : ∀ s → TRC (SL s)
  SLT (n , r) = PLT n r

  TR⁻ : ∀ {a b} (e : a ≅ᴵ b) {y : L.Ordᶜ b} {η} → y ⊴ η → L.tr⁻ e y ⊴ η
  TR⁺ : ∀ {a b} (e : a ≅ᴵ b) {y : L.Ordᶜ a} {η} → y ⊴ η → L.tr e y ⊴ η

  TR⁻ e zrˡ = zrˡ
  TR⁻ e (ssrˡ r) = ssrˡ (TR⁻ e r)
  TR⁻ e (srˡ r) = srˡ (TR⁻ e r)
  TR⁻ e (lrˡ n r) = lrˡ n (TR⁻ e r)
  TR⁻ e (llrˡ h) = llrˡ (λ n → TR⁻ e (h n))
  TR⁻ e (brˡ h) = brˡ (λ e′ → TR⁻ e (h e′))
  TR⁻ e (ndrˡ {s = s} {g = g} {q = q} {h = h₀} lv base h) =
    ndrˡ (Corr-≅ (L.≅ᴵ-sym (L.Restr.eq (L.res⁻ q e))) lv) base (λ y a e′ r →
      subst (λ w → L.tr⁻ e (h₀ (L.into (L.<→◃ q) (L.Restr.back (L.res⁻ q e) w))) ⊴ g a e′)
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res⁻ q e))) y))
        (TR⁻ e (h (L.Restr.back (L.res⁻ q e) y) a e′ (Back.back⁻ᴿ (SLT s) q e r))))
  TR⁻ e (emrˡ {n = n} r) = emrˡ (TRC.tr⁻ᴿ (PT n) e r)
  TR⁻ e (tlrˡ n r) = tlrˡ n (TRC.tr⁻ᴿ (PT n) e r)
  TR⁻ (L.s≅ e) (urˡ r) = urˡ (TR⁻ e r)
  TR⁻ (L.l≅ h) (usˡ {n = n} r) = usˡ (TR⁻ (h n) r)

  TR⁺ e zrˡ = zrˡ
  TR⁺ e (ssrˡ r) = ssrˡ (TR⁺ e r)
  TR⁺ e (srˡ r) = srˡ (TR⁺ e r)
  TR⁺ e (lrˡ n r) = lrˡ n (TR⁺ e r)
  TR⁺ e (llrˡ h) = llrˡ (λ n → TR⁺ e (h n))
  TR⁺ e (brˡ h) = brˡ (λ e′ → TR⁺ e (h e′))
  TR⁺ e (ndrˡ {s = s} {g = g} {q = q} {h = h₀} lv base h) =
    ndrˡ (Corr-≅ (L.≅ᴵ-sym (L.Restr.eq (L.res q e))) lv) base (λ y a e′ r →
      subst (λ w → L.tr e (h₀ (L.into (L.<→◃ q) (L.Restr.back (L.res q e) w))) ⊴ g a e′)
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res q e))) y))
        (TR⁺ e (h (L.Restr.back (L.res q e) y) a e′ (Back.backᴿ (SLT s) q e r))))
  TR⁺ e (emrˡ {n = n} r) = emrˡ (TRC.trᴿ (PT n) e r)
  TR⁺ e (tlrˡ n r) = tlrˡ n (TRC.trᴿ (PT n) e r)
  TR⁺ (L.s≅ e) (urˡ r) = urˡ (TR⁺ e r)
  TR⁺ (L.l≅ h) (usˡ {n = n} r) = usˡ (TR⁺ (h n) r)

  trc : TRC (RelF (B.lim f))
  trc = record { tr⁻ᴿ = TR⁻ ; trᴿ = TR⁺ }

TRC-all : ∀ K → TRC (RelF K)
TRC-L : ∀ K r → TRC (RelL K r)
TRC-all B.zero = TR0
TRC-all (B.suc k) = TRS.trc k (TRC-all k) (TRC-L k)
TRC-all (B.lim f) = TRL.trc f (λ n → TRC-all (f n)) (λ n → TRC-L (f n))
TRC-all (B.lc k c w b t g) = record { tr⁻ᴿ = λ e () ; trᴿ = λ e () }
TRC-L B.zero ()
TRC-L (B.suc k) (inj₁ _) = TRC-all k
TRC-L (B.suc k) (inj₂ r) = TRC-L k r
TRC-L (B.lim f) (n , r) = TRC-L (f n) r
TRC-L (B.lc k c w b t g) r = record { tr⁻ᴿ = λ e () ; trᴿ = λ e () }
```

## 3 带关系的加法值域

`RA A`：值域 `A` 上的关系与它的引入规则。`shRA`, `shLA` 沿 `shS`, `shL` 下移，投影定义性。

```agda
record RA {K : LF} (A : Alg K) : Set₁ where
  field
    ρ : ∀ {j} → L.Ordᶜ j → Alg.T A → Set
    rz : ∀ {j} {η} → ρ {j} L.zero η
    rss : ∀ {j} {x : L.Ordᶜ j} {η} → ρ x η → ρ (L.suc x) (Alg.sT A η)
    rs : ∀ {j} {x : L.Ordᶜ j} {η} → ρ x η → ρ x (Alg.sT A η)
    rl : ∀ {j} {x : L.Ordᶜ j} {F} n → ρ x (F n) → ρ x (Alg.lT A F)
    rll : ∀ {j} {F : ℕ → L.Ordᶜ j} {η} → (∀ n → ρ (F n) η) → ρ (L.lim F) η
    rb : ∀ {j} {x : L.Ordᶜ j} r c t g →
      (∀ .(e : GdL K r c c) → ρ x (g c e)) → ρ x (Alg.nT A r c t g)
    rnd : ∀ r c t g {j K′} {q : j <ᴵ K′} {f : L.U j (L.<→◃ q) → L.Ordᶜ K′} →
      Corr j (lev K r) → (∀ {j′} → Corr j′ (lev K r) → RelL K r (L.Ω j′) c) →
      (∀ (y : L.Ordᶜ j) a .(e : GdL K r c a) → RelL K r y a →
        ρ (f (L.into (L.<→◃ q) y)) (g a e)) →
      ρ (L.limᵢ q f) (Alg.nT A r c t g)
    ru : ∀ {j} {y : L.Ordᶜ j} {η} → ρ y η → ρ (L.up {k = j} L.zero y) η
    rus : ∀ {g : ℕ → L.Ordᴵ} {s′ : ∀ n → g n L.⊑ᴵ g (suc n)} {n} {y : L.Ordᶜ (g n)} {η} →
      ρ y η → ρ (L.up (L.self {f = g} {s = s′} n) y) η

shRA : ∀ {k} {A : Alg (B.suc k)} → RA A → RA (shS A)
shRA P = record
  { ρ = ρ; rz = rz; rss = rss; rs = rs; rl = rl; rll = rll
  ; rb = λ r → rb (inj₂ r); rnd = λ r → rnd (inj₂ r); ru = ru; rus = rus }
  where open RA P

shLA : ∀ {f} {A : Alg (B.lim f)} → RA A → ∀ n → RA (shL A n)
shLA P n = record
  { ρ = ρ; rz = rz; rss = rss; rs = rs; rl = rl; rll = rll
  ; rb = λ r → rb (n , r); rnd = λ r → rnd (n , r); ru = ru; rus = rus }
  where open RA P

rawRAS : ∀ k → RA (rawAlg (B.suc k))
rawRAS k = record
  { ρ = RelF (B.suc k); rz = zr; rss = ssr; rs = sr; rl = lr; rll = llr
  ; rb = λ r c t g h → br h
  ; rnd = λ r c t g lv base h → ndr lv base h
  ; ru = ur; rus = us }

rawRAL : ∀ f → RA (rawAlg (B.lim f))
rawRAL f = record
  { ρ = RelF (B.lim f); rz = zrˡ; rss = ssrˡ; rs = srˡ; rl = lrˡ; rll = llrˡ
  ; rb = λ r c t g h → brˡ h
  ; rnd = λ r c t g lv base h → ndrˡ lv base h
  ; ru = urˡ; rus = usˡ }
```

## 4 起点与位置

```agda
START : ∀ m {i} → Corr i m → RelF m (L.Ω i) (cO m)
STARTtop : ∀ m {i} → Corr i m → RelF m (L.Ω i) G.top
START B.zero cz = r0 (≼-refl _)
START (B.suc k) (cs c) = ntr c (START k) (λ y a r → ur (emr r))
START (B.lim f) (cl c) = llrˡ (λ n → usˡ (tlrˡ n (STARTtop (f n) (c n))))
STARTtop B.zero cz = r0 (≼-refl _)
STARTtop (B.suc k) c = START (B.suc k) c
STARTtop (B.lim f) c = START (B.lim f) c

POS : ∀ m s {j i} → Corr j (lev m s) → Corr i m → j L.≺ᴵ i
POS (B.suc k) (inj₁ _) cj (cs c) = L.via (Corr-uniq cj c) L.zero
POS (B.suc k) (inj₂ r) cj (cs c) with POS k r cj c
... | L.via e q = L.via e (L.suc q)
POS (B.lim f) (n , r) cj (cl c) with POS (f n) r cj (c n)
... | L.via e q = L.via e (L.lim n q)

posCorr : ∀ m {i a} → Corr i m → a <ᴵ i → Σ (Pre m) λ s → Corr a (lev m s)
posCorr (B.suc k) (cs c) L.zero = inj₁ tt , c
posCorr (B.suc k) (cs c) (L.suc q) with posCorr k c q
... | s , d = inj₂ s , d
posCorr (B.lim f) (cl c) (L.lim n q) with posCorr (f n) (c n) q
... | s , d = (n , s) , d
```
