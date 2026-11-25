# YiLvAll 底座：对一切层号一致的逐点前序

**验收文件，档位：定义与编译定理 (引理)。** 一个定义 `Rel M` 给出一切 `M` 的逐点前序 (`Level` 的树对 `Raw (sucᴹ 0)` 的值)；
结点槽位上的关系 `RelL M r` 对槽位递归，所以 `Low (sucᴹ 0) r` 不必搬成 `Raw`。参照一侧结点的层号只要求 `≅ᴵ` 于槽位的层号。
本篇还有起点 `START`、`natᴵ` 上的分类、对层间搬运封闭 (`TRC-all`)、带关系的加法值域 `RA`。入口 [YiLvAll](YiLvAll.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLvAllRel where

open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_; s≤s)
open import Data.Nat.Properties using (≤-refl; m<n⇒m<1+n; m≤n⇒m<n∨m≡n)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
import OCF.Align.RR5IrrCore as B
open B using (module G; LF; Raw; Pre; Low; GdL)
open import OCF.Align.RR5IrrCheck using (cO)
open import OCF.Align.YiIrrIf using (R)
open import OCF.Align.YiLvFoldAdd using (Alg; shS; rawAlg)
open import OCF.Align.YiLvFoldFin using (fin)
open import OCF.Align.YiIrrFoldValue using (read)
open import OCF.Align.YiLvValBase using (⟨_⟩)
import OCF.Align.Level as L
import OCF.Align.Value as V
open L using (_≅ᴵ_; _<ᴵ_)
open V using (_≼_; ≼-refl; ≼-trans; ≅→≼)
```

## 1 槽位的层号与关系族

`levN M r` 是槽位 `r` 上结点的层号。第 0 层的关系只认第 0 层的参照树 (`r0` 的下标)。
第 `N+1` 层的关系以第 `N` 层的关系与槽位关系为参数；`SL` 把槽位 `inj₁` 交给第 `N` 层，`inj₂ r` 交给第 `N` 层的槽位 `r`。

```agda
levN : ∀ M → Pre (fin M) → ℕ
levN zero ()
levN (suc N) (inj₁ _) = N
levN (suc N) (inj₂ r) = levN N r

levN< : ∀ M r → levN M r < M
levN< zero ()
levN< (suc N) (inj₁ _) = ≤-refl
levN< (suc N) (inj₂ r) = m<n⇒m<1+n (levN< N r)

data R0 : ∀ {k} → L.Ordᶜ k → R → Set where
  r0 : ∀ {y : L.Ordᶜ L.zero} {a} → y ≼ read a → R0 y a

un0 : ∀ {y : L.Ordᶜ L.zero} {a} → R0 y a → y ≼ read a
un0 (r0 q) = q

module Lv (N : ℕ)
  (Prev : ∀ {k} → L.Ordᶜ k → Raw (fin N) → Set)
  (PrevL : (r : Pre (fin N)) → ∀ {k} → L.Ordᶜ k → Low (fin N) r → Set) where

  SL : (s : Pre (fin (suc N))) → ∀ {k} → L.Ordᶜ k → Low (fin (suc N)) s → Set
  SL (inj₁ _) = Prev
  SL (inj₂ r) = PrevL r

  infix 4 _⊴_
  data _⊴_ : ∀ {k} → L.Ordᶜ k → Raw (fin (suc N)) → Set where
    zr : ∀ {k} {η} → _⊴_ {k} L.zero η
    ssr : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → L.suc x ⊴ G.suc η
    sr : ∀ {k} {x : L.Ordᶜ k} {η} → x ⊴ η → x ⊴ G.suc η
    lr : ∀ {k} {x : L.Ordᶜ k} {F : ℕ → Raw (fin (suc N))} n → x ⊴ F n → x ⊴ G.lim F
    llr : ∀ {k} {F : ℕ → L.Ordᶜ k} {η} → (∀ n → F n ⊴ η) → L.lim F ⊴ η
    br : ∀ {k} {x : L.Ordᶜ k} {s c t}
      {g : (a : Low (fin (suc N)) s) → .(GdL (fin (suc N)) s c a) → Raw (fin (suc N))} →
      (∀ .(e : GdL (fin (suc N)) s c c) → x ⊴ g c e) → x ⊴ G.lc s c t g
    ndr : ∀ {s c t} {g : (a : Low (fin (suc N)) s) → .(GdL (fin (suc N)) s c a) → Raw (fin (suc N))}
      {j K} {q : j <ᴵ K} {f : L.U j (L.<→◃ q) → L.Ordᶜ K} →
      j ≅ᴵ ⟨ levN (suc N) s ⟩ → SL s (L.Ω ⟨ levN (suc N) s ⟩) c →
      (∀ (y : L.Ordᶜ j) a .(e : GdL (fin (suc N)) s c a) → SL s y a →
        f (L.into (L.<→◃ q) y) ⊴ g a e) →
      L.limᵢ q f ⊴ G.lc s c t g
    ntr : ∀ {j K} {q : j <ᴵ K} {f : L.U j (L.<→◃ q) → L.Ordᶜ K} → j ≅ᴵ ⟨ N ⟩ →
      (∀ (y : L.Ordᶜ j) a → Prev y a → f (L.into (L.<→◃ q) y) ⊴ G.em tt a) →
      L.limᵢ q f ⊴ G.top
    emr : ∀ {k} {y : L.Ordᶜ k} {a} → Prev y a → y ⊴ G.em tt a
    ur : ∀ {k} {y : L.Ordᶜ k} {η} → y ⊴ η → L.up {k = k} L.zero y ⊴ η

open Lv public using (zr; ssr; sr; lr; llr; br; ndr; ntr; emr; ur)

Rel : (M : ℕ) → ∀ {k} → L.Ordᶜ k → Raw (fin M) → Set
RelL : (M : ℕ) (r : Pre (fin M)) → ∀ {k} → L.Ordᶜ k → Low (fin M) r → Set
Rel zero = R0
Rel (suc N) = Lv._⊴_ N (Rel N) (RelL N)
RelL zero ()
RelL (suc N) = Lv.SL N (Rel N) (RelL N)

START : ∀ M → Rel M (L.Ω ⟨ M ⟩) (cO (fin M))
START zero = r0 (≼-refl _)
START (suc N) = ntr (L.≅ᴵ-refl ⟨ N ⟩) (λ y a r → ur (emr r))
```

## 2 `natᴵ` 上的分类

`≅ᴵ` 在 `natᴵ` 上就是字面相等；`natᴵ m` 之下的字面证明给出 `ℕ` 的序。`<ᴵ-dec` 的三种结果由此读成 `ℕ` 的三歧。

```agda
nat-eq : ∀ {j} a → j ≅ᴵ L.natᴵ a → j ≡ L.natᴵ a
nat-eq zero L.z≅ = refl
nat-eq (suc a) (L.s≅ e) = cong L.suc (nat-eq a e)

nat-inj : ∀ a b → L.natᴵ a ≅ᴵ L.natᴵ b → a ≡ b
nat-inj zero zero e = refl
nat-inj (suc a) (suc b) (L.s≅ e) = cong suc (nat-inj a b e)
nat-inj zero (suc b) ()
nat-inj (suc a) zero ()

classify : ∀ m {a′} → a′ <ᴵ L.natᴵ m → Σ ℕ λ j → (a′ ≡ L.natᴵ j) × (j < m)
classify zero ()
classify (suc m) L.zero = m , refl , ≤-refl
classify (suc m) (L.suc r) =
  proj₁ (classify m r) , proj₁ (proj₂ (classify m r)) ,
  m<n⇒m<1+n (proj₂ (proj₂ (classify m r)))

below-nat : ∀ j m {a′} → L.natᴵ j ≅ᴵ a′ → a′ <ᴵ L.natᴵ m → j < m
below-nat j m e r =
  subst (λ z → z < m)
    (sym (nat-inj j (proj₁ (classify m r))
      (subst (λ w → L.natᴵ j ≅ᴵ w) (proj₁ (proj₂ (classify m r))) e)))
    (proj₂ (proj₂ (classify m r)))

slotOf : ∀ m j → j < m → Σ (Pre (fin m)) λ s → levN m s ≡ j
slotOf zero j ()
slotOf (suc m) j (s≤s le) with m≤n⇒m<n∨m≡n le
... | inj₁ lt = inj₂ (proj₁ (slotOf m j lt)) , proj₂ (slotOf m j lt)
... | inj₂ eq = inj₁ tt , sym eq
```

## 3 对层间搬运封闭

`TRC ρ`：`ρ` 对 `tr⁻ e`, `tr e` 封闭，对一切 `e`。结点处搬运把分支的输入经 `back (res⁻ q e)` 送回，那是 `e` 的子证明上的 `tr` 或 `tr⁻`，
所以槽位关系的封闭性 (低一层) 推出本层的封闭性。

```agda
record TRC {X : Set} (ρ : ∀ {k} → L.Ordᶜ k → X → Set) : Set where
  field
    tr⁻ᴿ : ∀ {a b} (e : a ≅ᴵ b) {y : L.Ordᶜ b} {η} → ρ y η → ρ (L.tr⁻ e y) η
    trᴿ : ∀ {a b} (e : a ≅ᴵ b) {y : L.Ordᶜ a} {η} → ρ y η → ρ (L.tr e y) η

module Back {X : Set} {ρ : ∀ {k} → L.Ordᶜ k → X → Set} (T : TRC ρ) where

  back⁻ᴿ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {y} {η} → ρ y η →
    ρ (L.Restr.back (L.res⁻ q e) y) η
  back⁻ᴿ L.zero (L.s≅ e) r = TRC.trᴿ T e r
  back⁻ᴿ (L.suc q) (L.s≅ e) r = back⁻ᴿ q e r
  back⁻ᴿ (L.lim n q) (L.l≅ h) r = back⁻ᴿ q (h n) r

  backᴿ : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {y} {η} → ρ y η →
    ρ (L.Restr.back (L.res q e) y) η
  backᴿ L.zero (L.s≅ e) r = TRC.tr⁻ᴿ T e r
  backᴿ (L.suc q) (L.s≅ e) r = backᴿ q e r
  backᴿ (L.lim n q) (L.l≅ h) r = backᴿ q (h n) r

tr0⁻ : ∀ {a} (e : a ≅ᴵ L.zero) {y : L.Ordᶜ L.zero} {η} → y ≼ read η → R0 (L.tr⁻ e y) η
tr0⁻ L.z≅ {y} q = r0 (≼-trans (≅→≼ (L.tr⁻-≅ L.z≅ (L.≅-refl⁰ y))) q)

tr0 : ∀ {b} (e : L.zero ≅ᴵ b) {y : L.Ordᶜ L.zero} {η} → y ≼ read η → R0 (L.tr e y) η
tr0 L.z≅ {y} q = r0 (≼-trans (≅→≼ (L.tr-≅ L.z≅ (L.≅-refl⁰ y))) q)

TR0 : TRC R0
TR0 = record { tr⁻ᴿ = λ e → go⁻ e ; trᴿ = λ e → go e }
  where
  go⁻ : ∀ {a b} (e : a ≅ᴵ b) {y : L.Ordᶜ b} {η} → R0 y η → R0 (L.tr⁻ e y) η
  go⁻ e (r0 q) = tr0⁻ e q
  go : ∀ {a b} (e : a ≅ᴵ b) {y : L.Ordᶜ a} {η} → R0 y η → R0 (L.tr e y) η
  go e (r0 q) = tr0 e q

module TRS (N : ℕ) (PT : TRC (Rel N)) (PLT : ∀ r → TRC (RelL N r)) where
  open Lv N (Rel N) (RelL N) using (SL; _⊴_)

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
    ndr (L.≅ᴵ-trans (L.≅ᴵ-sym (L.Restr.eq (L.res⁻ q e))) lv) base (λ y a e′ r →
      subst (λ w → L.tr⁻ e (f (L.into (L.<→◃ q) (L.Restr.back (L.res⁻ q e) w))) ⊴ g a e′)
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res⁻ q e))) y))
        (TR⁻ e (h (L.Restr.back (L.res⁻ q e) y) a e′ (Back.back⁻ᴿ (SLT s) q e r))))
  TR⁻ e (ntr {q = q} {f = f} lv h) =
    ntr (L.≅ᴵ-trans (L.≅ᴵ-sym (L.Restr.eq (L.res⁻ q e))) lv) (λ y a r →
      subst (λ w → L.tr⁻ e (f (L.into (L.<→◃ q) (L.Restr.back (L.res⁻ q e) w))) ⊴ G.em tt a)
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res⁻ q e))) y))
        (TR⁻ e (h (L.Restr.back (L.res⁻ q e) y) a (Back.back⁻ᴿ PT q e r))))
  TR⁻ e (emr r) = emr (TRC.tr⁻ᴿ PT e r)
  TR⁻ (L.s≅ e) (ur r) = ur (TR⁻ e r)

  TR⁺ e zr = zr
  TR⁺ e (ssr r) = ssr (TR⁺ e r)
  TR⁺ e (sr r) = sr (TR⁺ e r)
  TR⁺ e (lr n r) = lr n (TR⁺ e r)
  TR⁺ e (llr h) = llr (λ n → TR⁺ e (h n))
  TR⁺ e (br h) = br (λ e′ → TR⁺ e (h e′))
  TR⁺ e (ndr {s = s} {g = g} {q = q} {f = f} lv base h) =
    ndr (L.≅ᴵ-trans (L.≅ᴵ-sym (L.Restr.eq (L.res q e))) lv) base (λ y a e′ r →
      subst (λ w → L.tr e (f (L.into (L.<→◃ q) (L.Restr.back (L.res q e) w))) ⊴ g a e′)
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res q e))) y))
        (TR⁺ e (h (L.Restr.back (L.res q e) y) a e′ (Back.backᴿ (SLT s) q e r))))
  TR⁺ e (ntr {q = q} {f = f} lv h) =
    ntr (L.≅ᴵ-trans (L.≅ᴵ-sym (L.Restr.eq (L.res q e))) lv) (λ y a r →
      subst (λ w → L.tr e (f (L.into (L.<→◃ q) (L.Restr.back (L.res q e) w))) ⊴ G.em tt a)
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res q e))) y))
        (TR⁺ e (h (L.Restr.back (L.res q e) y) a (Back.backᴿ PT q e r))))
  TR⁺ e (emr r) = emr (TRC.trᴿ PT e r)
  TR⁺ (L.s≅ e) (ur r) = ur (TR⁺ e r)

  trc : TRC (Rel (suc N))
  trc = record { tr⁻ᴿ = TR⁻ ; trᴿ = TR⁺ }

TRC-all : ∀ M → TRC (Rel M)
TRC-L : ∀ M r → TRC (RelL M r)
TRC-all zero = TR0
TRC-all (suc N) = TRS.trc N (TRC-all N) (TRC-L N)
TRC-L zero ()
TRC-L (suc N) (inj₁ _) = TRC-all N
TRC-L (suc N) (inj₂ r) = TRC-L N r
```

## 4 带关系的加法值域

`RA A`：值域 `A` 上的一个关系与它的引入规则 (结点规则用槽位关系 `RelL`)。`shRA` 把它沿 `shS` 下移一层，投影是定义性的，
所以对变量深度的 `shS` 也成立；`rawRA N` 是 `Raw (sucᴺ⁺¹ 0)` 自己与 `Rel (N+1)`。

```agda
record RA {Lv : ℕ} (A : Alg (fin Lv)) : Set₁ where
  field
    ρ : ∀ {k} → L.Ordᶜ k → Alg.T A → Set
    rz : ∀ {k} {η} → ρ {k} L.zero η
    rss : ∀ {k} {x : L.Ordᶜ k} {η} → ρ x η → ρ (L.suc x) (Alg.sT A η)
    rs : ∀ {k} {x : L.Ordᶜ k} {η} → ρ x η → ρ x (Alg.sT A η)
    rl : ∀ {k} {x : L.Ordᶜ k} {F} n → ρ x (F n) → ρ x (Alg.lT A F)
    rll : ∀ {k} {F : ℕ → L.Ordᶜ k} {η} → (∀ n → ρ (F n) η) → ρ (L.lim F) η
    rb : ∀ {k} {x : L.Ordᶜ k} r c t g →
      (∀ .(e : GdL (fin Lv) r c c) → ρ x (g c e)) → ρ x (Alg.nT A r c t g)
    rnd : ∀ r c t g {j K} {q : j <ᴵ K} {f : L.U j (L.<→◃ q) → L.Ordᶜ K} →
      j ≅ᴵ ⟨ levN Lv r ⟩ → RelL Lv r (L.Ω ⟨ levN Lv r ⟩) c →
      (∀ (y : L.Ordᶜ j) a .(e : GdL (fin Lv) r c a) → RelL Lv r y a →
        ρ (f (L.into (L.<→◃ q) y)) (g a e)) →
      ρ (L.limᵢ q f) (Alg.nT A r c t g)
    ru : ∀ {k} {y : L.Ordᶜ k} {η} → ρ y η → ρ (L.up {k = k} L.zero y) η

shRA : ∀ {Lv} {A : Alg (fin (suc Lv))} → RA A → RA (shS A)
shRA P = record
  { ρ = ρ; rz = rz; rss = rss; rs = rs; rl = rl; rll = rll
  ; rb = λ r → rb (inj₂ r); rnd = λ r → rnd (inj₂ r); ru = ru }
  where open RA P

rawRA : ∀ N → RA (rawAlg (fin (suc N)))
rawRA N = record
  { ρ = Rel (suc N); rz = zr; rss = ssr; rs = sr; rl = lr; rll = llr
  ; rb = λ r c t g h → br h
  ; rnd = λ r c t g lv base h → ndr lv base h
  ; ru = ur }
```
