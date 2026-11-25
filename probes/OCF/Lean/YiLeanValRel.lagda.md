# YiLeanVal 底座：新块上按层号递归的逐点前序

**验收文件，档位：定义与编译定理 (引理)。** 关系族 `RelF K` (参照的树对第 `K` 层的树) 对层号 `K` 递归，各层是同一个带参数的归纳族 `Lvl`；参照层号与树的层号只要求结构对应 (`Corr`)。
另有起点 `START`、位置引理 `POS`、对层间搬运封闭 (`TRC-all`)，以及外部派发与参照一侧的比较一致 (`Agree`)，`cmp` 满足它 (`CMP`)。
不否定旧块上的写法 ([YiBtValRel](../Align/YiBtValRel.lagda.md))。主引理在 [YiLeanValFold](YiLeanValFold.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLeanValRel where

open import Data.Nat.Base using (ℕ; zero; suc; _⊔_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⊔m; ≤⇒≤′)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import Relation.Nullary using (¬_)
open import OCF.Lean.YiLeanCore
open import OCF.Lean.YiLeanFold
open import OCF.Lean.YiLeanAccFin using (read)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-refl; ≼-trans; ≅→≼; ≼l; l≼)
open L using (_≅ᴵ_; _<ᴵ_; _≺ᴵ_)
```

## 1 层号的对应与只含零、后继、极限的层号

```agda
data Corr : L.Ordᴵ → LF → Set where
  cz : Corr L.zero zero
  cs : ∀ {a k} → Corr a k → Corr (L.suc a) (suc k)
  cl : ∀ {g s f} → (∀ n → Corr (g n) (f n)) → Corr (L.lim g s) (lim f)

Corr-≅ : ∀ {a b x} → a ≅ᴵ b → Corr b x → Corr a x
Corr-≅ L.z≅ cz = cz
Corr-≅ (L.s≅ e) (cs c) = cs (Corr-≅ e c)
Corr-≅ (L.l≅ h) (cl c) = cl (λ n → Corr-≅ (h n) (c n))

Corr-uniq : ∀ {a b x} → Corr a x → Corr b x → a ≅ᴵ b
Corr-uniq cz cz = L.z≅
Corr-uniq (cs c) (cs d) = L.s≅ (Corr-uniq c d)
Corr-uniq (cl c) (cl d) = L.l≅ (λ n → Corr-uniq (c n) (d n))

POS : ∀ m (s : Pre m) {j i} → Corr j (lev m s) → Corr i m → j ≺ᴵ i
POS (suc k) (inj₁ _) cj (cs c) = L.via (Corr-uniq cj c) L.zero
POS (suc k) (inj₂ r) cj (cs c) = L.≺-suc (POS k r cj c)
POS (lim f) (n , r) cj (cl c) = L.≺-lim n (POS (f n) r cj (c n))

data Pl : LF → Set where
  pz : Pl zero
  ps : ∀ {k} → Pl k → Pl (suc k)
  pl : ∀ {f} → (∀ n → Pl (f n)) → Pl (lim f)

Lv→Pl : ∀ {k} → Lv k → Pl k
Lv→Pl v0 = pz
Lv→Pl (vs V) = ps (Lv→Pl V)
Lv→Pl (vl V st) = pl (λ n → Lv→Pl (V n))

Pl-lev : ∀ {k} → Pl k → ∀ r → Pl (lev k r)
Pl-lev (ps P) (inj₁ _) = P
Pl-lev (ps P) (inj₂ r) = Pl-lev P r
Pl-lev (pl P) (n , r) = Pl-lev (P n) r
```

## 2 关系族

`Lvl K`：第 `K` 层上的一般规则，孩子与槽位上的关系是参数 (`Kd`, `Sl`)。`top` 有两种规则：后继层号上 `top` 与根位置上分支为嵌入的结点折叠、加法都相同 (`tnr`，见 `YiLeanFold.top-as-node`)；
极限层号上 `top` 在各支的 `top` 之上 (`tlr`，经部分和)。第 0 层只认第 0 层的参照树 (对参照的层号分情况)。
`Ω` 结点层号上的关系取 `⊤`：验收只走只含零、后继、极限的层号 (`Pl`)。

```agda
module Lvl (K : LF)
  (Kd : (i : Kid K) → ∀ {j} → L.Ordᶜ j → Lay.A (KS K i) → Set)
  (Sl : (r : Pre K) → ∀ {j} → L.Ordᶜ j → Lay.A (Lo K r) → Set)
  (TN : Set) (tn : Raw K) (TL : Kid K → Set) where

  infix 4 _⊴_
  data _⊴_ : ∀ {j} → L.Ordᶜ j → Raw K → Set where
    zr : ∀ {j} {η} → _⊴_ {j} L.zero η
    ssr : ∀ {j} {x : L.Ordᶜ j} {η} → x ⊴ η → L.suc x ⊴ G.suc η
    sr : ∀ {j} {x : L.Ordᶜ j} {η} → x ⊴ η → x ⊴ G.suc η
    lr : ∀ {j} {x : L.Ordᶜ j} {F : ℕ → Raw K} n → x ⊴ F n → x ⊴ G.lim F
    llr : ∀ {j} {F : ℕ → L.Ordᶜ j} {η} → (∀ n → F n ⊴ η) → L.lim F ⊴ η
    br : ∀ {j} {x : L.Ordᶜ j} {r g} → x ⊴ g (Lay.tp (Lo K r)) → x ⊴ G.lc r g
    ndr : ∀ {r g} {j K′} {q : j <ᴵ K′} {f : L.U j (L.<→◃ q) → L.Ordᶜ K′} →
      Corr j (lev K r) → (∀ (y : L.Ordᶜ j) a → Sl r y a → f (L.into (L.<→◃ q) y) ⊴ g a) →
      L.limᵢ q f ⊴ G.lc r g
    emr : ∀ {j} {y : L.Ordᶜ j} {i a} → Kd i y a → y ⊴ G.em i a
    tnr : ∀ {j} {y : L.Ordᶜ j} → TN → y ⊴ tn → y ⊴ G.top
    tlr : ∀ {j} {y : L.Ordᶜ j} (i : Kid K) → TL i → Kd i y (Lay.tp (KS K i)) → y ⊴ G.top
    ur : ∀ {j} {y : L.Ordᶜ j} {η} → y ⊴ η → L.up {k = j} L.zero y ⊴ η
    us : ∀ {f : ℕ → L.Ordᴵ} {s′ : ∀ n → f n L.⊑ᴵ f (suc n)} {n} {y : L.Ordᶜ (f n)} {η} →
      y ⊴ η → L.up (L.self {f = f} {s = s′} n) y ⊴ η

open Lvl public using (zr; ssr; sr; lr; llr; br; ndr; emr; tnr; tlr; ur; us)

R0 : ∀ {j} → L.Ordᶜ j → Raw zero → Set
R0 {L.zero} y a = y ≼ read a
R0 {L.suc _} y a = ⊥
R0 {L.lim _ _} y a = ⊥

SLs : (k : LF) → (∀ {j} → L.Ordᶜ j → Raw k → Set) →
  ((r : Pre k) → ∀ {j} → L.Ordᶜ j → Lay.A (Lo k r) → Set) →
  (s : Pre (suc k)) → ∀ {j} → L.Ordᶜ j → Lay.A (Lo (suc k) s) → Set
SLs k P PL (inj₁ _) = P
SLs k P PL (inj₂ r) = PL r

SLl : (f : ℕ → LF) → (∀ n (r : Pre (f n)) → ∀ {j} → L.Ordᶜ j → Lay.A (Lo (f n) r) → Set) →
  (s : Pre (lim f)) → ∀ {j} → L.Ordᶜ j → Lay.A (Lo (lim f) s) → Set
SLl f PL (n , r) = PL n r

topS : ∀ k → Raw (suc k)
topS k = G.lc (inj₁ tt) (λ a → G.em tt a)

RelF : (K : LF) → ∀ {j} → L.Ordᶜ j → Raw K → Set
RelP : (K : LF) (r : Pre K) → ∀ {j} → L.Ordᶜ j → Lay.A (Lo K r) → Set
RelF zero = R0
RelF (suc k) = Lvl._⊴_ (suc k) (λ _ → RelF k) (SLs k (RelF k) (RelP k)) ⊤ (topS k) (λ _ → ⊥)
RelF (lim f) = Lvl._⊴_ (lim f) (λ n → RelF (f n)) (SLl f (λ n → RelP (f n))) ⊥ G.top (λ _ → ⊤)
RelF (lc k g) y a = ⊤
RelP zero ()
RelP (suc k) = SLs k (RelF k) (RelP k)
RelP (lim f) = SLl f (λ n → RelP (f n))
RelP (lc k g) (η , _ , r) = RelP (g η) r
```

## 3 起点、对任意目标层的两条规则

```agda
START : ∀ m {i} → Corr i m → RelF m (L.Ω i) G.top
START zero cz = ≼-refl _
START (suc k) (cs c) = tnr tt (ndr c (λ y a p → ur (emr p)))
START (lim f) (cl c) = llr (λ n → us (tlr n tt (START (f n) (c n))))

lr-any : ∀ m {j} {z : L.Ordᶜ j} {F : ℕ → Raw m} n → RelF m z (F n) → RelF m z (G.lim F)
lr-any zero {L.zero} n p = ≼l n p
lr-any (suc k) n p = lr n p
lr-any (lim f) n p = lr n p
lr-any (lc k g) n p = tt

llr-any : ∀ m {j} {F : ℕ → L.Ordᶜ j} {η} → (∀ n → RelF m (F n) η) → RelF m (L.lim F) η
llr-any zero {L.zero} h = l≼ h
llr-any zero {L.suc _} h = ⊥-elim (h 0)
llr-any zero {L.lim _ _} h = ⊥-elim (h 0)
llr-any (suc k) h = llr h
llr-any (lim f) h = llr h
llr-any (lc k g) h = tt
```

## 4 对层间搬运封闭

`TRC ρ`：`ρ` 对 `tr⁻ e`, `tr e` 封闭 (与 `YiLvAllRel.TRC` 同形，这里重写以免导入旧块)。

```agda
record TRC {X : Set} (ρ : ∀ {k} → L.Ordᶜ k → X → Set) : Set where
  field
    tr⁻ᴿ : ∀ {a b} (e : a ≅ᴵ b) {y : L.Ordᶜ b} {η} → ρ y η → ρ (L.tr⁻ e y) η
    trᴿ : ∀ {a b} (e : a ≅ᴵ b) {y : L.Ordᶜ a} {η} → ρ y η → ρ (L.tr e y) η

module Back {X : Set} {ρ : ∀ {k} → L.Ordᶜ k → X → Set} (T : TRC ρ) where
  back⁻ᴿ : ∀ {j a b} (q : j <ᴵ b) (e : a ≅ᴵ b) {y} {η} → ρ y η → ρ (L.Restr.back (L.res⁻ q e) y) η
  back⁻ᴿ L.zero (L.s≅ e) r = TRC.trᴿ T e r
  back⁻ᴿ (L.suc q) (L.s≅ e) r = back⁻ᴿ q e r
  back⁻ᴿ (L.lim n q) (L.l≅ h) r = back⁻ᴿ q (h n) r

  backᴿ : ∀ {j a b} (q : j <ᴵ a) (e : a ≅ᴵ b) {y} {η} → ρ y η → ρ (L.Restr.back (L.res q e) y) η
  backᴿ L.zero (L.s≅ e) r = TRC.tr⁻ᴿ T e r
  backᴿ (L.suc q) (L.s≅ e) r = backᴿ q e r
  backᴿ (L.lim n q) (L.l≅ h) r = backᴿ q (h n) r

TR0 : TRC R0
TR0 = record { tr⁻ᴿ = go⁻ ; trᴿ = go }
  where
  go⁻ : ∀ {a b} (e : a ≅ᴵ b) {y : L.Ordᶜ b} {η} → R0 y η → R0 (L.tr⁻ e y) η
  go⁻ L.z≅ {y} q = ≼-trans (≅→≼ (L.tr⁻-≅ L.z≅ (L.≅-refl⁰ y))) q
  go : ∀ {a b} (e : a ≅ᴵ b) {y : L.Ordᶜ a} {η} → R0 y η → R0 (L.tr e y) η
  go L.z≅ {y} q = ≼-trans (≅→≼ (L.tr-≅ L.z≅ (L.≅-refl⁰ y))) q

module TRG (K : LF)
  (Kd : (i : Kid K) → ∀ {j} → L.Ordᶜ j → Lay.A (KS K i) → Set)
  (Sl : (r : Pre K) → ∀ {j} → L.Ordᶜ j → Lay.A (Lo K r) → Set)
  (TN : Set) (tn : Raw K) (TL : Kid K → Set)
  (KT : ∀ i → TRC (Kd i)) (ST : ∀ r → TRC (Sl r)) where
  open Lvl K Kd Sl TN tn TL using (_⊴_)

  TR⁻ : ∀ {a b} (e : a ≅ᴵ b) {y : L.Ordᶜ b} {η} → y ⊴ η → L.tr⁻ e y ⊴ η
  TR⁻ e zr = zr
  TR⁻ e (ssr r) = ssr (TR⁻ e r)
  TR⁻ e (sr r) = sr (TR⁻ e r)
  TR⁻ e (lr n r) = lr n (TR⁻ e r)
  TR⁻ e (llr h) = llr (λ n → TR⁻ e (h n))
  TR⁻ e (br r) = br (TR⁻ e r)
  TR⁻ e (ndr {r = s} {g = g} {q = q} {f = f} lv h) =
    ndr (Corr-≅ (L.≅ᴵ-sym (L.Restr.eq (L.res⁻ q e))) lv) (λ y a r →
      subst (λ w → L.tr⁻ e (f (L.into (L.<→◃ q) (L.Restr.back (L.res⁻ q e) w))) ⊴ g a)
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res⁻ q e))) y))
        (TR⁻ e (h (L.Restr.back (L.res⁻ q e) y) a (Back.back⁻ᴿ (ST s) q e r))))
  TR⁻ e (emr {i = i} r) = emr (TRC.tr⁻ᴿ (KT i) e r)
  TR⁻ e (tnr t r) = tnr t (TR⁻ e r)
  TR⁻ e (tlr i t r) = tlr i t (TRC.tr⁻ᴿ (KT i) e r)
  TR⁻ (L.s≅ e) (ur r) = ur (TR⁻ e r)
  TR⁻ (L.l≅ h) (us {n = n} r) = us (TR⁻ (h n) r)

  TR⁺ : ∀ {a b} (e : a ≅ᴵ b) {y : L.Ordᶜ a} {η} → y ⊴ η → L.tr e y ⊴ η
  TR⁺ e zr = zr
  TR⁺ e (ssr r) = ssr (TR⁺ e r)
  TR⁺ e (sr r) = sr (TR⁺ e r)
  TR⁺ e (lr n r) = lr n (TR⁺ e r)
  TR⁺ e (llr h) = llr (λ n → TR⁺ e (h n))
  TR⁺ e (br r) = br (TR⁺ e r)
  TR⁺ e (ndr {r = s} {g = g} {q = q} {f = f} lv h) =
    ndr (Corr-≅ (L.≅ᴵ-sym (L.Restr.eq (L.res q e))) lv) (λ y a r →
      subst (λ w → L.tr e (f (L.into (L.<→◃ q) (L.Restr.back (L.res q e) w))) ⊴ g a)
        (sym (L.out-into (L.<→◃ (L.Restr.lt (L.res q e))) y))
        (TR⁺ e (h (L.Restr.back (L.res q e) y) a (Back.backᴿ (ST s) q e r))))
  TR⁺ e (emr {i = i} r) = emr (TRC.trᴿ (KT i) e r)
  TR⁺ e (tnr t r) = tnr t (TR⁺ e r)
  TR⁺ e (tlr i t r) = tlr i t (TRC.trᴿ (KT i) e r)
  TR⁺ (L.s≅ e) (ur r) = ur (TR⁺ e r)
  TR⁺ (L.l≅ h) (us {n = n} r) = us (TR⁺ (h n) r)

  trc : TRC _⊴_
  trc = record { tr⁻ᴿ = TR⁻ ; trᴿ = TR⁺ }

TRC-all : ∀ K → TRC (RelF K)
TRC-P : ∀ K r → TRC (RelP K r)
TRC-all zero = TR0
TRC-all (suc k) = TRG.trc (suc k) _ _ ⊤ (topS k) (λ _ → ⊥) (λ _ → TRC-all k) (TRC-P (suc k))
TRC-all (lim f) = TRG.trc (lim f) _ _ ⊥ G.top (λ _ → ⊤) (λ n → TRC-all (f n)) (TRC-P (lim f))
TRC-all (lc k g) = record { tr⁻ᴿ = λ _ _ → tt ; trᴿ = λ _ _ → tt }
TRC-P zero ()
TRC-P (suc k) (inj₁ _) = TRC-all k
TRC-P (suc k) (inj₂ r) = TRC-P k r
TRC-P (lim f) (n , r) = TRC-P (f n) r
TRC-P (lc k g) (η , _ , r) = TRC-P (g η) r
```

## 5 外部派发与参照的比较一致

`AgW w i`：派发 `w` 保留，则结点层号对应的参照层号在目标 `i` 之下；派发折叠，则不在之下。参照一侧的分情况 (`<ᴵ-dec`) 只看两个层号的 `≅ᴵ` 类，所以只用层号陈述。

```agda
AgW : ∀ {m J : LF} → Way m J → L.Ordᴵ → Set
AgW {J = J} (keep s e) i = ∀ {j} → Corr j J → j ≺ᴵ i
AgW {J = J} fold i = ∀ {j} → Corr j J → ¬ (j ≺ᴵ i)

Agree : ∀ {m K} → Ext m K → L.Ordᴵ → Set
Agree x i = ∀ r → AgW (x r) i

AgW-subst : ∀ {M M′ J J′} (e₁ : M ≡ M′) (e₂ : J ≡ J′) (w : Way M J) {i} → AgW w i → AgW (subst₂ Way e₁ e₂ w) i
AgW-subst refl refl w a = a

CMP : ∀ {k} (V : Lv k) q r {j} → Corr j (lev k q) → AgW (cmp V q r) j
CMP (vs V) (inj₁ _) (inj₂ r) c = λ c′ → POS _ r c′ c
CMP (vs V) (inj₂ q) (inj₂ r) c = CMP V q r c
CMP (vs V) (inj₁ _) (inj₁ _) c = λ c′ lt → L.≺ᴵ-irrefl (L.≺ᴵ-respˡ (Corr-uniq c c′) lt)
CMP (vs V) (inj₂ q) (inj₁ _) c = λ c′ lt → L.≺ᴵ-irrefl (L.≺ᴵ-trans lt (POS _ q c c′))
CMP (vl V st) (n , q) (m , r) c =
  AgW-subst (proj₂ (shift st (≤⇒≤′ (m≤m⊔n n m)) q)) (proj₂ (shift st (≤⇒≤′ (m≤n⊔m n m)) r)) _
    (CMP (V (n ⊔ m)) (proj₁ (shift st (≤⇒≤′ (m≤m⊔n n m)) q)) (proj₁ (shift st (≤⇒≤′ (m≤n⊔m n m)) r))
      (subst (Corr _) (sym (proj₂ (shift st (≤⇒≤′ (m≤m⊔n n m)) q))) c))

agree-fold : ∀ {K} → Agree {zero} {K} (λ _ → fold) L.zero
agree-fold r c (L.via e ())
```
