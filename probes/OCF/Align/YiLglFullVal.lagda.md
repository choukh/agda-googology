# 四处严格的规范构造：读回、Ω、塔与 Λ

只平行基础 Val，不迁移旧折叠。FullCore 的 Raw.lim/Raw.lc 已严格，
本篇 Legal 的 LF.lim/LF.lc 也分别要求 Properˢ 与 Dn→Properˢ。
第一支弱 CP 与守卫的下界等号保留；同坐标仍只要求守卫证据无关。
Ω̂、cO、up 的程序不变；严格证据随结构递归产生，无比较或事后挑列。
本篇所有类型属于新平行块，不能把旧 LF 的证据直接搬来使用。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiLglFullVal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Free.Level using (Ordᴵ)
import OCF.Free.Level as Lvl
open import OCF.Align.YiLglFullCore

up : (y : LF) → Raw y → LF
upT : LF → LF
cO : (k : LF) → Raw k
upK : (y : LF) (i : Kid y) → KidR y i → LF
upN : (y : LF) (r : Pre y) (c : Low y r) (t : LF) (g : (η : Low y r) → GdL y r c η → LF) → LF

upN (suc k) (inj₁ _) c t g = lc k c t g
upN (suc k) (inj₂ r) c t g = upN k r c t g
upN (lim f) (n , r) c t g = upN (f n) r c t g
upN (lc k c₀ t₀ g₀) (inj₁ (inj₁ _)) c t g = lc k c t g
upN (lc k c₀ t₀ g₀) (inj₁ (inj₂ r)) c t g = upN k r c t g
upN (lc k c₀ t₀ g₀) (inj₂ (inj₁ r)) c t g = upN t₀ r c t g
upN (lc k c₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c t g = upN (g₀ η e) r c t g

up y G.zero = zero
up y (G.suc a) = suc (up y a)
up y (G.lim f) = lim (λ n → up y (f n))
up y (G.lc r c t g) = upN y r c (up y t) (λ η e → up y (g η e))
up y (G.em i T) = upK y i T
up y G.top = upT y

upK (suc k) _ T = up k T
upK (lim f) n T = up (f n) T
upK (lc k c t g) (inj₁ _) T = up k T
upK (lc k c t g) (inj₂ (inj₁ _)) T = up t T
upK (lc k c t g) (inj₂ (inj₂ (η , e))) T = up (g η e) T

cO zero = G.suc G.zero
cO (suc k) = G.top
cO (lim f) = G.top
cO (lc k c t g) = G.top

upT zero = suc zero
upT (suc k) = lc k (cO k) (upT k) (λ η e → up k η)
upT (lim f) = lim (λ n → upT (f n))
upT (lc k c t g) = lc k c (upT t) (λ η e → upT (g η e))

Ω̂ : LF → LF
Ω̂ = upT

Ω̂-zero : Ω̂ zero ≡ suc zero
Ω̂-zero = refl

Ω̂-suc : ∀ k → Ω̂ (suc k) ≡ lc k (cO k) (Ω̂ k) (λ η e → up k η)
Ω̂-suc k = refl

Ω̂-lim : ∀ f → Ω̂ (lim f) ≡ lim (λ n → Ω̂ (f n))
Ω̂-lim f = refl

Ω̂-lc : ∀ k c t g → Ω̂ (lc k c t g) ≡ lc k c (Ω̂ t) (λ η e → Ω̂ (g η e))
Ω̂-lc k c t g = refl

natF : ℕ → LF
natF zero = zero
natF (suc n) = suc (natF n)

infixl 6 _+ᴸ_
_+ᴸ_ : LF → LF → LF
a +ᴸ zero = a
a +ᴸ suc b = suc (a +ᴸ b)
a +ᴸ lim f = lim (λ n → a +ᴸ f n)
a +ᴸ lc k c t g = lc k c (a +ᴸ t) (λ η e → a +ᴸ g η e)

tw : ℕ → LF
tw zero = zero
tw (suc n) = Ω̂ (tw n)

Λ : LF
Λ = lim tw

-- 验收目标 1 的值. 都是同一个类型, 同一个定义.
Ω₁ Ω₂ Ω₃ Ωω : LF
Ω₁ = Ω̂ (natF 1)
Ω₂ = Ω̂ (natF 2)
Ω₃ = Ω̂ (natF 3)
Ωω = Ω̂ (lim natF)

Ω₁+1 Ω₁·2 ΩΩ₂ : LF
Ω₁+1 = suc Ω₁
Ω₁·2 = Ω₁ +ᴸ Ω₁
ΩΩ₂ = Ω̂ Ω₂

-- Ω_{Ω_η}, η 是任意层号, 不限于可数
ΩΩ : LF → LF
ΩΩ η = Ω̂ (Ω̂ η)

Λ-form : Λ ≡ lim tw
Λ-form = refl

fix-form : Ω̂ Λ ≡ lim (λ n → tw (suc n))
fix-form = refl

tw-2 : tw 2 ≡ lc zero (G.suc G.zero) (suc zero) (λ η e → up zero η)
tw-2 = refl

-- 任何层号的 Ω_{x+1} 都有分支: 下界的后继
ofI : Ordᴵ → LF
ofI Lvl.zero = zero
ofI (Lvl.suc a) = suc (ofI a)
ofI (Lvl.lim f s) = lim (λ n → ofI (f n))

ΩΩᴵ : Ordᴵ → LF
ΩΩᴵ η = Ω̂ (Ω̂ (ofI η))

data CP : LF → LF → Set where
  self : ∀ {a} → CP a a
  suc  : ∀ {a b} → CP a b → CP a (suc b)
  lim  : ∀ {a f} n → CP a (f n) → CP a (lim f)
  fst  : ∀ {a k c t g} → CP a t → CP a (lc k c t g)

CP-tr : ∀ {a b d} → CP a b → CP b d → CP a d
CP-tr p self = p
CP-tr p (suc q) = suc (CP-tr p q)
CP-tr p (lim n q) = lim n (CP-tr p q)
CP-tr p (fst q) = fst (CP-tr p q)

data Properˢ : LF → LF → Set where
  under-suc : ∀ {a b} → CP a b → Properˢ a (suc b)
  under-lim : ∀ {a f} n → CP a (f n) → Properˢ a (lim f)
  under-first : ∀ {a k c t g} → CP a t → Properˢ a (lc k c t g)

weak : ∀ {a b} → Properˢ a b → CP a b
weak (under-suc p) = suc p
weak (under-lim n p) = lim n p
weak (under-first p) = fst p


Legal : LF → Set
Legal zero = ⊤
Legal (suc k) = Legal k
Legal (lim f) = (∀ n → Properˢ (f n) (f (suc n))) × (∀ n → Legal (f n))
Legal (lc k c t g) =
  Legal k ×
  (∀ η e → CP t (g η e)) ×
  (∀ η e η′ e′ → Dn k η η′ → Properˢ (g η e) (g η′ e′)) ×
  (∀ η e e′ → g η e ≡ g η e′) ×
  Legal t × (∀ η e → Legal (g η e))

fstN : ∀ y r c t g {a} → CP a t → CP a (upN y r c t g)
fstN (suc k) (inj₁ _) c t g p = fst p
fstN (suc k) (inj₂ r) c t g p = fstN k r c t g p
fstN (lim f) (n , r) c t g p = fstN (f n) r c t g p
fstN (lc k c₀ t₀ g₀) (inj₁ (inj₁ _)) c t g p = fst p
fstN (lc k c₀ t₀ g₀) (inj₁ (inj₂ r)) c t g p = fstN k r c t g p
fstN (lc k c₀ t₀ g₀) (inj₂ (inj₁ r)) c t g p = fstN t₀ r c t g p
fstN (lc k c₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c t g p = fstN (g₀ η e) r c t g p

cp→CP : ∀ y {a b} → Cp y a b → CP (up y a) (up y b)
dn→CP : ∀ y {a} b → Dn y a b → CP (up y a) (up y b)
dnk→CP : ∀ y i i′ {a b} → DnK y i i′ a b → CP (upK y i a) (upK y i′ b)

cp→CP y (inj₁ refl) = self
cp→CP y {b = b} (inj₂ p) = dn→CP y b p

dn→CP y (G.suc b) p = suc (cp→CP y p)
dn→CP y (G.lim f) (n , p) = lim n (cp→CP y p)
dn→CP y (G.lc r c t g) p = fstN y r c _ _ (cp→CP y p)
dn→CP y {a = G.em i′ _} (G.em i T) p = dnk→CP y i′ i p
dn→CP (suc k) {G.em _ _} G.top p = fst (cp→CP k p)
dn→CP (lc k c t g) {G.em (inj₂ (inj₁ _)) _} G.top p = fst (cp→CP t p)

dnk→CP (suc k) _ _ {b = b} p = dn→CP k b p
dnk→CP (lim f) n .n {b = b} (refl , p) = dn→CP (f n) b p
dnk→CP (lc k c t g) (inj₁ _) (inj₁ _) {b = b} p = dn→CP k b p
dnk→CP (lc k c t g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) {b = b} p = dn→CP t b p
dnk→CP (lc k c t g) (inj₂ (inj₂ (η , e))) (inj₂ (inj₂ .(η , e))) {b = b} (refl , p) = dn→CP (g η e) b p

firstN : ∀ y r c t g {a} → CP a t → Properˢ a (upN y r c t g)
firstN (suc k) (inj₁ _) c t g p = under-first p
firstN (suc k) (inj₂ r) c t g p = firstN k r c t g p
firstN (lim f) (n , r) c t g p = firstN (f n) r c t g p
firstN (lc k c₀ t₀ g₀) (inj₁ (inj₁ _)) c t g p = under-first p
firstN (lc k c₀ t₀ g₀) (inj₁ (inj₂ r)) c t g p = firstN k r c t g p
firstN (lc k c₀ t₀ g₀) (inj₂ (inj₁ r)) c t g p = firstN t₀ r c t g p
firstN (lc k c₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c t g p = firstN (g₀ η e) r c t g p

dn-proper : ∀ y {a} b → Dn y a b → Properˢ (up y a) (up y b)
dnk-proper : ∀ y i i′ {a b} → DnK y i i′ a b → Properˢ (upK y i a) (upK y i′ b)
dn-proper y (G.suc b) p = under-suc (cp→CP y p)
dn-proper y (G.lim f) (n , p) = under-lim n (cp→CP y p)
dn-proper y (G.lc r c t g) p = firstN y r c _ _ (cp→CP y p)
dn-proper y {a = G.em i′ _} (G.em i T) p = dnk-proper y i′ i p
dn-proper (suc k) {G.em _ _} G.top p = under-first (cp→CP k p)
dn-proper (lc k c t g) {G.em (inj₂ (inj₁ _)) _} G.top p = under-first (cp→CP t p)
dnk-proper (suc k) _ _ {b = b} p = dn-proper k b p
dnk-proper (lim f) n .n {b = b} (refl , p) = dn-proper (f n) b p
dnk-proper (lc k c t g) (inj₁ _) (inj₁ _) {b = b} p = dn-proper k b p
dnk-proper (lc k c t g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) {b = b} p = dn-proper t b p
dnk-proper (lc k c t g) (inj₂ (inj₂ (η , e))) (inj₂ (inj₂ .(η , e))) {b = b} (refl , p) = dn-proper (g η e) b p


legalN : ∀ y r c t g → Legal y →
  (∀ η e → CP t (g η e)) →
  (∀ η e η′ e′ → DnL y r η η′ → Properˢ (g η e) (g η′ e′)) →
  (∀ η e e′ → g η e ≡ g η e′) →
  Legal t → (∀ η e → Legal (g η e)) → Legal (upN y r c t g)
legalN (suc k) (inj₁ _) c t g L a b i u v = L , a , b , i , u , v
legalN (suc k) (inj₂ r) c t g L a b i u v = legalN k r c t g L a b i u v
legalN (lim f) (n , r) c t g L a b i u v = legalN (f n) r c t g (proj₂ L n) a b i u v
legalN (lc k c₀ t₀ g₀) (inj₁ (inj₁ _)) c t g L a b i u v = proj₁ L , a , b , i , u , v
legalN (lc k c₀ t₀ g₀) (inj₁ (inj₂ r)) c t g L a b i u v = legalN k r c t g (proj₁ L) a b i u v
legalN (lc k c₀ t₀ g₀) (inj₂ (inj₁ r)) c t g (_ , _ , _ , _ , lt , _) a b i u v = legalN t₀ r c t g lt a b i u v
legalN (lc k c₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c t g (_ , _ , _ , _ , _ , lg) a b i u v = legalN (g₀ η e) r c t g (lg η e) a b i u v

cO-CP : ∀ k {η} → Cp k (cO k) η → CP (Ω̂ k) (up k η)
cO-CP zero p = cp→CP zero p
cO-CP (suc k) p = cp→CP (suc k) p
cO-CP (lim f) p = cp→CP (lim f) p
cO-CP (lc k c t g) p = cp→CP (lc k c t g) p

Ω̂-CP : ∀ {a b} → CP a b → CP (Ω̂ a) (Ω̂ b)
Ω̂-CP self = self
Ω̂-CP (suc p) = fst (Ω̂-CP p)
Ω̂-CP (lim n p) = lim n (Ω̂-CP p)
Ω̂-CP (fst p) = fst (Ω̂-CP p)

Ω-proper : ∀ {a b} → Properˢ a b → Properˢ (Ω̂ a) (Ω̂ b)
Ω-proper (under-suc p) = under-first (Ω̂-CP p)
Ω-proper (under-lim n p) = under-lim n (Ω̂-CP p)
Ω-proper (under-first p) = under-first (Ω̂-CP p)


Legal-Ω̂ : ∀ x → Legal x → Legal (Ω̂ x)
lgl→Legal : ∀ y → Legal y → ∀ T → Lgl y T → Legal (up y T)
lglK→Legal : ∀ y → Legal y → ∀ i T → LglK y i T → Legal (upK y i T)

Legal-Ω̂ zero w = tt
Legal-Ω̂ (suc k) w =
  w ,
  (λ η e → cO-CP k (proj₁ e)) ,
  (λ η e η′ e′ d → dn-proper k η′ d) ,
  (λ η e e′ → refl) ,
  Legal-Ω̂ k w ,
  (λ η e → lgl→Legal k w η (proj₂ e))
Legal-Ω̂ (lim f) (st , w) = (λ n → Ω-proper (st n)) , (λ n → Legal-Ω̂ (f n) (w n))
Legal-Ω̂ (lc k c t g) (Lk , tg , dir , irr , wt , wg) =
  Lk ,
  (λ η e → Ω̂-CP (tg η e)) ,
  (λ η e η′ e′ d → Ω-proper (dir η e η′ e′ d)) ,
  (λ η e e′ → cong Ω̂ (irr η e e′)) ,
  Legal-Ω̂ t wt ,
  (λ η e → Legal-Ω̂ (g η e) (wg η e))

lgl→Legal y L G.zero w = tt
lgl→Legal y L (G.suc a) w = lgl→Legal y L a w
lgl→Legal y L (G.lim f) (st , w) = (λ n → dn-proper y (f (suc n)) (st n)) , (λ n → lgl→Legal y L (f n) (w n))
lgl→Legal y L (G.lc r c t g) (tg , dir , irr , lt , lg) =
  legalN y r c (up y t) (λ η e → up y (g η e)) L
    (λ η e → cp→CP y (tg η e))
    (λ η e η′ e′ d → dn-proper y (g η′ e′) (dir η e η′ e′ d))
    (λ η e e′ → cong (up y) (irr η e e′))
    (lgl→Legal y L t lt)
    (λ η e → lgl→Legal y L (g η e) (lg η e))
lgl→Legal y L (G.em i T) w = lglK→Legal y L i T w
lgl→Legal y L G.top w = Legal-Ω̂ y L

lglK→Legal (suc k) L _ T w = lgl→Legal k L T w
lglK→Legal (lim f) L n T w = lgl→Legal (f n) (proj₂ L n) T w
lglK→Legal (lc k c t g) L (inj₁ _) T w = lgl→Legal k (proj₁ L) T w
lglK→Legal (lc k c t g) (_ , _ , _ , _ , lt , _) (inj₂ (inj₁ _)) T w = lgl→Legal t lt T w
lglK→Legal (lc k c t g) (_ , _ , _ , _ , _ , lg) (inj₂ (inj₂ (η , e))) T w = lgl→Legal (g η e) (lg η e) T w

Lgl-cO : ∀ k → Lgl k (cO k)
Lgl-cO zero = tt
Lgl-cO (suc k) = tt
Lgl-cO (lim f) = tt
Lgl-cO (lc k c t g) = tt

-- 分支不空: 对一切 k, 下界的后继过守卫
branch : ∀ k → Gd k (cO k) (G.suc (cO k))
branch k = inj₂ (inj₁ refl) , Lgl-cO k

tw-step : ∀ n → Properˢ (tw n) (tw (suc n))
tw-step zero = under-suc self
tw-step (suc n) = Ω-proper (tw-step n)

Legal-tw : ∀ n → Legal (tw n)
Legal-tw zero = tt
Legal-tw (suc n) = Legal-Ω̂ (tw n) (Legal-tw n)

Legal-Λ : Legal Λ
Legal-Λ = tw-step , Legal-tw

Legal-ΩΛ : Legal (Ω̂ Λ)
Legal-ΩΛ = Legal-Ω̂ Λ Legal-Λ

natF-step : ∀ n → Properˢ (natF n) (natF (suc n))
natF-step n = under-suc self

Legal-nat : ∀ n → Legal (natF n)
Legal-nat zero = tt
Legal-nat (suc n) = Legal-nat n

Legal-ω : Legal (lim natF)
Legal-ω = natF-step , Legal-nat

Legal-Ωω : Legal Ωω
Legal-Ωω = Legal-Ω̂ (lim natF) Legal-ω

Legal-Ω₂ : Legal Ω₂
Legal-Ω₂ = Legal-Ω̂ (natF 2) tt

Legal-ΩΩ₂ : Legal ΩΩ₂
Legal-ΩΩ₂ = Legal-Ω̂ Ω₂ Legal-Ω₂

Legal-ΩΩ : ∀ η → Legal η → Legal (ΩΩ η)
Legal-ΩΩ η w = Legal-Ω̂ (Ω̂ η) (Legal-Ω̂ η w)

-- ofI 对一切 η 有值 (ΩΩᴵ η 是闭项); 合法性要 Ordᴵ 的步进是字面的第一位置. Ordᴵ 的 lim 只带 ⊑ᴵ, 所以这是条件.
Legal-ΩΩᴵ : ∀ η → Legal (ofI η) → Legal (ΩΩᴵ η)
Legal-ΩΩᴵ η w = Legal-ΩΩ (ofI η) w

add-CP : ∀ x {a b} → CP a b → CP (x +ᴸ a) (x +ᴸ b)
add-CP x self = self
add-CP x (suc p) = suc (add-CP x p)
add-CP x (lim n p) = lim n (add-CP x p)
add-CP x (fst p) = fst (add-CP x p)

add-proper : ∀ x {a b} → Properˢ a b → Properˢ (x +ᴸ a) (x +ᴸ b)
add-proper x (under-suc p) = under-suc (add-CP x p)
add-proper x (under-lim n p) = under-lim n (add-CP x p)
add-proper x (under-first p) = under-first (add-CP x p)

Legal-add : ∀ x a → Legal x → Legal a → Legal (x +ᴸ a)
Legal-add x zero w u = w
Legal-add x (suc a) w u = Legal-add x a w u
Legal-add x (lim f) w (st , u) = (λ n → add-proper x (st n)) , (λ n → Legal-add x (f n) w (u n))
Legal-add x (lc k c t g) w (Lk , tg , dir , irr , wt , wg) =
  Lk ,
  (λ η e → add-CP x (tg η e)) ,
  (λ η e η′ e′ d → add-proper x (dir η e η′ e′ d)) ,
  (λ η e e′ → cong (x +ᴸ_) (irr η e e′)) ,
  Legal-add x t w wt ,
  (λ η e → Legal-add x (g η e) w (wg η e))
```
