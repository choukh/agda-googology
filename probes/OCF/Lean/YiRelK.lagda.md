# 对目标层 k 一般的读回关系 `Rel k`

验收文件. 关系族 `Rel k : L.Ordᶜ ℓ → Raw (Lk k) → Set` 对 k ∈ ℕ 递归 (第 0 层是值 `R0`, 第 k+1 层是一个带参数的归纳族 `L1._⊴_`), 槽位关系 `Hyp` 与它互递归; 对角规则 `dg` 在每层层号 0 的槽位上 (`Z0`), 门槛 `top + Tw 2`.
编译定理, 对一切 k 一条: `Rel-cp` (右边沿第一位置上移), `lfR` / `Rel-+ˡ` (左加), `shR` / `Rel-+ʳ` (右加), `adR` / `Rel-add` (加法上下文), `Rel-ω` (ω 倍), `Ω⊴top`. 不陈述值; 与 `⊴⁺`, `⊴²` 的对应在 [YiRelKInst](YiRelKInst.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiRelK where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)
open import OCF.Lean.YiNextCore hiding (Le)
open import OCF.Lean.YiNextBase
import OCF.Lean.YiDlFold as W
import OCF.Lean.YiNextAcc as NA
open import OCF.Lean.YiDlVOne using (cp≼)
import OCF.Align.Level as L
open import OCF.Align.Value using (_≼_; ≼-trans; z≼; s≼s; ≼l; l≼; ≼i; i≼; ≼u; u≼)
open import OCF.BTBO using (module Ord-Ord)
open Ord-Ord using () renaming (iter to iterᴸ)
```

## 1 层号, 槽位的参照层号, 层号 0 的槽位

`lvI k r` 是位置 `r` 上那一层对应的参照层号; 结点规则只要求参照结点的下标与它 `≅ᴵ`. `Z0 k r` 说 `r` 是层号 0 的槽位, `toA` 把第 0 层的树当作那里的分支下标.

```agda
Lk : ℕ → LF
Lk zero = zero
Lk (suc k) = suc (Lk k)

ℓk : ℕ → L.Ordᴵ
ℓk zero = L.zero
ℓk (suc k) = L.suc (ℓk k)

lvI : ∀ k → Pre (Lk k) → L.Ordᴵ
lvI (suc k) (inj₁ _) = ℓk k
lvI (suc k) (inj₂ r) = lvI k r

data Z0 : ∀ k → Pre (Lk k) → Set where
  z1 : Z0 (suc zero) (inj₁ tt)
  zs : ∀ {k r} → Z0 k r → Z0 (suc k) (inj₂ r)

toA : ∀ {k r} → Z0 k r → R → Lay.A (Lo (Lk k) r)
toA z1 a = a
toA (zs z) a = toA z a

thr : R
thr = plus zero G.top (W.Tw 2)
```

## 2 关系族

第 k+1 层的规则: 零, 后继, ℕ 极限, 第一支 (`⊴b`), 结点 (`nd`, 假设取槽位关系 `H r`), `top` (`nt`, 假设取孩子层的关系), 嵌入 (`em`), 参照的提升 (`u⊴`), 对角 (`dg`), 换代表 (`≅⊴`, 同一参照层号).

```agda
module L1 (m : ℕ) (Rm : ∀ {ℓ} → L.Ordᶜ ℓ → Raw (Lk m) → Set)
  (H : (r : Pre (Lk (suc m))) → ∀ {ℓ} → L.Ordᶜ ℓ → Lay.A (Lo (Lk (suc m)) r) → Set) where
  infix 4 _⊴_
  data _⊴_ : ∀ {ℓ} → L.Ordᶜ ℓ → Raw (Lk (suc m)) → Set where
    z⊴ : ∀ {ℓ} {η} → _⊴_ {ℓ} L.zero η
    s⊴s : ∀ {ℓ} {x : L.Ordᶜ ℓ} {η} → x ⊴ η → L.suc x ⊴ G.suc η
    ⊴s : ∀ {ℓ} {x : L.Ordᶜ ℓ} {η} → x ⊴ η → x ⊴ G.suc η
    ⊴l : ∀ {ℓ} {x : L.Ordᶜ ℓ} {F : ℕ → Raw (Lk (suc m))} n → x ⊴ F n → x ⊴ G.lim F
    l⊴ : ∀ {ℓ} {F : ℕ → L.Ordᶜ ℓ} {η} → (∀ n → F n ⊴ η) → L.lim F ⊴ η
    ⊴b : ∀ {ℓ} {x : L.Ordᶜ ℓ} {r g} → x ⊴ g (Lay.tp (Lo (Lk (suc m)) r)) → x ⊴ G.lc r g
    nd : ∀ {r g} {i ℓ} {p : i L.<ᴵ ℓ} {f : L.U i (L.<→◃ p) → L.Ordᶜ ℓ} → i L.≅ᴵ lvI (suc m) r →
      (∀ (y : L.Ordᶜ i) a → H r y a → y L.≅ y → f (L.into (L.<→◃ p) y) ⊴ g a) → L.limᵢ p f ⊴ G.lc r g
    nt : ∀ {i ℓ} {p : i L.<ᴵ ℓ} {f : L.U i (L.<→◃ p) → L.Ordᶜ ℓ} → i L.≅ᴵ ℓk m →
      (∀ (y : L.Ordᶜ i) a → Rm y a → y L.≅ y → f (L.into (L.<→◃ p) y) ⊴ G.em tt a) → L.limᵢ p f ⊴ G.top
    em : ∀ {ℓ} {y : L.Ordᶜ ℓ} {a} → Rm y a → y ⊴ G.em tt a
    u⊴ : ∀ {k ℓ} {r : k L.◃₁ ℓ} {y : L.U k (L.◃₁→◃ r)} {η} → L.out (L.◃₁→◃ r) y ⊴ η → L.up r y ⊴ η
    dg : ∀ {r} (z : Z0 (suc m) r) {ℓ} {F : ℕ → L.Ordᶜ ℓ} {g} →
      (∀ n a → Cp zero thr a → F n ⊴ g (toA z a)) → L.lim F ⊴ G.lc r g
    ≅⊴ : ∀ {ℓ} {x y : L.Ordᶜ ℓ} {η} → x L.≅ y → y ⊴ η → x ⊴ η

open L1 public using (z⊴; s⊴s; ⊴s; ⊴l; l⊴; ⊴b; nd; nt; em; u⊴; dg; ≅⊴)

R0 : ∀ {ℓ} → L.Ordᶜ ℓ → R → Set
R0 {L.zero} y a = y ≼ NA.read a
R0 {L.suc _} y a = ⊥
R0 {L.lim _ _} y a = ⊥

Rel : (k : ℕ) → ∀ {ℓ} → L.Ordᶜ ℓ → Raw (Lk k) → Set
Hyp : (k : ℕ) (r : Pre (Lk k)) → ∀ {ℓ} → L.Ordᶜ ℓ → Lay.A (Lo (Lk k) r) → Set
Rel zero = R0
Rel (suc m) = L1._⊴_ m (Rel m) (Hyp (suc m))
Hyp (suc m) (inj₁ _) = Rel m
Hyp (suc m) (inj₂ r) = Hyp m r
```

## 3 右边沿第一位置上移

```agda
Rel-cp : ∀ k {ℓ} {x : L.Ordᶜ ℓ} {η η′} → Rel k x η → Cp (Lk k) η η′ → Rel k x η′
Rel-dn : ∀ m {ℓ} {x : L.Ordᶜ ℓ} {η} η′ → Rel (suc m) x η → Dn (Lk (suc m)) η η′ → Rel (suc m) x η′
em-dn : ∀ m {ℓ} {x : L.Ordᶜ ℓ} {a d : Raw (Lk m)} → Rel (suc m) x (G.em tt a) → Dn (Lk m) a d →
  Rel (suc m) x (G.em tt d)

Rel-cp zero {L.zero} h c = ≼-trans h (cp≼ c)
Rel-cp (suc m) h (inj₁ refl) = h
Rel-cp (suc m) h (inj₂ p) = Rel-dn m _ h p

Rel-dn m (G.suc η′) h p = ⊴s (Rel-cp (suc m) h p)
Rel-dn m (G.lim f) h (n , p) = ⊴l n (Rel-cp (suc m) h p)
Rel-dn m (G.lc r g) h p = ⊴b (Rel-cp (suc m) h p)
Rel-dn m {η = G.em _ a} (G.em _ d) h (refl , p) = em-dn m h p

em-dn m z⊴ p = z⊴
em-dn m (l⊴ h) p = l⊴ (λ n → em-dn m (h n) p)
em-dn m (em q) p = em (Rel-cp m q (inj₂ p))
em-dn m (u⊴ h) p = u⊴ (em-dn m h p)
em-dn m (≅⊴ e h) p = ≅⊴ e (em-dn m h p)
```

## 4 造结点的办法与它的相容性

`Bok M K B`: 用 `B` 在第 K 层的位置上造第 M 层的结点, 与关系的三条结点规则相容. `G.lc` 自身相容 (`bok-lc`); 进孩子时位置前面添 `inj₂`, 相容性定义性地传下去 (`bok-s`).

```agda
record Bok (M K : ℕ) (B : Bld (Lk M) (Lk K)) : Set where
  field
    bb : ∀ r {ℓ} {x : L.Ordᶜ ℓ} {g} → Rel M x (g (Lay.tp (Lo (Lk K) r))) → Rel M x (B r g)
    bn : ∀ r {i ℓ} {p : i L.<ᴵ ℓ} {f : L.U i (L.<→◃ p) → L.Ordᶜ ℓ} {g} → i L.≅ᴵ lvI K r →
      (∀ (y : L.Ordᶜ i) a → Hyp K r y a → y L.≅ y → Rel M (f (L.into (L.<→◃ p) y)) (g a)) →
      Rel M (L.limᵢ p f) (B r g)
    bd : ∀ {r} (z : Z0 K r) {ℓ} {F : ℕ → L.Ordᶜ ℓ} {g} →
      (∀ n a → Cp zero thr a → Rel M (F n) (g (toA z a))) → Rel M (L.lim F) (B r g)
open Bok public

bok-lc : ∀ m → Bok (suc m) (suc m) G.lc
bok-lc m = record { bb = λ r h → ⊴b h ; bn = λ r e h → nd e h ; bd = λ z h → dg z h }

bok-s : ∀ {M K} {B : Bld (Lk M) (Lk (suc K))} → Bok M (suc K) B → Bok M K (λ r → B (inj₂ r))
bok-s ok = record { bb = λ r → bb ok (inj₂ r) ; bn = λ r → bn ok (inj₂ r) ; bd = λ z → bd ok (zs z) }
```

## 5 加法: 右加, 左加, 加法上下文, ω 倍

```agda
shR : ∀ m K (B : Bld (Lk (suc m)) (Lk K)) → Bok (suc m) K B → ∀ {ℓ} {x : L.Ordᶜ ℓ} {θ} →
  Rel (suc m) x θ → ∀ a → Rel (suc m) x (add (Lk K) B θ a)
shR m K B ok h G.zero = h
shR m K B ok h (G.suc a) = ⊴s (shR m K B ok h a)
shR m K B ok h (G.lim f) = ⊴l 0 (shR m K B ok h (f 0))
shR m K B ok h (G.lc r g) = bb ok r (shR m K B ok h (g _))
shR m (suc K) B ok h (G.em _ a) = shR m K _ (bok-s ok) h a
shR m zero B ok h G.top = ⊴s h
shR m (suc K) B ok h G.top = bb ok (inj₁ tt) (shR m K _ (bok-s ok) h G.top)

lf0 : ∀ m (B : Bld (Lk (suc m)) zero) θ {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ a → b ≡ NA.read a →
  Rel (suc m) y (add zero B θ a)
lf0 m B θ z≼ a q = z⊴
lf0 m B θ (s≼s p) (G.suc a) refl = s⊴s (lf0 m B θ p a refl)
lf0 m B θ (s≼s p) G.top refl = s⊴s (lf0 m B θ p G.zero refl)
lf0 m B θ (≼l n p) (G.lim f) refl = ⊴l n (lf0 m B θ p (f n) refl)
lf0 m B θ (l≼ h) a q = l⊴ (λ n → lf0 m B θ (h n) a q)
lf0 m B θ (≼i {p = ()} x ex p) a q
lf0 m B θ (i≼ {p = ()} h) a q
lf0 m B θ (≼u {r = ()} p) a q
lf0 m B θ (u≼ {r = ()} p) a q

lfR : ∀ m K (B : Bld (Lk (suc m)) (Lk K)) → Bok (suc m) K B → ∀ θ {ℓ} {x : L.Ordᶜ ℓ} {η} →
  Rel K x η → Rel (suc m) x (add (Lk K) B θ η)
lfS : ∀ m K (B : Bld (Lk (suc m)) (Lk (suc K))) → Bok (suc m) (suc K) B → ∀ θ {ℓ} {x : L.Ordᶜ ℓ} {η} →
  Rel (suc K) x η → Rel (suc m) x (add (Lk (suc K)) B θ η)
lfR m zero B ok θ {L.zero} {η = η} q = lf0 m B θ q η refl
lfR m (suc K) B ok θ q = lfS m K B ok θ q
lfS m K B ok θ z⊴ = z⊴
lfS m K B ok θ (s⊴s p) = s⊴s (lfS m K B ok θ p)
lfS m K B ok θ (⊴s p) = ⊴s (lfS m K B ok θ p)
lfS m K B ok θ (⊴l n p) = ⊴l n (lfS m K B ok θ p)
lfS m K B ok θ (l⊴ h) = l⊴ (λ n → lfS m K B ok θ (h n))
lfS m K B ok θ (⊴b {r = r} p) = bb ok r (lfS m K B ok θ p)
lfS m K B ok θ (nd {r = r} e h) = bn ok r e (λ y a q s → lfS m K B ok θ (h y a q s))
lfS m K B ok θ (nt e h) = bn ok (inj₁ tt) e (λ y a q s → lfS m K B ok θ (h y a q s))
lfS m K B ok θ (em q) = lfR m K _ (bok-s ok) θ q
lfS m K B ok θ (u⊴ p) = u⊴ (lfS m K B ok θ p)
lfS m K B ok θ (dg z h) = bd ok z (λ n a c → lfS m K B ok θ (h n a c))
lfS m K B ok θ (≅⊴ e p) = ≅⊴ e (lfS m K B ok θ p)

Rel-+ˡ : ∀ m θ {ℓ} {x : L.Ordᶜ ℓ} {η} → Rel (suc m) x η → Rel (suc m) x (plus (Lk (suc m)) θ η)
Rel-+ˡ m θ = lfR m (suc m) G.lc (bok-lc m) θ

Rel-+ʳ : ∀ m {ℓ} {x : L.Ordᶜ ℓ} {η} → Rel (suc m) x η → ∀ η′ → Rel (suc m) x (plus (Lk (suc m)) η η′)
Rel-+ʳ m = shR m (suc m) G.lc (bok-lc m)
```

加法上下文: 左加数 `x` 在第 M 层的 `θ` 之下, 右加数 `y` 在第 K 层的 `a` 之下, 则 `x ⊕_σ y` 在 `θ ⊕_B a` 之下; `σ` 任意, 所以右加数可以在任一参照层号上 (层号下降时 `σ` 换成 `σ ∘ suc`).

```agda
ad0 : ∀ m (B : Bld (Lk (suc m)) zero) {ℓx} {x : L.Ordᶜ ℓx} {θ} → Rel (suc m) x θ →
  (σ : L.Simᴵ L.zero ℓx) {y b : L.Ordᶜ L.zero} → y ≼ b → ∀ a → b ≡ NA.read a →
  Rel (suc m) (L.add x σ y) (add zero B θ a)
ad0 m B px σ z≼ a q = shR m zero B (record { bb = λ () ; bn = λ () ; bd = λ () }) px a
ad0 m B px σ (s≼s p) (G.suc a) refl = s⊴s (ad0 m B px σ p a refl)
ad0 m B px σ (s≼s p) G.top refl = s⊴s (ad0 m B px σ p G.zero refl)
ad0 m B px σ (≼l n p) (G.lim f) refl = ⊴l n (ad0 m B px σ p (f n) refl)
ad0 m B px σ (l≼ h) a q = l⊴ (λ n → ad0 m B px σ (h n) a q)
ad0 m B px σ (≼i {p = ()} x ex p) a q
ad0 m B px σ (i≼ {p = ()} h) a q
ad0 m B px σ (≼u {r = ()} p) a q
ad0 m B px σ (u≼ {r = ()} p) a q

adR : ∀ m K (B : Bld (Lk (suc m)) (Lk K)) → Bok (suc m) K B → ∀ {ℓx} {x : L.Ordᶜ ℓx} {θ} → x L.≅ x →
  Rel (suc m) x θ → ∀ {ℓ} (σ : L.Simᴵ ℓ ℓx) {y : L.Ordᶜ ℓ} {a} → Rel K y a →
  Rel (suc m) (L.add x σ y) (add (Lk K) B θ a)
adS : ∀ m K (B : Bld (Lk (suc m)) (Lk (suc K))) → Bok (suc m) (suc K) B → ∀ {ℓx} {x : L.Ordᶜ ℓx} {θ} →
  x L.≅ x → Rel (suc m) x θ → ∀ {ℓ} (σ : L.Simᴵ ℓ ℓx) {y : L.Ordᶜ ℓ} {a} → Rel (suc K) y a →
  Rel (suc m) (L.add x σ y) (add (Lk (suc K)) B θ a)
adR m zero B ok s px {L.zero} σ {a = a} q = ad0 m B px σ q a refl
adR m (suc K) B ok s px σ q = adS m K B ok s px σ q
adS m K B ok s px σ {a = a} z⊴ = shR m (suc K) B ok px a
adS m K B ok s px σ (s⊴s q) = s⊴s (adS m K B ok s px σ q)
adS m K B ok s px σ (⊴s q) = ⊴s (adS m K B ok s px σ q)
adS m K B ok s px σ (⊴l n q) = ⊴l n (adS m K B ok s px σ q)
adS m K B ok s px σ (l⊴ h) = l⊴ (λ n → adS m K B ok s px σ (h n))
adS m K B ok s px σ (⊴b {r = r} q) = bb ok r (adS m K B ok s px σ q)
adS m K B ok {x = x} s px σ (nd {r = r} {g = g} {p = p} {f = f} e h) = bn ok r e (λ y a q t →
  subst (λ w → Rel (suc m) (L.add x σ (f (L.into (L.<→◃ p) w))) (add (Lk (suc K)) B _ (g a)))
    (sym (L.out-into (L.<→◃ (σ p)) y)) (adS m K B ok s px σ (h y a q t)))
adS m K B ok {x = x} s px σ (nt {p = p} {f = f} e h) = bn ok (inj₁ tt) e (λ y a q t →
  subst (λ w → Rel (suc m) (L.add x σ (f (L.into (L.<→◃ p) w))) (add (Lk (suc K)) B _ (G.em tt a)))
    (sym (L.out-into (L.<→◃ (σ p)) y)) (adS m K B ok s px σ (h y a q t)))
adS m K B ok s px σ (em q) = adR m K _ (bok-s ok) s px σ q
adS m K B ok s px σ (u⊴ {r = L.zero} q) = adS m K B ok s px (λ c → σ (L.suc c)) q
adS m K B ok s px σ (u⊴ {r = L.self n} q) = adS m K B ok s px (λ c → σ (L.lim n c)) q
adS m K B ok s px σ (dg z h) = bd ok z (λ n a c → adS m K B ok s px σ (h n a c))
adS m K B ok s px σ (≅⊴ e q) = ≅⊴ (L.add-≅ {σ = σ} {σ′ = σ} s e) (adS m K B ok s px σ q)

Rel-add : ∀ m {ℓ} {x : L.Ordᶜ ℓ} {η} → x L.≅ x → Rel (suc m) x η → ∀ {x′ : L.Ordᶜ ℓ} {η′} →
  Rel (suc m) x′ η′ → Rel (suc m) (x L.+ x′) (plus (Lk (suc m)) η η′)
Rel-add m s px q = adR m (suc m) G.lc (bok-lc m) s px (λ c → c) q

copiesK : ∀ m {ℓ} {A : L.Ordᶜ ℓ} {β} → A L.≅ A → Rel (suc m) A β → ∀ n →
  Rel (suc m) (iterᴸ (A L.+_) L.zero (suc n)) (acc (λ _ z → plus (Lk (suc m)) β z) β n)
copiesK m s p zero = p
copiesK m s p (suc n) = Rel-add m s p (copiesK m s p n)

Rel-ω : ∀ m {ℓ} {A : L.Ordᶜ ℓ} {β} → A L.≅ A → Rel (suc m) A β →
  Rel (suc m) (L.lim (iterᴸ (A L.+_) L.zero)) (succ (Lk (suc m)) β)
Rel-ω m s p = l⊴ λ where
  zero → z⊴
  (suc n) → ⊴l n (copiesK m s p n)
```

## 6 起点

```agda
Ω⊴top : ∀ m → Rel (suc m) (L.Ω (ℓk (suc m))) G.top
Ω⊴top m = nt (L.≅ᴵ-refl (ℓk m)) (λ y a q t → u⊴ (em q))
```
