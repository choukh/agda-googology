# 去头的树 (参照树用)

> **机械改写.** 由 [LadderOrdTree](LadderOrdTree.lagda.md) 经 `Survey/scripts/embvv/mk_sim.py` 生成, 只加一个开关 `dr`: `dr m` 为真时高度 $m$ 的链行去掉第 0 项 (`rowD`). 这是树的克隆, 不是证书克隆; 这棵树没有 `Goodᴺ` 闭包定理. 入口 [EmbVV](EmbVV.lagda.md).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
open import OCF.Align.LadderOrdBase
import OCF.Align.EmbVVMode
module OCF.Align.EmbVVTree (𝕊 : HtB) (dr : ∀ m → OCF.Align.EmbVVMode.HdM 𝕊 m) where

open HtB 𝕊 public
open OCF.Align.EmbVVMode 𝕊 public using (HdM; keep; drop; repl)
open import Agda.Primitive using (Level; Setω)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong; trans)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Free.Level
open import OCF.Free.Prefix using (Z; Ord₊ˢ; Ordˢ; intoˢ; toZ; Ωˢ)
open import OCF.Free.Aux using (Mlev)
open import OCF.Free.Floor using
  (Flr; fz; fk; fb; _⊔_; Ev; Run; wk; limA; limᵢA; ŝA; ĉA; cloA; flo; cvFlo; toFlo; ∅ᴿ; sucRun; bound; Bd; Fc; FB; evF; iF; liftEv; Top)
open import OCF.Free.Tree using (Fl; asl; asr; swp; dupr2; <◃)
```

## §0 序

```agda
evη : ∀ {i ℓ} (φ : Flr) (B : Top i ℓ (φ ⊔ fk zero)) η (e : Bd B ⊑ᴵ η) → Ev (Mlev (Fc B) (suc η) (FB B e)) (φ ⊔ fk η)
evη φ B η e = liftEv φ (λ q → lim 0 q) (proj₁ (evF B)) , (λ q → lim 1 q)
```

## §1 地板族

```agda
Fv : Set
Fv = Ht → Flr

updT : {A : Set} → (Ht → A) → A → ∀ i {n} → Tri _<ᴸ_ i n → A
updT χ x i (tlt _) = χ i
updT χ x i (teq _) = x
updT χ x i (tgt _) = χ i

upd : {A : Set} → (Ht → A) → Ht → A → Ht → A
upd χ n x i = updT χ x i (tri i n)

infixl 5 _∪_
_∪_ : Fv → Fv → Fv
(a ∪ b) n = a n ⊔ b n

κ : Flr → Fv
κ x _ = x

loT : Fv → ∀ i {n} → Tri _<ᴸ_ i n → Flr
loT χ i (tlt _) = χ i
loT χ i (teq _) = fz
loT χ i (tgt _) = fz

-- 高度 < H 的部分
lo : Ht → Fv → Fv
lo H χ i = loT χ i (tri i H)

-- ι↓ 的地板: 低于 n 的格读 χ, 第 n 格是 x, 高于 n 的格平凡
capT : Fv → Flr → ∀ i {n} → Tri _<ᴸ_ i n → Flr
capT χ x i (tlt _) = χ i
capT χ x i (teq _) = x
capT χ x i (tgt _) = fz

cap : Fv → Ht → Flr → Fv
cap χ n x i = capT χ x i (tri i n)

Sub : Ht → Fv → Fv → Set
Sub m a b = ∀ i → i <ᴸ m → ∀ {ℓ} → Ev ℓ (a i) → Ev ℓ (b i)

Sub∞ : Fv → Fv → Set
Sub∞ a b = ∀ i {ℓ} → Ev ℓ (a i) → Ev ℓ (b i)

⇑ : ∀ {m a b} → Sub∞ a b → Sub m a b
⇑ s i q e = s i e

-- upd 的逐点转移
upd-map : ∀ {a b : Fv} {x y} h → Sub∞ a b → (∀ {ℓ} → Ev ℓ x → Ev ℓ y) → Sub∞ (upd a h x) (upd b h y)
upd-map h s f i e with tri i h
... | tlt _ = s i e
... | teq _ = f e
... | tgt _ = s i e

upd-self : {A : Set} (χ : Ht → A) → ∀ h x → upd χ h x h ≡ x
upd-self χ h x with tri h h
... | tlt r = ⊥-elim (irr r)
... | teq _ = refl
... | tgt r = ⊥-elim (irr r)

upd-lt : {A : Set} → ∀ {j n} (χ : Ht → A) x → j <ᴸ n → upd χ n x j ≡ χ j
upd-lt {j = j} {n} χ x q with tri j n
... | tlt _ = refl
... | teq refl = ⊥-elim (irr q)
... | tgt r = ⊥-elim (irr (tr< r q))

upd-gt : {A : Set} → ∀ {j n} (χ : Ht → A) x → n <ᴸ j → upd χ n x j ≡ χ j
upd-gt {j = j} {n} χ x q with tri j n
... | tlt r = ⊥-elim (irr (tr< r q))
... | teq refl = ⊥-elim (irr q)
... | tgt _ = refl

lo-lt : ∀ {j H} χ → j <ᴸ H → lo H χ j ≡ χ j
lo-lt {j = j} {H} χ q with tri j H
... | tlt _ = refl
... | teq refl = ⊥-elim (irr q)
... | tgt r = ⊥-elim (irr (tr< r q))

cap-lt : ∀ {j n} (χ : Fv) x → j <ᴸ n → cap χ n x j ≡ χ j
cap-lt {j} {n} χ x q with tri j n
... | tlt _ = refl
... | teq refl = ⊥-elim (irr q)
... | tgt r = ⊥-elim (irr (tr< r q))

cap-gt : ∀ {j n} (χ : Fv) x → n <ᴸ j → cap χ n x j ≡ fz
cap-gt {j} {n} χ x q with tri j n
... | tlt r = ⊥-elim (irr (tr< r q))
... | teq refl = ⊥-elim (irr q)
... | tgt _ = refl

cap-self : (χ : Fv) → ∀ h x → cap χ h x h ≡ x
cap-self χ h x with tri h h
... | tlt r = ⊥-elim (irr r)
... | teq _ = refl
... | tgt r = ⊥-elim (irr r)

case-tri : ∀ {ℓ} {P : Set ℓ} i n → (i <ᴸ n → P) → (i ≡ n → P) → (n <ᴸ i → P) → P
case-tri i n a b c with tri i n
... | tlt r = a r
... | teq e = b e
... | tgt r = c r

upd-at : {A : Set} {a b : Ht → A} {y : A} (j i : Ht) → a i ≡ b i → upd a j y i ≡ upd b j y i
upd-at j i h with tri i j
... | tlt _ = h
... | teq _ = refl
... | tgt _ = h
```

## §2 数据树

`qcl n ψ s t g`: 高度 $n$ 的闭包. `qΩ↓ q`: 高度 $n<m$ 的节点, 输入是 `Vs m q k`, 也就是 `Q n k`. `qΩ`: 字面的顶层节点. `omk`: 记号 (见 [LadderNFTree](LadderNFTree.lagda.md)).

```agda
module _ (m : Ht) (α : Ordᴵ) (U : (i : Ordᴵ) → i ◃ α → Flr → Fv → Set) (V : ∀ {n} → n <ᴸ m → Ordᴵ → Flr → Fv → Set) where
  data Q₊ : Flr → Fv → Set where
    q0   : ∀ {φ χ} → Q₊ φ χ
    qs   : ∀ {φ χ} → Q₊ φ χ → Q₊ φ χ
    ql   : ∀ {φ χ} → (ℕ → Q₊ φ χ) → Q₊ φ χ
    qi   : ∀ {φ χ j} → (∀ {ℓ} → Ev ℓ φ → j <ᴵ ℓ) → (Ordˢ j → Q₊ φ χ) → Q₊ φ χ
    qŝ   : ∀ {φ χ} (c₀ : Ordᴵ) → Q₊ φ χ → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Q₊ φ χ) → Q₊ φ χ
    qĉ   : ∀ {φ χ} (c₀ : Ordᴵ) → Z → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Z) → Q₊ φ χ → ((η : Ordᴵ) → c₀ ⊑ᴵ η → Q₊ φ χ) → Q₊ φ χ
    qclo : ∀ {φ χ} → Q₊ (φ ⊔ fk zero) χ → ((η : Ordᴵ) → Q₊ (φ ⊔ fk η) χ) → Q₊ (φ ⊔ fk zero) χ
    qcl  : ∀ {φ χ n} (q : n <ᴸ m) (ψ : Flr) → (∀ {ℓ} → Ev ℓ (χ n) → Ev ℓ (ψ ⊔ fk zero)) → Q₊ φ χ → ((η : Ordᴵ) → Q₊ φ (upd χ n (ψ ⊔ fk η))) → Q₊ φ χ
    qwk  : ∀ {φ φ′ χ χ′} → (∀ {ℓ} → Ev ℓ φ′ → Ev ℓ φ) → Sub m χ′ χ → Q₊ φ χ → Q₊ φ′ χ′
    qΩ↓  : ∀ {φ χ n k} (q : n <ᴸ m) → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (∀ {ℓ} → Ev ℓ (χ n) → k <ᴵ ℓ) → (∀ ξ ζ → V q k ξ ζ → Q₊ (ξ ⊔ φ) (lo n ζ ∪ χ)) → Q₊ φ χ
    qΩ   : ∀ {φ χ k} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → (q : k <ᴵ α) → (∀ ξ ζ → U k (<→◃ q) ξ ζ → Q₊ (ξ ⊔ φ) (lo m ζ ∪ χ)) → Q₊ φ χ
    omk  : ∀ {φ χ k} → (r : k ◃₁ α) → U k (◃₁→◃ r) φ χ → Q₊ φ χ → Q₊ φ χ

XQ : Ht → Set₁
XQ _ = Ordᴵ → Flr → Fv → Set

QV : ∀ m → (∀ {n} → n <ᴸ m → XQ n) → XQ m
UV : ∀ m (V : ∀ {n} → n <ᴸ m → XQ n) {α} (i : Ordᴵ) → i ◃ α → Flr → Fv → Set
QV m V α φ χ = Q₊ m α (UV m V) V φ χ
UV m V i zero         φ χ = QV m V i φ χ
UV m V i (suc r)      φ χ = UV m V i r φ χ
UV m V _ (self {f} n) φ χ = QV m V (f n) φ χ
UV m V i (lim n r)    φ χ = UV m V i r φ χ

Vs : ∀ m {n} → n <ᴸ m → Ordᴵ → Flr → Fv → Set
Vs = Rec XQ QV

Q  : Ht → Ordᴵ → Flr → Fv → Set
Q m = QV m (Vs m)

Us : ∀ m {α} (i : Ordᴵ) → i ◃ α → Flr → Fv → Set
Us m = UV m (Vs m)

outU : ∀ {m i α} (r : i ◃ α) {φ χ} → Us m i r φ χ → Q m i φ χ
outU zero      x = x
outU (suc r)   x = outU r x
outU (self n)  x = x
outU (lim n r) x = outU r x

intoU : ∀ {m i α} (r : i ◃ α) {φ χ} → Q m i φ χ → Us m i r φ χ
intoU zero      x = x
intoU (suc r)   x = intoU r x
intoU (self n)  x = x
intoU (lim n r) x = intoU r x

outV : ∀ {m n} (q : n <ᴸ m) {k φ χ} → Vs m q k φ χ → Q n k φ χ
outV {m} q {k} {φ} {χ} x = subst (λ X → X k φ χ) (Rec-β XQ QV m q) x

intoV : ∀ {m n} (q : n <ᴸ m) {k φ χ} → Q n k φ χ → Vs m q k φ χ
intoV {m} q {k} {φ} {χ} x = subst (λ X → X k φ χ) (sym (Rec-β XQ QV m q)) x

subst-out-into : ∀ {ℓ ℓ′} {A : Set ℓ} {P : A → Set ℓ′} {a b : A} (e : a ≡ b) (x : P b) → subst P e (subst P (sym e) x) ≡ x
subst-out-into refl x = refl

out-intoV : ∀ {m n} (q : n <ᴸ m) {k ξ ζ} (z : Q n k ξ ζ) → outV q (intoV q z) ≡ z
out-intoV {m} q {k} {ξ} {ζ} z = subst-out-into {P = λ X → X k ξ ζ} (Rec-β XQ QV m q) z
```

## §3 加法, 同层嵌入, 搬运

```agda
sub-id : ∀ {m a} → Sub m a a
sub-id i q e = e

as-upd : ∀ {a b : Fv} {ψ} h η → Sub∞ (upd (a ∪ b) h (a h ⊔ ψ ⊔ fk η)) (a ∪ upd b h (ψ ⊔ fk η))
as-upd h η i e with tri i h
... | tlt _ = e
... | teq refl = (proj₁ (proj₁ e)) , (proj₂ (proj₁ e) , proj₂ e)
... | tgt _ = e

infixl 6 _⊞_
_⊞_ : ∀ {m c φ χ ψ ρ} → Q m c φ χ → Q m c ψ ρ → Q m c (φ ⊔ ψ) (χ ∪ ρ)
W ⊞ q0       = qwk proj₁ (λ i q → proj₁) W
W ⊞ qs a     = qs (W ⊞ a)
W ⊞ ql F     = ql (λ n → W ⊞ F n)
W ⊞ qi ac f  = qi (λ e → ac (proj₂ e)) (λ x → W ⊞ f x)
W ⊞ qŝ c₀ t g = qŝ c₀ (W ⊞ t) (λ η e → W ⊞ g η e)
W ⊞ qĉ c₀ z zg o₀ o = qĉ c₀ z zg (W ⊞ o₀) (λ η e → W ⊞ o η e)
W ⊞ qclo t g = qwk asl sub-id (qclo (qwk asr sub-id (W ⊞ t)) (λ η → qwk asr sub-id (W ⊞ g η)))
_⊞_ {χ = χ} W (qcl {n = n} q ψ s t g) = qcl q (χ n ⊔ ψ) (λ e → (proj₁ e , proj₁ (s (proj₂ e))) , proj₂ (s (proj₂ e))) (W ⊞ t) (λ η → qwk (λ e → e) (⇑ (as-upd {χ} n η)) (W ⊞ g η))
W ⊞ qwk le le′ t = qwk (λ e → proj₁ e , le (proj₂ e)) (λ i q e → proj₁ e , le′ i q (proj₂ e)) (W ⊞ t)
W ⊞ qΩ↓ q fe ac h = qΩ↓ q (λ e → fe (proj₂ e)) (λ e → ac (proj₂ e)) (λ ξ ζ z → qwk swp (λ i q → swp) (W ⊞ h ξ ζ z))
W ⊞ qΩ fe q h = qΩ (λ e → fe (proj₂ e)) q (λ ξ ζ z → qwk swp (λ i q → swp) (W ⊞ h ξ ζ z))
W ⊞ omk r z x = W ⊞ x

ι : ∀ {m a b} (r : a ◃ b) {φ χ} → Q m a φ χ → Q m b φ χ
ι r q0 = q0
ι r (qs a) = qs (ι r a)
ι r (ql F) = ql (λ n → ι r (F n))
ι r (qi ac f) = qi ac (λ x → ι r (f x))
ι r (qŝ c₀ t g) = qŝ c₀ (ι r t) (λ η e → ι r (g η e))
ι r (qĉ c₀ z zg o₀ o) = qĉ c₀ z zg (ι r o₀) (λ η e → ι r (o η e))
ι r (qclo t g) = qclo (ι r t) (λ η → ι r (g η))
ι r (qcl q ψ s t g) = qcl q ψ s (ι r t) (λ η → ι r (g η))
ι r (qwk le le′ t) = qwk le le′ (ι r t)
ι r (qΩ↓ q fe ac h) = qΩ↓ q fe ac (λ ξ ζ z → ι r (h ξ ζ z))
ι r (qΩ fe q h) = qΩ fe (<◃ q r) (λ ξ ζ z → ι r (h ξ ζ (intoU (<→◃ q) (outU (<→◃ (<◃ q r)) z))))
ι r (omk q z x) = ι r x

record RestrQ (m : Ht) (j b : Ordᴵ) : Set where
  constructor restrQ
  field
    {repQ} : Ordᴵ
    eqQ    : j ≅ᴵ repQ
    ltQ    : repQ <ᴵ b
    backQ  : ∀ {ξ ζ} → Q m repQ ξ ζ → Q m j ξ ζ
open RestrQ public

trQ  : ∀ {m a b φ χ} → a ≅ᴵ b → Q m a φ χ → Q m b φ χ
tr⁻Q : ∀ {m a b φ χ} → a ≅ᴵ b → Q m b φ χ → Q m a φ χ
resQ : ∀ {m j a b} → j <ᴵ a → a ≅ᴵ b → RestrQ m j b
res⁻Q : ∀ {m j a b} → j <ᴵ b → a ≅ᴵ b → RestrQ m j a

trQ e q0 = q0
trQ e (qs a) = qs (trQ e a)
trQ e (ql F) = ql (λ n → trQ e (F n))
trQ e (qi ac f) = qi ac (λ x → trQ e (f x))
trQ e (qŝ c₀ t g) = qŝ c₀ (trQ e t) (λ η d → trQ e (g η d))
trQ e (qĉ c₀ z zg o₀ o) = qĉ c₀ z zg (trQ e o₀) (λ η d → trQ e (o η d))
trQ e (qclo t g) = qclo (trQ e t) (λ η → trQ e (g η))
trQ e (qcl q ψ s t g) = qcl q ψ s (trQ e t) (λ η → trQ e (g η))
trQ e (qwk le le′ t) = qwk le le′ (trQ e t)
trQ e (qΩ↓ q fe ac h) = qΩ↓ q fe ac (λ ξ ζ z → trQ e (h ξ ζ z))
trQ e (qΩ fe q h) = qΩ fe (ltQ (resQ q e)) (λ ξ ζ z → trQ e (h ξ ζ (intoU (<→◃ q) (backQ (resQ q e) (outU (<→◃ (ltQ (resQ q e))) z)))))
trQ (s≅ e) (omk zero z x) = omk zero (trQ e z) (trQ (s≅ e) x)
trQ (l≅ h) (omk (self n) z x) = omk (self n) (trQ (h n) z) (trQ (l≅ h) x)

tr⁻Q e q0 = q0
tr⁻Q e (qs a) = qs (tr⁻Q e a)
tr⁻Q e (ql F) = ql (λ n → tr⁻Q e (F n))
tr⁻Q e (qi ac f) = qi ac (λ x → tr⁻Q e (f x))
tr⁻Q e (qŝ c₀ t g) = qŝ c₀ (tr⁻Q e t) (λ η d → tr⁻Q e (g η d))
tr⁻Q e (qĉ c₀ z zg o₀ o) = qĉ c₀ z zg (tr⁻Q e o₀) (λ η d → tr⁻Q e (o η d))
tr⁻Q e (qclo t g) = qclo (tr⁻Q e t) (λ η → tr⁻Q e (g η))
tr⁻Q e (qcl q ψ s t g) = qcl q ψ s (tr⁻Q e t) (λ η → tr⁻Q e (g η))
tr⁻Q e (qwk le le′ t) = qwk le le′ (tr⁻Q e t)
tr⁻Q e (qΩ↓ q fe ac h) = qΩ↓ q fe ac (λ ξ ζ z → tr⁻Q e (h ξ ζ z))
tr⁻Q e (qΩ fe q h) = qΩ fe (ltQ (res⁻Q q e)) (λ ξ ζ z → tr⁻Q e (h ξ ζ (intoU (<→◃ q) (backQ (res⁻Q q e) (outU (<→◃ (ltQ (res⁻Q q e))) z)))))
tr⁻Q (s≅ e) (omk zero z x) = omk zero (tr⁻Q e z) (tr⁻Q (s≅ e) x)
tr⁻Q (l≅ h) (omk (self n) z x) = omk (self n) (tr⁻Q (h n) z) (tr⁻Q (l≅ h) x)

resQ zero      (s≅ e) = restrQ e zero (tr⁻Q e)
resQ (suc q)   (s≅ e) = restrQ (eqQ (resQ q e)) (suc (ltQ (resQ q e))) (backQ (resQ q e))
resQ (lim n q) (l≅ h) = restrQ (eqQ (resQ q (h n))) (lim n (ltQ (resQ q (h n)))) (backQ (resQ q (h n)))

res⁻Q zero      (s≅ e) = restrQ (≅ᴵ-sym e) zero (trQ e)
res⁻Q (suc q)   (s≅ e) = restrQ (eqQ (res⁻Q q e)) (suc (ltQ (res⁻Q q e))) (backQ (res⁻Q q e))
res⁻Q (lim n q) (l≅ h) = restrQ (eqQ (res⁻Q q (h n))) (lim n (ltQ (res⁻Q q (h n)))) (backQ (res⁻Q q (h n)))
```

## §4 向下一层的嵌入, $\dot\Omega$

```agda
lo-ev : ∀ {j H} (a : Fv) → j <ᴸ H → ∀ {ℓ} → Ev ℓ (lo H a j) → Ev ℓ (a j)
lo-ev a q e = subst (Ev _) (lo-lt a q) e

ev-lo : ∀ {j H} (a : Fv) → j <ᴸ H → ∀ {ℓ} → Ev ℓ (a j) → Ev ℓ (lo H a j)
ev-lo a q e = subst (Ev _) (sym (lo-lt a q)) e

upd-sub : ∀ {m} {a b : Fv} {x y} n → Sub n a b → (∀ {ℓ} → Ev ℓ x → Ev ℓ y) → Sub m (cap a n x) (cap b n y)
upd-sub n s f i q e with tri i n
... | tlt r = s i r e
... | teq _ = f e
... | tgt _ = tt

upd-cap : ∀ {a b : Fv} {x y} n → Sub∞ a b → (∀ {ℓ} → Ev ℓ x → Ev ℓ y) → Sub∞ (upd a n x) (cap b n y)
upd-cap n s f i e with tri i n
... | tlt _ = s i e
... | teq _ = f e
... | tgt _ = tt

cap-map : ∀ {χ : Fv} {x y} n → (∀ {ℓ} → Ev ℓ x → Ev ℓ y) → Sub∞ (cap χ n x) (cap χ n y)
cap-map n f i e with tri i n
... | tlt _ = e
... | teq _ = f e
... | tgt _ = tt

κ-cap : ∀ {x} n → (∀ {ℓ} → Ev ℓ Fl → Ev ℓ x) → Sub∞ (κ Fl) (cap (κ Fl) n x)
κ-cap n f i e with tri i n
... | tlt _ = e
... | teq _ = f e
... | tgt _ = tt

-- ι↓ 的三个转换
c-∪ : ∀ {a χ : Fv} {x} n → Sub∞ (a ∪ cap χ n x) (cap (a ∪ χ) n x)
c-∪ n i e with tri i n
... | tlt _ = e
... | teq _ = proj₂ e
... | tgt _ = tt

c-sw : ∀ {χ : Fv} {x y j} n → j <ᴸ n → Sub∞ (upd (cap χ n x) j y) (cap (upd χ j y) n x)
c-sw {χ} {x} {y} {j} n q i {ℓ} e = case-tri i n
  (λ a → subst (Ev ℓ) (sym (cap-lt (upd χ j y) x a)) (subst (Ev ℓ) (upd-at j i (cap-lt χ x a)) e))
  (λ { refl → subst (Ev ℓ) (sym (cap-self (upd χ j y) n x)) (subst (Ev ℓ) (trans (upd-gt (cap χ n x) y q) (cap-self χ n x)) e) })
  (λ a → subst (Ev ℓ) (sym (cap-gt (upd χ j y) x a)) tt)

ι↓ : ∀ {n m k α φ χ} → n <ᴸ m → Q n k φ χ → Q m α φ (cap χ n (flo k))
ι↓ d q0 = q0
ι↓ d (qs a) = qs (ι↓ d a)
ι↓ d (ql F) = ql (λ i → ι↓ d (F i))
ι↓ d (qi ac f) = qi ac (λ x → ι↓ d (f x))
ι↓ d (qŝ c₀ t g) = qŝ c₀ (ι↓ d t) (λ η e → ι↓ d (g η e))
ι↓ d (qĉ c₀ z zg o₀ o) = qĉ c₀ z zg (ι↓ d o₀) (λ η e → ι↓ d (o η e))
ι↓ d (qclo t g) = qclo (ι↓ d t) (λ η → ι↓ d (g η))
ι↓ {χ = χ} d (qcl {n = j} q ψ s t g) =
  qcl (tr< q d) ψ (λ e → s (subst (Ev _) (cap-lt χ _ q) e)) (ι↓ d t) (λ η → qwk (λ e → e) (⇑ (c-sw {χ} _ q)) (ι↓ d (g η)))
ι↓ {n = n} d (qwk le le′ t) = qwk le (upd-sub n le′ (λ e → e)) (ι↓ d t)
ι↓ {χ = χ} d (qΩ↓ {n = j} q fe ac h) =
  qΩ↓ (tr< q d) fe (λ e → ac (subst (Ev _) (cap-lt χ _ q) e)) (λ ξ ζ z → qwk (λ e → e) (⇑ (c-∪ {lo j ζ} {χ} _)) (ι↓ d (h ξ ζ (intoV q (outV (tr< q d) z)))))
ι↓ {n = n} {k = k} {χ = χ} d (qΩ fe r h) =
  qΩ↓ d fe (λ e → cvFlo k (subst (Ev _) (cap-self χ n _) e) r) (λ ξ ζ z → qwk (λ e → e) (⇑ (c-∪ {lo n ζ} {χ} _)) (ι↓ d (h ξ ζ (intoU (<→◃ r) (outV d z)))))
ι↓ {n = n} {k = suc a} d (omk zero z x) = qwk (λ e → e) (⇑ (cap-map n (λ e → toFlo a (λ q → e (suc q))))) (ι↓ d z)
ι↓ {n = n} {k = lim f s} d (omk (self i) z x) = qwk (λ e → e) (⇑ (cap-map n (λ e → toFlo (f i) (λ q → e (lim i q))))) (ι↓ d z)

tl : ∀ {m c k χ} (φ : Flr) → (∀ {ℓ} → Ev ℓ φ → Simᴵ k ℓ) → Ordˢ k → Q m c φ χ
tl φ cv Ord₊ˢ.zero = q0
tl φ cv (Ord₊ˢ.suc a) = qs (tl φ cv a)
tl φ cv (Ord₊ˢ.lim f) = ql (λ n → tl φ cv (f n))
tl φ cv (Ord₊ˢ.limᵢ q f) = qi (λ e → cv e q) (λ x → tl φ cv (f (intoˢ (<→◃ q) x)))
tl {k = suc k′} φ cv (Ord₊ˢ.up zero x) = qwk (λ v → toFlo k′ (λ q → cv v (suc q))) sub-id (tl (flo k′) (cvFlo k′) x)
tl {k = lim f s} φ cv (Ord₊ˢ.up (self n) x) = qwk (λ v → toFlo (f n) (λ q → cv v (lim n q))) sub-id (tl (flo (f n)) (cvFlo (f n)) x)
tl {k = zero} φ cv (Ord₊ˢ.ŝ c₀ t₀ g) = qĉ c₀ (toZ t₀) (λ η e → toZ (g η e)) (tl φ cv t₀) (λ η e → tl φ cv (g η e))
tl {k = suc _} φ cv (Ord₊ˢ.ŝ c₀ t₀ g) = qŝ c₀ (tl φ cv t₀) (λ η e → tl φ cv (g η e))
tl {k = lim _ _} φ cv (Ord₊ˢ.ŝ c₀ t₀ g) = qŝ c₀ (tl φ cv t₀) (λ η e → tl φ cv (g η e))
tl φ cv (Ord₊ˢ.ĉᴸ c₀ t₀ g o₀ o) = qĉ c₀ t₀ g (tl φ cv o₀) (λ η e → tl φ cv (o η e))

-- 第 0 行的三种写法
XΩ : Ht → Set
XΩ m = (α : Ordᴵ) → Q m α Fl (κ Fl)

-- 闭包行
rowC : ∀ {m n} → n <ᴸ m → XΩ n → Q m zero Fl (κ Fl)
rowC {n = n} q X =
  qcl q fz (λ e → e)
      (qwk (λ e → e) (⇑ (κ-cap n proj₂)) (ι↓ q (X (suc zero))))
      (λ η → qwk (λ e → e) (⇑ (upd-cap n (λ i e → e) (λ e → toFlo η (λ q′ → proj₂ e (suc q′))))) (ι↓ q (X η)))

-- 链行: 第 0 项是 1, 其余项是低层 Ω̇ 的第 0 行
𝟏L : ∀ {m} → Q m zero Fl (κ Fl)
𝟏L = qwk (λ _ → tt) (λ i q _ → tt) (qs {φ = fz} {χ = κ fz} q0)

stepL : ∀ {m n} → n <ᴸ m → XΩ n → Q m zero Fl (κ Fl)
stepL {n = n} q X = qwk (λ e → e) (⇑ (κ-cap n (λ _ → tt))) (ι↓ q (X zero))

rowL : ∀ {m} (F : ℕ → Ht) → (∀ i → F i <ᴸ m) → (∀ i → XΩ (F i)) → ℕ → Q m zero Fl (κ Fl)
rowL F qs₁ X zero    = 𝟏L
rowL F qs₁ X (suc i) = stepL (qs₁ i) (X i)

-- 第 0 项的三种处理
rowD : ∀ {m} (F : ℕ → Ht) → (qs₁ : ∀ i → F i <ᴸ m) → (∀ {n} → n <ᴸ m → XΩ n) → HdM m → ℕ → Q m zero Fl (κ Fl)
rowD F qs₁ I keep = rowL F qs₁ (λ i → I (qs₁ i))
rowD F qs₁ I drop = λ i → stepL (qs₁ i) (I (qs₁ i))
rowD F qs₁ I (repl n q) zero = stepL q (I q)
rowD F qs₁ I (repl n q) (suc i) = stepL (qs₁ i) (I (qs₁ i))

-- 根层
rowB : ∀ {m} → Q m zero Fl (κ Fl)
rowB = qclo (tl (fz ⊔ fk zero) proj₂ (Ωˢ (suc zero))) (λ η → tl (fz ⊔ fk η) (λ e q → proj₂ e (suc q)) (Ωˢ η))

rowV : ∀ m → (∀ {n} → n <ᴸ m → XΩ n) → View _<ᴸ_ h₀ m → Q m zero Fl (κ Fl)
rowV _ I base         = rowB
rowV m I (clos q)     = rowC q (I q)
rowV m I (chain F qs₁) = ql (rowD F qs₁ I (dr m))

FΩ : ∀ m → (∀ {n} → n <ᴸ m → XΩ n) → XΩ m
FΩ m I (suc α) = qΩ (λ e → e) zero (λ ξ ζ z → qwk proj₁ (λ i q e → subst (Ev _) (lo-lt ζ q) (proj₁ e)) (omk zero z (ι zero z)))
FΩ m I (lim f s) = ql (λ n → omk (self n) (FΩ m I (f n)) (ι (self n) (FΩ m I (f n))))
FΩ m I zero = rowV m I (view m)

ΩI : ∀ m {n} → n <ᴸ m → XΩ n
ΩI = Rec XΩ FΩ

Ω̇ : ∀ m → XΩ m
Ω̇ m = FΩ m (ΩI m)

ΩI≡ : ∀ {m n} (q : n <ᴸ m) → ΩI m q ≡ Ω̇ n
ΩI≡ {m} q = Rec-β XΩ FΩ m q
```

## §5 折叠

`ψᵠ`: 字面目标 (顶层). `Ψ`: 目标在高度 $H<m$, 只吃高度 $\ge H$ 的证据, 输出在 `Q H t`. `ψ̄ᵠ`: 目标可数. 高度 $n$ 的闭包: $n<H$ 穿过; $n=H$ 落成字面闭包, 界含目标; $n>H$ 落成字面闭包, 界不含目标. 高度 $n$ 的节点: $n<H$ 穿过; $n=H$ 比较; $n>H$ 走链, 链在 `Q n k`. 与 [ScafLadderTree](ScafLadderTree.lagda.md) 是 $m=1$ 的同一个定义.

```agda
Ev-lo : ∀ {a : Fv} H i {ℓ} → Ev ℓ (a i) → Ev ℓ (lo H a i)
Ev-lo H i e with tri i H
... | tlt _ = e
... | teq _ = tt
... | tgt _ = tt

Hi : Ht → Ht → Set
Hi H i = (H ≡ i) ⊎ (H <ᴸ i)

lo-triv : ∀ {H i} (a : Fv) → Hi H i → ∀ {ℓ} → Ev ℓ (lo H a i)
lo-triv {H} {i} a h with tri i H
lo-triv {H} {i} a (inj₁ refl) | tlt r = ⊥-elim (irr r)
lo-triv {H} {i} a (inj₂ s) | tlt r = ⊥-elim (irr (tr< r s))
... | teq _ = tt
... | tgt _ = tt

Ok : (Ht → Ordᴵ) → Set
Ok w = ∀ i → Ev (w i) Fl

Eh : Ht → Ht → (Ht → Ordᴵ) → Fv → Set
Eh H m w χ = ∀ i → Hi H i → i <ᴸ m → Ev (w i) (χ i)

upd-ev : ∀ {ℓ′ z} n i (w : Ht → Ordᴵ) (χ : Fv) → Ev ℓ′ z → Ev (w i) (χ i) → Ev (upd w n ℓ′ i) (upd χ n z i)
upd-ev n i w χ a b with tri i n
... | tlt _ = b
... | teq _ = a
... | tgt _ = b

upd-ok : ∀ {ℓ′} n (w : Ht → Ordᴵ) → Ok w → Ev ℓ′ Fl → Ok (upd w n ℓ′)
upd-ok n w ok a i with tri i n
... | tlt _ = ok i
... | teq _ = a
... | tgt _ = ok i

repᵠ : ∀ {m c φ χ} → Q m c φ χ → ℕ → Q m c φ χ
repᵠ x zero          = q0
repᵠ x (suc zero)    = x
repᵠ x (suc (suc m)) = qwk (λ e → e , e) (λ i q e → e , e) (repᵠ x (suc m) ⊞ x)

chainᵠ : ∀ {m k φ χ} → (∀ {ℓ} → Ev ℓ φ → Ev ℓ Fl) → Sub m χ (κ Fl) → (Q m k φ χ → Q m k φ χ) → ℕ → Q m k φ χ
chainᵠ {m} {k} fe fc f zero    = qwk fe fc (Ω̇ m k)
chainᵠ fe fc f (suc n) = f (chainᵠ fe fc f n)

Z* : Fv → Fv
Z* χ = κ Fl ∪ χ

cv* : ∀ {χ : Fv} n → Sub∞ (Z* χ) (Z* (lo n (Z* χ) ∪ χ))
cv* {χ} n i (a , b) = a , (Ev-lo {Z* χ} n i (a , b) , b)

fc* : ∀ {m} {χ : Fv} → Sub m (Z* χ) (κ Fl)
fc* i q = proj₁

ψᵠ : ∀ {m α t} → t <ᴵ α → ∀ {φ χ} → Q m α φ χ → Q m t (Fl ⊔ φ) (Z* χ)
ψᵠ {m} {t = t} q q0 = qwk proj₁ fc* (Ω̇ m t)
ψᵠ q (qs a) = ql (repᵠ (ψᵠ q a))
ψᵠ q (ql F) = ql (λ n → ψᵠ q (F n))
ψᵠ q (qi ac f) = qi (λ e → ac (proj₂ e)) (λ x → ψᵠ q (f x))
ψᵠ q (qŝ c₀ t g) = qŝ c₀ (ψᵠ q t) (λ η e → ψᵠ q (g η e))
ψᵠ q (qĉ c₀ z zg o₀ o) = qĉ c₀ z zg (ψᵠ q o₀) (λ η e → ψᵠ q (o η e))
ψᵠ q (qclo t g) = qwk asl sub-id (qclo (qwk asr sub-id (ψᵠ q t)) (λ η → qwk asr sub-id (ψᵠ q (g η))))
ψᵠ q {χ = χ} (qcl {n = n} r ψ s t g) =
  qcl r (Fl ⊔ ψ) (λ e → (proj₁ e , proj₁ (s (proj₂ e))) , proj₂ (s (proj₂ e))) (ψᵠ q t) (λ η → qwk (λ e → e) (⇑ (as-upd {κ Fl} {χ} n η)) (ψᵠ q (g η)))
ψᵠ q (qwk le le′ x) = qwk (λ e → proj₁ e , le (proj₂ e)) (λ i r e → proj₁ e , le′ i r (proj₂ e)) (ψᵠ q x)
ψᵠ q (qΩ↓ r fe ac h) = qΩ↓ r proj₁ (λ e → ac (proj₂ e)) (λ ξ ζ z → qwk swp (λ i r′ → swp) (ψᵠ q (h ξ ζ z)))
ψᵠ {m} q {φ} {χ} (qΩ fe r h) with <ᴵ-dec r q
... | injᵃ (via e s) = qΩ proj₁ s (λ ξ ζ y → qwk swp (λ i r′ → swp) (ψᵠ q (h ξ ζ (intoU (<→◃ r) (tr⁻Q e (outU (<→◃ s) y))))))
... | injᵇ _ = ql (λ n → qwk dupr2 (⇑ (cv* m)) (ψᵠ q (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)))) n)))))
... | injᶜ _ = ql (λ n → qwk dupr2 (⇑ (cv* m)) (ψᵠ q (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)))) n)))))
ψᵠ q (omk r z x) = ψᵠ q x

-- 目标在高度 H
Hi-up : ∀ {H n i} → H <ᴸ n → Hi n i → Hi H i
Hi-up l (inj₁ refl) = inj₂ l
Hi-up l (inj₂ r) = inj₂ (tr< l r)

Hi-gt : ∀ {H n i} → n <ᴸ H → Hi H i → n <ᴸ i
Hi-gt l (inj₁ refl) = l
Hi-gt l (inj₂ r) = tr< l r

e⁺ : ∀ {H m w} {χ : Fv} (n : Ht) → Ok w → Eh H m w χ → Eh H m w (lo n (Z* χ) ∪ χ)
e⁺ {χ = χ} n ok e i h r = Ev-lo {Z* χ} n i (ok i , e i h r) , e i h r

Hi-tr : ∀ {n H i} → Hi n H → Hi H i → Hi n i
Hi-tr (inj₁ refl) h = h
Hi-tr (inj₂ l) (inj₁ refl) = inj₂ l
Hi-tr (inj₂ l) (inj₂ r) = inj₂ (tr< l r)

Hi-0 : ∀ i → Hi h₀ i
Hi-0 = bot

e-lo : ∀ {H m w n} {χ : Fv} (ζ : Fv) → Hi n H → Eh H m w χ → Eh H m w (lo n ζ ∪ χ)
e-lo ζ le e i h r = lo-triv ζ (Hi-tr le h) , e i h r

e↑ : ∀ {H n m w} {χ : Fv} → H <ᴸ n → Eh H m w χ → Eh n m w χ
e↑ l e i h′ r = e i (Hi-up l h′) r

e↓ : ∀ {n m w} {χ : Fv} → Eh h₀ m w χ → Eh n m w χ
e↓ e i h′ r = e i (Hi-0 i) r

zr : ∀ {w} → Ok w → ∀ n → zero <ᴵ w n
zr ok n = proj₂ (ok n) zero

Ψ : ∀ {H m α φ χ t w} → H <ᴸ m → Ok w → Eh H m w χ → t <ᴵ w H → Q m α φ χ → Q H t (Fl ⊔ φ) (Z* χ)
Ψ {H} {t = t} qH ok e p q0 = qwk proj₁ fc* (Ω̇ H t)
Ψ qH ok e p (qs a) = ql (repᵠ (Ψ qH ok e p a))
Ψ qH ok e p (ql F) = ql (λ n → Ψ qH ok e p (F n))
Ψ qH ok e p (qi ac f) = qi (λ u → ac (proj₂ u)) (λ x → Ψ qH ok e p (f x))
Ψ qH ok e p (qŝ c₀ x g) = qŝ c₀ (Ψ qH ok e p x) (λ η d → Ψ qH ok e p (g η d))
Ψ qH ok e p (qĉ c₀ z zg o₀ o) = qĉ c₀ z zg (Ψ qH ok e p o₀) (λ η d → Ψ qH ok e p (o η d))
Ψ qH ok e p (qclo x g) = qwk asl sub-id (qclo (qwk asr sub-id (Ψ qH ok e p x)) (λ η → qwk asr sub-id (Ψ qH ok e p (g η))))
Ψ qH ok e p (qwk le le′ x) = qwk (λ u → proj₁ u , le (proj₂ u)) (λ i r u → proj₁ u , le′ i (tr< r qH) (proj₂ u)) (Ψ qH ok (λ i h r → le′ i r (e i h r)) p x)
Ψ qH ok e p (omk r z x) = Ψ qH ok e p x
Ψ {H} {χ = χ} {w = w} qH ok e p (qcl {n = n} q ψ s x g) with tri n H
... | tlt l =
  qcl l (Fl ⊔ ψ) (λ u → (proj₁ u , proj₁ (s (proj₂ u))) , proj₂ (s (proj₂ u))) (Ψ qH ok e p x)
      (λ η → qwk (λ u → u) (⇑ (as-upd {κ Fl} {χ} n η))
         (Ψ qH ok (λ i h r → subst (Ev _) (sym (upd-gt χ _ (Hi-gt l h))) (e i h r)) p (g η)))
... | teq refl =
  qŝ (Bd B) (Ψ qH ok e p x)
     (λ η d → qwk (λ u → u) (λ i r u → proj₁ u , subst (Ev _) (sym (upd-lt χ _ r)) (proj₂ u))
              (Ψ qH (upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′)))
               (λ i h r → upd-ev n i w χ (evη ψ B η d) (e i h r))
               (subst (t′ <ᴵ_) (sym (upd-self w n _)) (lim 0 (iF B))) (g η)))
  where
  B = bound (ψ ⊔ fk zero) (s (e n (inj₁ refl) q)) p
  t′ = _
... | tgt l =
  qŝ (Bd B) (Ψ qH ok e p x)
     (λ η d → qwk (λ u → u) (λ i r u → proj₁ u , subst (Ev _) (sym (upd-lt χ _ (tr< r l))) (proj₂ u))
              (Ψ qH (upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′)))
               (λ i h r → upd-ev n i w χ (evη ψ B η d) (e i h r))
               (subst (t′ <ᴵ_) (sym (upd-lt w _ l)) p) (g η)))
  where
  B = bound (ψ ⊔ fk zero) (s (e n (inj₂ l) q)) (zr ok n)
  t′ = _
Ψ {H} {φ = φ} {χ = χ} qH ok e p (qΩ↓ {n = n} {k = k} q fe ac h) with tri n H
... | tlt l = qΩ↓ l proj₁ (λ u → ac (proj₂ u)) (λ ξ ζ z → qwk swp (λ i r → swp) (Ψ qH ok (e-lo ζ (inj₂ l) e) p (h ξ ζ (intoV q (outV l z)))))
... | teq refl with <ᴵ-dec (ac (e n (inj₁ refl) q)) p
...   | injᵃ (via d s) = qΩ proj₁ s (λ ξ ζ y → qwk swp (λ i r → swp) (Ψ qH ok (e-lo ζ (inj₁ refl) e) p (h ξ ζ (intoV q (tr⁻Q d (outU (<→◃ s) y))))))
...   | injᵇ _ = ql (λ i → qwk dupr2 (⇑ (cv* H)) (Ψ qH ok (e⁺ H ok e) p (h (Fl ⊔ φ) (Z* χ) (intoV q (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* n)) (Ψ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) (h (Fl ⊔ φ) (Z* χ) (intoV q z)))) i)))))
...   | injᶜ _ = ql (λ i → qwk dupr2 (⇑ (cv* H)) (Ψ qH ok (e⁺ H ok e) p (h (Fl ⊔ φ) (Z* χ) (intoV q (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* n)) (Ψ q ok (e⁺ n ok e) (ac (e n (inj₁ refl) q)) (h (Fl ⊔ φ) (Z* χ) (intoV q z)))) i)))))
Ψ {H} {φ = φ} {χ = χ} qH ok e p (qΩ↓ {n = n} {k = k} q fe ac h) | tgt l =
  ql (λ i → qwk dupr2 (⇑ (cv* n)) (Ψ qH ok (e⁺ n ok e) p (h (Fl ⊔ φ) (Z* χ) (intoV q (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* n)) (Ψ q ok (e⁺ n ok (e↑ l e)) (ac (e↑ l e n (inj₁ refl) q)) (h (Fl ⊔ φ) (Z* χ) (intoV q z)))) i)))))
Ψ {H} {m} {φ = φ} {χ = χ} qH ok e p (qΩ fe r h) =
  ql (λ i → qwk dupr2 (⇑ (cv* m)) (Ψ qH ok (e⁺ m ok e) p (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) (chainᵠ proj₁ fc* (λ z → qwk dupr2 (⇑ (cv* m)) (ψᵠ r (h (Fl ⊔ φ) (Z* χ) (intoU (<→◃ r) z)))) i)))))

-- 目标可数
ψ̄ᵠ : ∀ {m c φ χ w} → Ok w → Eh h₀ m w χ → Q m c φ χ → Run φ
ψ̄ᵠ ok e q0 = wk 0 (λ _ → tt) ∅ᴿ
ψ̄ᵠ ok e (qs a) = sucRun (ψ̄ᵠ ok e a)
ψ̄ᵠ ok e (ql F) = limA 0 (λ n → ψ̄ᵠ ok e (F n))
ψ̄ᵠ ok e (qi ac f) = limᵢA 0 ac (λ x → ψ̄ᵠ ok e (f x))
ψ̄ᵠ ok e (qŝ c₀ t g) = ŝA 0 c₀ (ψ̄ᵠ ok e t) (λ η d → ψ̄ᵠ ok e (g η d))
ψ̄ᵠ ok e (qĉ c₀ t₀ zg o₀ o) = ĉA 0 c₀ t₀ zg (ψ̄ᵠ ok e o₀) (λ η d → ψ̄ᵠ ok e (o η d))
ψ̄ᵠ ok e (qclo t g) = cloA 0 (ψ̄ᵠ ok e t) (λ η → ψ̄ᵠ ok e (g η))
ψ̄ᵠ {χ = χ} {w = w} ok e (qcl {n = n} q ψ s t g) =
  ŝA 0 (Bd B) (ψ̄ᵠ ok e t)
     (λ η d → ψ̄ᵠ (upd-ok n w ok (tt , λ q′ → lim 0 (proj₂ (evF B) q′))) (λ i h r → upd-ev n i w χ (evη ψ B η d) (e i h r)) (g η))
  where B = bound (ψ ⊔ fk zero) (s (e n (Hi-0 n) q)) (zr ok n)
ψ̄ᵠ ok e (qwk le le′ x) = wk 0 le (ψ̄ᵠ ok (λ i h r → le′ i r (e i h r)) x)
ψ̄ᵠ ok e (omk r z x) = ψ̄ᵠ ok e x
ψ̄ᵠ {φ = φ} {χ = χ} ok e (qΩ↓ {n = n} {k = k} q fe ac h) =
  limA 0 (λ i → wk 0 (λ v → v , v) (ψ̄ᵠ ok (e⁺ n ok e) (h φ (Z* χ) (intoV q (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* n)) (Ψ q ok (e⁺ n ok (e↓ e)) (ac (e↓ e n (inj₁ refl) q)) (h φ (Z* χ) (intoV q z)))) i)))))
ψ̄ᵠ {m} {φ = φ} {χ = χ} ok e (qΩ fe r h) =
  limA 0 (λ i → wk 0 (λ v → v , v) (ψ̄ᵠ ok (e⁺ m ok e) (h φ (Z* χ) (intoU (<→◃ r) (chainᵠ fe fc* (λ z → qwk (λ v → fe v , (v , v)) (⇑ (cv* m)) (ψᵠ r (h φ (Z* χ) (intoU (<→◃ r) z)))) i)))))

w₀ : Ht → Ordᴵ
w₀ _ = suc zero

ok₀ : Ok w₀
ok₀ i = tt , (λ q → q)

-- ψ₀(Ω_{m+α}), m 由结构解释
Tᵠ : ∀ m α → Run Fl
Tᵠ m α = ψ̄ᵠ ok₀ (λ i h r → ok₀ i) (Ω̇ m α)
```
