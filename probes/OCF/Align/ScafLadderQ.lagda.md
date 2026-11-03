# 阶梯 (八): 塔. 层号 $\Omega\cdot(m+1)+\alpha$ 的树, 对 $m$ 一致

> 结论写在 [ScafLadder](ScafLadder.lagda.md). 不导入记号的定义. 这是 [ScafLadderTree](ScafLadderTree.lagda.md) 对 $m$ 的一致版: `P` 的 $\chi$ 换成 `χ : ℕ → Flr`, 高度 $n$ 一格; 目标在高度 $H$ 的求值 `Ψ` 只吃高度 $\ge H$ 的世界, 输出在 `Q H t`, 地板只留高度 $<H$ (`lo`). 高度是层号 $\Omega\cdot m$ 的 $m$, 由类型分开, 不是节点上的标签. **只有定义与有限测试; 这个塔上没有标签.**

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.ScafLadderQ where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong)

open import OCF.BTBO using (module Ord-Ord; injᵃ; injᵇ; injᶜ)
open import OCF.Align.Level
open import OCF.Align.ScafLadderZPrefix using (Z; Ord₊ˢ; Ordˢ; intoˢ; toZ; Ωˢ)
open import OCF.Align.Symbolic using (Mlev)
open import OCF.Align.ScafLadderZUniform3Base using
  (Flr; fz; fk; fb; _⊔_; Ev; Run; wk; limA; limᵢA; ŝA; ĉA; cloA; flo; cvFlo; toFlo; ∅ᴿ; sucRun; bound; Bd; Fc; FB; evF; iF; liftEv; Top; evη)
open import OCF.Align.ScafLadderZUniform4Base using (Fl; asl; asr; swp; dupr; dupr2; _<ᴸ_; zero; suc; tr<)
open import OCF.Align.ScafLadderZUniform4Two using (<◃)
```

## §1 地板族

```agda
Fv : Set
Fv = ℕ → Flr

upd : {A : Set} → (ℕ → A) → ℕ → A → ℕ → A
upd χ zero    x zero    = x
upd χ zero    x (suc n) = χ (suc n)
upd χ (suc h) x zero    = χ zero
upd χ (suc h) x (suc n) = upd (λ m → χ (suc m)) h x n

infixl 5 _∪_
_∪_ : Fv → Fv → Fv
(a ∪ b) n = a n ⊔ b n

κ : Flr → Fv
κ x _ = x

-- 高度 < H 的部分
lo : ℕ → Fv → Fv
lo zero    χ n       = fz
lo (suc H) χ zero    = χ zero
lo (suc H) χ (suc n) = lo H (λ m → χ (suc m)) n

Sub : ℕ → Fv → Fv → Set
Sub m a b = ∀ i → i <ᴸ m → ∀ {ℓ} → Ev ℓ (a i) → Ev ℓ (b i)

Sub∞ : Fv → Fv → Set
Sub∞ a b = ∀ i {ℓ} → Ev ℓ (a i) → Ev ℓ (b i)

⇑ : ∀ {m a b} → Sub∞ a b → Sub m a b
⇑ s i q e = s i e

-- upd 的逐点转移
upd-map : ∀ {a b : Fv} {x y} h → Sub∞ a b → (∀ {ℓ} → Ev ℓ x → Ev ℓ y) → Sub∞ (upd a h x) (upd b h y)
upd-map zero    s f zero    e = f e
upd-map zero    s f (suc n) e = s (suc n) e
upd-map (suc h) s f zero    e = s zero e
upd-map (suc h) s f (suc n) e = upd-map h (λ m → s (suc m)) f n e

upd-self : {A : Set} (χ : ℕ → A) → ∀ h x → upd χ h x h ≡ x
upd-self χ zero    x = refl
upd-self χ (suc h) x = upd-self (λ m → χ (suc m)) h x

dn : ∀ {a b} → suc a <ᴸ suc b → a <ᴸ b
dn zero = zero
dn {b = suc b} (suc r) = suc (dn r)
dn {b = zero} (suc ())

upd-lt : {A : Set} → ∀ {j n} (χ : ℕ → A) x → j <ᴸ n → upd χ n x j ≡ χ j
upd-lt {j = zero}  {n = suc n} χ x q = refl
upd-lt {j = suc j} {n = suc n} χ x q = upd-lt (λ m → χ (suc m)) x (dn q)

upd-gt : {A : Set} → ∀ {j n} (χ : ℕ → A) x → n <ᴸ j → upd χ n x j ≡ χ j
upd-gt {j = suc j} {n = zero}  χ x q = refl
upd-gt {j = suc j} {n = suc n} χ x q = upd-gt (λ m → χ (suc m)) x (dn q)

lo-lt : ∀ {j H} χ → j <ᴸ H → lo H χ j ≡ χ j
lo-lt {j = zero}  {H = suc H} χ q = refl
lo-lt {j = suc j} {H = suc H} χ q = lo-lt (λ m → χ (suc m)) (dn q)

data Tri (a b : ℕ) : Set where
  tlt : a <ᴸ b → Tri a b
  teq : a ≡ b → Tri a b
  tgt : b <ᴸ a → Tri a b

z<s : ∀ b → zero <ᴸ suc b
z<s zero    = zero
z<s (suc b) = suc (z<s b)

s<s : ∀ {a b} → a <ᴸ b → suc a <ᴸ suc b
s<s zero    = zero
s<s (suc q) = suc (s<s q)

tri : ∀ a b → Tri a b
tri zero    zero    = teq refl
tri zero    (suc b) = tlt (z<s b)
tri (suc a) zero    = tgt (z<s a)
tri (suc a) (suc b) with tri a b
... | tlt p = tlt (s<s p)
... | teq e = teq (cong suc e)
... | tgt p = tgt (s<s p)
```

## §2 数据树

`qcl n ψ s t g`: 高度 $n$ 的闭包, 分支 $\eta$ 的地板第 $n$ 格是 $\psi\sqcup$ `fk η`. `qΩ↓ q`: 高度 $n<m$ 的节点, 输入是 `Q n k`, 证据只读第 $n$ 格. `qΩ`: 字面的顶层节点. `omk`: [ScafLadderTree](ScafLadderTree.lagda.md) 的记号.

```agda
module _ (m : ℕ) (α : Ordᴵ) (U : (i : Ordᴵ) → i ◃ α → Flr → Fv → Set) (V : ∀ {n} → n <ᴸ m → Ordᴵ → Flr → Fv → Set) where
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

Q  : ℕ → Ordᴵ → Flr → Fv → Set
Us : ∀ m {α} (i : Ordᴵ) → i ◃ α → Flr → Fv → Set
Vs : ∀ m {n} → n <ᴸ m → Ordᴵ → Flr → Fv → Set
Q m α φ χ = Q₊ m α (Us m) (Vs m) φ χ
Us m i zero         φ χ = Q m i φ χ
Us m i (suc r)      φ χ = Us m i r φ χ
Us m _ (self {f} n) φ χ = Q m (f n) φ χ
Us m i (lim n r)    φ χ = Us m i r φ χ
Vs (suc m) zero    k φ χ = Q m k φ χ
Vs (suc m) (suc q) k φ χ = Vs m q k φ χ

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
outV zero    x = x
outV (suc q) x = outV q x

intoV : ∀ {m n} (q : n <ᴸ m) {k φ χ} → Q n k φ χ → Vs m q k φ χ
intoV zero    x = x
intoV (suc q) x = intoV q x
```

## §3 加法, 同层嵌入, 搬运

```agda
sub-id : ∀ {m a} → Sub m a a
sub-id i q e = e

as-upd : ∀ {a b : Fv} {ψ} h η → Sub∞ (upd (a ∪ b) h (a h ⊔ ψ ⊔ fk η)) (a ∪ upd b h (ψ ⊔ fk η))
as-upd zero    η zero    ((u , v) , w) = u , (v , w)
as-upd zero    η (suc n) e = e
as-upd (suc h) η zero    e = e
as-upd {a} {b} {ψ} (suc h) η (suc n) e = as-upd {λ m → a (suc m)} {λ m → b (suc m)} {ψ} h η n e

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

record RestrQ (m : ℕ) (j b : Ordᴵ) : Set where
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

## §4 向上一层, $\dot\Omega$

```agda
lo-ev : ∀ {j H} (a : Fv) → j <ᴸ H → ∀ {ℓ} → Ev ℓ (lo H a j) → Ev ℓ (a j)
lo-ev a q e = subst (Ev _) (lo-lt a q) e

ev-lo : ∀ {j H} (a : Fv) → j <ᴸ H → ∀ {ℓ} → Ev ℓ (a j) → Ev ℓ (lo H a j)
ev-lo a q e = subst (Ev _) (sym (lo-lt a q)) e

upd-sub : ∀ {a b : Fv} {x y} n → Sub n a b → (∀ {ℓ} → Ev ℓ x → Ev ℓ y) → Sub (suc n) (upd a n x) (upd b n y)
upd-sub zero s f zero q e = f e
upd-sub zero s f (suc i) (suc ())
upd-sub (suc n) s f zero q e = s zero (z<s n) e
upd-sub (suc n) s f (suc i) q e = upd-sub n (λ j r → s (suc j) (s<s r)) f i (dn q) e

-- ι↓ 的三个转换
c-∪ : ∀ {a χ : Fv} {x} n → Sub∞ (a ∪ upd χ n x) (upd (a ∪ χ) n x)
c-∪ zero zero e = proj₂ e
c-∪ zero (suc i) e = e
c-∪ (suc n) zero e = e
c-∪ {a} {χ} (suc n) (suc i) e = c-∪ {λ m → a (suc m)} {λ m → χ (suc m)} n i e

c-sw : ∀ {χ : Fv} {x y j} n → j <ᴸ n → Sub∞ (upd (upd χ n x) j y) (upd (upd χ j y) n x)
c-sw {j = zero} (suc n) q zero e = e
c-sw {j = zero} (suc n) q (suc i) e = e
c-sw {j = suc j} (suc n) q zero e = e
c-sw {χ} {j = suc j} (suc n) q (suc i) e = c-sw {λ m → χ (suc m)} {j = j} n (dn q) i e

ι↓ : ∀ {n k α φ χ} → Q n k φ χ → Q (suc n) α φ (upd χ n (flo k))
ι↓ q0 = q0
ι↓ (qs a) = qs (ι↓ a)
ι↓ (ql F) = ql (λ i → ι↓ (F i))
ι↓ (qi ac f) = qi ac (λ x → ι↓ (f x))
ι↓ (qŝ c₀ t g) = qŝ c₀ (ι↓ t) (λ η e → ι↓ (g η e))
ι↓ (qĉ c₀ z zg o₀ o) = qĉ c₀ z zg (ι↓ o₀) (λ η e → ι↓ (o η e))
ι↓ (qclo t g) = qclo (ι↓ t) (λ η → ι↓ (g η))
ι↓ {χ = χ} (qcl {n = j} q ψ s t g) =
  qcl (suc q) ψ (λ e → s (subst (Ev _) (upd-lt χ _ q) e)) (ι↓ t) (λ η → qwk (λ e → e) (⇑ (c-sw {χ} _ q)) (ι↓ (g η)))
ι↓ {n = n} (qwk le le′ t) = qwk le (upd-sub n le′ (λ e → e)) (ι↓ t)
ι↓ {χ = χ} (qΩ↓ {n = j} q fe ac h) =
  qΩ↓ (suc q) fe (λ e → ac (subst (Ev _) (upd-lt χ _ q) e)) (λ ξ ζ z → qwk (λ e → e) (⇑ (c-∪ {lo j ζ} {χ} _)) (ι↓ (h ξ ζ z)))
ι↓ {n = n} {k = k} {χ = χ} (qΩ fe r h) =
  qΩ↓ zero fe (λ e → cvFlo k (subst (Ev _) (upd-self χ n _) e) r) (λ ξ ζ z → qwk (λ e → e) (⇑ (c-∪ {lo n ζ} {χ} _)) (ι↓ (h ξ ζ (intoU (<→◃ r) z))))
ι↓ {n = n} {k = suc a} (omk zero z x) = qwk (λ e → e) (⇑ (upd-map n (λ i e → e) (λ e → toFlo a (λ q → e (suc q))))) (ι↓ z)
ι↓ {n = n} {k = lim f s} (omk (self i) z x) = qwk (λ e → e) (⇑ (upd-map n (λ j e → e) (λ e → toFlo (f i) (λ q → e (lim i q))))) (ι↓ z)

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

Ω̇ : ∀ m α → Q m α Fl (κ Fl)
Ω̇ m (suc α) = qΩ (λ e → e) zero (λ ξ ζ z → qwk proj₁ (λ i q e → subst (Ev _) (lo-lt ζ q) (proj₁ e)) (omk zero z (ι zero z)))
Ω̇ m (lim f s) = ql (λ n → omk (self n) (Ω̇ m (f n)) (ι (self n) (Ω̇ m (f n))))
Ω̇ zero zero = qclo (tl (fz ⊔ fk zero) proj₂ (Ωˢ (suc zero))) (λ η → tl (fz ⊔ fk η) (λ e q → proj₂ e (suc q)) (Ωˢ η))
Ω̇ (suc m) zero =
  qcl zero fz (λ e → e)
      (qwk (λ e → e) (⇑ (λ i e → up₁ i e)) (ι↓ (Ω̇ m (suc zero))))
      (λ η → qwk (λ e → e) (upd-sub m (λ i q e → e) (λ e → toFlo η (λ q → proj₂ e (suc q)))) (ι↓ (Ω̇ m η)))
  where
  up₁ : ∀ i {ℓ} → Ev ℓ (κ Fl i) → Ev ℓ (upd (κ Fl) m (flo (suc zero)) i)
  up₁ i = go m i
    where
    go : ∀ m i {ℓ} → Ev ℓ Fl → Ev ℓ (upd (κ Fl) m (fk zero) i)
    go zero zero e = proj₂ e
    go zero (suc i) e = e
    go (suc m) zero e = e
    go (suc m) (suc i) e = go m i e
```

## §5 折叠

`ψᵠ`: 字面目标 (顶层). `Ψ`: 目标在高度 $H<m$, 只吃高度 $\ge H$ 的证据, 输出在 `Q H t`. `ψ̄ᵠ`: 目标可数. 高度 $n$ 的闭包: $n<H$ 穿过; $n=H$ 落成字面闭包, 界含目标; $n>H$ 落成字面闭包, 界不含目标. 高度 $n$ 的节点: $n<H$ 穿过; $n=H$ 比较; $n>H$ 走链, 链在 `Q n k`. 与 [ScafLadderTree](ScafLadderTree.lagda.md) 是 $m=1$ 的同一个定义.

```agda
Ev-lo : ∀ {a : Fv} H i {ℓ} → Ev ℓ (a i) → Ev ℓ (lo H a i)
Ev-lo zero    i e = tt
Ev-lo (suc H) zero e = e
Ev-lo {a} (suc H) (suc i) e = Ev-lo {λ m → a (suc m)} H i e

Hi : ℕ → ℕ → Set
Hi H i = (H ≡ i) ⊎ (H <ᴸ i)

lo-triv : ∀ {H i} (a : Fv) → Hi H i → ∀ {ℓ} → Ev ℓ (lo H a i)
lo-triv {H = zero} a h = tt
lo-triv {H = suc H} {i = suc i} a (inj₁ refl) = lo-triv {H = H} {i = i} (λ m → a (suc m)) (inj₁ refl)
lo-triv {H = suc H} {i = suc i} a (inj₂ r) = lo-triv {H = H} {i = i} (λ m → a (suc m)) (inj₂ (dn r))
lo-triv {H = suc H} {i = zero} a (inj₂ ())

Ok : (ℕ → Ordᴵ) → Set
Ok w = ∀ i → Ev (w i) Fl

Eh : ℕ → ℕ → (ℕ → Ordᴵ) → Fv → Set
Eh H m w χ = ∀ i → Hi H i → i <ᴸ m → Ev (w i) (χ i)

upd-ev : ∀ {ℓ′ z} n i (w : ℕ → Ordᴵ) (χ : Fv) → Ev ℓ′ z → Ev (w i) (χ i) → Ev (upd w n ℓ′ i) (upd χ n z i)
upd-ev zero zero w χ a b = a
upd-ev zero (suc i) w χ a b = b
upd-ev (suc n) zero w χ a b = b
upd-ev (suc n) (suc i) w χ a b = upd-ev n i (λ m → w (suc m)) (λ m → χ (suc m)) a b

upd-ok : ∀ {ℓ′} n (w : ℕ → Ordᴵ) → Ok w → Ev ℓ′ Fl → Ok (upd w n ℓ′)
upd-ok zero w ok a zero = a
upd-ok zero w ok a (suc i) = ok (suc i)
upd-ok (suc n) w ok a zero = ok zero
upd-ok (suc n) w ok a (suc i) = upd-ok n (λ m → w (suc m)) (λ m → ok (suc m)) a i

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

e⁺ : ∀ {H m w} {χ : Fv} (n : ℕ) → Ok w → Eh H m w χ → Eh H m w (lo n (Z* χ) ∪ χ)
e⁺ {χ = χ} n ok e i h r = Ev-lo {Z* χ} n i (ok i , e i h r) , e i h r

Hi-tr : ∀ {n H i} → Hi n H → Hi H i → Hi n i
Hi-tr (inj₁ refl) h = h
Hi-tr (inj₂ l) (inj₁ refl) = inj₂ l
Hi-tr (inj₂ l) (inj₂ r) = inj₂ (tr< l r)

Hi-0 : ∀ i → Hi zero i
Hi-0 zero = inj₁ refl
Hi-0 (suc i) = inj₂ (z<s i)

e-lo : ∀ {H m w n} {χ : Fv} (ζ : Fv) → Hi n H → Eh H m w χ → Eh H m w (lo n ζ ∪ χ)
e-lo ζ le e i h r = lo-triv ζ (Hi-tr le h) , e i h r

e↑ : ∀ {H n m w} {χ : Fv} → H <ᴸ n → Eh H m w χ → Eh n m w χ
e↑ l e i h′ r = e i (Hi-up l h′) r

e↓ : ∀ {n m w} {χ : Fv} → Eh zero m w χ → Eh n m w χ
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
ψ̄ᵠ : ∀ {m c φ χ w} → Ok w → Eh zero m w χ → Q m c φ χ → Run φ
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

w₀ : ℕ → Ordᴵ
w₀ _ = suc zero

ok₀ : Ok w₀
ok₀ i = tt , (λ q → q)

-- ψ₀(Ω_{Ω·(m+1)+α})
Tᵠ : ∀ m α → Run Fl
Tᵠ m α = ψ̄ᵠ ok₀ (λ i h r → ok₀ i) (Ω̇ m α)

-- ψ₀(Ω_{Ω·ω}): 第 n 项是 ψ₀(Ω_{Ω·n}), 第 0 项是 ψ₀(Ω₀) = ψ₀(1)
Tωn : ℕ → Run Fl
Tωn zero    = ψ̄ᵠ {m = 0} {c = zero} {χ = κ Fl} ok₀ (λ i h r → ok₀ i) (qs q0)
Tωn (suc n) = Tᵠ n zero

Tω : Run Fl
Tω = limA 0 Tωn
```
