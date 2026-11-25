# 带燃料的字面搜索: 可靠, 只保留有限层号; 在规范链问到的极限目标 `J` 上完全

非验收文件. 编译定理, 无前提. `look fu k n` 在目标层 `k` 里找层号字面为 `fin n` 的槽位 (ℕ 极限只看前 `fu + 1` 个分量, Ω 结点层号只看 `top` 支); 派发 `dpol φ` 用燃料 `φ n`. 保留的都在目标之下 (`sound`), 且层号字面有限 (`fin-only`), 所以不判定极限层号的相等.
[YiLamNAsk](YiLamNAsk.lagda.md) 那一处保留 (`keeps♯`, 有限测试); 燃料取层号本身时在 `J` 上对一切位置完全 (`dlev-full-J`), 而 `Lam` 的 `stp` 在那里不完全 (`lam-not-full-J`); 在 [YiLamNLim](YiLamNLim.lagda.md) 的 `j₀` 上不完全 (`dpol-not-full₀`).
不陈述值; 不把 `dpol` 接进折叠.

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiLamNFuel where

open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using (≤-refl; m<n⇒m<1+n; n<1+n; m≤n⇒m<n∨m≡n)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; subst)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using (R; lev; Way; keep; fold; Ext; succ)
open import OCF.Lean.YiLamFold using (fin; eqFin; finOf)
open import OCF.Lean.YiUniIf using (At; IsKeep; Full)
open import OCF.Lean.YiLamIf using (StpFullᴾ)
open import OCF.Lean.YiLamNInst using (Lam)
open import OCF.Lean.YiLamNAsk using (J; r♯; VJ; could)
open import OCF.Lean.YiLamNLim using (j₀; r₀′)
```

## 1 搜索与派发

```agda
Sl : LF → ℕ → Set
Sl k n = Σ (Pre k) λ s → lev k s ≡ fin n

IsJust : ∀ {A : Set} → Maybe A → Set
IsJust (just _) = ⊤
IsJust nothing = ⊥

orM : ∀ {A : Set} → Maybe A → Maybe A → Maybe A
orM (just a) b = just a
orM nothing b = b

firstJ : ∀ {A : Set} → ℕ → (ℕ → Maybe A) → Maybe A
firstJ zero h = h zero
firstJ (suc n) h = orM (h zero) (firstJ n (λ i → h (suc i)))

lookS : ∀ k n → Maybe (fin n ≡ k) → Maybe (Sl k n) → Maybe (Sl (suc k) n)
lookS k n (just e) b = just (inj₁ tt , sym e)
lookS k n nothing (just (s , e)) = just (inj₂ s , e)
lookS k n nothing nothing = nothing

mapL : ∀ {f : ℕ → LF} i n → Maybe (Sl (f i) n) → Maybe (Sl (lim f) n)
mapL i n (just (s , e)) = just ((i , s) , e)
mapL i n nothing = nothing

mapC : ∀ {k g} n → Maybe (Sl (g G.top) n) → Maybe (Sl (lc k g) n)
mapC n (just (s , e)) = just ((G.top , tt , s) , e)
mapC n nothing = nothing

look : ℕ → (k : LF) → (n : ℕ) → Maybe (Sl k n)
look fu zero n = nothing
look fu (suc k) n = lookS k n (eqFin n k) (look fu k n)
look fu (lim f) n = firstJ fu (λ i → mapL i n (look fu (f i) n))
look fu (lc k g) n = mapC n (look fu (g G.top) n)

byLook : ∀ k L n → fin n ≡ L → Maybe (Sl k n) → Way k L
byLook k L n e (just (s , e′)) = keep s (trans e′ e)
byLook k L n e nothing = fold

byFin : (ℕ → ℕ) → ∀ k L → Maybe (Σ ℕ λ n → fin n ≡ L) → Way k L
byFin φ k L (just (n , e)) = byLook k L n e (look (φ n) k n)
byFin φ k L nothing = fold

pol : (ℕ → ℕ) → ∀ k L → Way k L
pol φ k L = byFin φ k L (finOf L)

dpol : (ℕ → ℕ) → ∀ k K → Ext k K
dpol φ k K r = pol φ k (lev K r)

dlev : ∀ k K → Ext k K
dlev = dpol (λ n → n)
```

## 2 可靠, 只保留有限层号

```agda
sound : ∀ φ k K r → IsKeep (dpol φ k K r) → At k (lev K r)
sound φ k K r = go (dpol φ k K r)
  where
  go : ∀ {j} (w : Way k j) → IsKeep w → At k j
  go (keep s e) _ = s , e

fin-only : ∀ φ k L → IsKeep (pol φ k L) → Σ ℕ λ n → fin n ≡ L
fin-only φ k L = go (finOf L)
  where
  go : (mb : Maybe (Σ ℕ λ n → fin n ≡ L)) → IsKeep (byFin φ k L mb) → Σ ℕ λ n → fin n ≡ L
  go (just ne) _ = ne
```

## 3 有限测试与不完全

```agda
keeps♯ : IsKeep (dlev J (upT J) r♯)
keeps♯ = tt

dpol-not-full₀ : ∀ φ → Full j₀ (upT j₀) (dpol φ j₀ (upT j₀)) → ⊥
dpol-not-full₀ φ full = full r₀′ ((0 , inj₁ tt) , refl)
```

## 4 在 `J` 上完全

`J` 的第 `i` 个分量字面上是 `fin (i + 2)` (`F-fin`); 层号 `fin m` 的槽位在第 `m` 个分量里.

```agda
sucs : ℕ → R → R
sucs zero x = x
sucs (suc i) x = G.suc (sucs i x)

Tᵢ : ℕ → R
Tᵢ i = acc (λ _ z → plus zero G.top z) G.top i

F : ℕ → LF
F i = up zero (plus zero G.top (Tᵢ i))

plus-sucs : ∀ i x → plus zero G.top (sucs i x) ≡ sucs i (plus zero G.top x)
plus-sucs zero x = refl
plus-sucs (suc i) x = cong G.suc (plus-sucs i x)

sucs-suc : ∀ i x → sucs i (G.suc x) ≡ G.suc (sucs i x)
sucs-suc zero x = refl
sucs-suc (suc i) x = cong G.suc (sucs-suc i x)

T-sucs : ∀ i → Tᵢ i ≡ sucs i G.top
T-sucs zero = refl
T-sucs (suc i) = trans (cong (plus zero G.top) (T-sucs i))
  (trans (plus-sucs i G.top) (sucs-suc i G.top))

up-sucs : ∀ n → up zero (sucs n G.top) ≡ fin (suc n)
up-sucs zero = refl
up-sucs (suc n) = cong suc (up-sucs n)

F-fin : ∀ i → F i ≡ fin (suc (suc i))
F-fin i = trans (cong (λ t → up zero (plus zero G.top t)) (T-sucs i))
  (trans (cong (up zero) (trans (plus-sucs i G.top) (sucs-suc i G.top))) (cong suc (up-sucs i)))

lev-fin : ∀ N (s : Pre (fin N)) → Σ ℕ λ m → (lev (fin N) s ≡ fin m) × (m < N)
lev-fin zero ()
lev-fin (suc N) (inj₁ tt) = N , refl , ≤-refl
lev-fin (suc N) (inj₂ s) with lev-fin N s
... | m , e , p = m , e , m<n⇒m<1+n p

lev-tr : ∀ {A B : LF} (p : A ≡ B) (s : Pre A) → lev A s ≡ lev B (subst Pre p s)
lev-tr refl s = refl

finOf-fin : ∀ m → finOf (fin m) ≡ just (m , refl)
finOf-fin zero = refl
finOf-fin (suc m) with finOf (fin m) | finOf-fin m
... | .(just (m , refl)) | refl = refl

eqFin-fin : ∀ n → eqFin n (fin n) ≡ just refl
eqFin-fin zero = refl
eqFin-fin (suc n) with eqFin n (fin n) | eqFin-fin n
... | .(just refl) | refl = refl

orM-l : ∀ {A : Set} (a b : Maybe A) → IsJust a → IsJust (orM a b)
orM-l (just a) b _ = tt

orM-r : ∀ {A : Set} (a b : Maybe A) → IsJust b → IsJust (orM a b)
orM-r (just a) b _ = tt
orM-r nothing b q = q

firstJ-hit : ∀ {A : Set} n (h : ℕ → Maybe A) i → i ≤ n → IsJust (h i) → IsJust (firstJ n h)
firstJ-hit zero h zero z≤n q = q
firstJ-hit (suc n) h zero p q = orM-l (h zero) _ q
firstJ-hit (suc n) h (suc i) (s≤s p) q = orM-r (h zero) _ (firstJ-hit n (λ j → h (suc j)) i p q)

mapL-j : ∀ {f : ℕ → LF} i n (mb : Maybe (Sl (f i) n)) → IsJust mb → IsJust (mapL {f} i n mb)
mapL-j i n (just _) _ = tt

lookS-r : ∀ k n a (b : Maybe (Sl k n)) → IsJust b → IsJust (lookS k n a b)
lookS-r k n (just e) b q = tt
lookS-r k n nothing (just _) q = tt

look-fin : ∀ fu N m → m < N → IsJust (look fu (fin N) m)
look-fin fu zero m ()
look-fin fu (suc N) m (s≤s p) with m≤n⇒m<n∨m≡n p
... | inj₁ lt = lookS-r (fin N) m _ _ (look-fin fu N m lt)
... | inj₂ refl = subst (λ a → IsJust (lookS (fin m) m a (look fu (fin m) m))) (sym (eqFin-fin m)) tt

look-J : ∀ m → IsJust (look m J m)
look-J m = firstJ-hit m _ m ≤-refl
  (mapL-j {F} m m _ (subst (λ X → IsJust (look m X m)) (sym (F-fin m))
    (look-fin m (suc (suc m)) m (m<n⇒m<1+n (n<1+n m)))))

byLook-j : ∀ k L n e (mb : Maybe (Sl k n)) → IsJust mb → IsKeep (byLook k L n e mb)
byLook-j k L n e (just _) _ = tt

pol-fin : ∀ m → IsKeep (pol (λ n → n) J (fin m))
pol-fin m = subst (λ mb → IsKeep (byFin (λ n → n) J (fin m) mb)) (sym (finOf-fin m))
  (byLook-j J (fin m) m refl _ (look-J m))

pol-J : ∀ L → At J L → IsKeep (pol (λ n → n) J L)
pol-J L ((i , s) , e) with lev-fin (suc (suc i)) (subst Pre (F-fin i) s)
... | m , em , p = subst (λ X → IsKeep (pol (λ n → n) J X))
  (trans (sym em) (trans (sym (lev-tr (F-fin i) s)) e)) (pol-fin m)

dlev-full-J : ∀ K → Full J K (dlev J K)
dlev-full-J K r a = pol-J (lev K r) a

lam-not-full-J : StpFullᴾ Lam VJ G.top tt → ⊥
lam-not-full-J full = full r♯ could
```
