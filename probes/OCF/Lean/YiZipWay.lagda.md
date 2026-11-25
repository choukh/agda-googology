# 派发结果带搬运: `Way′` 与结点的两行

非验收文件. 编译定理, 无前提. `Way′ m j` 的保留项 `keep′ s t` 带一个保 `top`, 保第一位置, 保合法的搬运 `t : Mv (lev m s) j`, 不带层号的字面相等; 实例 `byMv` (结构搬运 `mv`), `byEq` (沿相等, 就是旧的 `keep`).
结点那一行 `ΨN′` 与 `top` 那一行 `ΩT′` 对一切 `Way′` 保合法 (`ΨN′-lgl`, `ΩT′-lgl`), `ΨN′-dn` 保第一位置; 旧的 `keep s e` 经 `fromWay` 给出逐字相同的结点 (`ΨN′-eq`, `ΩT′-eq`, 都是 `refl` 归纳).

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiZipWay where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import OCF.Lean.YiNextCore
open import OCF.Lean.YiNextBase using
  ( Br; DnB; LgB; dnLc; lgLc; lev; Way; keep; fold; nodeAt; nodeAt-dn; nodeAt-lgl; chain; chain-lgl
  ; plus-weak; Ψn; ΨN; ΩT )
open import OCF.Lean.YiZipMove
```

## 1 搬运的接口

```agda
record Mv (L j : LF) : Set where
  constructor mvr
  field
    run    : Raw L → Raw j
    run-tp : run G.top ≡ G.top
    run-cp : ∀ {x y} → Cp L x y → Cp j (run x) (run y)
    run-lg : ∀ x → Lgl L x → Lgl j (run x)
open Mv public

byMv : ∀ L j → Mv L j
byMv L j = mvr (mv L j) refl (mv-cp L j) (mv-lgl L j)

byEq : ∀ {L j} → L ≡ j → Mv L j
byEq refl = mvr (λ x → x) refl (λ p → p) (λ x l → l)

_⨾_ : ∀ {a b c} → Mv a b → Mv b c → Mv a c
t ⨾ u = mvr (λ x → run u (run t x)) (trans (cong (run u) (run-tp t)) (run-tp u))
  (λ p → run-cp u (run-cp t p)) (λ x l → run-lg u _ (run-lg t x l))

Br-run : ∀ {L j M} (t : Mv L j) (g : Raw j → Raw M) → Br (layer j) M g → Br (layer L) M (λ η → g (run t η))
Br-run t g (lg , mo) = (λ η l → lg (run t η) (run-lg t η l)) ,
  (λ η η′ l e l′ → mo _ _ (run-lg t η l) (run-cp t e) (run-lg t η′ l′))
```

## 2 派发结果

```agda
data Way′ (m j : LF) : Set where
  keep′ : (s : Pre m) → Mv (lev m s) j → Way′ m j
  fold′ : Way′ m j

Ext′ : LF → LF → Set
Ext′ m k = (r : Pre k) → Way′ m (lev k r)

fromWay : ∀ {m j} → Way m j → Way′ m j
fromWay (keep s e) = keep′ s (byEq e)
fromWay fold = fold′

thenMv : ∀ {m j j′} → Way′ m j → Mv j j′ → Way′ m j′
thenMv (keep′ s t) u = keep′ s (t ⨾ u)
thenMv fold′ u = fold′
```

## 3 结点的两行

```agda
Ψn′ : ∀ m j → Way′ m j → (Raw j → Raw m) → (Raw j → Raw j) → Raw m
Ψn′ m j (keep′ p t) gm gk = nodeAt m p G.lc (λ η → gm (run t η))
Ψn′ m j fold′ gm gk = G.lim (λ n → gm (chain j gk n))

ΨN′ : ∀ m k (r : Pre k) → Way′ m (lev k r) →
  (Lay.A (Lo k r) → Raw m) → (Lay.A (Lo k r) → Raw (lev k r)) → Raw m
ΨN′ m (suc k) (inj₁ _) = Ψn′ m k
ΨN′ m (suc k) (inj₂ r) = ΨN′ m k r
ΨN′ m (lim f) (n , r) = ΨN′ m (f n) r
ΨN′ m (lc j g) (η , _ , r) = ΨN′ m (g η) r

ΩT′ : ∀ m j → Way′ m j → (Raw j → Raw m) → (ℕ → Raw m) → Raw m
ΩT′ m j (keep′ p t) K o = nodeAt m p G.lc (λ η → K (run t η))
ΩT′ m j fold′ K o = G.lim o

Ψn′-dn : ∀ m j (w : Way′ m j) gm gk {z} → Cp m z (gm G.top) → Dn m z (Ψn′ m j w gm gk)
Ψn′-dn m j (keep′ p t) gm gk {z} q =
  nodeAt-dn m p G.lc dnLc (λ η → gm (run t η)) (subst (λ u → Cp m z (gm u)) (sym (run-tp t)) q)
Ψn′-dn m j fold′ gm gk q = 0 , q

Ψn′-lgl : ∀ m j (w : Way′ m j) gm gk → Br (layer j) m gm → (∀ η → Lgl j η → Lgl j (gk η)) →
  Lgl m (Ψn′ m j w gm gk)
Ψn′-lgl m j (keep′ p t) gm gk hm hk = nodeAt-lgl m p G.lc lgLc _ (Br-run t gm hm)
Ψn′-lgl m j fold′ gm gk (lg , mo) hk =
  (λ n → mo _ _ (chain-lgl j gk hk n) (plus-weak j _ _) (chain-lgl j gk hk (suc n))) ,
  (λ n → lg _ (chain-lgl j gk hk n))

ΨN′-dn : ∀ m k r (w : Way′ m (lev k r)) gm gk {z} → Cp m z (gm (Lay.tp (Lo k r))) →
  Dn m z (ΨN′ m k r w gm gk)
ΨN′-dn m (suc k) (inj₁ _) = Ψn′-dn m k
ΨN′-dn m (suc k) (inj₂ r) = ΨN′-dn m k r
ΨN′-dn m (lim f) (n , r) = ΨN′-dn m (f n) r
ΨN′-dn m (lc j g) (η , _ , r) = ΨN′-dn m (g η) r

ΨN′-lgl : ∀ m k r (w : Way′ m (lev k r)) gm gk → Br (Lo k r) m gm →
  (∀ η → Lay.lg (Lo k r) η → Lgl (lev k r) (gk η)) → Lgl m (ΨN′ m k r w gm gk)
ΨN′-lgl m (suc k) (inj₁ _) = Ψn′-lgl m k
ΨN′-lgl m (suc k) (inj₂ r) = ΨN′-lgl m k r
ΨN′-lgl m (lim f) (n , r) = ΨN′-lgl m (f n) r
ΨN′-lgl m (lc j g) (η , _ , r) = ΨN′-lgl m (g η) r

ΩT′-lgl : ∀ m j (w : Way′ m j) K o → Br (layer j) m K → Lgl m (G.lim o) → Lgl m (ΩT′ m j w K o)
ΩT′-lgl m j (keep′ p t) K o b l = nodeAt-lgl m p G.lc lgLc _ (Br-run t K b)
ΩT′-lgl m j fold′ K o b l = l
```

## 4 旧的保留是特例

```agda
Ψn′-eq : ∀ m j (w : Way m j) gm gk → Ψn′ m j (fromWay w) gm gk ≡ Ψn m j w gm gk
Ψn′-eq m .(lev m p) (keep p refl) gm gk = refl
Ψn′-eq m j fold gm gk = refl

ΨN′-eq : ∀ m k r (w : Way m (lev k r)) gm gk → ΨN′ m k r (fromWay w) gm gk ≡ ΨN m k r w gm gk
ΨN′-eq m (suc k) (inj₁ _) = Ψn′-eq m k
ΨN′-eq m (suc k) (inj₂ r) = ΨN′-eq m k r
ΨN′-eq m (lim f) (n , r) = ΨN′-eq m (f n) r
ΨN′-eq m (lc j g) (η , _ , r) = ΨN′-eq m (g η) r

ΩT′-eq : ∀ m j (w : Way m j) K o → ΩT′ m j (fromWay w) K o ≡ ΩT m j w K o
ΩT′-eq m .(lev m p) (keep p refl) K o = refl
ΩT′-eq m j fold K o = refl
```
