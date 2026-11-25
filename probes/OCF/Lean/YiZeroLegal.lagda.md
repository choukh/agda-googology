# YiZero 合法性：加法与折叠的输出合法，保持第一位置

**判决：编译定理 (第 3 层)。** 对任意外部派发 `x`：`Ψ` 保持第一位置 (`Ψ-cp`)，合法的输入折成合法的输出 (`Ψ-lgl`)；加法同样。证法照 [YiLeanLegal](YiLeanLegal.lagda.md)。
ω 倍从零起多出两条引理：折叠的输出在第一位置上不低于 `zero` (`zero≤`)，`top` 的折叠严格高于 `top` (`top<`)；`x + top` 严格高于 `x` (`add-top`)。
合法性不携带强度。折叠在 [YiZeroFold](YiZeroFold.lagda.md)，闭项在 [YiZeroTw3](YiZeroTw3.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiZeroLegal where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiZeroCore
open import OCF.Lean.YiZeroFold
```

## 1 造结点的办法

```agda
Br : (X : Lay) (M : LF) → (Lay.A X → Raw M) → Set
Br X M g = (∀ η → Lay.lg X η → Lgl M (g η)) ×
  (∀ η η′ → Lay.lg X η → Le X η η′ → Lay.lg X η′ → Cp M (g η) (g η′))

DnB : ∀ {M k} → Bld M k → Set
DnB {M} {k} B = ∀ r g {z} → Cp M z (g (Lay.tp (Lo k r))) → Dn M z (B r g)

LgB : ∀ {M k} → Bld M k → Set
LgB {M} {k} B = ∀ r g → Br (Lo k r) M g → Lgl M (B r g)

dnLc : ∀ {M} → DnB {M} {M} G.lc
dnLc r g p = p

lgLc : ∀ {M} → LgB {M} {M} G.lc
lgLc r g h = h

acc-ind : ∀ {T : Set} (P : T → Set) (s : ℕ → T → T) →
  (∀ n y → P y → P (s n y)) → ∀ x → P x → ∀ n → P (acc s x n)
acc-ind P s h x px zero = px
acc-ind P s h x px (suc n) = h n _ (acc-ind P s h x px n)
```

## 2 加法

```agda
add-top : ∀ {M} k (B : Bld M k) → DnB B → ∀ x → Dn M x (add k B x G.top)
add-top zero B h x = inj₁ refl
add-top (suc k) B h x = h (inj₁ tt) _ (inj₂ (add-top k _ (λ r → h (inj₂ r)) x))
add-top (lim f) B h x = 0 , inj₂ (add-top (f 0) _ (λ r → h (0 , r)) x)
add-top (lc j g) B h x = inj₁ refl

add-cp : ∀ {M} k (B : Bld M k) → DnB B → ∀ x {a b} → Cp k a b → Cp M (add k B x a) (add k B x b)
add-dn : ∀ {M} k (B : Bld M k) → DnB B → ∀ x {a} b → Dn k a b → Dn M (add k B x a) (add k B x b)

add-cp k B h x (inj₁ refl) = inj₁ refl
add-cp k B h x (inj₂ p) = inj₂ (add-dn k B h x _ p)

add-dn k B h x (G.suc b) p = add-cp k B h x p
add-dn k B h x (G.lim f) (n , p) = n , add-cp k B h x p
add-dn k B h x (G.lc r g) p = h r _ (add-cp k B h x p)
add-dn (suc k) B h x {G.em _ a} (G.em _ d) (refl , p) = add-dn k _ (λ r → h (inj₂ r)) x d p
add-dn (lim f) B h x {G.em n a} (G.em _ d) (refl , p) = add-dn (f n) _ (λ r → h (n , r)) x d p
add-dn (lc j g) B h x {G.em (η , l) a} (G.em _ d) (refl , p) =
  add-dn (g η) _ (λ r → h (η , l , r)) x d p
add-dn k B h x G.top refl = add-top k B h x

add-weak : ∀ {M} k (B : Bld M k) → DnB B → ∀ x a → Cp M x (add k B x a)
add-weak k B h x G.zero = inj₁ refl
add-weak k B h x (G.suc a) = inj₂ (add-weak k B h x a)
add-weak k B h x (G.lim f) = inj₂ (0 , add-weak k B h x (f 0))
add-weak k B h x (G.lc r g) = inj₂ (h r _ (add-weak k B h x (g _)))
add-weak zero B h x (G.em () a)
add-weak (suc k) B h x (G.em _ a) = add-weak k _ (λ r → h (inj₂ r)) x a
add-weak (lim f) B h x (G.em n a) = add-weak (f n) _ (λ r → h (n , r)) x a
add-weak (lc j g) B h x (G.em (η , l) a) = add-weak (g η) _ (λ r → h (η , l , r)) x a
add-weak k B h x G.top = inj₂ (add-top k B h x)

add-lgl : ∀ {M} k (B : Bld M k) → DnB B → LgB B → ∀ x a → Lgl M x → Lgl k a → Lgl M (add k B x a)
add-lgl k B h b x G.zero lx la = lx
add-lgl k B h b x (G.suc a) lx la = add-lgl k B h b x a lx la
add-lgl k B h b x (G.lim f) lx (st , lf) =
  (λ n → add-cp k B h x (st n)) , (λ n → add-lgl k B h b x (f n) lx (lf n))
add-lgl k B h b x (G.lc r g) lx (lg , mo) = b r _
  ((λ η l → add-lgl k B h b x (g η) lx (lg η l)) ,
   (λ η η′ l e l′ → add-cp k B h x (mo η η′ l e l′)))
add-lgl zero B h b x (G.em () a) lx la
add-lgl (suc k) B h b x (G.em _ a) lx la =
  add-lgl k _ (λ r → h (inj₂ r)) (λ r → b (inj₂ r)) x a lx la
add-lgl (lim f) B h b x (G.em n a) lx la =
  add-lgl (f n) _ (λ r → h (n , r)) (λ r → b (n , r)) x a lx la
add-lgl (lc j g) B h b x (G.em (η , l) a) lx la =
  add-lgl (g η) _ (λ r → h (η , l , r)) (λ r → b (η , l , r)) x a lx la
add-lgl zero B h b x G.top lx la = lx
add-lgl (suc k) B h b x G.top lx la = b (inj₁ tt) _
  ((λ η l → add-lgl k _ (λ r → h (inj₂ r)) (λ r → b (inj₂ r)) x η lx l) ,
   (λ η η′ l e l′ → add-cp k _ (λ r → h (inj₂ r)) x e))
add-lgl (lim f) B h b x G.top lx la =
  (λ n → add-weak (f (suc n)) _ (λ r → h (suc n , r)) _ G.top) ,
  (λ n → acc-ind (Lgl _) _ (λ i y ly →
    add-lgl (f i) _ (λ r → h (i , r)) (λ r → b (i , r)) y G.top ly tt) x lx (suc n))
add-lgl (lc j g) B h b x G.top lx la = lx
```

第 `m` 层自己的加法、ω 倍与部分和。ω 倍的第 0 步要 `zero` 是 `y` 的第一位置 (前提 `z`)。

```agda
plus-weak : ∀ m x a → Cp m x (plus m x a)
plus-weak m = add-weak m G.lc dnLc

plus-lgl : ∀ m x a → Lgl m x → Lgl m a → Lgl m (plus m x a)
plus-lgl m = add-lgl m G.lc dnLc lgLc

succ-step : ∀ m y → Cp m G.zero y →
  ∀ n → Cp m (acc (λ _ z → plus m y z) G.zero n) (acc (λ _ z → plus m y z) G.zero (suc n))
succ-step m y z zero = z
succ-step m y z (suc n) = add-cp m G.lc dnLc y (succ-step m y z n)

succ-lgl : ∀ m y → Cp m G.zero y → Lgl m y → Lgl m (succ m y)
succ-lgl m y z ly = succ-step m y z , acc-ind (Lgl m) _ (λ _ w lw → plus-lgl m y w ly lw) G.zero tt

psum-lgl : ∀ m h → (∀ n → Lgl m (h n)) → Lgl m (G.lim (psum m h))
psum-lgl m h lh = (λ n → plus-weak m _ (h (suc n))) ,
  acc-ind (Lgl m) _ (λ n z lz → plus-lgl m z (h (suc n)) lz (lh (suc n))) (h zero) (lh zero)
```

## 3 结点的两行

```agda
nodeAt-dn : ∀ {M} m p (B : Bld M m) → DnB B → ∀ g {z} → Cp M z (g G.top) → Dn M z (nodeAt m p B g)
nodeAt-dn (suc k) (inj₁ _) B h g q = h (inj₁ tt) g q
nodeAt-dn (suc k) (inj₂ p) B h = nodeAt-dn k p _ (λ r → h (inj₂ r))
nodeAt-dn (lim f) (n , p) B h = nodeAt-dn (f n) p _ (λ r → h (n , r))
nodeAt-dn (lc j g) (η , l , p) B h = nodeAt-dn (g η) p _ (λ r → h (η , l , r))

nodeAt-lgl : ∀ {M} m p (B : Bld M m) → LgB B → ∀ g → Br (layer (lev m p)) M g → Lgl M (nodeAt m p B g)
nodeAt-lgl (suc k) (inj₁ _) B b = b (inj₁ tt)
nodeAt-lgl (suc k) (inj₂ p) B b = nodeAt-lgl k p _ (λ r → b (inj₂ r))
nodeAt-lgl (lim f) (n , p) B b = nodeAt-lgl (f n) p _ (λ r → b (n , r))
nodeAt-lgl (lc j g) (η , l , p) B b = nodeAt-lgl (g η) p _ (λ r → b (η , l , r))

chain-lgl : ∀ j gk → (∀ η → Lgl j η → Lgl j (gk η)) → ∀ n → Lgl j (chain j gk n)
chain-lgl j gk h zero = tt
chain-lgl j gk h (suc n) = plus-lgl j _ _ (chain-lgl j gk h n) (h _ (chain-lgl j gk h n))

Ψn-dn : ∀ m j (w : Way m j) gm gk {z} → Cp m z (gm G.top) → Dn m z (Ψn m j w gm gk)
Ψn-dn m .(lev m p) (keep p refl) gm gk q = nodeAt-dn m p G.lc dnLc gm q
Ψn-dn m j fold gm gk q = 0 , q

Ψn-lgl : ∀ m j (w : Way m j) gm gk → Br (layer j) m gm → (∀ η → Lgl j η → Lgl j (gk η)) →
  Lgl m (Ψn m j w gm gk)
Ψn-lgl m .(lev m p) (keep p refl) gm gk hm hk = nodeAt-lgl m p G.lc lgLc gm hm
Ψn-lgl m j fold gm gk (lg , mo) hk =
  (λ n → mo _ _ (chain-lgl j gk hk n) (plus-weak j _ _) (chain-lgl j gk hk (suc n))) ,
  (λ n → lg _ (chain-lgl j gk hk n))

ΨN-dn : ∀ m k r (w : Way m (lev k r)) gm gk {z} → Cp m z (gm (Lay.tp (Lo k r))) →
  Dn m z (ΨN m k r w gm gk)
ΨN-dn m (suc k) (inj₁ _) = Ψn-dn m k
ΨN-dn m (suc k) (inj₂ r) = ΨN-dn m k r
ΨN-dn m (lim f) (n , r) = ΨN-dn m (f n) r
ΨN-dn m (lc j g) (η , _ , r) = ΨN-dn m (g η) r

ΨN-lgl : ∀ m k r (w : Way m (lev k r)) gm gk → Br (Lo k r) m gm →
  (∀ η → Lay.lg (Lo k r) η → Lgl (lev k r) (gk η)) → Lgl m (ΨN m k r w gm gk)
ΨN-lgl m (suc k) (inj₁ _) = Ψn-lgl m k
ΨN-lgl m (suc k) (inj₂ r) = ΨN-lgl m k r
ΨN-lgl m (lim f) (n , r) = ΨN-lgl m (f n) r
ΨN-lgl m (lc j g) (η , _ , r) = ΨN-lgl m (g η) r
```

## 4 折叠

`zero≤`, `top<`：ω 倍从零起之后，ω 倍的第 0 步与 `zero` 对 `top` 的那一步要它们。

```agda
zero≤ : ∀ m {k} (V : Lv k) x ξ → Cp m G.zero (Ψ m V x ξ)
zero≤ m V x G.zero = inj₂ refl
zero≤ m V x (G.suc a) = inj₂ (0 , inj₁ refl)
zero≤ m V x (G.lim f) = inj₂ (0 , zero≤ m V x (f 0))
zero≤ m {k} V x (G.lc r g) = inj₂ (ΨN-dn m k r (x r) _ _ (zero≤ m V x (g _)))
zero≤ m v0 x (G.em () a)
zero≤ m (vs V) x (G.em _ a) = zero≤ m V _ a
zero≤ m (vl V st) x (G.em n a) = zero≤ m (V n) _ a
zero≤ m v0 x G.top = inj₂ (0 , inj₁ refl)
zero≤ m {suc k} (vs V) x G.top = inj₂ (Ψn-dn m k (x (inj₁ tt)) _ _ (zero≤ m V _ G.top))
zero≤ m (vl V st) x G.top = inj₂ (0 , zero≤ m (V 0) _ G.top)

top< : ∀ m {k} (V : Lv k) x → Dn m G.top (Ψ m V x G.top)
top< m v0 x = 1 , inj₁ refl
top< m {suc k} (vs V) x = Ψn-dn m k (x (inj₁ tt)) _ _ (inj₂ (top< m V _))
top< m (vl V st) x = 0 , inj₂ (top< m (V 0) _)

Ψ-cp : ∀ m {k} (V : Lv k) x {ξ ξ′} → Cp k ξ ξ′ → Cp m (Ψ m V x ξ) (Ψ m V x ξ′)
Ψ-dn : ∀ m {k} (V : Lv k) x {ξ} ξ′ → Dn k ξ ξ′ → Dn m (Ψ m V x ξ) (Ψ m V x ξ′)

Ψ-cp m V x (inj₁ refl) = inj₁ refl
Ψ-cp m V x (inj₂ p) = inj₂ (Ψ-dn m V x _ p)

Ψ-dn m V x (G.suc d) p = 1 , Ψ-cp m V x p
Ψ-dn m V x (G.lim f) (n , p) = n , Ψ-cp m V x p
Ψ-dn m {k} V x (G.lc r g) p = ΨN-dn m k r (x r) _ _ (Ψ-cp m V x p)
Ψ-dn m (vs V) x {G.em _ a} (G.em _ d) (refl , p) = Ψ-dn m V _ d p
Ψ-dn m (vl V st) x {G.em n a} (G.em _ d) (refl , p) = Ψ-dn m (V n) _ d p
Ψ-dn m V x G.top refl = top< m V x

Ψ-lgl : ∀ m {k} (V : Lv k) x ξ → Lgl k ξ → Lgl m (Ψ m V x ξ)
Ψ-lgl m V x G.zero l = tt
Ψ-lgl m V x (G.suc a) l = succ-lgl m _ (zero≤ m V x a) (Ψ-lgl m V x a l)
Ψ-lgl m V x (G.lim f) (st , lf) = (λ n → Ψ-cp m V x (st n)) , (λ n → Ψ-lgl m V x (f n) (lf n))
Ψ-lgl m {k} V x (G.lc r g) (lg , mo) = ΨN-lgl m k r (x r) _ _
  ((λ η l → Ψ-lgl m V x (g η) (lg η l)) , (λ η η′ l e l′ → Ψ-cp m V x (mo η η′ l e l′)))
  (λ η l → Ψ-lgl (lev k r) V (cmp V r) (g η) (lg η l))
Ψ-lgl m (vs V) x (G.em _ a) l = Ψ-lgl m V _ a l
Ψ-lgl m (vl V st) x (G.em n a) l = Ψ-lgl m (V n) _ a l
Ψ-lgl m v0 x G.top l = succ-lgl m G.top (inj₂ refl) tt
Ψ-lgl m {suc k} (vs V) x G.top l = Ψn-lgl m k (x (inj₁ tt)) _ _
  ((λ η l → Ψ-lgl m V _ η l) , (λ η η′ l e l′ → Ψ-cp m V _ e)) (λ η l → Ψ-lgl k V (self k) η l)
Ψ-lgl m (vl V st) x G.top l = psum-lgl m _ (λ n → Ψ-lgl m (V n) _ G.top tt)
```
