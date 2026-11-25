# YiDiag 合法性：不累加的链靠 "top 是输出的第一位置" 与 "折叠保持第一位置"

**判决：编译定理 (第 3 层)。** `Ψ-cp`：折叠保持第一位置 (不要输入合法)；`Ψ-low`：`top` 与零是一切输出的第一位置；`top-mono`：目标层 0 上 `top` 的折叠沿层号的第一位置路径 (`≤ᵛ`) 是第一位置；
`Ψ-lgl`：层号带路径 (`LvL`) 时合法的输入折成合法的输出。不累加的链靠前两条，逐项的那一行靠第三条。不否定别的写法。闭项在 [YiDiagTw3](YiDiagTw3.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Lean.YiDiagLegal where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Lean.YiDiagCore
open import OCF.Lean.YiDiagFold
```

## 1 造结点的办法

与主线相同。

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

与主线相同，多一种情形：`x + top` 以 `x` 为严格第一位置 (`add-top`)，对应块里零是 `top` 的第一位置。

```agda
add-cp : ∀ {M} k (B : Bld M k) → DnB B → ∀ x {a b} → Cp k a b → Cp M (add k B x a) (add k B x b)
add-dn : ∀ {M} k (B : Bld M k) → DnB B → ∀ x {a} b → Dn k a b → Dn M (add k B x a) (add k B x b)
add-weak : ∀ {M} k (B : Bld M k) → DnB B → ∀ x a → Cp M x (add k B x a)
add-top : ∀ {M} k (B : Bld M k) → DnB B → ∀ x → Dn M x (add k B x G.top)

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

add-weak k B h x G.zero = inj₁ refl
add-weak k B h x (G.suc a) = inj₂ (add-weak k B h x a)
add-weak k B h x (G.lim f) = inj₂ (0 , add-weak k B h x (f 0))
add-weak k B h x (G.lc r g) = inj₂ (h r _ (add-weak k B h x (g _)))
add-weak zero B h x (G.em () a)
add-weak (suc k) B h x (G.em _ a) = add-weak k _ (λ r → h (inj₂ r)) x a
add-weak (lim f) B h x (G.em n a) = add-weak (f n) _ (λ r → h (n , r)) x a
add-weak (lc j g) B h x (G.em (η , l) a) = add-weak (g η) _ (λ r → h (η , l , r)) x a
add-weak k B h x G.top = inj₂ (add-top k B h x)

add-top zero B h x = inj₁ refl
add-top (suc k) B h x = h (inj₁ tt) _ (add-weak k _ (λ r → h (inj₂ r)) x G.top)
add-top (lim f) B h x = 0 , add-weak (f 0) _ (λ r → h (0 , r)) x G.top
add-top (lc j g) B h x = inj₁ refl

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

plus-cp : ∀ m y {a b} → Cp m a b → Cp m (plus m y a) (plus m y b)
plus-cp m = add-cp m G.lc dnLc

plus-weak : ∀ m x a → Cp m x (plus m x a)
plus-weak m = add-weak m G.lc dnLc

plus-lgl : ∀ m x a → Lgl m x → Lgl m a → Lgl m (plus m x a)
plus-lgl m = add-lgl m G.lc dnLc lgLc
```

## 3 ω 倍、部分和与极限层号的顶行

ω 倍从零起：第 0 步要 `y` 以零为第一位置，以后每步由加法保持第一位置给出。逐项的那一行要各项依次是第一位置 (`StepIf`，只在目标层 0 出现)。

```agda
mult-lgl : ∀ m y → Lgl m y → Cp m G.zero y → Lgl m (mult m y)
mult-lgl m y ly z = step , lgl
  where
  step : ∀ n → Cp m (iter (plus m y) G.zero n) (iter (plus m y) G.zero (suc n))
  step zero = z
  step (suc n) = plus-cp m y (step n)
  lgl : ∀ n → Lgl m (iter (plus m y) G.zero n)
  lgl zero = tt
  lgl (suc n) = plus-lgl m y _ ly (lgl n)

psum-lgl : ∀ m h → (∀ n → Lgl m (h n)) → Lgl m (G.lim (psum m h))
psum-lgl m h lh = (λ n → plus-weak m _ (h (suc n))) ,
  acc-ind (Lgl m) _ (λ n z lz → plus-lgl m z (h (suc n)) lz (lh (suc n))) (h zero) (lh zero)

StepIf : ∀ m → (ℕ → Raw m) → Set
StepIf zero h = ∀ n → Cp zero (h n) (h (suc n))
StepIf (suc m) h = ⊤
StepIf (lim f) h = ⊤
StepIf (lc k g) h = ⊤

ltop-lgl : ∀ m h → (∀ n → Lgl m (h n)) → StepIf m h → Lgl m (ltop m h)
ltop-lgl zero h lh st = st , lh
ltop-lgl (suc m) h lh st = psum-lgl (suc m) h lh
ltop-lgl (lim f) h lh st = psum-lgl (lim f) h lh
ltop-lgl (lc k g) h lh st = psum-lgl (lc k g) h lh

ltop-dn : ∀ m h {z} → Cp m z (h 0) → Dn m z (ltop m h)
ltop-dn zero h p = 0 , p
ltop-dn (suc m) h p = 0 , p
ltop-dn (lim f) h p = 0 , p
ltop-dn (lc k g) h p = 0 , p
```

## 4 结点的两行

折叠的链不累加：相邻两点 `ηₙ`, `gk ηₙ` 的第一位置由 "`top` 是 `gk` 的输出的第一位置" (第 0 步) 与 "`gk` 保持第一位置" (以后每步) 给出。

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

-- 结点层的折叠 gk 需要的三条：保持合法、保持第一位置、以 top 为第一位置。
Gk : (X : Lay) (j : LF) → (Lay.A X → Raw j) → Set
Gk X j gk = (∀ η → Lay.lg X η → Lgl j (gk η)) ×
  (∀ η η′ → Lay.lg X η → Le X η η′ → Lay.lg X η′ → Cp j (gk η) (gk η′)) ×
  (∀ η → Cp j G.top (gk η))

chain-lgl : ∀ j gk → Gk (layer j) j gk → ∀ n → Lgl j (chain j gk n)
chain-lgl j gk H zero = tt
chain-lgl j gk H (suc n) = proj₁ H _ (chain-lgl j gk H n)

chain-step : ∀ j gk → Gk (layer j) j gk → ∀ n → Cp j (chain j gk n) (chain j gk (suc n))
chain-step j gk H zero = proj₂ (proj₂ H) G.top
chain-step j gk H (suc n) =
  proj₁ (proj₂ H) _ _ (chain-lgl j gk H n) (chain-step j gk H n) (chain-lgl j gk H (suc n))

Ψw-dn : ∀ m j (w : W m j) gm gk {z} → Cp m z (gm G.top) → Dn m z (Ψw m j w gm gk)
Ψw-dn m .(lev m p) (keep p refl) gm gk q = nodeAt-dn m p G.lc dnLc gm q
Ψw-dn m j fold gm gk q = 0 , q

Ψw-lgl : ∀ m j (w : W m j) gm gk → Br (layer j) m gm → Gk (layer j) j gk → Lgl m (Ψw m j w gm gk)
Ψw-lgl m .(lev m p) (keep p refl) gm gk hm hk = nodeAt-lgl m p G.lc lgLc gm hm
Ψw-lgl m j fold gm gk (lg , mo) hk =
  (λ n → mo _ _ (chain-lgl j gk hk n) (chain-step j gk hk n) (chain-lgl j gk hk (suc n))) ,
  (λ n → lg _ (chain-lgl j gk hk n))

ΨN-dn : ∀ m k r (w : Way m (lev k r)) gm gk {z} → Cp m z (gm (Lay.tp (Lo k r))) →
  Dn m z (ΨN m k r w gm gk)
ΨN-dn m (suc k) (inj₁ _) w = Ψw-dn m k (wv m k w)
ΨN-dn m (suc k) (inj₂ r) = ΨN-dn m k r
ΨN-dn m (lim f) (n , r) = ΨN-dn m (f n) r
ΨN-dn m (lc j g) (η , _ , r) = ΨN-dn m (g η) r

ΨN-lgl : ∀ m k r (w : Way m (lev k r)) gm gk → Br (Lo k r) m gm → Gk (Lo k r) (lev k r) gk →
  Lgl m (ΨN m k r w gm gk)
ΨN-lgl m (suc k) (inj₁ _) w = Ψw-lgl m k (wv m k w)
ΨN-lgl m (suc k) (inj₂ r) = ΨN-lgl m k r
ΨN-lgl m (lim f) (n , r) = ΨN-lgl m (f n) r
ΨN-lgl m (lc j g) (η , _ , r) = ΨN-lgl m (g η) r
```

## 5 折叠的输出以 `top` (从而以零) 为第一位置，折叠保持第一位置

```agda
Ψ-low : ∀ m {k} (V : Lv k) x ξ {z} → Cp m z G.top → Cp m z (Ψ m V x ξ)
Ψ-low m V x G.zero p = p
Ψ-low m V x (G.suc a) p = inj₂ (1 , Ψ-low m V x a p)
Ψ-low m V x (G.lim f) p = inj₂ (0 , Ψ-low m V x (f 0) p)
Ψ-low m {k} V x (G.lc r g) p = inj₂ (ΨN-dn m k r (x r) _ _ (Ψ-low m V x (g _) p))
Ψ-low m (vs V) x (G.em _ a) p = Ψ-low m V _ a p
Ψ-low m (vl V) x (G.em n a) p = Ψ-low m (V n) _ a p
Ψ-low m v0 x G.top p = inj₂ (1 , p)
Ψ-low m {suc k} (vs V) x G.top p =
  inj₂ (Ψw-dn m k (wv m k (x (inj₁ tt))) _ _ (Ψ-low m V _ G.top p))
Ψ-low m (vl V) x G.top p = inj₂ (ltop-dn m _ (Ψ-low m (V 0) _ G.top p))

top-dn : ∀ m {k} (V : Lv k) x → Dn m G.top (Ψ m V x G.top)
top-dn m v0 x = 1 , inj₁ refl
top-dn m {suc k} (vs V) x = Ψw-dn m k (wv m k (x (inj₁ tt))) _ _ (Ψ-low m V _ G.top (inj₁ refl))
top-dn m (vl V) x = ltop-dn m _ (Ψ-low m (V 0) _ G.top (inj₁ refl))

Ψ-cp : ∀ m {k} (V : Lv k) x {ξ ξ′} → Cp k ξ ξ′ → Cp m (Ψ m V x ξ) (Ψ m V x ξ′)
Ψ-dn : ∀ m {k} (V : Lv k) x {ξ} ξ′ → Dn k ξ ξ′ → Dn m (Ψ m V x ξ) (Ψ m V x ξ′)

Ψ-cp m V x (inj₁ refl) = inj₁ refl
Ψ-cp m V x (inj₂ p) = inj₂ (Ψ-dn m V x _ p)

Ψ-dn m V x (G.suc d) p = 1 , Ψ-cp m V x p
Ψ-dn m V x (G.lim f) (n , p) = n , Ψ-cp m V x p
Ψ-dn m {k} V x (G.lc r g) p = ΨN-dn m k r (x r) _ _ (Ψ-cp m V x p)
Ψ-dn m (vs V) x {G.em _ a} (G.em _ d) (refl , p) = Ψ-dn m V _ d p
Ψ-dn m (vl V) x {G.em n a} (G.em _ d) (refl , p) = Ψ-dn m (V n) _ d p
Ψ-dn m V x G.top refl = top-dn m V x
```

## 6 目标层 0 的逐项行：沿层号路径单调

`V ≤ᵛ W`：`V` 沿后继与 ℕ 极限的某一支到达 `W` (层号上的第一位置路径)。`top-mono`：目标层 0 上，
`top` 在 `V` 层的折叠是它在 `W` 层的折叠的第一位置；派发是到 `⊤` 的函数，两边自动相同。`LvL V`：极限层号相邻两支之间有路径。

```agda
data _≤ᵛ_ : ∀ {a b} → Lv a → Lv b → Set where
  rf : ∀ {a} {V : Lv a} → V ≤ᵛ V
  ps : ∀ {a b} {V : Lv a} {W : Lv b} → V ≤ᵛ W → V ≤ᵛ vs W
  pl : ∀ {a} {f : ℕ → LF} {V : Lv a} {W : ∀ n → Lv (f n)} n → V ≤ᵛ W n → V ≤ᵛ vl W

top-mono : ∀ {a b} {V : Lv a} {W : Lv b} → V ≤ᵛ W → ∀ x y →
  Cp zero (Ψ zero V x G.top) (Ψ zero W y G.top)
top-mono rf x y = inj₁ refl
top-mono {W = vs W} (ps p) x y = inj₂ (0 , top-mono p x _)
top-mono (pl n p) x y = inj₂ (n , top-mono p x _)

LvL : ∀ {k} → Lv k → Set
LvL v0 = ⊤
LvL (vs V) = LvL V
LvL (vl V) = (∀ n → V n ≤ᵛ V (suc n)) × (∀ n → LvL (V n))

top-step : ∀ m {f} (V : ∀ n → Lv (f n)) → (∀ n → V n ≤ᵛ V (suc n)) → (x : Ext m (lim f)) →
  StepIf m (λ n → Ψ m (V n) (λ r → x (n , r)) G.top)
top-step zero V st x n = top-mono (st n) _ _
top-step (suc m) V st x = tt
top-step (lim f) V st x = tt
top-step (lc k g) V st x = tt
```

## 7 折叠保持合法

```agda
Ψ-lgl : ∀ m {k} (V : Lv k) → LvL V → ∀ x ξ → Lgl k ξ → Lgl m (Ψ m V x ξ)
Ψ-lgl m V L x G.zero l = tt
Ψ-lgl m V L x (G.suc a) l = mult-lgl m _ (Ψ-lgl m V L x a l) (Ψ-low m V x a (inj₂ refl))
Ψ-lgl m V L x (G.lim f) (st , lf) = (λ n → Ψ-cp m V x (st n)) , (λ n → Ψ-lgl m V L x (f n) (lf n))
Ψ-lgl m {k} V L x (G.lc r g) (lg , mo) = ΨN-lgl m k r (x r) _ _
  ((λ η l → Ψ-lgl m V L x (g η) (lg η l)) , (λ η η′ l e l′ → Ψ-cp m V x (mo η η′ l e l′)))
  ((λ η l → Ψ-lgl (lev k r) V L (cmp V r) (g η) (lg η l)) ,
   (λ η η′ l e l′ → Ψ-cp (lev k r) V (cmp V r) (mo η η′ l e l′)) ,
   (λ η → Ψ-low (lev k r) V (cmp V r) (g η) (inj₁ refl)))
Ψ-lgl m (vs V) L x (G.em _ a) l = Ψ-lgl m V L _ a l
Ψ-lgl m (vl V) (st , L) x (G.em n a) l = Ψ-lgl m (V n) (L n) _ a l
Ψ-lgl m v0 L x G.top l = mult-lgl m G.top tt (inj₂ refl)
Ψ-lgl m {suc k} (vs V) L x G.top l = Ψw-lgl m k (wv m k (x (inj₁ tt))) _ _
  ((λ η l → Ψ-lgl m V L _ η l) , (λ η η′ l e l′ → Ψ-cp m V _ e))
  ((λ η l → Ψ-lgl k V L (self k) η l) , (λ η η′ l e l′ → Ψ-cp k V (self k) e) ,
   (λ η → Ψ-low k V (self k) η (inj₁ refl)))
Ψ-lgl m (vl V) (st , L) x G.top l =
  ltop-lgl m _ (λ n → Ψ-lgl m (V n) (L n) _ G.top tt) (top-step m V st x)
```
