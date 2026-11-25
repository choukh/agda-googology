# YiPsumFold：极限层号上 `top` 取逐项极限的折叠 (不带部分和)

**判决 (编译定理，带前提)：`Ψᵗ` 是 [YiRawFold](YiRawFold.lagda.md) 的 `Ψ` 改一行：极限层号上 `top` 不分保留与否都取各支的逐项极限。输出带嵌套证据、保持第一位置；
输出合法要前提 `Dm` (`CohP` 加结点自己那一层的派发一致 `CohS`) 与外部派发一致 `CohX`。** 折叠的定义本身无关地用到 `Dm` (链点的守卫要推进输出合法)，所以定义域比 `Ψ` 小。
对派发方案 `Scheme` 参数化；前提在哪些实例上成立见 [YiPsumInst](YiPsumInst.lagda.md)。不否定 `Ψ` 的部分和写法；没有值定理。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiPsumFold where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (cO; cO-Lgl; cO-Nested)
open import OCF.Align.YiIrrIf using (CP; self; suc; lim; fst; Legal)
open import OCF.Align.YiIrrFbRaw using (Cp-tr)
open import OCF.Align.YiLvIf using (Plain; lev; lev-plain; Kept)
open import OCF.Align.YiLvFoldAdd
open import OCF.Align.YiLvFoldBase using (Way; keep; fold; cO-pos)
open import OCF.Align.YiLvFoldFin using (IsKeep)
open import OCF.Align.YiLvNegRestrict using (restrictL)
open import OCF.Align.YiRawIf using (IsLim)
open import OCF.Align.YiRawFoldBase
open import OCF.Align.YiPsumBase
```

## 1 前提

`CohS K pl L`：`K` 与它的每个孩子上，方案的 `ownˢ` (一切位置) 与 `ownTˢ` 都一致。`Dm` 再加上 `CohP`。两者沿路径遗传。

```agda
module Termwise (S : Scheme) where
  open Scheme S

  CohS : ∀ K → Plain K → Legal K → Set
  CohS zero pl L = ⊤
  CohS (suc k) pl L =
    (∀ r → CohX (suc k) L (ownˢ (suc k) pl L r)) ×
    CohX (suc k) L (ownTˢ (suc k) pl L) × CohS k pl L
  CohS (lim f) pl L =
    (∀ r → CohX (lim f) L (ownˢ (lim f) pl L r)) ×
    CohX (lim f) L (ownTˢ (lim f) pl L) × (∀ n → CohS (f n) (pl n) (proj₂ L n))
  CohS (lc k c w b t g) pl L = ⊥

  hereS : ∀ K pl L → CohS K pl L → ∀ r → CohX K L (ownˢ K pl L r)
  hereS (suc k) pl L h = proj₁ h
  hereS (lim f) pl L h = proj₁ h

  topS : ∀ K pl L → CohS K pl L → CohX K L (ownTˢ K pl L)
  topS zero pl L h = tt
  topS (suc k) pl L h = proj₁ (proj₂ h)
  topS (lim f) pl L h = proj₁ (proj₂ h)

  Dm : ∀ K → Plain K → Legal K → Set
  Dm K pl L = CohP K pl L × CohS K pl L

  dS : ∀ k pl L → Dm (suc k) pl L → Dm k pl L
  dS k pl L D = proj₁ D , proj₂ (proj₂ (proj₂ D))

  dL : ∀ f pl L → Dm (lim f) pl L → ∀ n → Dm (f n) (pl n) (proj₂ L n)
  dL f pl L D n = proj₂ (proj₁ D) n , proj₂ (proj₂ (proj₂ D)) n

  restrictD : ∀ {a} b (p : CP a b) (pb : Plain b) (Lb : Legal b) → Dm b pb Lb →
    Dm a (plainR b p pb) (restrictL b p Lb)
  restrictD b self pb Lb D = D
  restrictD (suc b) (suc p) pb Lb D = restrictD b p pb Lb (dS b pb Lb D)
  restrictD (lim f) (lim n p) pb Lb D = restrictD (f n) p (pb n) (proj₂ Lb n) (dL f pb Lb D n)

  -- 换成相等的 (Plain, Legal) 与相等的派发; 无关的 Dm 不参与.
  recoh : ∀ {m k} (F : (z : Plain k × Legal k) → .(Dm k (proj₁ z) (proj₂ z)) → Ext m k → Raw m)
    {z z′} → z ≡ z′ → .(D : Dm k (proj₁ z) (proj₂ z)) .(D′ : Dm k (proj₁ z′) (proj₂ z′))
    {x x′ : Ext m k} → x ≡ x′ → ∀ {Y} → Cp m (F z D x) Y → Cp m (F z′ D′ x′) Y
  recoh F refl D D′ refl c = c
```

## 2 一个互递归块

与 `YiRawFold.Ψ` 逐子句平行。不同的只有：多一个无关参数 `Dm`；`own`, `ownT` 换成方案的；极限层号上 `top` 的两个子句合成一个逐项的。
`belowᵗ` 对任意外部派发成立 (原来只对 `low`)：大的那边沿路径走下去遇到的折叠，字面上就是小的那边用限制下来的 (`Plain`, `Legal`, 派发) 的折叠。

```agda
  Ψᵗ : ∀ m k (pl : Plain k) (L : Legal k) → .(Dm k pl L) → Ext m k →
    (ξ : Raw k) → .(Lgl k ξ) → .(Nested k ξ) → Raw m
  ndLᵗ : ∀ m k (pl : Plain k) (L : Legal k) → .(Dm k pl L) → (x : Ext m k) → ∀ r c t
    (g : (η : Low k r) → .(GdL k r c η) → Raw k) →
    .(Lgl k (G.lc r c t g)) → .(Nested k (G.lc r c t g)) → NdL m k r
  ndTᵗ : ∀ m k (pl : Plain k) (L : Legal k) → .(Dm k pl L) → (x : Ext m k) → NdR m k
  Ψᵗ-pos : ∀ m k pl L .(D : Dm k pl L) (x : Ext m k) ξ .(l : Lgl k ξ) .(nb : Nested k ξ) →
    Pos m (Ψᵗ m k pl L D x ξ l nb)
  Ψᵗ-legal : ∀ m → Plain m → ∀ k pl L (D : Dm k pl L) (x : Ext m k) → CohX k L x →
    ∀ ξ (l : Lgl k ξ) (nb : Nested k ξ) → Lgl m (Ψᵗ m k pl L D x ξ l nb)
  Ψᵗ-nested : ∀ m k pl L (D : Dm k pl L) (x : Ext m k) ξ (l : Lgl k ξ) (nb : Nested k ξ) →
    Nested m (Ψᵗ m k pl L D x ξ l nb)
  Ψᵗ-cp : ∀ m k pl L .(D : Dm k pl L) (x : Ext m k) {ξ} ξ′ (l : Lgl k ξ) (nb : Nested k ξ)
    (l′ : Lgl k ξ′) (nb′ : Nested k ξ′) → Cp k ξ ξ′ →
    Cp m (Ψᵗ m k pl L D x ξ l nb) (Ψᵗ m k pl L D x ξ′ l′ nb′)
  Ψᵗ-dn : ∀ m k pl L .(D : Dm k pl L) (x : Ext m k) {ξ} ξ′ (l : Lgl k ξ) (nb : Nested k ξ)
    (l′ : Lgl k ξ′) (nb′ : Nested k ξ′) → Dn k ξ ξ′ →
    Dn m (Ψᵗ m k pl L D x ξ l nb) (Ψᵗ m k pl L D x ξ′ l′ nb′)
  Ψᵗ-top : ∀ m k pl L .(D : Dm k pl L) (x : Ext m k) {ξ} (l : Lgl k ξ) (nb : Nested k ξ) →
    Cp k ξ G.top →
    Cp m (Ψᵗ m k pl L D x ξ l nb) (Ψᵗ m k pl L D x (cO k) (cO-Lgl k) (cO-Nested k))
  belowᵗ : ∀ m {a} b (p : CP a b) (pb : Plain b) (Lb : Legal b) .(D : Dm b pb Lb)
    (x : Ext m b) →
    Cp m (Ψᵗ m a (plainR b p pb) (restrictL b p Lb) (restrictD b p pb Lb D) (restrictX b p x)
            G.top tt tt)
         (Ψᵗ m b pb Lb D x G.top tt tt)

  Ψᵗ m k pl L D x G.zero l nb = cO m
  Ψᵗ m k pl L D x (G.suc a) l nb = successor m (Ψᵗ m k pl L D x a l nb)
  Ψᵗ m k pl L D x (G.lim f) l nb = G.lim (λ n → Ψᵗ m k pl L D x (f n) (proj₂ l n) (nb n))
  Ψᵗ m k pl L D x (G.lc r c t g) l nb = ΨN m k pl r (wayOf x r) (ndLᵗ m k pl L D x r c t g l nb)
  Ψᵗ m (suc k) pl L D x (G.em _ T) l nb = Ψᵗ m k pl L (dS k pl L D) (inS x) T l nb
  Ψᵗ m (lim f) pl L D x (G.em n T) l nb =
    Ψᵗ m (f n) (pl n) (proj₂ L n) (dL f pl L D n) (inL x n) T l nb
  Ψᵗ m zero pl L D x G.top l nb = successor m (cO m)
  Ψᵗ m (suc k) pl L D x G.top l nb =
    Ψn m k pl (wayOf x (inj₁ tt)) (ndTᵗ m k pl L (dS k pl L D) (inS x))
  Ψᵗ m (lim f) pl L D x G.top l nb =
    G.lim (λ n → Ψᵗ m (f n) (pl n) (proj₂ L n) (dL f pl L D n) (inL x n) G.top tt tt)

  ndLᵗ m k pl L D x r c t g l nb = nd c (proj₁ nb) (proj₁ (proj₂ nb))
    (Ψᵗ m k pl L D x t (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
    (λ η e → Ψᵗ m k pl L D x (g η e)
      (proj₂ (proj₂ (proj₂ (proj₂ l))) η e) (proj₂ (proj₂ (proj₂ nb)) η e))
    (λ η e → Ψᵗ (lev k r) k pl L D (ownˢ k pl L r) (g η e)
      (proj₂ (proj₂ (proj₂ (proj₂ l))) η e) (proj₂ (proj₂ (proj₂ nb)) η e))
    (λ η e → Ψᵗ-legal (lev k r) (lev-plain k pl r) k pl L D (ownˢ k pl L r)
      (hereS k pl L (proj₂ D) r) (g η e)
      (proj₂ (proj₂ (proj₂ (proj₂ l))) η e) (proj₂ (proj₂ (proj₂ nb)) η e))
    (λ η e → Ψᵗ-nested (lev k r) k pl L D (ownˢ k pl L r) (g η e)
      (proj₂ (proj₂ (proj₂ (proj₂ l))) η e) (proj₂ (proj₂ (proj₂ nb)) η e))
    (λ η e → Ψᵗ-pos (lev k r) k pl L D (ownˢ k pl L r) (g η e)
      (proj₂ (proj₂ (proj₂ (proj₂ l))) η e) (proj₂ (proj₂ (proj₂ nb)) η e))

  ndTᵗ m k pl L D x = nd (cO k) (cO-Lgl k) (cO-Nested k)
    (Ψᵗ m k pl L D x (cO k) (cO-Lgl k) (cO-Nested k))
    (λ η e → Ψᵗ m k pl L D x η (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
    (λ η e → Ψᵗ k k pl L D (ownTˢ k pl L) η (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
    (λ η e → Ψᵗ-legal k pl k pl L D (ownTˢ k pl L) (topS k pl L (proj₂ D)) η
      (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
    (λ η e → Ψᵗ-nested k k pl L D (ownTˢ k pl L) η (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
    (λ η e → Ψᵗ-pos k k pl L D (ownTˢ k pl L) η (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))

  Ψᵗ-pos m k pl L D x G.zero l nb = cO-pos m
  Ψᵗ-pos m k pl L D x (G.suc a) l nb = tt
  Ψᵗ-pos m k pl L D x (G.lim f) l nb = tt
  Ψᵗ-pos m k pl L D x (G.lc r c t g) l nb =
    ΨN-pos m k pl r (wayOf x r) (ndLᵗ m k pl L D x r c t g l nb)
  Ψᵗ-pos m (suc k) pl L D x (G.em _ T) l nb = Ψᵗ-pos m k pl L (dS k pl L D) (inS x) T l nb
  Ψᵗ-pos m (lim f) pl L D x (G.em n T) l nb =
    Ψᵗ-pos m (f n) (pl n) (proj₂ L n) (dL f pl L D n) (inL x n) T l nb
  Ψᵗ-pos m zero pl L D x G.top l nb = tt
  Ψᵗ-pos m (suc k) pl L D x G.top l nb =
    Ψn-pos m k pl (wayOf x (inj₁ tt)) (ndTᵗ m k pl L (dS k pl L D) (inS x))
  Ψᵗ-pos m (lim f) pl L D x G.top l nb = tt

  Ψᵗ-legal m pm k pl L D x hx G.zero l nb = cO-Lgl m
  Ψᵗ-legal m pm k pl L D x hx (G.suc a) l nb =
    copies-step m pm (Ψᵗ m k pl L D x a l nb) ,
    copies-legal m pm (Ψᵗ m k pl L D x a l nb) (Ψᵗ-legal m pm k pl L D x hx a l nb)
  Ψᵗ-legal m pm k pl L D x hx (G.lim f) (st , lf) nb =
    (λ n → Ψᵗ-cp m k pl L D x (f (suc n)) (lf n) (nb n) (lf (suc n)) (nb (suc n)) (st n)) ,
    (λ n → Ψᵗ-legal m pm k pl L D x hx (f n) (lf n) (nb n))
  Ψᵗ-legal m pm k pl L D x hx (G.lc r c t g) (tg , dir , irr , lt , lg) (lw , nw , nt , ng) =
    ΨN-legal m k pl r (wayOf x r)
      (ndLᵗ m k pl L D x r c t g (tg , dir , irr , lt , lg) (lw , nw , nt , ng))
      (record
        { seed = seedL k r c lw nw
        ; tg = λ η e → Ψᵗ-cp m k pl L D x (g η e) lt nt (lg η e) (ng η e) (tg η e)
        ; dir = λ η e η′ e′ q →
            Ψᵗ-cp m k pl L D x (g η′ e′) (lg η e) (ng η e) (lg η′ e′) (ng η′ e′)
              (dir η e η′ e′ q)
        ; lt = Ψᵗ-legal m pm k pl L D x hx t lt nt
        ; lg = λ η e → Ψᵗ-legal m pm k pl L D x hx (g η e) (lg η e) (ng η e)
        ; lkʳ = λ η e → Ψᵗ-legal (lev k r) (lev-plain k pl r) k pl L D (ownˢ k pl L r)
            (hereS k pl L (proj₂ D) r) (g η e) (lg η e) (ng η e)
        ; nkʳ = λ η e → Ψᵗ-nested (lev k r) k pl L D (ownˢ k pl L r) (g η e) (lg η e) (ng η e) })
  Ψᵗ-legal m pm (suc k) pl L D x hx (G.em _ T) l nb =
    Ψᵗ-legal m pm k pl L (dS k pl L D) (inS x) hx T l nb
  Ψᵗ-legal m pm (lim f) pl L D x hx (G.em n T) l nb =
    Ψᵗ-legal m pm (f n) (pl n) (proj₂ L n) (dL f pl L D n) (inL x n) (proj₂ hx n) T l nb
  Ψᵗ-legal m pm zero pl L D x hx G.top l nb =
    copies-step m pm (cO m) , copies-legal m pm (cO m) (cO-Lgl m)
  Ψᵗ-legal m pm (suc k) pl L D x hx G.top l nb =
    Ψn-legal m k pl (wayOf x (inj₁ tt)) (ndTᵗ m k pl L (dS k pl L D) (inS x))
      (record
        { seed = inj₁ refl , cO-Lgl k , cO-Nested k
        ; tg = λ η e → Ψᵗ-cp m k pl L (dS k pl L D) (inS x) η (cO-Lgl k) (cO-Nested k)
            (proj₁ (proj₂ e)) (proj₂ (proj₂ e)) (proj₁ e)
        ; dir = λ η e η′ e′ q →
            Ψᵗ-cp m k pl L (dS k pl L D) (inS x) η′ (proj₁ (proj₂ e)) (proj₂ (proj₂ e))
              (proj₁ (proj₂ e′)) (proj₂ (proj₂ e′)) (proj₁ q)
        ; lt = Ψᵗ-legal m pm k pl L (dS k pl L D) (inS x) hx (cO k) (cO-Lgl k) (cO-Nested k)
        ; lg = λ η e → Ψᵗ-legal m pm k pl L (dS k pl L D) (inS x) hx η
            (proj₁ (proj₂ e)) (proj₂ (proj₂ e))
        ; lkʳ = λ η e → Ψᵗ-legal k pl k pl L (dS k pl L D) (ownTˢ k pl L)
            (topS k pl L (proj₂ (dS k pl L D))) η (proj₁ (proj₂ e)) (proj₂ (proj₂ e))
        ; nkʳ = λ η e → Ψᵗ-nested k k pl L (dS k pl L D) (ownTˢ k pl L) η
            (proj₁ (proj₂ e)) (proj₂ (proj₂ e)) })
  Ψᵗ-legal m pm (lim f) pl L D x hx G.top l nb =
    (λ n → recoh (λ z D′ y → Ψᵗ m (f n) (proj₁ z) (proj₂ z) D′ y G.top tt tt)
      (proj₁ (proj₁ D) n)
      (restrictD (f (suc n)) (proj₁ L n) (pl (suc n)) (proj₂ L (suc n)) (dL f pl L D (suc n)))
      (dL f pl L D n)
      (proj₁ hx n)
      (belowᵗ m (f (suc n)) (proj₁ L n) (pl (suc n)) (proj₂ L (suc n)) (dL f pl L D (suc n))
        (inL x (suc n)))) ,
    (λ n → Ψᵗ-legal m pm (f n) (pl n) (proj₂ L n) (dL f pl L D n) (inL x n) (proj₂ hx n)
      G.top tt tt)

  Ψᵗ-nested m k pl L D x G.zero l nb = cO-Nested m
  Ψᵗ-nested m k pl L D x (G.suc a) l nb =
    copies-nested m (Ψᵗ m k pl L D x a l nb) (Ψᵗ-nested m k pl L D x a l nb)
  Ψᵗ-nested m k pl L D x (G.lim f) (st , lf) nb =
    λ n → Ψᵗ-nested m k pl L D x (f n) (lf n) (nb n)
  Ψᵗ-nested m k pl L D x (G.lc r c t g) (tg , dir , irr , lt , lg) (lw , nw , nt , ng) =
    ΨN-nested m k pl r (wayOf x r)
      (ndLᵗ m k pl L D x r c t g (tg , dir , irr , lt , lg) (lw , nw , nt , ng))
      (record
        { seed = seedL k r c lw nw
        ; lcʳ = lw
        ; ncʳ = nw
        ; nt = Ψᵗ-nested m k pl L D x t lt nt
        ; ng = λ η e → Ψᵗ-nested m k pl L D x (g η e) (lg η e) (ng η e)
        ; lkʳ = λ η e → Ψᵗ-legal (lev k r) (lev-plain k pl r) k pl L D (ownˢ k pl L r)
            (hereS k pl L (proj₂ D) r) (g η e) (lg η e) (ng η e)
        ; nkʳ = λ η e → Ψᵗ-nested (lev k r) k pl L D (ownˢ k pl L r) (g η e) (lg η e) (ng η e) })
  Ψᵗ-nested m (suc k) pl L D x (G.em _ T) l nb =
    Ψᵗ-nested m k pl L (dS k pl L D) (inS x) T l nb
  Ψᵗ-nested m (lim f) pl L D x (G.em n T) l nb =
    Ψᵗ-nested m (f n) (pl n) (proj₂ L n) (dL f pl L D n) (inL x n) T l nb
  Ψᵗ-nested m zero pl L D x G.top l nb = copies-nested m (cO m) (cO-Nested m)
  Ψᵗ-nested m (suc k) pl L D x G.top l nb =
    Ψn-nested m k pl (wayOf x (inj₁ tt)) (ndTᵗ m k pl L (dS k pl L D) (inS x))
      (record
        { seed = inj₁ refl , cO-Lgl k , cO-Nested k
        ; lcʳ = cO-Lgl k
        ; ncʳ = cO-Nested k
        ; nt = Ψᵗ-nested m k pl L (dS k pl L D) (inS x) (cO k) (cO-Lgl k) (cO-Nested k)
        ; ng = λ η e → Ψᵗ-nested m k pl L (dS k pl L D) (inS x) η
            (proj₁ (proj₂ e)) (proj₂ (proj₂ e))
        ; lkʳ = λ η e → Ψᵗ-legal k pl k pl L (dS k pl L D) (ownTˢ k pl L)
            (topS k pl L (proj₂ (dS k pl L D))) η (proj₁ (proj₂ e)) (proj₂ (proj₂ e))
        ; nkʳ = λ η e → Ψᵗ-nested k k pl L (dS k pl L D) (ownTˢ k pl L) η
            (proj₁ (proj₂ e)) (proj₂ (proj₂ e)) })
  Ψᵗ-nested m (lim f) pl L D x G.top l nb =
    λ n → Ψᵗ-nested m (f n) (pl n) (proj₂ L n) (dL f pl L D n) (inL x n) G.top tt tt

  Ψᵗ-cp m k pl L D x ξ′ l nb l′ nb′ (inj₁ refl) = inj₁ refl
  Ψᵗ-cp m k pl L D x ξ′ l nb l′ nb′ (inj₂ p) = inj₂ (Ψᵗ-dn m k pl L D x ξ′ l nb l′ nb′ p)

  Ψᵗ-dn m k pl L D x (G.suc d) l nb l′ nb′ p = zero , Ψᵗ-cp m k pl L D x d l nb l′ nb′ p
  Ψᵗ-dn m k pl L D x (G.lim f) l nb (st , lf) nb′ (n , p) =
    n , Ψᵗ-cp m k pl L D x (f n) l nb (lf n) (nb′ n) p
  Ψᵗ-dn m k pl L D x (G.lc r c t g) l nb (tg , dir , irr , lt , lg) (lw , nw , nt , ng) p =
    ΨN-dn m k pl r (wayOf x r)
      (ndLᵗ m k pl L D x r c t g (tg , dir , irr , lt , lg) (lw , nw , nt , ng))
      (Ψᵗ-cp m k pl L D x t l nb lt nt p)
      (seedL k r c lw nw)
      (Ψᵗ-cp m k pl L D x (g c (seedL k r c lw nw)) l nb
        (lg c (seedL k r c lw nw)) (ng c (seedL k r c lw nw))
        (Cp-tr k p (tg c (seedL k r c lw nw))))
  Ψᵗ-dn m (suc k) pl L D x {G.em _ a} (G.em _ T) l nb l′ nb′ p =
    Ψᵗ-dn m k pl L (dS k pl L D) (inS x) T l nb l′ nb′ p
  Ψᵗ-dn m (lim f) pl L D x {G.em n a} (G.em .n T) l nb l′ nb′ (refl , p) =
    Ψᵗ-dn m (f n) (pl n) (proj₂ L n) (dL f pl L D n) (inL x n) T l nb l′ nb′ p
  Ψᵗ-dn m (suc k) pl L D x {G.em _ a} G.top l nb l′ nb′ p =
    Ψn-dn m k pl (wayOf x (inj₁ tt)) (ndTᵗ m k pl L (dS k pl L D) (inS x))
      (Ψᵗ-top m k pl L (dS k pl L D) (inS x) l nb p)
      (inj₁ refl , cO-Lgl k , cO-Nested k)
      (Ψᵗ-top m k pl L (dS k pl L D) (inS x) l nb p)

  Ψᵗ-top m zero pl L D x l nb (inj₁ refl) = inj₁ refl
  Ψᵗ-top m (suc k) pl L D x l nb p = Ψᵗ-cp m (suc k) pl L D x G.top l nb tt tt p
  Ψᵗ-top m (lim f) pl L D x l nb p = Ψᵗ-cp m (lim f) pl L D x G.top l nb tt tt p

  belowᵗ m b self pb Lb D x = inj₁ refl
  belowᵗ m (suc zero) (suc p) pb Lb D x =
    inj₂ (Ψn-dn m zero pb (wayOf x (inj₁ tt)) (ndTᵗ m zero pb Lb (dS zero pb Lb D) (inS x))
      (belowᵗ m zero p pb Lb (dS zero pb Lb D) (inS x)) (inj₁ refl , tt , tt)
      (belowᵗ m zero p pb Lb (dS zero pb Lb D) (inS x)))
  belowᵗ m (suc (suc b)) (suc p) pb Lb D x =
    inj₂ (Ψn-dn m (suc b) pb (wayOf x (inj₁ tt))
      (ndTᵗ m (suc b) pb Lb (dS (suc b) pb Lb D) (inS x))
      (belowᵗ m (suc b) p pb Lb (dS (suc b) pb Lb D) (inS x)) (inj₁ refl , tt , tt)
      (belowᵗ m (suc b) p pb Lb (dS (suc b) pb Lb D) (inS x)))
  belowᵗ m (suc (lim f)) (suc p) pb Lb D x =
    inj₂ (Ψn-dn m (lim f) pb (wayOf x (inj₁ tt))
      (ndTᵗ m (lim f) pb Lb (dS (lim f) pb Lb D) (inS x))
      (belowᵗ m (lim f) p pb Lb (dS (lim f) pb Lb D) (inS x)) (inj₁ refl , tt , tt)
      (belowᵗ m (lim f) p pb Lb (dS (lim f) pb Lb D) (inS x)))
  belowᵗ m (lim f) (lim n p) pb Lb D x =
    inj₂ (n , belowᵗ m (f n) p (pb n) (proj₂ Lb n) (dL f pb Lb D n) (inL x n))
```

## 3 行与携带强度的两条

改的那一行与没改的行，都是 `refl`。`keepᵗ`, `foldᵗ` 与 `YiRawFold.keepᴳ`, `foldᴳ` 同一陈述。

```agda
  top-rowᵗ : ∀ m f pl L .(D : Dm (lim f) pl L) (x : Ext m (lim f)) →
    Ψᵗ m (lim f) pl L D x G.top tt tt ≡
    G.lim (λ n → Ψᵗ m (f n) (pl n) (proj₂ L n) (dL f pl L D n) (inL x n) G.top tt tt)
  top-rowᵗ m f pl L D x = refl

  node-rowᵗ : ∀ m k pl L .(D : Dm k pl L) (x : Ext m k) r c t g
    (l : Lgl k (G.lc r c t g)) (nb : Nested k (G.lc r c t g)) →
    Ψᵗ m k pl L D x (G.lc r c t g) l nb ≡
    ΨN m k pl r (wayOf x r) (ndLᵗ m k pl L D x r c t g l nb)
  node-rowᵗ m k pl L D x r c t g l nb = refl

  top-rowˢᵗ : ∀ m k pl L .(D : Dm (suc k) pl L) (x : Ext m (suc k)) →
    Ψᵗ m (suc k) pl L D x G.top tt tt ≡
    Ψn m k pl (wayOf x (inj₁ tt)) (ndTᵗ m k pl L (dS k pl L D) (inS x))
  top-rowˢᵗ m k pl L D x = refl

  keepᵗ : ∀ m → Plain m → ∀ k pl L .(D : Dm k pl L) (x : Ext m k) r c t g
    (l : Lgl k (G.lc r c t g)) (nb : Nested k (G.lc r c t g)) →
    IsKeep (wayOf x r) → Kept m (lev k r) (Ψᵗ m k pl L D x (G.lc r c t g) l nb)
  keepᵗ m pm k pl L D x r c t g l nb h =
    ΨN-kept m pm k pl r (wayOf x r) (ndLᵗ m k pl L D x r c t g l nb) h

  foldᵗ : ∀ m k pl L .(D : Dm k pl L) (x : Ext m k) r c t g
    (l : Lgl k (G.lc r c t g)) (nb : Nested k (G.lc r c t g)) →
    (IsKeep (wayOf x r) → ⊥) → IsLim (Ψᵗ m k pl L D x (G.lc r c t g) l nb)
  foldᵗ m k pl L D x r c t g l nb h =
    ΨN-lim m k pl r (wayOf x r) (ndLᵗ m k pl L D x r c t g l nb) h
```
