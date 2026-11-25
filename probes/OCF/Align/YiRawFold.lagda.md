# YiRawFold：写在第 K 层的树上的折叠

**判决 (编译定理，第 A 站)：`Ψ` 对 (公共上界, `Raw` 的树) 递归，证书无关；输出合法、带嵌套证据、保持第一位置。派发读树里的位置：
`Φᵐ` 是接口 `YiRawIf.RawFold` 的实例，没有前提；`Φ` 在目标第 0 层把极限层号上的 `top` 取成各支的极限，合法性要 `CohP`。**
没有值定理。不否定别的写法。底座 [YiRawFoldBase](YiRawFoldBase.lagda.md)，实例 [YiRawFoldInst](YiRawFoldInst.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRawFold where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (cO; cO-Lgl; cO-Nested)
open import OCF.Align.YiIrrIf using (CP; self; suc; lim; fst; Legal; iterate)
open import OCF.Align.YiIrrFbIf using (Pt; pt) renaming (at to atᵖ)
open import OCF.Align.YiIrrFbRaw using (Cp-tr)
open import OCF.Align.YiLvIf using (Plain; lev; lev-plain; Kept)
open import OCF.Align.YiLvFoldAdd
open import OCF.Align.YiLvFoldBase using (Way; keep; fold; cO-pos; nodeAt; startᴸ; module Chain)
open import OCF.Align.YiLvFoldFin using (IsKeep)
open import OCF.Align.YiLvNegCompare using (At)
open import OCF.Align.YiLvNegRestrict using (restrictL)
open import OCF.Align.YiRawIf
open import OCF.Align.YiRawFoldBase
```

## 1 结点自己那一层的派发

链由结点自己那一层的折叠推进。位置 `r` 上的结点，目标取 `at r`，派发是接口的规范比较，读当前这一层的 `Legal`。
进孩子以后 "当前这一层" 换成孩子，`Legal` 取孩子的那一份，所以小的公共上界上的折叠字面地出现在大的里面 (第 B 站用)。
`top` 在后继层号上展开成根位置的结点；它自己那一层的派发取根位置的 `own` 限制到孩子 (`ownT`)，这样 `top` 与字面写出的那个结点折叠相同 (`top-as-node`)。

```agda
own : ∀ k → Plain k → Legal k → (r : Pre k) → Ext (lev k r) k
own k pl L r = mix (dispatch k pl L (at r))

ownT : ∀ k → Plain k → Legal k → Ext k k
ownT k pl L = inS (own (suc k) pl L (inj₁ tt))
```

## 2 一个互递归块

对 (`k`, `ξ`) 按字典序递归：`em` 与 `top` 处 `k` 变小，其余处 `ξ` 变小；目标层 `m` 在链行里换成结点自己的层。

- `em`：进孩子的层号，外部派发限制到孩子。
- `top`：层号 0 上是 1 的像；后继层号上是根位置的结点 (下界 `cO k`，分支是孩子里的树)，与 `upT` 一致；
  极限层号上，`low` 之下是各支的极限，`mix` 之下是各支的部分和 (`YiRawFoldBase` §5)。

```agda
Ψ : ∀ m k → Plain k → Legal k → Ext m k → (ξ : Raw k) → .(Lgl k ξ) → .(Nested k ξ) → Raw m
ndL : ∀ m k (pl : Plain k) (L : Legal k) (x : Ext m k) r c t
  (g : (η : Low k r) → .(GdL k r c η) → Raw k) →
  .(Lgl k (G.lc r c t g)) → .(Nested k (G.lc r c t g)) → NdL m k r
ndT : ∀ m k (pl : Plain k) (L : Legal k) (x : Ext m k) → NdR m k
Ψ-pos : ∀ m k pl L (x : Ext m k) ξ .(l : Lgl k ξ) .(nb : Nested k ξ) →
  Pos m (Ψ m k pl L x ξ l nb)
Ψ-legal : ∀ m → Plain m → ∀ k pl L (x : Ext m k) → Good k pl L x →
  ∀ ξ (l : Lgl k ξ) (nb : Nested k ξ) → Lgl m (Ψ m k pl L x ξ l nb)
Ψ-nested : ∀ m k pl L (x : Ext m k) ξ (l : Lgl k ξ) (nb : Nested k ξ) →
  Nested m (Ψ m k pl L x ξ l nb)
Ψ-cp : ∀ m k pl L (x : Ext m k) {ξ} ξ′ (l : Lgl k ξ) (nb : Nested k ξ)
  (l′ : Lgl k ξ′) (nb′ : Nested k ξ′) → Cp k ξ ξ′ →
  Cp m (Ψ m k pl L x ξ l nb) (Ψ m k pl L x ξ′ l′ nb′)
Ψ-dn : ∀ m k pl L (x : Ext m k) {ξ} ξ′ (l : Lgl k ξ) (nb : Nested k ξ)
  (l′ : Lgl k ξ′) (nb′ : Nested k ξ′) → Dn k ξ ξ′ →
  Dn m (Ψ m k pl L x ξ l nb) (Ψ m k pl L x ξ′ l′ nb′)
Ψ-top : ∀ m k pl L (x : Ext m k) {ξ} (l : Lgl k ξ) (nb : Nested k ξ) → Cp k ξ G.top →
  Cp m (Ψ m k pl L x ξ l nb) (Ψ m k pl L x (cO k) (cO-Lgl k) (cO-Nested k))
below : ∀ m {a} b (p : CP a b) (pb : Plain b) (Lb : Legal b) →
  Cp m (Ψ m a (plainR b p pb) (restrictL b p Lb) low G.top tt tt)
       (Ψ m b pb Lb low G.top tt tt)

Ψ m k pl L x G.zero l nb = cO m
Ψ m k pl L x (G.suc a) l nb = successor m (Ψ m k pl L x a l nb)
Ψ m k pl L x (G.lim f) l nb = G.lim (λ n → Ψ m k pl L x (f n) (proj₂ l n) (nb n))
Ψ m k pl L x (G.lc r c t g) l nb = ΨN m k pl r (wayOf x r) (ndL m k pl L x r c t g l nb)
Ψ m (suc k) pl L x (G.em _ T) l nb = Ψ m k pl L (inS x) T l nb
Ψ m (lim f) pl L x (G.em n T) l nb = Ψ m (f n) (pl n) (proj₂ L n) (inL x n) T l nb
Ψ m zero pl L x G.top l nb = successor m (cO m)
Ψ m (suc k) pl L x G.top l nb = Ψn m k pl (wayOf x (inj₁ tt)) (ndT m k pl L (inS x))
Ψ m (lim f) pl L low G.top l nb =
  G.lim (λ n → Ψ m (f n) (pl n) (proj₂ L n) low G.top tt tt)
Ψ m (lim f) pl L (mix w) G.top l nb =
  G.lim (psum m (λ n → Ψ m (f n) (pl n) (proj₂ L n) (mix (λ r → w (n , r))) G.top tt tt))

ndL m k pl L x r c t g l nb = nd c (proj₁ nb) (proj₁ (proj₂ nb))
  (Ψ m k pl L x t (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
  (λ η e → Ψ m k pl L x (g η e)
    (proj₂ (proj₂ (proj₂ (proj₂ l))) η e) (proj₂ (proj₂ (proj₂ nb)) η e))
  (λ η e → Ψ (lev k r) k pl L (own k pl L r) (g η e)
    (proj₂ (proj₂ (proj₂ (proj₂ l))) η e) (proj₂ (proj₂ (proj₂ nb)) η e))
  (λ η e → Ψ-legal (lev k r) (lev-plain k pl r) k pl L (own k pl L r) tt (g η e)
    (proj₂ (proj₂ (proj₂ (proj₂ l))) η e) (proj₂ (proj₂ (proj₂ nb)) η e))
  (λ η e → Ψ-nested (lev k r) k pl L (own k pl L r) (g η e)
    (proj₂ (proj₂ (proj₂ (proj₂ l))) η e) (proj₂ (proj₂ (proj₂ nb)) η e))
  (λ η e → Ψ-pos (lev k r) k pl L (own k pl L r) (g η e)
    (proj₂ (proj₂ (proj₂ (proj₂ l))) η e) (proj₂ (proj₂ (proj₂ nb)) η e))

ndT m k pl L x = nd (cO k) (cO-Lgl k) (cO-Nested k)
  (Ψ m k pl L x (cO k) (cO-Lgl k) (cO-Nested k))
  (λ η e → Ψ m k pl L x η (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
  (λ η e → Ψ k k pl L (ownT k pl L) η (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
  (λ η e → Ψ-legal k pl k pl L (ownT k pl L) tt η (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
  (λ η e → Ψ-nested k k pl L (ownT k pl L) η (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))
  (λ η e → Ψ-pos k k pl L (ownT k pl L) η (proj₁ (proj₂ e)) (proj₂ (proj₂ e)))

Ψ-pos m k pl L x G.zero l nb = cO-pos m
Ψ-pos m k pl L x (G.suc a) l nb = tt
Ψ-pos m k pl L x (G.lim f) l nb = tt
Ψ-pos m k pl L x (G.lc r c t g) l nb =
  ΨN-pos m k pl r (wayOf x r) (ndL m k pl L x r c t g l nb)
Ψ-pos m (suc k) pl L x (G.em _ T) l nb = Ψ-pos m k pl L (inS x) T l nb
Ψ-pos m (lim f) pl L x (G.em n T) l nb = Ψ-pos m (f n) (pl n) (proj₂ L n) (inL x n) T l nb
Ψ-pos m zero pl L x G.top l nb = tt
Ψ-pos m (suc k) pl L x G.top l nb = Ψn-pos m k pl (wayOf x (inj₁ tt)) (ndT m k pl L (inS x))
Ψ-pos m (lim f) pl L low G.top l nb = tt
Ψ-pos m (lim f) pl L (mix w) G.top l nb = tt

Ψ-legal m pm k pl L x h G.zero l nb = cO-Lgl m
Ψ-legal m pm k pl L x h (G.suc a) l nb =
  copies-step m pm (Ψ m k pl L x a l nb) ,
  copies-legal m pm (Ψ m k pl L x a l nb) (Ψ-legal m pm k pl L x h a l nb)
Ψ-legal m pm k pl L x h (G.lim f) (st , lf) nb =
  (λ n → Ψ-cp m k pl L x (f (suc n)) (lf n) (nb n) (lf (suc n)) (nb (suc n)) (st n)) ,
  (λ n → Ψ-legal m pm k pl L x h (f n) (lf n) (nb n))
Ψ-legal m pm k pl L x h (G.lc r c t g) (tg , dir , irr , lt , lg) (lw , nw , nt , ng) =
  ΨN-legal m k pl r (wayOf x r)
    (ndL m k pl L x r c t g (tg , dir , irr , lt , lg) (lw , nw , nt , ng))
    (record
      { seed = seedL k r c lw nw
      ; tg = λ η e → Ψ-cp m k pl L x (g η e) lt nt (lg η e) (ng η e) (tg η e)
      ; dir = λ η e η′ e′ q →
          Ψ-cp m k pl L x (g η′ e′) (lg η e) (ng η e) (lg η′ e′) (ng η′ e′) (dir η e η′ e′ q)
      ; lt = Ψ-legal m pm k pl L x h t lt nt
      ; lg = λ η e → Ψ-legal m pm k pl L x h (g η e) (lg η e) (ng η e)
      ; lkʳ = λ η e → Ψ-legal (lev k r) (lev-plain k pl r) k pl L (own k pl L r) tt
          (g η e) (lg η e) (ng η e)
      ; nkʳ = λ η e → Ψ-nested (lev k r) k pl L (own k pl L r) (g η e) (lg η e) (ng η e) })
Ψ-legal m pm (suc k) pl L x h (G.em _ T) l nb =
  Ψ-legal m pm k pl L (inS x) (good-S k pl L x h) T l nb
Ψ-legal m pm (lim f) pl L x h (G.em n T) l nb =
  Ψ-legal m pm (f n) (pl n) (proj₂ L n) (inL x n) (good-L f pl L x h n) T l nb
Ψ-legal m pm zero pl L x h G.top l nb =
  copies-step m pm (cO m) , copies-legal m pm (cO m) (cO-Lgl m)
Ψ-legal m pm (suc k) pl L x h G.top l nb =
  Ψn-legal m k pl (wayOf x (inj₁ tt)) (ndT m k pl L (inS x))
    (record
      { seed = inj₁ refl , cO-Lgl k , cO-Nested k
      ; tg = λ η e → Ψ-cp m k pl L (inS x) η (cO-Lgl k) (cO-Nested k)
          (proj₁ (proj₂ e)) (proj₂ (proj₂ e)) (proj₁ e)
      ; dir = λ η e η′ e′ q → Ψ-cp m k pl L (inS x) η′ (proj₁ (proj₂ e)) (proj₂ (proj₂ e))
          (proj₁ (proj₂ e′)) (proj₂ (proj₂ e′)) (proj₁ q)
      ; lt = Ψ-legal m pm k pl L (inS x) (good-S k pl L x h) (cO k) (cO-Lgl k) (cO-Nested k)
      ; lg = λ η e → Ψ-legal m pm k pl L (inS x) (good-S k pl L x h) η
          (proj₁ (proj₂ e)) (proj₂ (proj₂ e))
      ; lkʳ = λ η e → Ψ-legal k pl k pl L (ownT k pl L) tt η
          (proj₁ (proj₂ e)) (proj₂ (proj₂ e))
      ; nkʳ = λ η e → Ψ-nested k k pl L (ownT k pl L) η
          (proj₁ (proj₂ e)) (proj₂ (proj₂ e)) })
Ψ-legal m pm (lim f) pl (st , lg) low (coh , hs) G.top l nb =
  (λ n → subst
    (λ z → Cp m (Ψ m (f n) (proj₁ z) (proj₂ z) low G.top tt tt)
                (Ψ m (f (suc n)) (pl (suc n)) (lg (suc n)) low G.top tt tt))
    (coh n) (below m (f (suc n)) (st n) (pl (suc n)) (lg (suc n)))) ,
  (λ n → Ψ-legal m pm (f n) (pl n) (lg n) low (hs n) G.top tt tt)
Ψ-legal m pm (lim f) pl L (mix w) h G.top l nb =
  psum-step m (λ n → Ψ m (f n) (pl n) (proj₂ L n) (mix (λ r → w (n , r))) G.top tt tt) ,
  psum-legal m pm (λ n → Ψ m (f n) (pl n) (proj₂ L n) (mix (λ r → w (n , r))) G.top tt tt)
    (λ n → Ψ-legal m pm (f n) (pl n) (proj₂ L n) (mix (λ r → w (n , r))) tt G.top tt tt)

Ψ-nested m k pl L x G.zero l nb = cO-Nested m
Ψ-nested m k pl L x (G.suc a) l nb =
  copies-nested m (Ψ m k pl L x a l nb) (Ψ-nested m k pl L x a l nb)
Ψ-nested m k pl L x (G.lim f) (st , lf) nb = λ n → Ψ-nested m k pl L x (f n) (lf n) (nb n)
Ψ-nested m k pl L x (G.lc r c t g) (tg , dir , irr , lt , lg) (lw , nw , nt , ng) =
  ΨN-nested m k pl r (wayOf x r)
    (ndL m k pl L x r c t g (tg , dir , irr , lt , lg) (lw , nw , nt , ng))
    (record
      { seed = seedL k r c lw nw
      ; lcʳ = lw
      ; ncʳ = nw
      ; nt = Ψ-nested m k pl L x t lt nt
      ; ng = λ η e → Ψ-nested m k pl L x (g η e) (lg η e) (ng η e)
      ; lkʳ = λ η e → Ψ-legal (lev k r) (lev-plain k pl r) k pl L (own k pl L r) tt
          (g η e) (lg η e) (ng η e)
      ; nkʳ = λ η e → Ψ-nested (lev k r) k pl L (own k pl L r) (g η e) (lg η e) (ng η e) })
Ψ-nested m (suc k) pl L x (G.em _ T) l nb = Ψ-nested m k pl L (inS x) T l nb
Ψ-nested m (lim f) pl L x (G.em n T) l nb =
  Ψ-nested m (f n) (pl n) (proj₂ L n) (inL x n) T l nb
Ψ-nested m zero pl L x G.top l nb = copies-nested m (cO m) (cO-Nested m)
Ψ-nested m (suc k) pl L x G.top l nb =
  Ψn-nested m k pl (wayOf x (inj₁ tt)) (ndT m k pl L (inS x))
    (record
      { seed = inj₁ refl , cO-Lgl k , cO-Nested k
      ; lcʳ = cO-Lgl k
      ; ncʳ = cO-Nested k
      ; nt = Ψ-nested m k pl L (inS x) (cO k) (cO-Lgl k) (cO-Nested k)
      ; ng = λ η e → Ψ-nested m k pl L (inS x) η (proj₁ (proj₂ e)) (proj₂ (proj₂ e))
      ; lkʳ = λ η e → Ψ-legal k pl k pl L (ownT k pl L) tt η
          (proj₁ (proj₂ e)) (proj₂ (proj₂ e))
      ; nkʳ = λ η e → Ψ-nested k k pl L (ownT k pl L) η
          (proj₁ (proj₂ e)) (proj₂ (proj₂ e)) })
Ψ-nested m (lim f) pl L low G.top l nb =
  λ n → Ψ-nested m (f n) (pl n) (proj₂ L n) low G.top tt tt
Ψ-nested m (lim f) pl L (mix w) G.top l nb =
  psum-nested m (λ n → Ψ m (f n) (pl n) (proj₂ L n) (mix (λ r → w (n , r))) G.top tt tt)
    (λ n → Ψ-nested m (f n) (pl n) (proj₂ L n) (mix (λ r → w (n , r))) G.top tt tt)

Ψ-cp m k pl L x ξ′ l nb l′ nb′ (inj₁ refl) = inj₁ refl
Ψ-cp m k pl L x ξ′ l nb l′ nb′ (inj₂ p) = inj₂ (Ψ-dn m k pl L x ξ′ l nb l′ nb′ p)

Ψ-dn m k pl L x (G.suc d) l nb l′ nb′ p = zero , Ψ-cp m k pl L x d l nb l′ nb′ p
Ψ-dn m k pl L x (G.lim f) l nb (st , lf) nb′ (n , p) =
  n , Ψ-cp m k pl L x (f n) l nb (lf n) (nb′ n) p
Ψ-dn m k pl L x (G.lc r c t g) l nb (tg , dir , irr , lt , lg) (lw , nw , nt , ng) p =
  ΨN-dn m k pl r (wayOf x r)
    (ndL m k pl L x r c t g (tg , dir , irr , lt , lg) (lw , nw , nt , ng))
    (Ψ-cp m k pl L x t l nb lt nt p)
    (seedL k r c lw nw)
    (Ψ-cp m k pl L x (g c (seedL k r c lw nw)) l nb
      (lg c (seedL k r c lw nw)) (ng c (seedL k r c lw nw))
      (Cp-tr k p (tg c (seedL k r c lw nw))))
Ψ-dn m (suc k) pl L x {G.em _ a} (G.em _ T) l nb l′ nb′ p =
  Ψ-dn m k pl L (inS x) T l nb l′ nb′ p
Ψ-dn m (lim f) pl L x {G.em n a} (G.em .n T) l nb l′ nb′ (refl , p) =
  Ψ-dn m (f n) (pl n) (proj₂ L n) (inL x n) T l nb l′ nb′ p
Ψ-dn m (suc k) pl L x {G.em _ a} G.top l nb l′ nb′ p =
  Ψn-dn m k pl (wayOf x (inj₁ tt)) (ndT m k pl L (inS x))
    (Ψ-top m k pl L (inS x) l nb p)
    (inj₁ refl , cO-Lgl k , cO-Nested k)
    (Ψ-top m k pl L (inS x) l nb p)

Ψ-top m zero pl L x l nb (inj₁ refl) = inj₁ refl
Ψ-top m (suc k) pl L x l nb p = Ψ-cp m (suc k) pl L x G.top l nb tt tt p
Ψ-top m (lim f) pl L x l nb p = Ψ-cp m (lim f) pl L x G.top l nb tt tt p

below m b self pb Lb = inj₁ refl
below m (suc zero) (suc p) pb Lb = inj₂ (zero , below m zero p pb Lb)
below m (suc (suc b)) (suc p) pb Lb = inj₂ (zero , below m (suc b) p pb Lb)
below m (suc (lim f)) (suc p) pb Lb = inj₂ (zero , below m (lim f) p pb Lb)
below m (lim f) (lim n p) pb Lb = inj₂ (n , below m (f n) p (pb n) (proj₂ Lb n))
```

## 3 行

都是 `refl`。结点行把结点接到 `ΨN`，`ΨN` 在根位置是 `Ψn` (`YiRawFoldBase` §3 的三个子句)，`Ψn` 的两行是保留行与链行。

```agda
zero-row : ∀ m k pl L (x : Ext m k) → Ψ m k pl L x G.zero tt tt ≡ cO m
zero-row m k pl L x = refl

suc-row : ∀ m k pl L (x : Ext m k) a (l : Lgl k a) (nb : Nested k a) →
  Ψ m k pl L x (G.suc a) l nb ≡ successor m (Ψ m k pl L x a l nb)
suc-row m k pl L x a l nb = refl

lim-row : ∀ m k pl L (x : Ext m k) f (l : Lgl k (G.lim f)) (nb : Nested k (G.lim f)) →
  Ψ m k pl L x (G.lim f) l nb ≡ G.lim (λ n → Ψ m k pl L x (f n) (proj₂ l n) (nb n))
lim-row m k pl L x f l nb = refl

node-row : ∀ m k pl L (x : Ext m k) r c t g
  (l : Lgl k (G.lc r c t g)) (nb : Nested k (G.lc r c t g)) →
  Ψ m k pl L x (G.lc r c t g) l nb ≡
  ΨN m k pl r (wayOf x r) (ndL m k pl L x r c t g l nb)
node-row m k pl L x r c t g l nb = refl

em-rowˢ : ∀ m k pl L (x : Ext m (suc k)) T (l : Lgl k T) (nb : Nested k T) →
  Ψ m (suc k) pl L x (G.em tt T) l nb ≡ Ψ m k pl L (inS x) T l nb
em-rowˢ m k pl L x T l nb = refl

em-rowˡ : ∀ m f pl L (x : Ext m (lim f)) n T (l : Lgl (f n) T) (nb : Nested (f n) T) →
  Ψ m (lim f) pl L x (G.em n T) l nb ≡ Ψ m (f n) (pl n) (proj₂ L n) (inL x n) T l nb
em-rowˡ m f pl L x n T l nb = refl

top-row⁰ : ∀ m pl L (x : Ext m zero) → Ψ m zero pl L x G.top tt tt ≡ successor m (cO m)
top-row⁰ m pl L x = refl

top-rowˢ : ∀ m k pl L (x : Ext m (suc k)) →
  Ψ m (suc k) pl L x G.top tt tt ≡ Ψn m k pl (wayOf x (inj₁ tt)) (ndT m k pl L (inS x))
top-rowˢ m k pl L x = refl

-- top 与字面写出的根位置结点 (下界 cO k, 第一支与分支是嵌入) 折叠相同.
top-as-node : ∀ m k pl L (x : Ext m (suc k))
  .(l : Lgl (suc k) (G.lc (inj₁ tt) (cO k) (G.em tt (cO k)) (λ η e → G.em tt η)))
  .(nb : Nested (suc k) (G.lc (inj₁ tt) (cO k) (G.em tt (cO k)) (λ η e → G.em tt η))) →
  Ψ m (suc k) pl L x G.top tt tt ≡
  Ψ m (suc k) pl L x (G.lc (inj₁ tt) (cO k) (G.em tt (cO k)) (λ η e → G.em tt η)) l nb
top-as-node m k pl L x l nb = refl

top-rowˡ : ∀ m f pl L → Ψ m (lim f) pl L low G.top tt tt ≡
  G.lim (λ n → Ψ m (f n) (pl n) (proj₂ L n) low G.top tt tt)
top-rowˡ m f pl L = refl

top-rowᶜ : ∀ m f pl L w → Ψ m (lim f) pl L (mix w) G.top tt tt ≡
  G.lim (psum m (λ n → Ψ m (f n) (pl n) (proj₂ L n) (mix (λ r → w (n , r))) G.top tt tt))
top-rowᶜ m f pl L w = refl
```

`Ψn` 的两行。链的四件 (起点、下一点、推进用的输出、观察) 从记录里取；下一点是这一点加上 `gk` 在这一点的输出，
`gk` 在 `ndL` 里是结点自己那一层的折叠 (`own`)，观察 `gm` 是目标层的折叠。

```agda
ΨN-rowʳ : ∀ m k pl (y : Way m k) (N : NdR m k) → ΨN m (suc k) pl (inj₁ tt) y N ≡ Ψn m k pl y N
ΨN-rowʳ m k pl y N = refl

ΨN-rowˢ : ∀ m k pl r (y : Way m (lev k r)) (N : NdL m k r) →
  ΨN m (suc k) pl (inj₂ r) y N ≡ ΨN m k pl r y N
ΨN-rowˢ m k pl r y N = refl

ΨN-rowˡ : ∀ m f pl n r (y : Way m (lev (f n) r)) (N : NdL m (f n) r) →
  ΨN m (lim f) pl (n , r) y N ≡ ΨN m (f n) (pl n) r y N
ΨN-rowˡ m f pl n r y N = refl

keep-row : ∀ m s .(pl : Plain (lev m s)) (N : NdR m (lev m s)) →
  Ψn m (lev m s) pl (keep s refl) N ≡ nodeAt m s (rawAlg m) (Nd.c N) (Nd.t N) (Nd.gm N)
keep-row m s pl N = refl

startᴿ : ∀ {m k} (N : NdR m k) → Pt k (Nd.c N)
startᴿ {k = k} (nd c lw nw t gm gk lk nk pk) = startᴸ k c lw nw

nextᴿ : ∀ {m k} → .(Plain k) → (N : NdR m k) → Pt k (Nd.c N) → Pt k (Nd.c N)
nextᴿ {k = k} pl (nd c lw nw t gm gk lk nk pk) = Chain.next k pl c gk lk nk pk

bodyᴿ : ∀ {m k} (N : NdR m k) → Pt k (Nd.c N) → Raw k
bodyᴿ N (pt η e) = Nd.gk N η e

obsᴿ : ∀ {m k} (N : NdR m k) → Pt k (Nd.c N) → Raw m
obsᴿ N (pt η e) = Nd.gm N η e

fold-row : ∀ m k .(pl : Plain k) (N : NdR m k) →
  Ψn m k pl fold N ≡ G.lim (λ n → obsᴿ N (iterate (nextᴿ pl N) (startᴿ N) n))
fold-row m k pl N = refl

next-additive : ∀ {m k} .(pl : Plain k) (N : NdR m k) p →
  atᵖ (nextᴿ pl N p) ≡ plus k (atᵖ p) (bodyᴿ N p)
next-additive pl N p = refl

next-grow : ∀ {m k} .(pl : Plain k) (N : NdR m k) p → Dn k (atᵖ p) (atᵖ (nextᴿ pl N p))
next-grow {k = k} pl (nd c lw nw t gm gk lk nk pk) = Chain.grows k pl c gk lk nk pk

certificate-free : ∀ m k pl L (x : Ext m k) ξ (l l′ : Lgl k ξ) (nb nb′ : Nested k ξ) →
  Ψ m k pl L x ξ l nb ≡ Ψ m k pl L x ξ l′ nb′
certificate-free m k pl L x ξ l l′ nb nb′ = refl
```

## 4 接口

`Φᵐ`：三种目标都用接口的派发，`mix` 之下。它满足 `YiRawIf.RawFold`，没有前提。
`Φ`：目标第 0 层用 `low`，合法性在那里要 `CohP K pl L`；在 `self`, `at q` 上与 `Φᵐ` 是同一个定义 (`Φ-self`, `Φ-at`)。
互递归块里 `low` 与 `mix` 分开写的子句只有极限层号上 `top` 的那一行；派发在两边都是折叠 (`ext-way`)。
`keepᴳ`, `foldᴳ` 是携带强度的两条在一般外部派发上的形式。

```agda
tplain : ∀ K → Plain K → ∀ τ → Plain (tlev K τ)
tplain K pl base = tt
tplain K pl self = pl
tplain K pl (at q) = lev-plain K pl q

keepᴳ : ∀ m → Plain m → ∀ k pl L (x : Ext m k) r c t g
  (l : Lgl k (G.lc r c t g)) (nb : Nested k (G.lc r c t g)) →
  IsKeep (wayOf x r) → Kept m (lev k r) (Ψ m k pl L x (G.lc r c t g) l nb)
keepᴳ m pm k pl L x r c t g l nb h =
  ΨN-kept m pm k pl r (wayOf x r) (ndL m k pl L x r c t g l nb) h

foldᴳ : ∀ m k pl L (x : Ext m k) r c t g
  (l : Lgl k (G.lc r c t g)) (nb : Nested k (G.lc r c t g)) →
  (IsKeep (wayOf x r) → ⊥) → IsLim (Ψ m k pl L x (G.lc r c t g) l nb)
foldᴳ m k pl L x r c t g l nb h =
  ΨN-lim m k pl r (wayOf x r) (ndL m k pl L x r c t g l nb) h

Φᵐ : ∀ K → Plain K → Legal K → (τ : Tgt K) (ξ : Raw K) →
  .(Lgl K ξ) → .(Nested K ξ) → Raw (tlev K τ)
Φᵐ K pl L τ ξ l nb = Ψ (tlev K τ) K pl L (mix (dispatch K pl L τ)) ξ l nb

rawFold : RawFold
rawFold = record
  { Φ = Φᵐ
  ; keep-law = λ K pl L τ r c t g l nb a →
      keepᴳ (tlev K τ) (tplain K pl τ) K pl L (mix (dispatch K pl L τ)) r c t g l nb
        (dispatch-complete K pl L τ r a)
  ; fold-law = λ K pl L τ r c t g l nb na →
      foldᴳ (tlev K τ) K pl L (mix (dispatch K pl L τ)) r c t g l nb
        (λ h → na (dispatch-sound K pl L τ r h))
  ; position = λ K pl L τ ξ ξ′ l nb l′ nb′ p →
      Ψ-cp (tlev K τ) K pl L (mix (dispatch K pl L τ)) ξ′ l nb l′ nb′ p
  ; legal = λ K pl L τ ξ l nb →
      Ψ-legal (tlev K τ) (tplain K pl τ) K pl L (mix (dispatch K pl L τ)) tt ξ l nb }

ext : ∀ K → Plain K → Legal K → (τ : Tgt K) → Ext (tlev K τ) K
ext K pl L base = low
ext K pl L self = mix (dispatch K pl L self)
ext K pl L (at q) = mix (dispatch K pl L (at q))

ext-way : ∀ K pl L τ r → wayOf (ext K pl L τ) r ≡ dispatch K pl L τ r
ext-way K pl L base r = refl
ext-way K pl L self r = refl
ext-way K pl L (at q) r = refl

Φ : ∀ K → Plain K → Legal K → (τ : Tgt K) (ξ : Raw K) →
  .(Lgl K ξ) → .(Nested K ξ) → Raw (tlev K τ)
Φ K pl L τ ξ l nb = Ψ (tlev K τ) K pl L (ext K pl L τ) ξ l nb

Φ-self : ∀ K pl L ξ (l : Lgl K ξ) (nb : Nested K ξ) → Φ K pl L self ξ l nb ≡ Φᵐ K pl L self ξ l nb
Φ-self K pl L ξ l nb = refl

Φ-at : ∀ K pl L q ξ (l : Lgl K ξ) (nb : Nested K ξ) →
  Φ K pl L (at q) ξ l nb ≡ Φᵐ K pl L (at q) ξ l nb
Φ-at K pl L q ξ l nb = refl

-- 目标是 K 自己: 根位置与根下一格的结点原样保留, 槽位就是结点的位置.
self-keep₀ : ∀ k pl L c t g (l : Lgl (suc k) (G.lc (inj₁ tt) c t g))
  (nb : Nested (suc k) (G.lc (inj₁ tt) c t g)) →
  Φ (suc k) pl L self (G.lc (inj₁ tt) c t g) l nb ≡
  G.lc (inj₁ tt) c
    (Φ (suc k) pl L self t (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
    (λ η e → Φ (suc k) pl L self (g η e)
      (proj₂ (proj₂ (proj₂ (proj₂ l))) η e) (proj₂ (proj₂ (proj₂ nb)) η e))
self-keep₀ k pl L c t g l nb = refl

self-keep₁ : ∀ k pl L c t g (l : Lgl (suc (suc k)) (G.lc (inj₂ (inj₁ tt)) c t g))
  (nb : Nested (suc (suc k)) (G.lc (inj₂ (inj₁ tt)) c t g)) →
  Φ (suc (suc k)) pl L self (G.lc (inj₂ (inj₁ tt)) c t g) l nb ≡
  G.lc (inj₂ (inj₁ tt)) c
    (Φ (suc (suc k)) pl L self t (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
    (λ η e → Φ (suc (suc k)) pl L self (g η e)
      (proj₂ (proj₂ (proj₂ (proj₂ l))) η e) (proj₂ (proj₂ (proj₂ nb)) η e))
self-keep₁ k pl L c t g l nb = refl

GoodT : ∀ K → Plain K → Legal K → Tgt K → Set
GoodT K pl L τ = Good K pl L (ext K pl L τ)

good-self : ∀ K pl L → GoodT K pl L self
good-self K pl L = tt

good-at : ∀ K pl L q → GoodT K pl L (at q)
good-at K pl L q = tt

Φ-keep : ∀ K pl L τ r c t g
  (l : Lgl K (G.lc r c t g)) (nb : Nested K (G.lc r c t g)) →
  At (tlev K τ) (lev K r) → Kept (tlev K τ) (lev K r) (Φ K pl L τ (G.lc r c t g) l nb)
Φ-keep K pl L τ r c t g l nb a =
  keepᴳ (tlev K τ) (tplain K pl τ) K pl L (ext K pl L τ) r c t g l nb
    (subst IsKeep (sym (ext-way K pl L τ r)) (dispatch-complete K pl L τ r a))

Φ-fold : ∀ K pl L τ r c t g
  (l : Lgl K (G.lc r c t g)) (nb : Nested K (G.lc r c t g)) →
  (At (tlev K τ) (lev K r) → ⊥) → IsLim (Φ K pl L τ (G.lc r c t g) l nb)
Φ-fold K pl L τ r c t g l nb na =
  foldᴳ (tlev K τ) K pl L (ext K pl L τ) r c t g l nb
    (λ h → na (dispatch-sound K pl L τ r (subst IsKeep (ext-way K pl L τ r) h)))

Φ-position : ∀ K pl L τ ξ ξ′ (l : Lgl K ξ) (nb : Nested K ξ)
  (l′ : Lgl K ξ′) (nb′ : Nested K ξ′) → Cp K ξ ξ′ →
  Cp (tlev K τ) (Φ K pl L τ ξ l nb) (Φ K pl L τ ξ′ l′ nb′)
Φ-position K pl L τ ξ ξ′ l nb l′ nb′ p =
  Ψ-cp (tlev K τ) K pl L (ext K pl L τ) ξ′ l nb l′ nb′ p

Φ-legal : ∀ K pl L τ → GoodT K pl L τ → ∀ ξ (l : Lgl K ξ) (nb : Nested K ξ) →
  Lgl (tlev K τ) (Φ K pl L τ ξ l nb)
Φ-legal K pl L τ h ξ l nb =
  Ψ-legal (tlev K τ) (tplain K pl τ) K pl L (ext K pl L τ) h ξ l nb

Φ-nested : ∀ K pl L τ ξ (l : Lgl K ξ) (nb : Nested K ξ) →
  Nested (tlev K τ) (Φ K pl L τ ξ l nb)
Φ-nested K pl L τ ξ l nb = Ψ-nested (tlev K τ) K pl L (ext K pl L τ) ξ l nb
```

## 5 折叠问到的派发都完全

`Complete x`：结点层在目标层的某个位置上，`x` 就保留。保留时反过来总是对的 (`keep` 自带槽位与方程)。
互递归块里出现的外部派发只有五种来源：入口的 `ext` 或 `mix (dispatch …)`，`inS`，`inL` (极限层号上 `top` 的 `mix` 行也是它)，`own`，`ownT`。五种都完全。

```agda
Complete : ∀ {m k} → Ext m k → Set
Complete {m} {k} x = ∀ r → At m (lev k r) → IsKeep (wayOf x r)

complete-S : ∀ {m k} (x : Ext m (suc k)) → Complete x → Complete (inS x)
complete-S low h r a = h (inj₂ r) a
complete-S (mix w) h r a = h (inj₂ r) a

complete-L : ∀ {m f} (x : Ext m (lim f)) → Complete x → ∀ n → Complete (inL x n)
complete-L low h n r a = h (n , r) a
complete-L (mix w) h n r a = h (n , r) a

complete-own : ∀ k pl L r → Complete (own k pl L r)
complete-own k pl L r r′ a = dispatch-complete k pl L (at r) r′ a

complete-ownT : ∀ k pl L → Complete (ownT k pl L)
complete-ownT k pl L = complete-S (own (suc k) pl L (inj₁ tt)) (complete-own (suc k) pl L (inj₁ tt))

complete-mix : ∀ K pl L τ → Complete (mix (dispatch K pl L τ))
complete-mix K pl L τ r a = dispatch-complete K pl L τ r a

complete-ext : ∀ K pl L τ → Complete (ext K pl L τ)
complete-ext K pl L τ r a =
  subst IsKeep (sym (ext-way K pl L τ r)) (dispatch-complete K pl L τ r a)
```
