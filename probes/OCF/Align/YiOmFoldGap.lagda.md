# YiOmFold：缺的行，写成带类型的前提与编译的实例

**判决 (编译定理)：保留模式下 `top` 的行，分支族只拿到无关的守卫；它若满足保留律 (`KeepLaw`：第 `suc a` 支是层号 `read0 a` 的保留结点)，则 `IrrSearch` (`keep→irr-search`)，并且输出不在 `Tr` 里 (`keep-not-tr`)。
守卫相关时那一支写得出 (`keep-rel`)；但各支逐槽位搬进来以后互不为第一位置，也不在第一支之上 (`moved-undirected`, `moved-not-first`，两个闭实例)。** 分支槽位上结点的目标层 0 行条件于那一支里的目标的折叠 (`BranchRow`)。
不否定别的放法 (例如各支共用一套槽位)；`IrrSearch` 没有被反驳。折叠在 [YiOmFold](YiOmFold.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiOmFoldGap where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim; ⊥-elim-irr)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1; raw0-Nested; cO; cO-Lgl; cO-Nested)
open import OCF.Align.YiIrrIf using (R; one; read0; read0-legal; CP; self; suc; lim; fst; Legal)
open import OCF.Align.YiIrrNegWide using (Found; IrrSearch; seen; seen-found; flag; dense)
open import OCF.Align.YiLvIf using (lev; Kept)
open import OCF.Align.YiLvFoldAdd using (Pos; add)
open import OCF.Align.YiLvFoldBase using (fold; cO-pos)
open import OCF.Align.YiLvNegCompare using (coordᴺ; levelᴺ; found→lgl; lev-legal)
open import OCF.Align.YiLvNegKeep using (kept-at; kept-node)
open import OCF.Align.YiRawFoldBase using (NdL; nd; ΨN; ΨN-legal; seedL)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; first₂; br)
open import OCF.Align.YiOmIf using (kid-rel)
open import OCF.Align.YiOmFoldBase
open import OCF.Align.YiOmFold
```

## 1 保留模式下 `top` 的行：前提的类型

`Branches`：结点的分支函数的类型，守卫无关。`RowLegal β`：以 `β` 为分支的根槽位结点合法所要的四条。
`KeepLaw β`：`tw 3` 的第 `suc a` 支是层号 `read0 a` 的结点，这个层号在 `tw 2` 的位置 `br (suc a) e (inj₁ tt)` 上，所以目标为 `tw 2` 自己时它必须保留。

```agda
Branches : Set
Branches = (η : R) → .(Gd zero raw1 η) → RΩ

record RowLegal (β : Branches) : Set where
  field
    first : ∀ η (e : Gd zero raw1 η) → Cp K₂ω t₀ (β η e)
    directed : ∀ η (e : Gd zero raw1 η) η′ (e′ : Gd zero raw1 η′) → Gd zero η η′ →
      Cp K₂ω (β η e) (β η′ e′)
    lawful : ∀ η (e : Gd zero raw1 η) → Lgl K₂ω (β η e)
    nested : ∀ η (e : Gd zero raw1 η) → Nested K₂ω (β η e)

KeepLaw : Branches → Set
KeepLaw β = ∀ a (e : Gd zero raw1 (G.suc a)) → Kept K₂ω (read0 a) (β (G.suc a) e)

row : Branches → RΩ
row β = G.lc root₂ raw1 t₀ β

row-legal : ∀ β → RowLegal β → Lgl K₂ω (row β)
row-legal β H = first , directed , (λ η e e′ → refl) , F₁-legal G.top tt , lawful
  where open RowLegal H

row-nested : ∀ β → RowLegal β → Nested K₂ω (row β)
row-nested β H = tt , tt , F₁-nested G.top tt , RowLegal.nested H
```

替代行满足 `RowLegal`，不满足 `KeepLaw`：它在 `suc a` 上是 ℕ 极限。

```agda
βˢ : Branches
βˢ η e = plusΩ t₀ (F₀ η)

βˢ-row : row βˢ ≡ Φˢ G.top tt
βˢ-row = refl

βˢ-legal : RowLegal βˢ
βˢ-legal = record
  { first = λ η e → plus-weak t₀ (F₀ η)
  ; directed = λ η e η′ e′ q → plus-cp t₀ (F₀-cp (proj₁ q))
  ; lawful = λ η e → plus-lgl t₀ (F₀ η) (F₁-legal G.top tt) (F₀-legal η (proj₁ (proj₂ e)))
  ; nested = λ η e → plus-ns t₀ (F₀ η) (F₁-nested G.top tt) (F₀-nested η) }

two three : R
two = G.suc one
three = G.suc two

e-two : Gd zero raw1 two
e-two = inj₂ (inj₁ refl) , tt , tt

e-three : Gd zero raw1 three
e-three = inj₂ (inj₂ (inj₁ refl)) , tt , tt

βˢ-not-keep : KeepLaw βˢ → ⊥
βˢ-not-keep kl with kl one e-two
... | r , q , c , t , g , ()
```

满足保留律的分支族把结点放到分支槽位上，所以不在 `Tr` 里：第 2 支的输出是层号 1 的保留结点，主干上的层号只有 0。

```agda
keep-not-tr : ∀ (β : Branches) → KeepLaw β →
  (∀ η (e : Gd zero raw1 η) → Tr (β η e)) → ⊥
keep-not-tr β kl tr with β two e-two | kl one e-two | tr two e-two
... | .(G.lc (inj₁ (inj₁ _)) c t g) | inj₁ (inj₁ _) , () , c , t , g , refl | d
... | .(G.lc (inj₂ (inj₁ (inj₁ _))) c t g) | inj₂ (inj₁ (inj₁ _)) , () , c , t , g , refl | d
... | .(G.lc (inj₂ (inj₂ _)) c t g) | inj₂ (inj₂ _) , q , c , t , g , refl | ()
```

## 2 保留律推出 `IrrSearch`

坐标 `suc (coordᴺ α)` 的守卫与 `Found α` 等价 (`YiLvNegCompare`)。分支族只拿到无关的守卫，但它的输出是相关的树：
输出若是保留结点，槽位是相关的位置；槽位在第 `η″` 支里时带相关的守卫，读出那个层号的 `Legal`，其中第 0 步的路径交出见证。
层号相等只无关地知道，所以先按构造子拆开层号，再读路径。

```agda
at : ℕ → LF → LF
at n (lim f) = f n
at n zero = zero
at n (suc x) = zero
at n (lc k c w b t g) = zero

pred : LF → LF
pred (suc x) = x
pred zero = zero
pred (lim f) = zero
pred (lc k c w b t g) = zero

decide : (b : Bool) → .(b ≡ true) → b ≡ true
decide true e = refl
decide false e = ⊥-elim-irr (no e)
  where no : false ≡ true → ⊥
        no ()

no-cp : CP (suc zero) zero → ⊥
no-cp ()

hit : ∀ (b : Bool) x z → CP x z → x ≡ suc zero → z ≡ read0 (flag b) → b ≡ true
hit true x z p ex ez = refl
hit false x z p refl refl = ⊥-elim (no-cp p)

climb : ∀ α x y → CP x y → .(x ≡ suc zero) → .(y ≡ read0 (dense α)) → Found α
climb α x .x self ex ey = ⊥-elim-irr (no ex ey)
  where no : x ≡ suc zero → x ≡ read0 (dense α) → ⊥
        no refl ()
climb α x (suc y) (suc p) ex ey = ⊥-elim-irr (no ey)
  where no : suc y ≡ read0 (dense α) → ⊥
        no ()
climb α x (lim f) (lim m p) ex ey =
  seen-found α m (decide (seen α m) (hit (seen α m) x (f m) p ex (cong (at m) ey)))
climb α x (lc k c w b t g) (fst p) ex ey = ⊥-elim-irr (no ey)
  where no : lc k c w b t g ≡ read0 (dense α) → ⊥
        no ()

step : ∀ α x y → CP x y → .(x ≡ suc zero) → .(y ≡ suc (read0 (dense α))) → Found α
step α x .x self ex ey = ⊥-elim-irr (no ex ey)
  where no : x ≡ suc zero → x ≡ suc (read0 (dense α)) → ⊥
        no refl ()
step α x (suc y) (suc p) ex ey = climb α x y p ex (cong pred ey)
step α x (lim f) (lim m p) ex ey = ⊥-elim-irr (no ey)
  where no : lim f ≡ suc (read0 (dense α)) → ⊥
        no ()
step α x (lc k c w b t g) (fst p) ex ey = ⊥-elim-irr (no ey)
  where no : lc k c w b t g ≡ suc (read0 (dense α)) → ⊥
        no ()

legal→found : ∀ α (L : LF) → Legal L → .(L ≡ levelᴺ α) → Found α
legal→found α zero lg eq = ⊥-elim-irr (no eq)
  where no : zero ≡ levelᴺ α → ⊥
        no ()
legal→found α (suc L) lg eq = ⊥-elim-irr (no eq)
  where no : suc L ≡ levelᴺ α → ⊥
        no ()
legal→found α (lim f) (st , lg) eq =
  step α (f 0) (f 1) (st 0) (cong (at 0) eq) (cong (at 1) eq)
legal→found α (lc k c w b t g) lg eq = ⊥-elim-irr (no eq)
  where no : lc k c w b t g ≡ levelᴺ α → ⊥
        no ()

zero≢level : ∀ α → zero ≡ levelᴺ α → ⊥
zero≢level α ()

slot→found : ∀ α (y : RΩ) → .(Kept K₂ω (levelᴺ α) y) → Found α
slot→found α (G.lc (inj₁ (inj₁ u)) c t g) kp =
  ⊥-elim-irr (zero≢level α (kept-at K₂ω (levelᴺ α) (inj₁ (inj₁ u)) c t g kp))
slot→found α (G.lc (inj₂ (inj₁ (inj₁ u))) c t g) kp =
  ⊥-elim-irr (zero≢level α (kept-at K₂ω (levelᴺ α) (inj₂ (inj₁ (inj₁ u))) c t g kp))
slot→found α (G.lc (inj₂ (inj₂ (η , e , r))) c t g) kp =
  legal→found α (lev (read0 η) r)
    (lev-legal (read0 η) (rplain η) (read0-legal η (proj₁ (proj₂ e))) r)
    (kept-at K₂ω (levelᴺ α) (br η e r) c t g kp)
slot→found α G.zero kp = ⊥-elim-irr (kept-node K₂ω (levelᴺ α) G.zero kp)
slot→found α (G.suc y) kp = ⊥-elim-irr (kept-node K₂ω (levelᴺ α) (G.suc y) kp)
slot→found α (G.lim f) kp = ⊥-elim-irr (kept-node K₂ω (levelᴺ α) (G.lim f) kp)
slot→found α (G.em i T) kp = ⊥-elim-irr (kept-node K₂ω (levelᴺ α) (G.em i T) kp)
slot→found α G.top kp = ⊥-elim-irr (kept-node K₂ω (levelᴺ α) G.top kp)

guardᴺ : ∀ α → Found α → Gd zero raw1 (G.suc (coordᴺ α))
guardᴺ α s =
  inj₂ (inj₂ (zero , inj₁ refl)) , found→lgl α s , raw0-Nested (G.suc (coordᴺ α))

keep→irr-search : ∀ (β : Branches) → KeepLaw β → IrrSearch
keep→irr-search β kl α s =
  slot→found α (β (G.suc (coordᴺ α)) (guardᴺ α s)) (kl (coordᴺ α) (guardᴺ α s))
```

## 3 守卫相关时：那一支写得出，但各支用各自的槽位

`move η e T`：把第 `η` 支的树逐槽位搬进 `tw 2` (加法在 `em (η , e) T` 上的行，加到零上)。它在 `top` 上是那一支根槽位上的保留结点，合法。
所以缺的不是某一支，是 "对一切 `η` 只凭无关的守卫" 的分支函数。

```agda
move : ∀ η (e : Gd zero raw1 η) → Raw (read0 η) → RΩ
move η e T = plusΩ G.zero (kid-rel η e T)

keep-rel : ∀ a (e : Gd zero raw1 (G.suc a)) → Kept K₂ω (read0 a) (move (G.suc a) e G.top)
keep-rel a e = br (G.suc a) e (inj₁ tt) , refl , cO (read0 a) , _ , _ , refl

move-legal : ∀ η (e : Gd zero raw1 η) T → Lgl (read0 η) T → Lgl K₂ω (move η e T)
move-legal η e T l = plus-lgl G.zero (kid-rel η e T) tt l

-- 保留律这个前提不是空的: 守卫若能从无关变回相关, 就有满足它的分支族.
GdData : Set
GdData = ∀ η → .(Gd zero raw1 η) → Gd zero raw1 η

keep-from-data : GdData → Σ Branches KeepLaw
keep-from-data gd =
  (λ η e → move η (gd η e) G.top) , (λ a e → keep-rel a (gd (G.suc a) e))
```

即使守卫相关，把各支这样搬进来排成结点也不合法：嵌入的孩子跨支不可比，不在第一支的孩子之上；
搬进来的结点落在各支自己的槽位上，第 2 支的不是第 3 支的第一位置，第一支的也不是第 2 支的第一位置。后两条是闭实例。

```agda
kidOf : RΩ → R
kidOf (G.em (inj₂ (inj₂ (η , e))) T) = η
kidOf _ = G.zero

kid-same-branch : ∀ η e T η′ e′ T′ →
  Cp K₂ω (kid-rel η e T) (kid-rel η′ e′ T′) → η ≡ η′
kid-same-branch η e T η′ e′ T′ (inj₁ q) = cong kidOf q
kid-same-branch η e T η′ e′ T′ (inj₂ (q , p)) = cong proj₁ q

kid-not-above-first : ∀ η e T T₁ →
  Cp K₂ω (G.em (inj₂ (inj₁ tt)) T₁) (kid-rel η e T) → ⊥
kid-not-above-first η e T T₁ (inj₁ ())
kid-not-above-first η e T T₁ (inj₂ ())

moved-undirected : Cp K₂ω (move two e-two G.top) (move three e-three G.top) → ⊥
moved-undirected (inj₁ ())
moved-undirected (inj₂ (inj₁ ()))
moved-undirected (inj₂ (inj₂ (inj₁ ())))
moved-undirected (inj₂ (inj₂ (inj₂ (inj₁ ()))))
moved-undirected (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ ())))))
moved-undirected (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ ())))))

moved-not-first :
  Cp K₂ω (plusΩ G.zero (G.em (inj₂ (inj₁ tt)) G.top)) (move two e-two G.top) → ⊥
moved-not-first (inj₁ ())
moved-not-first (inj₂ (inj₁ ()))
moved-not-first (inj₂ (inj₂ (inj₁ ())))
moved-not-first (inj₂ (inj₂ (inj₂ (inj₁ ()))))
moved-not-first (inj₂ (inj₂ (inj₂ (inj₂ ()))))
```

## 4 分支槽位上的结点，目标层 0 (条件)

结点在第 `η` 支的位置 `r` 上，层号 `lev (read0 η) r`。它的链在那一层里，由 "目标在这个位置上的折叠" 在各支上的输出 `own` 推进，观察 `Φ⁰`。
给了 `own` 与它的合法、嵌套、头为正，这一行合法 (`YiRawFoldBase.ΨN` 的折叠行)。前提可满足 (`own-const`)，但不携带强度：`own` 应当是派发完全的折叠。
各支里的 `top` 有一行可写 ([YiOmFoldRel](YiOmFoldRel.lagda.md))；各支里已经放在别的支的槽位上的结点，与目标之间没有路径数据，这一种没有写出。

```agda
module BranchRow (η : R) (e : Gd zero raw1 η) (r : Pre (read0 η))
  (c : Low (read0 η) r) (t : RΩ)
  (g : (ζ : Low (read0 η) r) → .(GdL (read0 η) r c ζ) → RΩ)
  (l : Lgl K₂ω (G.lc (br η e r) c t g)) (nb : Nested K₂ω (G.lc (br η e r) c t g))
  (dt : Dom⁰ t) (dg : ∀ ζ (e′ : GdL (read0 η) r c ζ) → Dom⁰ (g ζ e′))
  (own : (ζ : Low (read0 η) r) → .(GdL (read0 η) r c ζ) → Raw (lev (read0 η) r))
  (own-lgl : ∀ ζ (e′ : GdL (read0 η) r c ζ) → Lgl (lev (read0 η) r) (own ζ e′))
  (own-ns : ∀ ζ (e′ : GdL (read0 η) r c ζ) → Nested (lev (read0 η) r) (own ζ e′))
  (own-pos : ∀ ζ .(e′ : GdL (read0 η) r c ζ) → Pos (lev (read0 η) r) (own ζ e′)) where

  N : NdL zero (read0 η) r
  N = nd c (proj₁ nb) (proj₁ (proj₂ nb))
    (Φ⁰ t dt (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
    (λ ζ e′ → Φ⁰ (g ζ e′) (dg ζ e′) (proj₂ (proj₂ (proj₂ (proj₂ l))) ζ e′)
      (proj₂ (proj₂ (proj₂ nb)) ζ e′))
    own own-lgl own-ns own-pos

  branch-row : R
  branch-row = ΨN zero (read0 η) (rplain η) r fold N

  branch-row-legal : Lgl zero branch-row
  branch-row-legal = ΨN-legal zero (read0 η) (rplain η) r fold N
    (record
      { seed = seedL (read0 η) r c (proj₁ nb) (proj₁ (proj₂ nb))
      ; tg = λ ζ e′ → Φ⁰-cp (g ζ e′) dt (dg ζ e′)
          (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb)))
          (proj₂ (proj₂ (proj₂ (proj₂ l))) ζ e′) (proj₂ (proj₂ (proj₂ nb)) ζ e′)
          (proj₁ l ζ e′)
      ; dir = λ ζ e′ ζ′ e″ q → Φ⁰-cp (g ζ′ e″) (dg ζ e′) (dg ζ′ e″)
          (proj₂ (proj₂ (proj₂ (proj₂ l))) ζ e′) (proj₂ (proj₂ (proj₂ nb)) ζ e′)
          (proj₂ (proj₂ (proj₂ (proj₂ l))) ζ′ e″) (proj₂ (proj₂ (proj₂ nb)) ζ′ e″)
          (proj₁ (proj₂ l) ζ e′ ζ′ e″ q)
      ; lt = Φ⁰-legal t dt (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb)))
      ; lg = λ ζ e′ → Φ⁰-legal (g ζ e′) (dg ζ e′)
          (proj₂ (proj₂ (proj₂ (proj₂ l))) ζ e′) (proj₂ (proj₂ (proj₂ nb)) ζ e′)
      ; lkʳ = own-lgl
      ; nkʳ = own-ns })

-- 前提可满足: 常值的 own. 它不是折叠.
module OwnConst (η : R) (r : Pre (read0 η)) where
  own-const : ∀ {A : Set} {B : A → Set} (ζ : A) → .(B ζ) → Raw (lev (read0 η) r)
  own-const ζ e′ = cO (lev (read0 η) r)

  own-const-lgl : Lgl (lev (read0 η) r) (cO (lev (read0 η) r))
  own-const-lgl = cO-Lgl (lev (read0 η) r)

  own-const-ns : Nested (lev (read0 η) r) (cO (lev (read0 η) r))
  own-const-ns = cO-Nested (lev (read0 η) r)

  own-const-pos : Pos (lev (read0 η) r) (cO (lev (read0 η) r))
  own-const-pos = cO-pos (lev (read0 η) r)
```
