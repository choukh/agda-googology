# YiRawNeg 第 2 项：`Raw K` 之内的搬运，与它从 `L` 读到的路径

**判决：编译构造与编译定理 (正面为主，一条边界)。** 沿第一位置路径把 `Raw a` 的树提升到 `Raw b` 的函数 `wrap` 写成了 (逐步包一层 `em`)，保持第一位置、合法性、嵌套证据与读回，对一切层号。
`RawFold` 有做了跨支搬运的模型 `moved` (树在小编号支时提升树，在大编号支时搬目标位置)，四条律都过；它仍是便宜的模型，不是折叠。
边界：提升依赖路径。`Kᶜ` 的两份证书给出的提升互不为第一位置 (`lift-apart`)；任何带 `CrossRow` 与 `BranchRow` 两行的 `RawFold`，换 `L` 后的输出互不为第一位置 (`Rows.reads-L`)。
不否定同一个 `L` 之内的 `position`；否定的是 "换 `L` 输出相等或可比" 这一类要求。接口 [YiRawIf](YiRawIf.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRawNegLift where

open import Data.Nat.Base using (ℕ; zero; suc; _<_)
open import Data.Nat.Properties using (<-cmp; <⇒<′)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>) renaming (Tri to Triℕ)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
open import OCF.Align.YiLvIf
open import OCF.Align.YiLvNegCompare using (At)
open import OCF.Align.YiLvNegCert using (Kᶜ; Kᶜ-plain; Kᶜ-legal; hiᶜ; Bᶜ; zero≢one)
open import OCF.Align.YiRawIf
open import OCF.Align.YiRawNegModel
  using (out; out-dn; out-lgl; out-kept; out-lim; topv; topv-lgl)
```

## 1 提升

路径的每一步对应一种 `em`：后继层号的唯一一支，极限层号的第 `n` 支，Ω 结点层号的第一支。

```agda
wrap : ∀ {a} b → CP a b → Raw a → Raw b
wrap b self T = T
wrap (suc b) (suc p) T = G.em tt (wrap b p T)
wrap (lim f) (lim n p) T = G.em n (wrap (f n) p T)
wrap (lc k c w b t g) (fst p) T = G.em (inj₂ (inj₁ tt)) (wrap t p T)

wrap-dn : ∀ {a} b (p : CP a b) {x y : Raw a} → Dn a x y → Dn b (wrap b p x) (wrap b p y)
wrap-dn b self d = d
wrap-dn (suc b) (suc p) d = wrap-dn b p d
wrap-dn (lim f) (lim n p) d = refl , wrap-dn (f n) p d
wrap-dn (lc k c w b t g) (fst p) d = wrap-dn t p d

wrap-cp : ∀ {a} b (p : CP a b) {x y : Raw a} → Cp a x y → Cp b (wrap b p x) (wrap b p y)
wrap-cp b p (inj₁ refl) = inj₁ refl
wrap-cp b p (inj₂ d) = inj₂ (wrap-dn b p d)

wrap-lgl : ∀ {a} b (p : CP a b) x → Lgl a x → Lgl b (wrap b p x)
wrap-lgl b self x l = l
wrap-lgl (suc b) (suc p) x l = wrap-lgl b p x l
wrap-lgl (lim f) (lim n p) x l = wrap-lgl (f n) p x l
wrap-lgl (lc k c w b t g) (fst p) x l = wrap-lgl t p x l

wrap-nested : ∀ {a} b (p : CP a b) x → Nested a x → Nested b (wrap b p x)
wrap-nested b self x nb = nb
wrap-nested (suc b) (suc p) x nb = wrap-nested b p x nb
wrap-nested (lim f) (lim n p) x nb = wrap-nested (f n) p x nb
wrap-nested (lc k c w b t g) (fst p) x nb = wrap-nested t p x nb

-- 读回不变: 提升后的树读成同一个层号, 与路径无关.
wrap-read : ∀ {a} b (p : CP a b) x (nb : Nested a x) →
  up b (wrap b p x) (wrap-nested b p x nb) ≡ up a x nb
wrap-read b self x nb = refl
wrap-read (suc b) (suc p) x nb = wrap-read b p x nb
wrap-read (lim f) (lim n p) x nb = wrap-read (f n) p x nb
wrap-read (lc k c w b t g) (fst p) x nb = wrap-read t p x nb

wrap-read-free : ∀ {a} b (p p′ : CP a b) x (nb : Nested a x) →
  up b (wrap b p x) (wrap-nested b p x nb) ≡ up b (wrap b p′ x) (wrap-nested b p′ x nb)
wrap-read-free b p p′ x nb = trans (wrap-read b p x nb) (sym (wrap-read b p′ x nb))
```

## 2 提升依赖路径

`Kᶜ` 的第 0 支到第 1 支的路径取自证书；两份证书在第 1 支里的极限处选了不同的分支。极限层号里不同分支的 `em` 互不为第一位置。

```agda
em-index : ∀ {f : ℕ → LF} → Raw (lim f) → ℕ
em-index (G.em n T) = n
em-index _ = zero

branch-apart : ∀ {f : ℕ → LF} n m (X : Raw (f n)) (Y : Raw (f m)) → (n ≡ m → ⊥) →
  Cp (lim f) (G.em n X) (G.em m Y) → ⊥
branch-apart n m X Y ne (inj₁ e) = ne (cong em-index e)
branch-apart n m X Y ne (inj₂ (q , d)) = ne q

liftᶜ : ℕ → Raw (suc zero) → Raw (suc Bᶜ)
liftᶜ j T = wrap (suc Bᶜ) (proj₁ (Kᶜ-legal j) 0) T

lift-form : ∀ j T → liftᶜ j T ≡ G.em tt (G.em j T)
lift-form j T = refl

lift-apart : ∀ T → Cp (suc Bᶜ) (liftᶜ 0 T) (liftᶜ 1 T) ⊎ Cp (suc Bᶜ) (liftᶜ 1 T) (liftᶜ 0 T) → ⊥
lift-apart T (inj₁ (inj₁ e)) = zero≢one (cong em-index (cong under e))
  where under : Raw (suc Bᶜ) → Raw Bᶜ
        under (G.em _ X) = X
        under _ = G.zero
lift-apart T (inj₁ (inj₂ d)) = branch-apart 0 1 T T zero≢one (inj₂ d)
lift-apart T (inj₂ (inj₁ e)) = zero≢one (sym (cong em-index (cong under e)))
  where under : Raw (suc Bᶜ) → Raw Bᶜ
        under (G.em _ X) = X
        under _ = G.zero
lift-apart T (inj₂ (inj₂ d)) = branch-apart 1 0 T T (λ e → zero≢one (sym e)) (inj₂ d)
```

## 3 做了搬运的模型

与 [YiRawNegModel](YiRawNegModel.lagda.md) 的便宜模型相同，只改 `em` 与 `top` 在目标 `at q` 处的值：后继层号处目标在根上时交出子树自己 (便宜的取法，真的折叠在这里还要按目标 `self` 折一遍)，否则进到低一层；
极限层号处目标在第 `m` 支、树在第 `n` 支：`n < m` 提升树，`n ≡ m` 直接递归，`m < n` 把目标位置搬到第 `n` 支并沿层号的相等搬回输出。派发用接口的 `dispatch`。

```agda
subst-cp : ∀ {i j} (e : i ≡ j) {x y : Raw i} → Cp i x y → Cp j (subst Raw e x) (subst Raw e y)
subst-cp refl c = c

subst-lgl : ∀ {i j} (e : i ≡ j) {x : Raw i} → Lgl i x → Lgl j (subst Raw e x)
subst-lgl refl l = l

topm : ∀ K (τ : Tgt K) → Raw (tlev K τ)
topm K self = G.zero
topm K base = topv K base
topm zero (at ())
topm (suc k) (at (inj₁ _)) = G.top
topm (suc k) (at (inj₂ q)) = topm k (at q)
topm (lim f) (at (n , q)) = G.zero
topm (lc k c w b t g) (at q) = G.zero

topm-lgl : ∀ K → Plain K → Legal K → (τ : Tgt K) → Lgl (tlev K τ) (topm K τ)
topm-lgl K pl L self = tt
topm-lgl K pl L base = topv-lgl K pl L base
topm-lgl zero pl L (at ())
topm-lgl (suc k) pl L (at (inj₁ _)) = tt
topm-lgl (suc k) pl L (at (inj₂ q)) = topm-lgl k pl L (at q)
topm-lgl (lim f) pl L (at (n , q)) = tt
topm-lgl (lc k c w b t g) pl L (at q) = tt

Φᵐ : ∀ K → Plain K → Legal K → (τ : Tgt K) → Raw K → Raw (tlev K τ)
emv : ∀ K → Plain K → Legal K → (τ : Tgt K) (i : Kid K) → KidR K i → Raw (tlev K τ)
move : ∀ (f : ℕ → LF) (pl : ∀ n → Plain (f n)) (st : ∀ n → CP (f n) (f (suc n)))
  (lg : ∀ n → Legal (f n)) m (q : Pre (f m)) n → Raw (f n) →
  Triℕ (n < m) (n ≡ m) (m < n) → Raw (lev (f m) q)

Φᵐ K pl L τ G.zero = G.zero
Φᵐ K pl L τ (G.suc a) = G.suc (Φᵐ K pl L τ a)
Φᵐ K pl L τ (G.lim f) = G.lim (λ n → Φᵐ K pl L τ (f n))
Φᵐ K pl L τ (G.lc r c t g) = out (dispatch K pl L τ r) (Φᵐ K pl L τ t)
Φᵐ K pl L τ (G.em i T) = emv K pl L τ i T
Φᵐ K pl L τ G.top = topm K τ

emv K pl L self i T = G.zero
emv zero pl L base () T
emv (suc k) pl L base i T = Φᵐ k pl L base T
emv (lim f) pl (st , lg) base n T = Φᵐ (f n) (pl n) (lg n) base T
emv (lc k c w b t g) () L base i T
emv zero pl L (at ()) i T
emv (suc k) pl L (at (inj₁ _)) i T = T
emv (suc k) pl L (at (inj₂ q)) i T = Φᵐ k pl L (at q) T
emv (lim f) pl (st , lg) (at (m , q)) n T = move f pl st lg m q n T (<-cmp n m)
emv (lc k c w b t g) () L (at q) i T

move f pl st lg m q n T (tri< lt _ _) =
  Φᵐ (f m) (pl m) (lg m) (at q) (wrap (f m) (steps st (<⇒<′ lt)) T)
move f pl st lg m q .m T (tri≈ _ refl _) = Φᵐ (f m) (pl m) (lg m) (at q) T
move f pl st lg m q n T (tri> _ _ gt) =
  subst Raw (proj₂ (shift (steps st (<⇒<′ gt)) q))
    (Φᵐ (f n) (pl n) (lg n) (at (proj₁ (shift (steps st (<⇒<′ gt)) q))) T)

pos : ∀ K pl L τ ξ ξ′ → Cp K ξ ξ′ → Cp (tlev K τ) (Φᵐ K pl L τ ξ) (Φᵐ K pl L τ ξ′)
dn : ∀ K pl L τ ξ ξ′ → Dn K ξ ξ′ → Cp (tlev K τ) (Φᵐ K pl L τ ξ) (Φᵐ K pl L τ ξ′)
dn-em : ∀ K pl L τ i′ i a T → DnK K i′ i a T →
  Cp (tlev K τ) (emv K pl L τ i′ a) (emv K pl L τ i T)
move-dn : ∀ f pl st lg m q n (a T : Raw (f n)) (c : Triℕ (n < m) (n ≡ m) (m < n)) →
  Dn (f n) a T → Cp (lev (f m) q) (move f pl st lg m q n a c) (move f pl st lg m q n T c)
em-top : ∀ k pl L (τ : Tgt (suc k)) a → Cp k a G.top →
  Cp (tlev (suc k) τ) (emv (suc k) pl L τ tt a) (topm (suc k) τ)

pos K pl L τ ξ .ξ (inj₁ refl) = inj₁ refl
pos K pl L τ ξ ξ′ (inj₂ p) = dn K pl L τ ξ ξ′ p

dn-em K pl L self i′ i a T p = inj₁ refl
dn-em zero pl L base () i a T p
dn-em (suc k) pl L base i′ i a T p = dn k pl L base a T p
dn-em (lim f) pl (st , lg) base n .n a T (refl , p) = dn (f n) (pl n) (lg n) base a T p
dn-em (lc k c w b t g) () L base i′ i a T p
dn-em zero pl L (at ()) i′ i a T p
dn-em (suc k) pl L (at (inj₁ _)) i′ i a T p = inj₂ p
dn-em (suc k) pl L (at (inj₂ q)) i′ i a T p = dn k pl L (at q) a T p
dn-em (lim f) pl (st , lg) (at (m , q)) n .n a T (refl , p) =
  move-dn f pl st lg m q n a T (<-cmp n m) p
dn-em (lc k c w b t g) () L (at q) i′ i a T p

move-dn f pl st lg m q n a T (tri< lt _ _) p =
  dn (f m) (pl m) (lg m) (at q) _ _ (wrap-dn (f m) (steps st (<⇒<′ lt)) p)
move-dn f pl st lg m q .m a T (tri≈ _ refl _) p = dn (f m) (pl m) (lg m) (at q) a T p
move-dn f pl st lg m q n a T (tri> _ _ gt) p =
  subst-cp (proj₂ (shift (steps st (<⇒<′ gt)) q))
    (dn (f n) (pl n) (lg n) (at (proj₁ (shift (steps st (<⇒<′ gt)) q))) a T p)

em-top k pl L self a p = inj₁ refl
em-top k pl L base a p = inj₂ (pos k pl L base a G.top p)
em-top k pl L (at (inj₁ _)) a p = p
em-top k pl L (at (inj₂ q)) a p = pos k pl L (at q) a G.top p

dn K pl L τ ξ G.zero ()
dn K pl L τ ξ (G.suc d) p = inj₂ (pos K pl L τ ξ d p)
dn K pl L τ ξ (G.lim f) (n , p) = inj₂ (n , pos K pl L τ ξ (f n) p)
dn K pl L τ ξ (G.lc r c t g) p = inj₂ (out-dn (dispatch K pl L τ r) (pos K pl L τ ξ t p))
dn K pl L τ (G.em i′ a) (G.em i T) p = dn-em K pl L τ i′ i a T p
dn K pl L τ G.zero (G.em i T) ()
dn K pl L τ (G.suc _) (G.em i T) ()
dn K pl L τ (G.lim _) (G.em i T) ()
dn K pl L τ (G.lc _ _ _ _) (G.em i T) ()
dn K pl L τ G.top (G.em i T) ()
dn zero pl L τ ξ G.top ()
dn (suc k) pl L τ (G.em _ a) G.top p = em-top k pl L τ a p
dn (suc k) pl L τ G.zero G.top ()
dn (suc k) pl L τ (G.suc _) G.top ()
dn (suc k) pl L τ (G.lim _) G.top ()
dn (suc k) pl L τ (G.lc _ _ _ _) G.top ()
dn (suc k) pl L τ G.top G.top ()
dn (lim f) pl L τ ξ G.top ()
dn (lc k c w b t g) () L τ ξ G.top p

lgl : ∀ K pl L τ ξ → Lgl K ξ → Lgl (tlev K τ) (Φᵐ K pl L τ ξ)
lgl-em : ∀ K pl L τ i T → LglK K i T → Lgl (tlev K τ) (emv K pl L τ i T)
move-lgl : ∀ f pl st lg m q n (T : Raw (f n)) (c : Triℕ (n < m) (n ≡ m) (m < n)) →
  Lgl (f n) T → Lgl (lev (f m) q) (move f pl st lg m q n T c)

lgl-em K pl L self i T l = tt
lgl-em zero pl L base () T l
lgl-em (suc k) pl L base i T l = lgl k pl L base T l
lgl-em (lim f) pl (st , lg) base n T l = lgl (f n) (pl n) (lg n) base T l
lgl-em (lc k c w b t g) () L base i T l
lgl-em zero pl L (at ()) i T l
lgl-em (suc k) pl L (at (inj₁ _)) i T l = l
lgl-em (suc k) pl L (at (inj₂ q)) i T l = lgl k pl L (at q) T l
lgl-em (lim f) pl (st , lg) (at (m , q)) n T l = move-lgl f pl st lg m q n T (<-cmp n m) l
lgl-em (lc k c w b t g) () L (at q) i T l

move-lgl f pl st lg m q n T (tri< lt _ _) l =
  lgl (f m) (pl m) (lg m) (at q) _ (wrap-lgl (f m) (steps st (<⇒<′ lt)) T l)
move-lgl f pl st lg m q .m T (tri≈ _ refl _) l = lgl (f m) (pl m) (lg m) (at q) T l
move-lgl f pl st lg m q n T (tri> _ _ gt) l =
  subst-lgl (proj₂ (shift (steps st (<⇒<′ gt)) q))
    (lgl (f n) (pl n) (lg n) (at (proj₁ (shift (steps st (<⇒<′ gt)) q))) T l)

lgl K pl L τ G.zero l = tt
lgl K pl L τ (G.suc a) l = lgl K pl L τ a l
lgl K pl L τ (G.lim f) (st , lf) =
  (λ n → pos K pl L τ (f n) (f (suc n)) (st n)) , (λ n → lgl K pl L τ (f n) (lf n))
lgl K pl L τ (G.lc r c t g) (tg , dir , irr , lt , lg) =
  out-lgl (dispatch K pl L τ r) (lgl K pl L τ t lt)
lgl K pl L τ (G.em i T) l = lgl-em K pl L τ i T l
lgl K pl L τ G.top l = topm-lgl K pl L τ

moved : RawFold
moved = record
  { Φ = λ K pl L τ ξ l nb → Φᵐ K pl L τ ξ
  ; keep-law = λ K pl L τ r c t g l nb a →
      out-kept (dispatch K pl L τ r) (Φᵐ K pl L τ t) (dispatch-complete K pl L τ r a)
  ; fold-law = λ K pl L τ r c t g l nb no → out-lim (dispatch K pl L τ r) (Φᵐ K pl L τ t) no
  ; position = λ K pl L τ ξ ξ′ l nb l′ nb′ p → pos K pl L τ ξ ξ′ p
  ; legal = λ K pl L τ ξ l nb → lgl K pl L τ ξ l
  }
```

## 4 两行逼出对 `L` 的依赖

`CrossRow`：极限层号处目标在第 1 支、树在第 0 支时，先沿 `L` 的第 0 步提升再折。
`BranchRow`：目标在 `suc (lim g)` 的根上 (目标层是 `lim g`)，树是第 `j` 支里的 `em`，输出仍是第 `j` 支里的 `em`；支里是什么不限定，
所以 "原样交出" 与 "在支里继续折" 两种写法都满足它。带这两行的 `RawFold` 在 `Kᶜ` 上：树 `em 0 zero`，目标在第 1 支的根，证书 `Kᶜ-legal j` 给出第 `j` 支里的 `em`。

```agda
module Rows (F : RawFold) where
  open RawFold F

  CrossRow : Set
  CrossRow = ∀ f (pl : Plain (lim f)) (L : Legal (lim f)) (q : Pre (f 1)) (T : Raw (f 0))
    (l : Lgl (f 0) T) (nb : Nested (f 0) T) →
    Φ (lim f) pl L (at (1 , q)) (G.em 0 T) l nb ≡
    Φ (f 1) (pl 1) (proj₂ L 1) (at q) (wrap (f 1) (proj₁ L 0) T)
      (wrap-lgl (f 1) (proj₁ L 0) T l) (wrap-nested (f 1) (proj₁ L 0) T nb)

  BranchRow : Set
  BranchRow = ∀ (g : ℕ → LF) (pl : Plain (lim g)) (L : Legal (lim g)) j (T : Raw (g j))
    (l : Lgl (g j) T) (nb : Nested (g j) T) →
    Σ (Raw (g j)) λ Y →
      Φ (suc (lim g)) pl L (at (inj₁ tt)) (G.em tt (G.em j T)) l nb ≡ G.em j Y

  module _ (cross : CrossRow) (branch : BranchRow) where

    Out : ℕ → Raw Bᶜ
    Out j = Φ Kᶜ Kᶜ-plain (Kᶜ-legal j) (at hiᶜ) (G.em 0 G.zero) tt tt

    out-j : ∀ j → Σ (Raw (suc zero)) λ Y → Out j ≡ G.em j Y
    out-j j =
      proj₁ (branch _ (Kᶜ-plain 1) (proj₂ (Kᶜ-legal j) 1) j G.zero tt tt) ,
      trans (cross _ Kᶜ-plain (Kᶜ-legal j) (inj₁ tt) G.zero tt tt)
        (proj₂ (branch _ (Kᶜ-plain 1) (proj₂ (Kᶜ-legal j) 1) j G.zero tt tt))

    reads-L : Cp Bᶜ (Out 0) (Out 1) ⊎ Cp Bᶜ (Out 1) (Out 0) → ⊥
    reads-L (inj₁ c) = branch-apart 0 1 _ _ zero≢one
      (subst₂ (Cp Bᶜ) (proj₂ (out-j 0)) (proj₂ (out-j 1)) c)
    reads-L (inj₂ c) = branch-apart 1 0 _ _ (λ e → zero≢one (sym e))
      (subst₂ (Cp Bᶜ) (proj₂ (out-j 1)) (proj₂ (out-j 0)) c)

-- 前提的实例: 做了搬运的模型满足两行.
moved-cross : Rows.CrossRow moved
moved-cross f pl L q T l nb = refl

moved-branch : Rows.BranchRow moved
moved-branch g pl L j T l nb = T , refl

moved-reads-L :
  Cp Bᶜ (Φᵐ Kᶜ Kᶜ-plain (Kᶜ-legal 0) (at hiᶜ) (G.em 0 G.zero))
        (Φᵐ Kᶜ Kᶜ-plain (Kᶜ-legal 1) (at hiᶜ) (G.em 0 G.zero)) ⊎
  Cp Bᶜ (Φᵐ Kᶜ Kᶜ-plain (Kᶜ-legal 1) (at hiᶜ) (G.em 0 G.zero))
        (Φᵐ Kᶜ Kᶜ-plain (Kᶜ-legal 0) (at hiᶜ) (G.em 0 G.zero)) → ⊥
moved-reads-L = Rows.reads-L moved moved-cross moved-branch
```

## 5 位置上的下界类型与该层的树

折叠一个位置 `r` 上的结点时，链在 `Low K r` 里走，而结点自己那一层的折叠交出 `Raw (lev K r)` 的值。两个类型对一般的 `K` 只是命题相等 (`YiLvIf.Low-lev`)。
这里按 `K` 与 `r` 递归给出往返，每个子句都是恒等；守卫随之往返。所以这一处不需要沿类型的相等搬运。

```agda
toRaw : ∀ K r → Low K r → Raw (lev K r)
toRaw (suc k) (inj₁ _) x = x
toRaw (suc k) (inj₂ r) x = toRaw k r x
toRaw (lim f) (n , r) x = toRaw (f n) r x
toRaw (lc k c w b t g) (inj₁ (inj₁ _)) x = x
toRaw (lc k c w b t g) (inj₁ (inj₂ r)) x = toRaw k r x
toRaw (lc k c w b t g) (inj₂ (inj₁ r)) x = toRaw t r x
toRaw (lc k c w b t g) (inj₂ (inj₂ (η , e , r))) x = toRaw (g η e) r x

fromRaw : ∀ K r → Raw (lev K r) → Low K r
fromRaw (suc k) (inj₁ _) x = x
fromRaw (suc k) (inj₂ r) x = fromRaw k r x
fromRaw (lim f) (n , r) x = fromRaw (f n) r x
fromRaw (lc k c w b t g) (inj₁ (inj₁ _)) x = x
fromRaw (lc k c w b t g) (inj₁ (inj₂ r)) x = fromRaw k r x
fromRaw (lc k c w b t g) (inj₂ (inj₁ r)) x = fromRaw t r x
fromRaw (lc k c w b t g) (inj₂ (inj₂ (η , e , r))) x = fromRaw (g η e) r x

from-to : ∀ K r x → fromRaw K r (toRaw K r x) ≡ x
from-to (suc k) (inj₁ _) x = refl
from-to (suc k) (inj₂ r) x = from-to k r x
from-to (lim f) (n , r) x = from-to (f n) r x
from-to (lc k c w b t g) (inj₁ (inj₁ _)) x = refl
from-to (lc k c w b t g) (inj₁ (inj₂ r)) x = from-to k r x
from-to (lc k c w b t g) (inj₂ (inj₁ r)) x = from-to t r x
from-to (lc k c w b t g) (inj₂ (inj₂ (η , e , r))) x = from-to (g η e) r x

to-from : ∀ K r y → toRaw K r (fromRaw K r y) ≡ y
to-from (suc k) (inj₁ _) y = refl
to-from (suc k) (inj₂ r) y = to-from k r y
to-from (lim f) (n , r) y = to-from (f n) r y
to-from (lc k c w b t g) (inj₁ (inj₁ _)) y = refl
to-from (lc k c w b t g) (inj₁ (inj₂ r)) y = to-from k r y
to-from (lc k c w b t g) (inj₂ (inj₁ r)) y = to-from t r y
to-from (lc k c w b t g) (inj₂ (inj₂ (η , e , r))) y = to-from (g η e) r y

gd-to : ∀ K r c η → GdL K r c η → Gd (lev K r) (toRaw K r c) (toRaw K r η)
gd-to (suc k) (inj₁ _) c η e = e
gd-to (suc k) (inj₂ r) c η e = gd-to k r c η e
gd-to (lim f) (n , r) c η e = gd-to (f n) r c η e
gd-to (lc k c₀ w b t g) (inj₁ (inj₁ _)) c η e = e
gd-to (lc k c₀ w b t g) (inj₁ (inj₂ r)) c η e = gd-to k r c η e
gd-to (lc k c₀ w b t g) (inj₂ (inj₁ r)) c η e = gd-to t r c η e
gd-to (lc k c₀ w b t g) (inj₂ (inj₂ (η₀ , e₀ , r))) c η e = gd-to (g η₀ e₀) r c η e

gd-from : ∀ K r c y → Gd (lev K r) (toRaw K r c) y → GdL K r c (fromRaw K r y)
gd-from (suc k) (inj₁ _) c y e = e
gd-from (suc k) (inj₂ r) c y e = gd-from k r c y e
gd-from (lim f) (n , r) c y e = gd-from (f n) r c y e
gd-from (lc k c₀ w b t g) (inj₁ (inj₁ _)) c y e = e
gd-from (lc k c₀ w b t g) (inj₁ (inj₂ r)) c y e = gd-from k r c y e
gd-from (lc k c₀ w b t g) (inj₂ (inj₁ r)) c y e = gd-from t r c y e
gd-from (lc k c₀ w b t g) (inj₂ (inj₂ (η₀ , e₀ , r))) c y e = gd-from (g η₀ e₀) r c y e
```

范围。§1 对一切层号成立，不要 `Plain` 与合法性。§5 同样。§3 的 `moved` 只说明搬运与四条律不冲突；它的结点处理仍是便宜的 (各支取常值)。
§4 的两份证书都是闭的并且各自一致 (`YiLvNegRestrict.κ-coh`)；`Kᶜ` 是不是 `tw 3` 的折叠走到的链点没有判定。
同一个 `L` 之内 `position` 不受影响 (`moved` 满足它)。要输出与 `L` 无关，除规范槽位外还要把提升的路径也取成规范的；这一步没有写 (判断：极限处取最小可行分支，要一条 "同一棵合法树的两个第一位置可比" 的判定)。
