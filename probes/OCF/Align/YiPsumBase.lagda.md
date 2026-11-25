# YiPsum 底座：派发沿路径的限制、派发的一致、位置的结构规范化

**档位：定义与编译定理，没有折叠。** `restrictX` 把外部派发沿字面第一位置路径限制下来；`CohX` 说极限处后一支的派发限制回来等于前一支的 (是函数的相等)。
`csQ K L v r` 是 `v` 在 `r` 的规范位置上的值：极限处先在本支里规范化，再看结果是不是从前一支沿这一步的路径搬上来的，是就退到前一支。对层号与分支编号结构递归，没有搬运，没有搜索。
`pre` 把派发先过一遍 `csQ`。不否定什么。一致性的一般定理在 [YiPsumZp](YiPsumZp.lagda.md)，折叠在 [YiPsumFold](YiPsumFold.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiPsumBase where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import OCF.Align.RR5IrrCore
open import OCF.Align.YiIrrIf using (CP; self; suc; lim; fst; Legal)
open import OCF.Align.YiLvIf using (Plain; lev)
open import OCF.Align.YiLvFoldBase using (Way; keep; fold)
open import OCF.Align.YiLvFoldFin
  using (IsKeep; fin; ω; ω-plain; ω-legal; fin-plain; fin-legal)
open import OCF.Align.YiLvNegCompare using (At)
open import OCF.Align.YiLvNegCanon using (ccompare; shape; belowˢ)
open import OCF.Align.YiRawIf using (dispatch; self; at)
open import OCF.Align.YiRawFoldBase
open import OCF.Align.YiRawFold using (own; ownT; Complete)
```

## 1 派发沿路径的限制与一致

`restrictX` 是 `inS`, `inL` 沿路径的复合，与 `plainR`, `restrictL` 同形；`restrictF` 是位置上的函数的同一个限制。
`CohX K L x`：`K` 的每个极限处，第 `n+1` 支的派发沿第 `n` 步限制下来等于第 `n` 支的；各支遗传。方程两边是位置上的函数。

```agda
inF : ∀ {m k c t g} .{w : Lgl k c} .{b : Nested k c} → Ext m (lc k c w b t g) → Ext m t
inF low = low
inF (mix v) = mix (λ r → v (inj₂ (inj₁ r)))

restrictX : ∀ {m a} b → CP a b → Ext m b → Ext m a
restrictX b self x = x
restrictX (suc b) (suc p) x = restrictX b p (inS x)
restrictX (lim f) (lim n p) x = restrictX (f n) p (inL x n)
restrictX (lc k c w b t g) (fst p) x = restrictX t p (inF x)

restrictF : ∀ {Q : LF → Set} {a} b → CP a b →
  ((s : Pre b) → Q (lev b s)) → (r : Pre a) → Q (lev a r)
restrictF b self v = v
restrictF {Q} (suc b) (suc p) v = restrictF {Q = Q} b p (λ s → v (inj₂ s))
restrictF {Q} (lim f) (lim n p) v = restrictF {Q = Q} (f n) p (λ s → v (n , s))
restrictF {Q} (lc k c w b t g) (fst p) v = restrictF {Q = Q} t p (λ s → v (inj₂ (inj₁ s)))

restrictX-mix : ∀ {m a} b (p : CP a b) (v : (s : Pre b) → Way m (lev b s)) →
  restrictX b p (mix v) ≡ mix (restrictF {Q = Way m} b p v)
restrictX-mix b self v = refl
restrictX-mix (suc b) (suc p) v = restrictX-mix b p (λ s → v (inj₂ s))
restrictX-mix (lim f) (lim n p) v = restrictX-mix (f n) p (λ s → v (n , s))
restrictX-mix (lc k c w b t g) (fst p) v = restrictX-mix t p (λ s → v (inj₂ (inj₁ s)))

CohX : ∀ {m} K → Legal K → Ext m K → Set
CohX zero L x = ⊤
CohX (suc k) L x = CohX k L (inS x)
CohX (lim f) L x =
  (∀ n → restrictX (f (suc n)) (proj₁ L n) (inL x (suc n)) ≡ inL x n) ×
  (∀ n → CohX (f n) (proj₂ L n) (inL x n))
CohX (lc k c w b t g) L x = ⊥

cohX-low : ∀ {m} K (pl : Plain K) (L : Legal K) → CohX {m} K L low
restrict-low : ∀ {m a} b (p : CP a b) → Plain b → restrictX {m} b p low ≡ low
restrict-low b self pl = refl
restrict-low (suc b) (suc p) pl = restrict-low b p pl
restrict-low (lim f) (lim n p) pl = restrict-low (f n) p (pl n)
cohX-low zero pl L = tt
cohX-low (suc k) pl L = cohX-low k pl L
cohX-low (lim f) pl L =
  (λ n → restrict-low (f (suc n)) (proj₁ L n) (pl (suc n))) , (λ n → cohX-low (f n) (pl n) (proj₂ L n))
```

## 2 位置的结构规范化

`unshiftQ b p down s stay`：位置 `s` 若在路径 `p : CP a b` 搬上来的像里，交出 `down` 在原像上的值，否则交出 `stay`。只认路径在极限处取第 0 支的像。
`upQ f st n v s`：`v` 在 `(n , s)` 的规范位置上的值，逐步退到最小的分支。`csQ`：先进到 `r` 所在的那一支，在里面规范化，再做 `upQ`。
值的类型 `Q (lev …)` 沿这些递归定义性不变，所以不出现层号的方程与搬运。

```agda
unshiftQ : ∀ {Q : LF → Set} {a} b (p : CP a b) → ((s₀ : Pre a) → Q (lev a s₀)) →
  (s : Pre b) → Q (lev b s) → Q (lev b s)
unshiftQ b self down s stay = down s
unshiftQ (suc b) (suc p) down (inj₁ x) stay = stay
unshiftQ {Q} (suc b) (suc p) down (inj₂ s) stay = unshiftQ {Q = Q} b p down s stay
unshiftQ {Q} (lim g) (lim zero p) down (zero , s) stay = unshiftQ {Q = Q} (g zero) p down s stay
unshiftQ (lim g) (lim zero p) down (suc i , s) stay = stay
unshiftQ (lim g) (lim (suc m) p) down s stay = stay
unshiftQ (lc k c w b t g) (fst p) down s stay = stay

upQ : ∀ {Q : LF → Set} (f : ℕ → LF) (st : ∀ n → CP (f n) (f (suc n))) n →
  ((s : Pre (lim f)) → Q (lev (lim f) s)) → (s : Pre (f n)) → Q (lev (f n) s)
upQ f st zero v s = v (zero , s)
upQ {Q} f st (suc n) v s =
  unshiftQ {Q = Q} (f (suc n)) (st n) (upQ {Q = Q} f st n v) s (v (suc n , s))

csQ : ∀ {Q : LF → Set} K → Legal K → ((s : Pre K) → Q (lev K s)) → (r : Pre K) → Q (lev K r)
csQ (suc k) L v (inj₁ x) = v (inj₁ x)
csQ {Q} (suc k) L v (inj₂ r) = csQ {Q = Q} k L (λ s → v (inj₂ s)) r
csQ {Q} (lim f) L v (n , r) = csQ {Q = Q} (f n) (proj₂ L n) (upQ {Q = Q} f (proj₁ L) n v) r
csQ (lc k c w b t g) L v r = v r

pre : ∀ {m} K → Legal K → Ext m K → Ext m K
pre K L low = low
pre {m} K L (mix v) = mix (csQ {Q = Way m} K L v)

-- pre 与后继处的限制可交换.
pre-inS : ∀ {m} k L (x : Ext m (suc k)) → inS (pre (suc k) L x) ≡ pre k L (inS x)
pre-inS k L low = refl
pre-inS k L (mix v) = refl
```

`csQ` 交出的总是 `v` 在某个位置上的值，所以 `v` 处处有的性质它也有。派发完全与不多保留由此不丢。

```agda
module _ (Q : LF → Set) (Pr : ∀ j → Q j → Set) where

  unshiftQ-ind : ∀ {a} b (p : CP a b) (down : (s₀ : Pre a) → Q (lev a s₀)) →
    (∀ s₀ → Pr (lev a s₀) (down s₀)) →
    ∀ s stay → Pr (lev b s) stay → Pr (lev b s) (unshiftQ {Q = Q} b p down s stay)
  unshiftQ-ind b self down hd s stay hs = hd s
  unshiftQ-ind (suc b) (suc p) down hd (inj₁ x) stay hs = hs
  unshiftQ-ind (suc b) (suc p) down hd (inj₂ s) stay hs = unshiftQ-ind b p down hd s stay hs
  unshiftQ-ind (lim g) (lim zero p) down hd (zero , s) stay hs =
    unshiftQ-ind (g zero) p down hd s stay hs
  unshiftQ-ind (lim g) (lim zero p) down hd (suc i , s) stay hs = hs
  unshiftQ-ind (lim g) (lim (suc m) p) down hd s stay hs = hs
  unshiftQ-ind (lc k c w b t g) (fst p) down hd s stay hs = hs

  upQ-ind : ∀ (f : ℕ → LF) st n (v : (s : Pre (lim f)) → Q (lev (lim f) s)) →
    (∀ s → Pr (lev (lim f) s) (v s)) → ∀ s → Pr (lev (f n) s) (upQ {Q = Q} f st n v s)
  upQ-ind f st zero v h s = h (zero , s)
  upQ-ind f st (suc n) v h s =
    unshiftQ-ind (f (suc n)) (st n) (upQ {Q = Q} f st n v) (upQ-ind f st n v h) s
      (v (suc n , s)) (h (suc n , s))

  csQ-ind : ∀ K L (v : (s : Pre K) → Q (lev K s)) → (∀ s → Pr (lev K s) (v s)) →
    ∀ r → Pr (lev K r) (csQ {Q = Q} K L v r)
  csQ-ind (suc k) L v h (inj₁ x) = h (inj₁ x)
  csQ-ind (suc k) L v h (inj₂ r) = csQ-ind k L (λ s → v (inj₂ s)) (λ s → h (inj₂ s)) r
  csQ-ind (lim f) L v h (n , r) =
    csQ-ind (f n) (proj₂ L n) (upQ {Q = Q} f (proj₁ L) n v) (upQ-ind f (proj₁ L) n v h) r
  csQ-ind (lc k c w b t g) L v h r = h r

pre-complete : ∀ {m} K L (x : Ext m K) → Complete x → Complete (pre K L x)
pre-complete K L low h r a = h r a
pre-complete {m} K L (mix v) h = csQ-ind (Way m) (λ j y → At m j → IsKeep y) K L v h

pre-sound : ∀ {m} K L (v : (s : Pre K) → Way m (lev K s)) →
  (∀ s → IsKeep (v s) → At m (lev K s)) →
  ∀ r → IsKeep (wayOf (pre K L (mix v)) r) → At m (lev K r)
pre-sound {m} K L v h = csQ-ind (Way m) (λ j y → IsKeep y → At m j) K L v h
```

## 3 结点自己那一层的派发：两种方案

`orig` 是 [YiRawFold](YiRawFold.lagda.md) 的 `own`, `ownT`。`canonˢ` 是它们先过 `pre`；`ownT` 仍取根位置的 `own` 限制到孩子。

```agda
record Scheme : Set where
  field
    ownˢ : ∀ k → Plain k → Legal k → (r : Pre k) → Ext (lev k r) k
    ownTˢ : ∀ k → Plain k → Legal k → Ext k k

orig : Scheme
orig = record { ownˢ = own ; ownTˢ = ownT }

ownᶜ : ∀ k → Plain k → Legal k → (r : Pre k) → Ext (lev k r) k
ownᶜ k pl L r = pre k L (own k pl L r)

ownTᶜ : ∀ k → Plain k → Legal k → Ext k k
ownTᶜ k pl L = inS (ownᶜ (suc k) pl L (inj₁ tt))

canonˢ : Scheme
canonˢ = record { ownˢ = ownᶜ ; ownTˢ = ownTᶜ }
```

## 4 在 ω 上的计算核对

`ω = lim fin` 的第 `n` 步是字面的 `suc self`，所以过了 `pre` 的派发在位置 `(n+1 , inj₂ q)` 与 `(n , q)` 上定义性相同 (`pre-ω-step`)。
槽位：第 3 支里根下一格 (层号 1) 落在 `(2 , 根)`，与 `ccompare` 的规范槽位、`YiRawFoldInst.test-slot-ω` 同一格。

```agda
pre-ω-step : ∀ {m} (v : (s : Pre ω) → Way m (lev ω s)) n →
  inS (inL (pre ω ω-legal (mix v)) (suc n)) ≡ inL (pre ω ω-legal (mix v)) n
pre-ω-step v n = refl

slotOf : ∀ {m k} → Way m k → Pre m → Pre m
slotOf (keep s e) d = s
slotOf fold d = d

test-pre-slot : slotOf (wayOf (pre ω ω-legal (mix (dispatch ω ω-plain ω-legal self)))
  (3 , inj₂ (inj₁ tt))) (1 , inj₁ tt) ≡ (2 , inj₁ tt)
test-pre-slot = refl

test-canon-slot : shape (ccompare (suc ω) ω-plain ω-legal (inj₁ tt) (inj₂ (3 , inj₂ (inj₁ tt)))) ≡
  belowˢ (2 , inj₁ tt)
test-canon-slot = refl
```

接口的 `self` 派发 (槽位取位置自己) 在 ω 上不一致：第 2 支限制到第 1 支，根位置上的槽位是 `(2 , 根下一格)`，不是 `(1 , 根)`。

```agda
branchᵂ : Pre ω → ℕ
branchᵂ (n , r) = n

self-not-cohX : CohX ω ω-legal (mix (dispatch ω ω-plain ω-legal self)) → ⊥
self-not-cohX (h , _) = two≢one (cong′ (h 1))
  where
  two≢one : 2 ≡ 1 → ⊥
  two≢one ()
  cong′ : inS (inL (mix (dispatch ω ω-plain ω-legal self)) 2) ≡
          inL (mix (dispatch ω ω-plain ω-legal self)) 1 → 2 ≡ 1
  cong′ e = subst (λ x → branchᵂ (slotOf (wayOf x (inj₁ tt)) (1 , inj₁ tt)) ≡ 1) (sym e) refl
```
