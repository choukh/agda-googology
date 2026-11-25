# YiPsumZp：规范化之后的派发一致，不用函数外延

**判决 (编译定理)：层号 `K` 的证书一致 (`CohL`，`CohP` 的一半) 并且每个极限的每一步路径在极限处只取第 0 支 (`ZpL`) 时，任何派发过了 `pre` 以后在 `K` 上一致 (`preCoh`)。
`K` 与路径都是变量，没有 `Funext`，没有 K：对路径归纳，把 "规范化之后问的那个函数" 一起推广，每一步是定义性的 (`cs-restrict`, `unshift-restrict`)。**
范围：`ZpL` 之外的层号 (某一步在极限处取第 `n ≥ 1` 支) 没有证也没有否定。实例与闭项在 [YiPsumInst](YiPsumInst.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiPsumZp where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import OCF.Align.RR5IrrCore
open import OCF.Align.YiIrrIf using (CP; self; suc; lim; fst; Legal)
open import OCF.Align.YiLvIf using (Plain; lev)
open import OCF.Align.YiLvFoldBase using (Way)
open import OCF.Align.YiLvNegRestrict using (restrictL)
open import OCF.Align.YiRawFoldBase
open import OCF.Align.YiRawFoldUp using (Zp)
open import OCF.Align.YiPsumBase
```

## 1 范围与陈述

`ZpL`：极限的每一步是 `Zp` 的，各支遗传。`CohL`：极限处后一支的 `Legal` 沿这一步限制下来等于前一支的。`CohF` 是 `CohX` 写在位置上的函数上。

```agda
ZpL : ∀ K → Legal K → Set
ZpL zero L = ⊤
ZpL (suc k) L = ZpL k L
ZpL (lim f) L = (∀ n → Zp (proj₁ L n)) × (∀ n → ZpL (f n) (proj₂ L n))
ZpL (lc k c w b t g) L = ⊥

CohL : ∀ K → Legal K → Set
CohL zero L = ⊤
CohL (suc k) L = CohL k L
CohL (lim f) L =
  (∀ n → restrictL (f (suc n)) (proj₁ L n) (proj₂ L (suc n)) ≡ proj₂ L n) ×
  (∀ n → CohL (f n) (proj₂ L n))
CohL (lc k c w b t g) L = ⊥

cohP→L : ∀ K pl L → CohP K pl L → CohL K L
cohP→L zero pl L h = tt
cohP→L (suc k) pl L h = cohP→L k pl L h
cohP→L (lim f) pl L (e , h) =
  (λ n → cong proj₂ (e n)) , (λ n → cohP→L (f n) (pl n) (proj₂ L n) (h n))

CohF : ∀ (Q : LF → Set) K → Legal K → ((s : Pre K) → Q (lev K s)) → Set
CohF Q zero L v = ⊤
CohF Q (suc k) L v = CohF Q k L (λ s → v (inj₂ s))
CohF Q (lim f) L v =
  (∀ n → restrictF {Q = Q} (f (suc n)) (proj₁ L n) (λ s → v (suc n , s)) ≡ (λ s → v (n , s))) ×
  (∀ n → CohF Q (f n) (proj₂ L n) (λ s → v (n , s)))
CohF Q (lc k c w b t g) L v = ⊥
```

## 2 两条沿路径的引理

`cs-restrict`：规范化与沿 `Zp` 路径的限制可交换 (小的那边用限制下来的 `Legal`)。后继一步与极限第 0 支一步上 `csQ` 的子句正好把限制吃进去。
`unshift-restrict`：`unshiftQ` 沿它自己的路径限制下来就是 `down`，`stay` 不出现。

```agda
cs-restrict : ∀ (Q : LF → Set) {a} b (p : CP a b) → Zp p → (Lb : Legal b)
  (v : (s : Pre b) → Q (lev b s)) →
  restrictF {Q = Q} b p (csQ {Q = Q} b Lb v) ≡
  csQ {Q = Q} a (restrictL b p Lb) (restrictF {Q = Q} b p v)
cs-restrict Q b self z Lb v = refl
cs-restrict Q (suc b) (suc p) z Lb v = cs-restrict Q b p z Lb (λ s → v (inj₂ s))
cs-restrict Q (lim g) (lim zero p) z Lb v =
  cs-restrict Q (g zero) p z (proj₂ Lb zero) (λ s → v (zero , s))
cs-restrict Q (lim g) (lim (suc m) p) () Lb v
cs-restrict Q (lc k c w b t g) (fst p) () Lb v

unshift-restrict : ∀ (Q : LF → Set) {a} b (p : CP a b) → Zp p →
  (down : (s₀ : Pre a) → Q (lev a s₀)) (stay : (s : Pre b) → Q (lev b s)) →
  restrictF {Q = Q} b p (λ s → unshiftQ {Q = Q} b p down s (stay s)) ≡ down
unshift-restrict Q b self z down stay = refl
unshift-restrict Q (suc b) (suc p) z down stay =
  unshift-restrict Q b p z down (λ s → stay (inj₂ s))
unshift-restrict Q (lim g) (lim zero p) z down stay =
  unshift-restrict Q (g zero) p z down (λ s → stay (zero , s))
unshift-restrict Q (lim g) (lim (suc m) p) () down stay
unshift-restrict Q (lc k c w b t g) (fst p) () down stay
```

## 3 定理

对 `K` 归纳。极限处第 `n` 支上的函数是 `csQ (f n) … (upQ … n v)`：遗传部分直接是归纳假设 (换一个 `v`)；
这一步的方程是上面两条引理接起来，再用 `CohL` 把限制下来的 `Legal` 换成第 `n` 支自己的。

```agda
csQ-coh : ∀ (Q : LF → Set) K L → ZpL K L → CohL K L →
  (v : (s : Pre K) → Q (lev K s)) → CohF Q K L (csQ {Q = Q} K L v)
csQ-coh Q zero L z c v = tt
csQ-coh Q (suc k) L z c v = csQ-coh Q k L z c (λ s → v (inj₂ s))
csQ-coh Q (lim f) L (z , zs) (c , cs) v =
  (λ n →
    trans (cs-restrict Q (f (suc n)) (proj₁ L n) (z n) (proj₂ L (suc n))
            (upQ {Q = Q} f (proj₁ L) (suc n) v))
      (trans (cong (csQ {Q = Q} (f n) (restrictL (f (suc n)) (proj₁ L n) (proj₂ L (suc n))))
               (unshift-restrict Q (f (suc n)) (proj₁ L n) (z n)
                 (upQ {Q = Q} f (proj₁ L) n v) (λ s → v (suc n , s))))
        (cong (λ ℓ → csQ {Q = Q} (f n) ℓ (upQ {Q = Q} f (proj₁ L) n v)) (c n)))) ,
  (λ n → csQ-coh Q (f n) (proj₂ L n) (zs n) (cs n) (upQ {Q = Q} f (proj₁ L) n v))

cohF→X : ∀ {m} K L (v : (s : Pre K) → Way m (lev K s)) → CohF (Way m) K L v → CohX K L (mix v)
cohF→X zero L v h = tt
cohF→X (suc k) L v h = cohF→X k L (λ s → v (inj₂ s)) h
cohF→X (lim f) L v (e , h) =
  (λ n → trans (restrictX-mix (f (suc n)) (proj₁ L n) (λ s → v (suc n , s))) (cong mix (e n))) ,
  (λ n → cohF→X (f n) (proj₂ L n) (λ s → v (n , s)) (h n))

preCoh : ∀ {m} K (pl : Plain K) L → ZpL K L → CohL K L → (x : Ext m K) → CohX K L (pre K L x)
preCoh K pl L z c low = cohX-low K pl L
preCoh {m} K pl L z c (mix v) = cohF→X K L (csQ {Q = Way m} K L v) (csQ-coh (Way m) K L z c v)
```
