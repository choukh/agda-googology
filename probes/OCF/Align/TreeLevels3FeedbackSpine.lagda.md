# 第三轮：指定差树形状的零支脊柱不变量

本篇只提炼 `TreeLevelsO3Shape` 的必要性质，不展开任何具体高闭项。
First a b 允许沿后继或 ℕ 极限第 0 支向下找到 `a`。它不要求
极限的第 0 项为零；任意起点 `a` 都被追加动作保留为这种脊柱前缀。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.TreeLevels3FeedbackSpine where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Product using (Σ; _,_; _×_; proj₁)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
import OCF.Free.Level as F
import OCF.Align.NoKCertEval as E
open import OCF.Align.TreeLevelsO3Shape using (Difference; idle; tick; then; limit; act; partial; Shape; shaped)

lim-at : E.Zᵁ → ℕ → E.Zᵁ
lim-at (E.lim f) n = f n
lim-at _ n = E.zero

first : E.Zᵁ → E.Zᵁ
first (E.ŝ c t g) = t
first _ = E.zero

data IsLimit : E.Zᵁ → Set where
  is-limit : ∀ {f} → IsLimit (E.lim f)

data IsSelfClosure : E.Zᵁ → Set where
  is-self-closure : ∀ {c t g} → IsSelfClosure (E.ŝ c t g)

is-limit? : E.Zᵁ → Bool
is-limit? (E.lim _) = true
is-limit? _ = false

is-self-closure? : E.Zᵁ → Bool
is-self-closure? (E.ŝ _ _ _) = true
is-self-closure? _ = false

reflect-limit : ∀ x → is-limit? x ≡ true → IsLimit x
reflect-limit (E.lim _) p = is-limit

reflect-self-closure : ∀ x → is-self-closure? x ≡ true → IsSelfClosure x
reflect-self-closure (E.ŝ _ _ _) p = is-self-closure

limit-exact : ∀ {x} → IsLimit x → x ≡ E.lim (lim-at x)
limit-exact is-limit = refl

data First : E.Ord₀ → E.Ord₀ → Set where
  same : ∀ {a} → First a a
  above-suc : ∀ {a b} → First a b → First a (F.suc b)
  above-zero : ∀ {a f} → First a (f 0) → First a (F.lim f)

first-trans : ∀ {a b c} → First a b → First b c → First a c
first-trans p same = p
first-trans p (above-suc q) = above-suc (first-trans p q)
first-trans p (above-zero q) = above-zero (first-trans p q)

prefix-act : ∀ d a → First a (act d a)
prefix-act idle a = same
prefix-act (tick d) a = above-suc (prefix-act d a)
prefix-act (then d e) a = first-trans (prefix-act d a) (prefix-act e (act d a))
prefix-act (limit ds) a = above-zero same

SpineLegal : E.Ord₀ → Set
SpineLegal F.zero = ⊤
SpineLegal (F.suc x) = SpineLegal x
SpineLegal (F.lim f) = (∀ n → First (f n) (f (suc n))) × (∀ n → SpineLegal (f n))
SpineLegal (F.limᵢ () f)
SpineLegal (F.up () x)

spine-act : ∀ d a → SpineLegal a → SpineLegal (act d a)
spine-partial : ∀ ds a → SpineLegal a → ∀ n → SpineLegal (partial ds a n)
spine-act idle a h = h
spine-act (tick d) a h = spine-act d a h
spine-act (then d e) a h = spine-act e (act d a) (spine-act d a h)
spine-act (limit ds) a h =
  (λ n → prefix-act (ds n) (partial ds a n)) , spine-partial ds a h
spine-partial ds a h zero = h
spine-partial ds a h (suc n) = spine-act (ds n) (partial ds a n) (spine-partial ds a h n)

shape→spine : ∀ y → Shape y → SpineLegal y
shape→spine .(act d F.zero) (shaped d refl) = spine-act d F.zero tt

no-lim-one : ∀ {f} → First (F.lim f) (F.suc F.zero) → ⊥
no-lim-one (above-suc ())

zero≢one : _≡_ {A = E.Ord₀} F.zero (F.suc F.zero) → ⊥
zero≢one ()

no-limit-step : ∀ {f g} → f 0 ≡ F.zero → g 0 ≡ F.suc F.zero →
  First (F.lim f) (F.lim g) → ⊥
no-limit-step p q same = zero≢one (trans (sym p) q)
no-limit-step p q (above-zero h) = no-lim-one (subst (First _) q h)

force-zero : ∀ (G : E.Goodᵁ E.zero) → E.forceᵁ E.zero G ≡ F.zero
force-zero E.gz = refl

force-one : ∀ (G : E.Goodᵁ (E.suc E.zero)) → E.forceᵁ (E.suc E.zero) G ≡ F.suc F.zero
force-one (E.gs E.gz) = refl

force-zero-at : ∀ {x} → x ≡ E.zero → (G : E.Goodᵁ x) → E.forceᵁ x G ≡ F.zero
force-zero-at refl G = force-zero G

force-one-at : ∀ {x} → x ≡ E.suc E.zero → (G : E.Goodᵁ x) → E.forceᵁ x G ≡ F.suc F.zero
force-one-at refl G = force-one G

no-valued-step : ∀ {x y f g} → x ≡ E.lim f → y ≡ E.lim g →
  f 0 ≡ E.zero → g 0 ≡ E.suc E.zero →
  (G : E.Goodᵁ x) (H : E.Goodᵁ y) →
  First (E.forceᵁ x G) (E.forceᵁ y H) → ⊥
no-valued-step refl refl p q (E.gl G st) (E.gl H su) h =
  no-limit-step (force-zero-at p (G 0)) (force-one-at q (H 0)) h

-- 只观察有限头部：两个相邻的极限，其第 0 项分别为 0 与 1。
is-zero? : E.Zᵁ → Bool
is-zero? E.zero = true
is-zero? _ = false

is-one? : E.Zᵁ → Bool
is-one? (E.suc E.zero) = true
is-one? _ = false

reflect-zero : ∀ x → is-zero? x ≡ true → x ≡ E.zero
reflect-zero E.zero p = refl

reflect-one : ∀ x → is-one? x ≡ true → x ≡ E.suc E.zero
reflect-one (E.suc E.zero) p = refl

record BadPair (x : E.Zᵁ) : Set where
  constructor bad-pair
  field
    outer-limit : IsLimit x
    left-limit : IsLimit (lim-at x 0)
    right-limit : IsLimit (lim-at x 1)
    left-zero : lim-at (lim-at x 0) 0 ≡ E.zero
    right-one : lim-at (lim-at x 1) 0 ≡ E.suc E.zero

no-bad-pair-shape : ∀ x → BadPair x →
  ¬ (Σ (E.Goodᵁ x) (λ G → Shape (E.forceᵁ x G)))
no-bad-pair-shape (E.lim f) (bad-pair outer left right p q) (E.gl gs steps , h) =
  no-valued-step (limit-exact left) (limit-exact right) p q (gs 0) (gs 1)
    (proj₁ (shape→spine _ h) 0)

-- 第 0 层没有 up；结构互模拟保留本证明所用的有限构造子头。
_≈₀_ : E.Ord₀ → E.Ord₀ → Set
a ≈₀ b = a F.≅ b

zero-only : ∀ {y : E.Ord₀} → F.zero ≈₀ y → y ≡ F.zero
zero-only F.z≅ = refl

one-only : ∀ {y : E.Ord₀} → F.suc F.zero ≈₀ y → y ≡ F.suc F.zero
one-only (F.s≅ e) rewrite zero-only e = refl

no-limit-step-bisim : ∀ {f g : ℕ → E.Ord₀} {a b : E.Ord₀} →
  f 0 ≡ F.zero → g 0 ≡ F.suc F.zero →
  F.lim f ≈₀ a → F.lim g ≈₀ b → First a b → ⊥
no-limit-step-bisim p q (F.l≅ e) (F.l≅ d) h =
  no-limit-step (zero-only (subst (λ z → z ≈₀ _) p (e 0)))
    (one-only (subst (λ z → z ≈₀ _) q (d 0))) h

no-valued-step-bisim : ∀ {x y f g} {a b : E.Ord₀} →
  x ≡ E.lim f → y ≡ E.lim g → f 0 ≡ E.zero → g 0 ≡ E.suc E.zero →
  (G : E.Goodᵁ x) (H : E.Goodᵁ y) →
  E.forceᵁ x G F.≅ a → E.forceᵁ y H F.≅ b → First a b → ⊥
no-valued-step-bisim refl refl p q (E.gl G st) (E.gl H su) e d h =
  no-limit-step-bisim (force-zero-at p (G 0)) (force-one-at q (H 0)) e d h

no-bad-pair-shape-bisim : ∀ x → BadPair x →
  (G : E.Goodᵁ x) (y : E.Ord₀) → E.forceᵁ x G F.≅ y → Shape y → ⊥
no-bad-pair-shape-bisim (E.lim f) (bad-pair outer left right p q)
  (E.gl gs steps) (F.lim ys) (F.l≅ e) h =
  no-valued-step-bisim (limit-exact left) (limit-exact right) p q (gs 0) (gs 1)
    (e 0) (e 1) (proj₁ (shape→spine _ h) 0)
```

这是对指定 `Shape` 的必要条件。证明不假定原程序的全部 `Goodᵁ`
存在；它排除的是某个 `BadPair` 同时拥有计值证书和该形状证书。
后续叶模块必须把 `BadPair` 接到原运行的实际种子，才构成运行否定。
`no-bad-pair-shape-bisim` 还排除第 0 层与此计值结构互模拟的任何
`Shape` 代表；这里没有把结构互模拟换成序数值相等。
