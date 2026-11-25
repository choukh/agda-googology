# YiGenNeg 第 4 项 (对照)：第 1 个链点上，这条路径只问到层号 0 与 1 的目标

**判决 (编译定理，正面)：第 1 个链点的根上取同样的第 1 个内部链点 (`y` 的最左叶是 1)，目标 `r₁` (层号 1) 被问到 (`asked-r₁`)；它之下被折的树里一切结点的层号都是 0，
所以从这一对出发问到的对目标都还是 `r₁`，结点都保留，没有新的目标 (`under-r₁`)。目标层 1 上派发可判定。** 与第 2 个链点的差别：这里被加数是 `top`，树里没有 `Φˢ⁺ top` 的像。
只管这一条路径 (最左叶)；`y` 的其余叶上问到什么没有判定。第 2 个链点见 [YiGenNegWall](YiGenNegWall.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiGenNegOne where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1; raw0-Nested)
open import OCF.Align.YiIrrIf using (R; one)
open import OCF.Align.YiLvIf using (lev)
open import OCF.Align.YiLvFoldAdd using (add; plus; rawAlg; add-weak; add-lgl)
open import OCF.Align.YiLvNegCompare using (At)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; first₂)
open import OCF.Align.YiOmNegBranch using (at-one-dec)
open import OCF.Align.YiOmFoldBase
open import OCF.Align.YiOmFold using (F₀; t₀)
open import OCF.Align.YiOmFoldNorm
open import OCF.Align.YiOmFoldChain using (pointsᴺ; pointsᴺ-nested)
open import OCF.Align.YiGenNegShape
open import OCF.Align.YiGenNegAsk
open import OCF.Align.YiGenNegLeft
  using (valˢ; valˢ-legal; Outˢ; rowsˢ; rows→left; Desc; d-top; dp-one)
open import OCF.Align.YiGenNegWall using (two; r₁)
```

## 1 一切结点层号为 0 的树

`Lz ξ`：没有嵌入的孩子，一切结点 (第一支与各支里的) 层号是 0。对加法封闭。

```agda
Lz : RΩ → Set
Lz G.zero = ⊤
Lz (G.suc a) = Lz a
Lz (G.lim f) = ∀ n → Lz (f n)
Lz (G.lc r c t g) =
  (lev K₂ω r ≡ zero) × Lz t × (∀ η (e : GdL K₂ω r c η) → Lz (g η e))
Lz (G.em i a) = ⊥
Lz G.top = ⊤

add₀-Lz : ∀ x → Lz x → ∀ (a : R) → Lz (add zero alg₀ x a)
add₀-Lz x lx G.zero = lx
add₀-Lz x lx (G.suc a) = add₀-Lz x lx a
add₀-Lz x lx (G.lim f) = λ n → add₀-Lz x lx (f n)
add₀-Lz x lx G.top = lx

top₁-Lz : ∀ x → Lz x → Lz (top₁ x)
top₁-Lz x lx = refl , lx , (λ η e → add₀-Lz x lx η)

plus-Lz : ∀ x a → Lz x → Lz a → Lz (plusΩ x a)
plus-Lz x G.zero lx la = lx
plus-Lz x (G.suc a) lx la = plus-Lz x a lx la
plus-Lz x (G.lim f) lx la = λ n → plus-Lz x (f n) lx (la n)
plus-Lz x (G.lc r c t g) lx (z , lt , lg) =
  z , plus-Lz x t lx lt , (λ η e → plus-Lz x (g η e) lx (lg η e))
plus-Lz x G.top lx la =
  refl , top₁-Lz x lx , (λ η e → add₀-Lz (top₁ x) (top₁-Lz x lx) η)

copies-Lz : ∀ y → Lz y → ∀ n → Lz (copiesΩ y n)
copies-Lz y ly zero = ly
copies-Lz y ly (suc n) = plus-Lz y (copiesΩ y n) ly (copies-Lz y ly n)

KA₀-Lz : ∀ (ν : Nod zero) ζ → Lz (keepAll zero ν ζ)
KA₀-Lz ν G.zero = tt
KA₀-Lz ν (G.suc a) = copies-Lz (keepAll zero ν a) (KA₀-Lz ν a)
KA₀-Lz ν (G.lim f) = λ n → KA₀-Lz ν (f n)
KA₀-Lz ν G.top = copies-Lz G.top tt

F₀-Lz : ∀ a → Lz (F₀ a)
F₀-Lz G.zero = tt
F₀-Lz (G.suc a) = copies-Lz (F₀ a) (F₀-Lz a)
F₀-Lz (G.lim f) = λ n → F₀-Lz (f n)
F₀-Lz G.top = copies-Lz G.top tt

t₀-Lz : Lz t₀
t₀-Lz = refl , F₀-Lz raw1 , (λ η e → F₀-Lz η)

one-Lz : Lz (Gκ one)
one-Lz = plus-Lz t₀ (KT G.zero) t₀-Lz
  (refl , KA₀-Lz (νᴺ G.zero) raw1 , (λ ζ e → KA₀-Lz (νᴺ G.zero) ζ))

tree₁ : RΩ
tree₁ = plusΩ G.top (plusΩ (Gκ one) (keepAll (suc zero) (νᴺ one) G.top))

tree₁-Lz : Lz tree₁
tree₁-Lz = plus-Lz G.top (plusΩ (Gκ one) (keepAll (suc zero) (νᴺ one) G.top)) tt
  (plus-Lz (Gκ one) (keepAll (suc zero) (νᴺ one) G.top) one-Lz
    (refl , KA₀-Lz (nS (νᴺ one)) raw1 , (λ ζ e → KA₀-Lz (nS (νᴺ one)) ζ)))
```

## 2 `r₁` 被问到，它之下没有新的目标

`Under q₀ ξ₀`：从 `(q₀, ξ₀)` 出发按目标一侧的规则问到的对。它们都在 `Ask` 里 (`under-asked`)。

```agda
data Under (q₀ : Pre K₂ω) (ξ₀ : RΩ) : Pre K₂ω → RΩ → Set where
  u-start : Under q₀ ξ₀ q₀ ξ₀
  u-suc : ∀ {q a} → Under q₀ ξ₀ q (G.suc a) → Under q₀ ξ₀ q a
  u-lim : ∀ {q f} → Under q₀ ξ₀ q (G.lim f) → ∀ n → Under q₀ ξ₀ q (f n)
  u-keep : ∀ {q r c t g} → Under q₀ ξ₀ q (G.lc r c t g) → At (lev K₂ω q) (lev K₂ω r) →
    ∀ η (e : GdL K₂ω r c η) → Under q₀ ξ₀ q (g η e)
  u-own : ∀ {q r c t g} → Under q₀ ξ₀ q (G.lc r c t g) → At (lev K₂ω r) (lev K₂ω q) →
    (e : GdL K₂ω r c c) → Under q₀ ξ₀ r (g c e)

module _ (ξ : RΩ) (Out : RΩ → R → Set) where
  open Asked ξ Out

  under-asked : ∀ {q₀ ξ₀ q ξ′} → Ask q₀ ξ₀ → Under q₀ ξ₀ q ξ′ → Ask q ξ′
  under-asked p₀ u-start = p₀
  under-asked p₀ (u-suc u) = o-suc (under-asked p₀ u)
  under-asked p₀ (u-lim u n) = o-lim (under-asked p₀ u) n
  under-asked p₀ (u-keep u a η e) = o-keep (under-asked p₀ u) a η e
  under-asked p₀ (u-own u a e) = o-own (under-asked p₀ u) a e

under-zero : ∀ {q₀ ξ₀ q ξ} → Lz ξ₀ → Under q₀ ξ₀ q ξ → (q ≡ q₀) × Lz ξ
under-zero l₀ u-start = refl , l₀
under-zero l₀ (u-suc u) = under-zero l₀ u
under-zero l₀ (u-lim u n) = proj₁ (under-zero l₀ u) , proj₂ (under-zero l₀ u) n
under-zero l₀ (u-keep u a η e) =
  proj₁ (under-zero l₀ u) , proj₂ (proj₂ (proj₂ (under-zero l₀ u))) η e
under-zero l₀ (u-own u a e) = ⊥-elim (no-at (proj₁ (proj₂ (under-zero l₀ u))) a)

module Path₁ (Out : RΩ → R → Set) (y : R) (out : Out (B₁ one) y) (ly : LeftOne y)
  (e₁ : Gd zero raw1 (plus zero one y)) where
  open Asked (pointsᴺ 1) Out

  to-two : ∀ {z} → LeftOne z → Ask⁰ (B₁ (plus zero one z)) → Ask⁰ (B₁ two)
  to-two lo-one p = p
  to-two lo-top p = p
  to-two (lo-lim l) p = to-two l (z-lim p 0)

  asked-r₁ : Ask r₁ tree₁
  asked-r₁ = z-own (to-two ly (z-next z-start s₀ y out e₁)) (inj₁ refl , tt , tt)

  -- r₁ 之下: 目标不变, 树里只有层号 0 的结点; 它们在目标层 1 之下, 都保留.
  under-r₁ : ∀ {q ξ} → Under r₁ tree₁ q ξ → (q ≡ r₁) × Lz ξ
  under-r₁ = under-zero tree₁-Lz

  under-r₁-kept : ∀ {r c t g} → Lz (G.lc r c t g) → At (lev K₂ω r₁) (lev K₂ω r)
  under-r₁-kept (z , _) = inj₁ tt , sym′ z
    where
    sym′ : ∀ {A : Set} {a b : A} → a ≡ b → b ≡ a
    sym′ refl = refl

r₁-dec′ : ∀ k → At (lev K₂ω r₁) k ⊎ (At (lev K₂ω r₁) k → ⊥)
r₁-dec′ = at-one-dec
```

前提的实例 (骨架的值 `valˢ`，同 [YiGenNegLeft](YiGenNegLeft.lagda.md) §4)。

```agda
nb₁ : Nested K₂ω (B₁ one)
nb₁ = proj₂ (proj₂ (proj₂ (pointsᴺ-nested 1))) one s₀

y₁ : R
y₁ = valˢ (B₁ one) nb₁

module Instance₁ = Path₁ Outˢ y₁ (nb₁ , refl)
  (rows→left rowsˢ (dp-one G.top d-top) (nb₁ , refl))
  (add-weak zero (rawAlg zero) one y₁ ,
   add-lgl zero tt (rawAlg zero) one y₁ tt (valˢ-legal (B₁ one) nb₁) ,
   raw0-Nested (plus zero one y₁))
```
