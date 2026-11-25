# YiGenNeg 第 2、3 项：链点的折叠问到的对；只取第 0 点时层号都是 0

**判决 (编译定理，正面)：把链点 `pointsᴺ n` 折到第 0 层时，若结点内部的链只取第 0 点 (下界那一支)，对一切 `n`，问到的每个目标位置的层号都是 0 (`zero-point-level`)；
那里 `Honest` 的保留一支空真，派发不需要判定。** 所以两路走查说的墙不在第 0 点的片段里：它要用到结点内部第 1 个以后的链点，那依赖折叠自己的输出。
`Ask` 是问到的对的归纳谓词，行取自上一轮 `YiRawFold.Ψ` 的保留行与链行；`Out` 是第 0 层折叠的图 (参数)，取空关系就是只取第 0 点。墙在 [YiGenNegWall](YiGenNegWall.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiGenNegAsk where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1)
open import OCF.Align.YiIrrIf using (R; one)
open import OCF.Align.YiLvFoldAdd using (plus)
open import OCF.Align.YiLvIf using (lev)
open import OCF.Align.YiLvNegCompare using (At)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; first₂; br)
open import OCF.Align.YiOmFoldBase
open import OCF.Align.YiOmFold using (F₀; t₀)
open import OCF.Align.YiOmFoldNorm
open import OCF.Align.YiOmFoldChain using (Φˢ⁺; pointsᴺ)
open import OCF.Align.YiGenIf using (OwnFold; Honest)
open import OCF.Align.YiGenNegShape
```

## 1 问到的对

`Ask⁰ ξ`：目标层 0 的折叠问到树 `ξ`。`Ask q ξ`：目标在位置 `q` 上的折叠 (`YiGenIf.OwnFold q`) 问到树 `ξ`。规则只有：

- 后继与 ℕ 极限逐项；
- 目标层 0，结点：链在结点自己的层里。第 0 点是下界 `c`：观察问 `Ask⁰ (g c)`，推进问 `Ask r (g c)` (`r` 是结点的位置)；
- 目标层 0，根槽位上的结点 (层号 0)，第 1 点 `c + y` (第 0 层的加法 `plus zero`，同 `YiOmFold.NodeRow.next-row`)，`y` 是第 0 层折叠在 `g c` 上的输出 (`Out (g c) y`)：观察问 `Ask⁰ (g (c + y))`。只写了这一种后续点；
- 目标 `q`，结点层在目标层的位置上 (保留行)：保留结点的各支是各支的折叠，对一切带守卫的坐标 (`o-keep`)；
- 目标 `q`，目标层在结点层的位置上 (链行)：推进问 `Ask r (g c)` (`o-own`)。

守卫都取相关的证明。规则比折叠实际问的少 (只取第 0 点与一种第 1 点)，所以对 "问到的对" 成立的否定更强。

```agda
module Asked (ξ₀ : RΩ) (Out : RΩ → R → Set) where
  data Ask⁰ : RΩ → Set
  data Ask : Pre K₂ω → RΩ → Set

  data Ask⁰ where
    z-start : Ask⁰ ξ₀
    z-suc : ∀ {a} → Ask⁰ (G.suc a) → Ask⁰ a
    z-lim : ∀ {f} → Ask⁰ (G.lim f) → ∀ n → Ask⁰ (f n)
    z-obs : ∀ {r c t g} → Ask⁰ (G.lc r c t g) → (e : GdL K₂ω r c c) → Ask⁰ (g c e)
    z-next : ∀ {c t g} → Ask⁰ (G.lc root₂ c t g) →
      (e₀ : GdL K₂ω root₂ c c) (y : R) → Out (g c e₀) y →
      (e₁ : GdL K₂ω root₂ c (plus zero c y)) → Ask⁰ (g (plus zero c y) e₁)

  data Ask where
    z-own : ∀ {r c t g} → Ask⁰ (G.lc r c t g) → (e : GdL K₂ω r c c) → Ask r (g c e)
    o-suc : ∀ {q a} → Ask q (G.suc a) → Ask q a
    o-lim : ∀ {q f} → Ask q (G.lim f) → ∀ n → Ask q (f n)
    o-keep : ∀ {q r c t g} → Ask q (G.lc r c t g) → At (lev K₂ω q) (lev K₂ω r) →
      ∀ η (e : GdL K₂ω r c η) → Ask q (g η e)
    o-own : ∀ {q r c t g} → Ask q (G.lc r c t g) → At (lev K₂ω r) (lev K₂ω q) →
      (e : GdL K₂ω r c c) → Ask r (g c e)

None : RΩ → R → Set
None ξ y = ⊥

s₀ : Gd zero raw1 raw1
s₀ = inj₁ refl , tt , tt

-- 第 1 个内部链点用到的前提: 输出的最左叶是 1 (沿极限的第 0 项走到 1 或第 0 层的 top).
data LeftOne : R → Set where
  lo-one : LeftOne one
  lo-top : LeftOne G.top
  lo-lim : ∀ {f} → LeftOne (f 0) → LeftOne (G.lim f)

-- 第 2 个链点各支的上下文.
C₃ : RΩ → RΩ
C₃ X = plusΩ P₁ (Φˢ⁺ (plusΩ G.top X))
```

## 2 具体的对

第 1 个链点：起点那一支的结点 (位置 `rᴺ 0`) 的下界那一支被 "目标在 `rᴺ 0` 上" 的折叠问到。
第 2 个链点：沿第 0 点走到 `N₂` (`Φˢ⁺ top` 的像，外加 `P₁`)，对任何 `Out` 成立。

```agda
module _ (Out : RΩ → R → Set) where
  open Asked (pointsᴺ 1) Out

  asked₁ : Ask (rᴺ G.zero) (G.lim (λ n → plusΩ G.top (plusΩ t₀ (copiesΩ G.top n))))
  asked₁ = z-own (z-obs z-start s₀) s₀

module _ (Out : RΩ → R → Set) where
  open Asked (pointsᴺ 2) Out

  z-thru : ∀ X → Ask⁰ (C₃ (topᴬ X)) → Ask⁰ (C₃ X)
  z-thru X p = z-lim (z-obs (z-lim (z-obs p s₀) 0) s₀) 0

  asked₂-start : Ask (rᴺ G.zero) (G.lim (λ n → C₃ (plusΩ t₀ (copiesΩ G.top n))))
  asked₂-start = z-own (z-obs z-start s₀) s₀

  asked₂-t₀ : Ask⁰ (C₃ t₀)
  asked₂-t₀ = z-thru t₀ (z-lim (z-obs (z-obs z-start s₀) s₀) 0)

  asked₂-N₂ : Ask⁰ N₂
  asked₂-N₂ =
    z-lim (z-obs (z-lim (z-obs (z-lim (z-obs asked₂-t₀ s₀) 0) s₀) 0) s₀) 0
```

## 3 只取第 0 点：层号都是 0

`E ξ`：`ξ` 没有嵌入的孩子，沿下界那一支走到的结点层号都是 0。它对加法与 `Φˢ⁺` 封闭，链点都在里面。

```agda
E : RΩ → Set
E G.zero = ⊤
E (G.suc a) = E a
E (G.lim f) = ∀ n → E (f n)
E (G.lc r c t g) = (lev K₂ω r ≡ zero) × ((e : GdL K₂ω r c c) → E (g c e))
E (G.em i a) = ⊥
E G.top = ⊤

E-plus : ∀ x a → E x → E a → E (plusΩ x a)
E-plus x G.zero ex ea = ex
E-plus x (G.suc a) ex ea = E-plus x a ex ea
E-plus x (G.lim f) ex ea = λ n → E-plus x (f n) ex (ea n)
E-plus x (G.lc r c t g) ex (z , eg) = z , (λ e → E-plus x (g c e) ex (eg e))
E-plus x G.top ex ea = refl , (λ e → refl , (λ e′ → ex))

E-copies : ∀ y → E y → ∀ n → E (copiesΩ y n)
E-copies y ey zero = ey
E-copies y ey (suc n) = E-plus y (copiesΩ y n) ey (E-copies y ey n)

E-t₀ : E t₀
E-t₀ = refl , (λ e → E-copies G.top tt)

E-Φ : ∀ ξ → E ξ → E (Φˢ⁺ ξ)
E-Φ G.zero e = tt
E-Φ (G.suc a) e = E-copies (Φˢ⁺ a) (E-Φ a e)
E-Φ (G.lim f) e = λ n → E-Φ (f n) (e n)
E-Φ (G.lc r c t g) (z , eg) = z , (λ e → E-Φ (g c e) (eg e))
E-Φ G.top e =
  refl , (λ e₁ → refl , (λ e₂ n → E-plus t₀ (copiesΩ G.top n) E-t₀ (E-copies G.top tt n)))

E-points : ∀ n → E (pointsᴺ n)
E-points zero = tt
E-points (suc n) = E-plus (pointsᴺ n) (Φˢ⁺ (pointsᴺ n)) (E-points n) (E-Φ (pointsᴺ n) (E-points n))

no-at : ∀ {L k} → L ≡ zero → At L k → ⊥
no-at refl (() , e)

constF : ∀ q → OwnFold q
constF q ξ l nb = G.lim (λ _ → G.zero)

const-honest : ∀ {q} → lev K₂ω q ≡ zero → ∀ ξ → Honest q (constF q) ξ
const-honest z (G.lc r c t g) = λ l nb → (λ a → ⊥-elim (no-at z a)) , (λ _ → tt)
const-honest z G.zero = tt
const-honest z (G.suc a) = tt
const-honest z (G.lim f) = tt
const-honest z (G.em i T) = tt
const-honest z G.top = tt

module ZeroPoint (n : ℕ) where
  open Asked (pointsᴺ n) None

  inv⁰ : ∀ {ξ} → Ask⁰ ξ → E ξ
  inv : ∀ {q ξ} → Ask q ξ → (lev K₂ω q ≡ zero) × E ξ

  inv⁰ z-start = E-points n
  inv⁰ (z-suc p) = inv⁰ p
  inv⁰ (z-lim p m) = inv⁰ p m
  inv⁰ (z-obs p e) = proj₂ (inv⁰ p) e

  inv (z-own p e) = proj₁ (inv⁰ p) , proj₂ (inv⁰ p) e
  inv (o-suc p) = inv p
  inv (o-lim p m) = proj₁ (inv p) , proj₂ (inv p) m
  inv (o-keep p a η e) with no-at (proj₁ (inv p)) a
  ... | ()
  inv (o-own p a e) = proj₁ (proj₂ (inv p)) , proj₂ (proj₂ (inv p)) e

  zero-point-level : ∀ {q ξ} → Ask q ξ → lev K₂ω q ≡ zero
  zero-point-level p = proj₁ (inv p)

  -- 这些目标上没有要保留的结点: 派发不需要判定.
  zero-point-fold : ∀ {q ξ} → Ask q ξ → ∀ k → At (lev K₂ω q) k → ⊥
  zero-point-fold p k = no-at (zero-point-level p)

  -- 所以常值极限的折叠族在这些对上就是 Honest 的: Honest 在这里不携带判定.
  zero-point-honest : ∀ {q ξ} → Ask q ξ → Honest q (constF q) ξ
  zero-point-honest {ξ = ξ} p = const-honest (zero-point-level p) ξ
```
