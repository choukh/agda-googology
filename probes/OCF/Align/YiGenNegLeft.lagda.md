# YiGenNeg：第 1 个内部链点的前提从折叠的四行推出

**判决 (编译定理)：第 0 层折叠的图 `Out` 若满足四行 (`Rows`：`top` 的值最左叶是 1；后继、ℕ 极限、结点的输出都是 ℕ 极限，第 0 项是下一层的值)，
则它在第 2 个链点起点那一支上的输出 `y` 满足 `LeftOne y` (`premise₂`)。** 这就是 [YiGenNegWall](YiGenNegWall.lagda.md) 用到的唯一依赖折叠的前提。
四行可满足：上一轮的 `Φ⁰` 在它的定义域上满足 (`rows⁰`；`top` 的值是 `T₃ᵐ`)。不对 `Out` 作别的要求，也不要求它是函数。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiGenNegLeft where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1; raw0-Nested)
open import OCF.Align.YiIrrIf using (R; one)
open import OCF.Align.YiLvFoldAdd using (plus; rawAlg; add-weak; add-lgl)
open import OCF.Align.YiRawFoldBase using (seedL)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; first₂)
open import OCF.Align.YiOmFoldBase
open import OCF.Align.YiOmFold using (t₀; Dom⁰; Φ⁰)
open import OCF.Align.YiOmFoldNorm
open import OCF.Align.YiOmFoldChain using (Φˢ⁺; pointsᴺ; pointsᴺ-nested)
open import OCF.Align.YiGenNegShape
open import OCF.Align.YiGenNegAsk
```

## 1 四行与最左的下降

`Desc ξ`：从 `ξ` 沿后继、极限的第 0 项、结点的下界那一支走到叶 `top`。

```agda
record Rows (Out : RΩ → R → Set) : Set where
  field
    r-top : ∀ {y} → Out G.top y → LeftOne y
    r-suc : ∀ {a y} → Out (G.suc a) y → Σ (ℕ → R) λ h → (y ≡ G.lim h) × Out a (h 0)
    r-lim : ∀ {f y} → Out (G.lim f) y → Σ (ℕ → R) λ h → (y ≡ G.lim h) × Out (f 0) (h 0)
    r-node : ∀ {r c t g y} → Out (G.lc r c t g) y → (e : GdL K₂ω r c c) →
      Σ (ℕ → R) λ h → (y ≡ G.lim h) × Out (g c e) (h 0)

data Desc : RΩ → Set where
  d-top : Desc G.top
  d-suc : ∀ {a} → Desc a → Desc (G.suc a)
  d-lim : ∀ {f} → Desc (f 0) → Desc (G.lim f)
  d-node : ∀ {r c t g} (e : GdL K₂ω r c c) → Desc (g c e) → Desc (G.lc r c t g)

rows→left : ∀ {Out} → Rows Out → ∀ {ξ} → Desc ξ → ∀ {y} → Out ξ y → LeftOne y
rows→left H d-top o = Rows.r-top H o
rows→left H (d-suc d) o with Rows.r-suc H o
... | h , refl , o′ = lo-lim (rows→left H d o′)
rows→left H (d-lim d) o with Rows.r-lim H o
... | h , refl , o′ = lo-lim (rows→left H d o′)
rows→left H (d-node e d) o with Rows.r-node H o e
... | h , refl , o′ = lo-lim (rows→left H d o′)
```

## 2 第 2 个链点起点那一支的下降

经过 `N₂` 与 `P₁`，在 `P₁` 里走到叶 `top`。

```agda
dp-top : ∀ x → Desc x → Desc (plusΩ x G.top)
dp-top x d = d-node s₀ (d-suc (d-node s₀ (d-suc d)))

dp-thru : ∀ x X → Desc (plusΩ x X) → Desc (plusΩ x (topᴬ X))
dp-thru x X d = d-node s₀ (d-suc (d-node s₀ (d-suc d)))

dp-t₀ : ∀ x → Desc x → Desc (plusΩ x t₀)
dp-t₀ x d = d-node s₀ (d-lim (dp-top x d))

dp-one : ∀ x → Desc x → Desc (plusΩ x (Gκ one))
dp-one x d = d-node s₀ (d-lim (dp-thru x t₀ (dp-t₀ x d)))

desc-P₁ : Desc P₁
desc-P₁ = d-node s₀ (dp-one G.top d-top)

desc-N₂ : Desc N₂
desc-N₂ = d-node s₀ (dp-one P₁ desc-P₁)

d3-thru : ∀ X → Desc (C₃ X) → Desc (C₃ (topᴬ X))
d3-thru X d = d-node s₀ (d-lim (d-node s₀ (d-lim d)))

d3-top : Desc (C₃ G.top)
d3-top = d-node s₀ (d-lim (d-node s₀ (d-lim desc-N₂)))

d3-t₀ : Desc (C₃ t₀)
d3-t₀ = d-node s₀ (d-lim d3-top)

desc-start₂ : Desc (B₂ one)
desc-start₂ = d-node s₀ (d-lim (d3-thru t₀ d3-t₀))

premise₂ : ∀ {Out} → Rows Out → ∀ {y} → Out (B₂ one) y → LeftOne y
premise₂ H = rows→left H desc-start₂
```

## 3 四行可满足

`Φ⁰` 的图 (带定义域与证书) 满足四行：`top` 给 `T₃ᵐ`，它的最左叶在三层极限之下是 1；后继给 ω 倍，第 0 项取一份；主干槽位上的结点给链的极限，第 0 项是下界那一支的值；
分支槽位上的结点不在 `Dom⁰` 里。`B₂ 1` 不在 `Dom⁰` 里，所以这只是四行的实例，不是 `premise₂` 的前提的实例。

```agda
Out⁰ : RΩ → R → Set
Out⁰ ξ y = Σ (Dom⁰ ξ) λ d → Σ (Lgl K₂ω ξ) λ l → Σ (Nested K₂ω ξ) λ nb → y ≡ Φ⁰ ξ d l nb

rows⁰ : Rows Out⁰
rows⁰ = record
  { r-top = λ { (d , l , nb , refl) → lo-lim (lo-lim (lo-lim lo-one)) }
  ; r-suc = λ { (d , l , nb , refl) → _ , refl , (d , l , nb , refl) }
  ; r-lim = λ { (d , (st , lf) , nb , refl) → _ , refl , (d 0 , lf 0 , nb 0 , refl) }
  ; r-node = node }
  where
  node : ∀ {r c t g y} → Out⁰ (G.lc r c t g) y → (e : GdL K₂ω r c c) →
    Σ (ℕ → R) λ h → (y ≡ G.lim h) × Out⁰ (g c e) (h 0)
  node {inj₁ (inj₁ _)} ((dt , dg) , (tg , dir , irr , lt , lg) , (lw , nw , nt , ng) , refl) e =
    _ , refl , (dg _ e , lg _ e , ng _ e , refl)
  node {inj₂ (inj₁ (inj₁ _))}
    ((dt , dg) , (tg , dir , irr , lt , lg) , (lw , nw , nt , ng) , refl) e =
    _ , refl , (dg _ e , lg _ e , ng _ e , refl)
  node {inj₂ (inj₂ _)} (() , l , nb , eq) e
```

## 4 含起点那一支的实例

`Out⁰` 的定义域不含 `B₂ 1`。为说明 "四行，加上在 `B₂ 1` 上有输出，加上链点 `1 + y` 带守卫" 可以同时满足，给一个骨架的值 `valˢ`：
它只沿下界那一支与极限的第 0 项走，各层取常值序列。它满足四行，但不是折叠 (不携带强度)；只用来说明前提不空。

```agda
valˢ : (ξ : RΩ) → .(Nested K₂ω ξ) → R
valˢ G.zero nb = one
valˢ (G.suc a) nb = G.lim (λ _ → valˢ a nb)
valˢ (G.lim f) nb = G.lim (λ _ → valˢ (f 0) (nb 0))
valˢ (G.lc r c t g) nb = G.lim (λ _ →
  valˢ (g c (seedL K₂ω r c (proj₁ nb) (proj₁ (proj₂ nb))))
    (proj₂ (proj₂ (proj₂ nb)) c (seedL K₂ω r c (proj₁ nb) (proj₁ (proj₂ nb)))))
valˢ (G.em i T) nb = one
valˢ G.top nb = one

valˢ-legal : ∀ ξ .(nb : Nested K₂ω ξ) → Lgl zero (valˢ ξ nb)
valˢ-legal G.zero nb = tt
valˢ-legal (G.suc a) nb = (λ n → inj₁ refl) , (λ n → valˢ-legal a nb)
valˢ-legal (G.lim f) nb = (λ n → inj₁ refl) , (λ n → valˢ-legal (f 0) (nb 0))
valˢ-legal (G.lc r c t g) nb = (λ n → inj₁ refl) , (λ n →
  valˢ-legal (g c (seedL K₂ω r c (proj₁ nb) (proj₁ (proj₂ nb))))
    (proj₂ (proj₂ (proj₂ nb)) c (seedL K₂ω r c (proj₁ nb) (proj₁ (proj₂ nb)))))
valˢ-legal (G.em i T) nb = tt
valˢ-legal G.top nb = tt

Outˢ : RΩ → R → Set
Outˢ ξ y = Σ (Nested K₂ω ξ) λ nb → y ≡ valˢ ξ nb

rowsˢ : Rows Outˢ
rowsˢ = record
  { r-top = λ { (nb , refl) → lo-one }
  ; r-suc = λ { (nb , refl) → _ , refl , (nb , refl) }
  ; r-lim = λ { (nb , refl) → _ , refl , (nb 0 , refl) }
  ; r-node = λ { (nb , refl) e → _ , refl , (proj₂ (proj₂ (proj₂ nb)) _ e , refl) } }

nbˢ : Nested K₂ω (B₂ one)
nbˢ = proj₂ (proj₂ (proj₂ (pointsᴺ-nested 2))) one s₀

yˢ : R
yˢ = valˢ (B₂ one) nbˢ

outˢ : Outˢ (B₂ one) yˢ
outˢ = nbˢ , refl

guardˢ : Gd zero raw1 (plus zero one yˢ)
guardˢ =
  add-weak zero (rawAlg zero) one yˢ ,
  add-lgl zero tt (rawAlg zero) one yˢ tt (valˢ-legal (B₂ one) nbˢ) ,
  raw0-Nested (plus zero one yˢ)
```

