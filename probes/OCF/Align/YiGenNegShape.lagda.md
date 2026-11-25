# YiGenNeg 第 1 项：第 1、2 个链点的形状

**档位：编译事实 (`refl` 的等式与一条封闭引理)，没有折叠，没有否定。** 归一链的第 1、2 个链点：根是根槽位上的结点，第 `suc a` 支的根是第 `suc (nrm a)` 支根槽位上的结点 `rᴺ a`，层号 `read0 (nrm a)`；
起点那一支 (`a = 0`) 的结点层号是 0。第 1 个链点里这一支的各支都在主干片段里；第 2 个链点里出现 `N₂ = P₁ + topᴺ`，它的各支的根遍历一切 `rᴺ a`。
接口 [YiGenIf](YiGenIf.lagda.md)；问到的对在 [YiGenNegAsk](YiGenNegAsk.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiGenNegShape where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1; cO)
open import OCF.Align.YiIrrIf using (R; one; read0)
open import OCF.Align.YiLvIf using (lev)
open import OCF.Align.YiLvFoldAdd using (add)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; first₂; br)
open import OCF.Align.YiOmFoldBase
open import OCF.Align.YiOmFold using (F₀; t₀; F₀-tr; F₁-tr)
open import OCF.Align.YiOmFoldNorm
open import OCF.Align.YiOmFoldChain using (Φˢ⁺; pointsᴺ)
```

## 1 根与各支的根

`B₁ η`, `B₂ η`：第 1、2 个链点的第 `η` 支。`rᴺ a`：第 `suc (nrm a)` 支的根槽位，守卫 `γ a` 由树算出。

```agda
P₁ : RΩ
P₁ = pointsᴺ 1

B₁ B₂ : R → RΩ
B₁ η = plusΩ G.top (Gκ η)
B₂ η = plusΩ P₁ (Φˢ⁺ (plusΩ G.top (Gκ η)))

point₁-root : pointsᴺ 1 ≡ G.lc root₂ raw1 (plusΩ G.top t₀) (λ η e → B₁ η)
point₁-root = refl

point₂-root : pointsᴺ 2 ≡
  G.lc root₂ raw1 (plusΩ P₁ (Φˢ⁺ (plusΩ G.top t₀))) (λ η e → B₂ η)
point₂-root = refl

rᴺ : R → Pre K₂ω
rᴺ a = br (G.suc (nrm a)) (γ a) (inj₁ tt)

rᴺ-level : ∀ a → lev K₂ω (rᴺ a) ≡ read0 (nrm a)
rᴺ-level a = refl

νᴺ : ∀ a → Nod (read0 (nrm a))
νᴺ a = nS (νᴮ (G.suc (nrm a)) (γ a))

branch₁-root : ∀ a → B₁ (G.suc a) ≡
  G.lc (rᴺ a) (cO (read0 (nrm a)))
    (plusΩ G.top (plusΩ (Gκ a) (keepAll (read0 (nrm a)) (νᴺ a) (cO (read0 (nrm a))))))
    (λ ζ e → plusΩ G.top (plusΩ (Gκ a) (keepAll (read0 (nrm a)) (νᴺ a) ζ)))
branch₁-root a = refl

branch₂-root : ∀ a → B₂ (G.suc a) ≡
  G.lc (rᴺ a) (cO (read0 (nrm a)))
    (plusΩ P₁ (Φˢ⁺ (plusΩ G.top (plusΩ (Gκ a)
      (keepAll (read0 (nrm a)) (νᴺ a) (cO (read0 (nrm a))))))))
    (λ ζ e → plusΩ P₁ (Φˢ⁺ (plusΩ G.top (plusΩ (Gκ a) (keepAll (read0 (nrm a)) (νᴺ a) ζ)))))
branch₂-root a = refl
```

## 2 起点那一支

坐标 1 的那一支：结点在第 1 支的根槽位上，层号 0，下界 1。第 1 个链点里它的各支都在主干片段 `Tr` 里 (没有分支槽位上的结点)；
下界那一支是 ℕ 极限，第 0 项是 `top + (t₀ + top)`，其中 `t₀ + top` 是加法的替代行 `topᴬ t₀`。

```agda
start-level : lev K₂ω (rᴺ G.zero) ≡ zero
start-level = refl

start-bound : cO (read0 (nrm G.zero)) ≡ raw1
start-bound = refl

KA₀-tr : ∀ (ν : Nod zero) ζ → Tr (keepAll zero ν ζ)
KA₀-tr ν G.zero = tt
KA₀-tr ν (G.suc a) = copiesΩ-tr (keepAll zero ν a) (KA₀-tr ν a)
KA₀-tr ν (G.lim f) = λ n → KA₀-tr ν (f n)
KA₀-tr ν G.top = copiesΩ-tr G.top tt

start₁-trunk : ∀ ζ → Tr (plusΩ G.top (plusΩ t₀ (keepAll zero (νᴺ G.zero) ζ)))
start₁-trunk ζ =
  plus-tr G.top (plusΩ t₀ (keepAll zero (νᴺ G.zero) ζ)) tt
    (plus-tr t₀ (keepAll zero (νᴺ G.zero) ζ) (F₁-tr G.top) (KA₀-tr (νᴺ G.zero) ζ))

start₁-low : plusΩ G.top (plusΩ t₀ (keepAll zero (νᴺ G.zero) raw1)) ≡
  G.lim (λ n → plusΩ G.top (plusΩ t₀ (copiesΩ G.top n)))
start₁-low = refl

start₁-term₀ : plusΩ G.top (plusΩ t₀ (copiesΩ G.top 0)) ≡ plusΩ G.top (topᴬ t₀)
start₁-term₀ = refl
```

## 3 `top` 的叶与 `Φˢ⁺` 在它上面的像

加法把被加数放到 `top` 的展开之下：`x + top` 的下界那一支是 `suc (x + top₁)`，`x + top₁` 的下界那一支是 `suc x`。
所以第 1 个链点里有字面的叶 `top`；第 2 个链点里 `Φˢ⁺` 把它换成 `topᴺ`，外面再加 `P₁`：这就是 `N₂`。

```agda
top₁ : RΩ → RΩ
top₁ x = add (suc zero) alg₁ x G.top

topᴬ-low : ∀ x → add zero alg₀ (top₁ x) raw1 ≡ G.suc (top₁ x)
topᴬ-low x = refl

top₁-node : ∀ x → top₁ x ≡ G.lc first₂ raw1 (G.suc x) (λ η e → add zero alg₀ x η)
top₁-node x = refl

N₂ : RΩ
N₂ = plusΩ P₁ topᴺ

N₂-image : N₂ ≡ plusΩ P₁ (Φˢ⁺ G.top)
N₂-image = refl

N₂-root : N₂ ≡ G.lc root₂ raw1 (plusΩ P₁ t₀) (λ η e → plusΩ P₁ (Gκ η))
N₂-root = refl

-- N₂ 的第 suc a 支: 根在 rᴺ a 上, 对一切 a. 这些是别的支上的结点.
N₂-branch : ∀ a → plusΩ P₁ (Gκ (G.suc a)) ≡
  G.lc (rᴺ a) (cO (read0 (nrm a)))
    (plusΩ P₁ (plusΩ (Gκ a) (keepAll (read0 (nrm a)) (νᴺ a) (cO (read0 (nrm a))))))
    (λ ζ e → plusΩ P₁ (plusΩ (Gκ a) (keepAll (read0 (nrm a)) (νᴺ a) ζ)))
N₂-branch a = refl

-- 被加数出现在 top 的叶之下.
plus-top : plusΩ P₁ G.top ≡ G.lc root₂ raw1 (top₁ P₁) (λ η e → add zero alg₀ (top₁ P₁) η)
plus-top = refl
```
