# YiOmFold：目标是 `tw 2` 自己的折叠对一切树，与用归一行推进的链点

**判决 (编译定理)：`Φˢ⁺ : Raw (tw 2) → Raw (tw 2)` 对一切树有定义，合法，保持第一位置；每个结点 (主干的与分支的) 都保留在自己的位置上 (`Φˢ⁺-keep`)，分支的孩子逐槽位搬进来。
只有 `top` 的行不是本该有的：取归一行 `topᴺ`。用它推进，`Ω₁⁺` 的链点 `pointsᴺ n` 对一切 `n` 写得出，是带守卫的坐标，严格增长。** 缺的是观察：
目标层 0 的折叠在 `pointsᴺ 1` 上已经没有定义 (`YiOmFoldNorm.point₁ᴺ-not-dom`)。所以这里没有闭项，也没有值。有闭项的那条链在 [YiOmFoldTop](YiOmFoldTop.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiOmFoldChain where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1; up)
open import OCF.Align.YiIrrIf using (R; read0)
open import OCF.Align.YiIrrFbRaw using (Cp-tr)
open import OCF.Align.YiLvIf using (lev; Kept)
open import OCF.Align.YiLvFoldAdd using (Pos)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; first₂; br)
open import OCF.Align.YiOmFoldBase
open import OCF.Align.YiOmFold using (F₀; F₁; F₀-dn; F₁-dn; F₁-cp; F₀-legal; F₁-legal;
  F₀-nested; F₁-nested; F₀-pos; F₁-pos; t₀)
open import OCF.Align.YiOmFoldNorm
```

## 1 折叠

结点的行对一切位置一样：保留在原位。分支的孩子 `em (η , e) T` 带相关的守卫，用 `keepAll` 搬到第 `η` 支的槽位上。

```agda
Φˢ⁺ : RΩ → RΩ
Φˢ⁺ G.zero = G.top
Φˢ⁺ (G.suc a) = successorΩ (Φˢ⁺ a)
Φˢ⁺ (G.lim f) = G.lim (λ n → Φˢ⁺ (f n))
Φˢ⁺ (G.lc r c t g) = G.lc r c (Φˢ⁺ t) (λ η e → Φˢ⁺ (g η e))
Φˢ⁺ (G.em (inj₁ _) a) = F₀ a
Φˢ⁺ (G.em (inj₂ (inj₁ _)) a) = F₁ a
Φˢ⁺ (G.em (inj₂ (inj₂ (η , e))) a) = keepAll (read0 η) (νᴮ η e) a
Φˢ⁺ G.top = topᴺ

Φˢ⁺-pos : ∀ ξ → Pos K₂ω (Φˢ⁺ ξ)
Φˢ⁺-pos G.zero = tt
Φˢ⁺-pos (G.suc a) = tt
Φˢ⁺-pos (G.lim f) = tt
Φˢ⁺-pos (G.lc r c t g) = tt
Φˢ⁺-pos (G.em (inj₁ _) a) = F₀-pos a
Φˢ⁺-pos (G.em (inj₂ (inj₁ _)) a) = F₁-pos a
Φˢ⁺-pos (G.em (inj₂ (inj₂ (η , e))) a) = KA-pos (read0 η) (rplain η) (νᴮ η e) (lawᴮ η e) a
Φˢ⁺-pos G.top = tt

Φˢ⁺-cp : ∀ {ξ ξ′} → Cp K₂ω ξ ξ′ → Cp K₂ω (Φˢ⁺ ξ) (Φˢ⁺ ξ′)
Φˢ⁺-dn : ∀ {ξ} ξ′ → Dn K₂ω ξ ξ′ → Dn K₂ω (Φˢ⁺ ξ) (Φˢ⁺ ξ′)
Φˢ⁺-cp (inj₁ refl) = inj₁ refl
Φˢ⁺-cp {ξ′ = ξ′} (inj₂ p) = inj₂ (Φˢ⁺-dn ξ′ p)
Φˢ⁺-dn (G.suc b) p = zero , Φˢ⁺-cp p
Φˢ⁺-dn (G.lim f) (n , p) = n , Φˢ⁺-cp p
Φˢ⁺-dn (G.lc r c t g) p = Φˢ⁺-cp p
Φˢ⁺-dn {G.em (inj₁ _) a} (G.em (inj₁ _) T) p = F₀-dn T p
Φˢ⁺-dn {G.em (inj₂ (inj₁ _)) a} (G.em (inj₂ (inj₁ _)) T) p = F₁-dn T p
Φˢ⁺-dn {G.em (inj₂ (inj₂ (η , e))) a} (G.em (inj₂ (inj₂ .(η , e))) T) (refl , p) =
  KA-dn (read0 η) (rplain η) (νᴮ η e) (lawᴮ η e) T p
Φˢ⁺-dn {G.em (inj₂ (inj₁ _)) a} G.top p = F₁-cp p

Φˢ⁺-legal : ∀ ξ → Lgl K₂ω ξ → Lgl K₂ω (Φˢ⁺ ξ)
Φˢ⁺-legal G.zero l = tt
Φˢ⁺-legal (G.suc a) l = copiesΩ-step (Φˢ⁺ a) , copiesΩ-legal (Φˢ⁺ a) (Φˢ⁺-legal a l)
Φˢ⁺-legal (G.lim f) (st , lf) = (λ n → Φˢ⁺-cp (st n)) , (λ n → Φˢ⁺-legal (f n) (lf n))
Φˢ⁺-legal (G.lc r c t g) (tg , dir , irr , lt , lg) =
  (λ η e → Φˢ⁺-cp (tg η e)) , (λ η e η′ e′ q → Φˢ⁺-cp (dir η e η′ e′ q)) ,
  (λ η e e′ → refl) , Φˢ⁺-legal t lt , (λ η e → Φˢ⁺-legal (g η e) (lg η e))
Φˢ⁺-legal (G.em (inj₁ _) a) l = F₀-legal a l
Φˢ⁺-legal (G.em (inj₂ (inj₁ _)) a) l = F₁-legal a l
Φˢ⁺-legal (G.em (inj₂ (inj₂ (η , e))) a) l =
  KA-legal (read0 η) (rplain η) (νᴮ η e) (lawᴮ η e) a l
Φˢ⁺-legal G.top l = topᴺ-legal

Φˢ⁺-nested : ∀ ξ → Nested K₂ω ξ → Nested K₂ω (Φˢ⁺ ξ)
Φˢ⁺-nested G.zero nb = tt
Φˢ⁺-nested (G.suc a) nb = copiesΩ-nested (Φˢ⁺ a) (Φˢ⁺-nested a nb)
Φˢ⁺-nested (G.lim f) nb = λ n → Φˢ⁺-nested (f n) (nb n)
Φˢ⁺-nested (G.lc r c t g) (l , nl , nt , ng) =
  l , nl , Φˢ⁺-nested t nt , (λ η e → Φˢ⁺-nested (g η e) (ng η e))
Φˢ⁺-nested (G.em (inj₁ _) a) nb = F₀-nested a
Φˢ⁺-nested (G.em (inj₂ (inj₁ _)) a) nb = F₁-nested a nb
Φˢ⁺-nested (G.em (inj₂ (inj₂ (η , e))) a) nb =
  KA-nested (read0 η) (rplain η) (νᴮ η e) (lawᴮ η e) a nb
Φˢ⁺-nested G.top nb = topᴺ-nested
```

派发完全：目标是 `tw 2` 自己时每个位置都是槽位，输出是那个位置上的保留结点。分支的孩子的根结点落在那一支的根槽位上。

```agda
Φˢ⁺-keep : ∀ r c t g → Kept K₂ω (lev K₂ω r) (Φˢ⁺ (G.lc r c t g))
Φˢ⁺-keep r c t g = r , refl , c , _ , _ , refl

Φˢ⁺-kid-row : ∀ η (e : Gd zero raw1 η) T →
  Φˢ⁺ (G.em (inj₂ (inj₂ (η , e))) T) ≡ keepAll (read0 η) (νᴮ η e) T
Φˢ⁺-kid-row η e T = refl

Φˢ⁺-top-row : Φˢ⁺ G.top ≡ G.lc root₂ raw1 t₀ (λ η e → Gκ η)
Φˢ⁺-top-row = refl
```

## 2 链点

起点 `top`，下一点是这一点加上 `Φˢ⁺` 在这一点的输出。链点合法、带嵌套证据，是下界 `top` 的带守卫坐标，严格增长。

```agda
pointsᴺ : ℕ → RΩ
pointsᴺ zero = G.top
pointsᴺ (suc n) = plusΩ (pointsᴺ n) (Φˢ⁺ (pointsᴺ n))

pointsᴺ-legal : ∀ n → Lgl K₂ω (pointsᴺ n)
pointsᴺ-legal zero = tt
pointsᴺ-legal (suc n) =
  plus-lgl (pointsᴺ n) (Φˢ⁺ (pointsᴺ n)) (pointsᴺ-legal n) (Φˢ⁺-legal (pointsᴺ n) (pointsᴺ-legal n))

pointsᴺ-nested : ∀ n → Nested K₂ω (pointsᴺ n)
pointsᴺ-nested zero = tt
pointsᴺ-nested (suc n) =
  plus-ns (pointsᴺ n) (Φˢ⁺ (pointsᴺ n)) (pointsᴺ-nested n)
    (Φˢ⁺-nested (pointsᴺ n) (pointsᴺ-nested n))

pointsᴺ-grow : ∀ n → Dn K₂ω (pointsᴺ n) (pointsᴺ (suc n))
pointsᴺ-grow n = plus-grow (pointsᴺ n) (Φˢ⁺ (pointsᴺ n)) (Φˢ⁺-pos (pointsᴺ n))

pointsᴺ-guard : ∀ n → Gd K₂ω G.top (pointsᴺ n)
pointsᴺ-guard zero = inj₁ refl , tt , tt
pointsᴺ-guard (suc n) =
  Cp-tr K₂ω (proj₁ (pointsᴺ-guard n)) (inj₂ (pointsᴺ-grow n)) ,
  pointsᴺ-legal (suc n) , pointsᴺ-nested (suc n)

-- 第 n 个链点上 Ω₁⁺ 的分支 (读回).
branchᴺ : ℕ → LF
branchᴺ n = up K₂ω (pointsᴺ n) (pointsᴺ-nested n)

pointsᴺ-one : pointsᴺ 1 ≡ point₁ᴺ
pointsᴺ-one = refl
```
