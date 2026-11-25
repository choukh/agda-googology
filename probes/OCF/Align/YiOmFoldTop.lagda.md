# YiOmFold 第 C、D 站：链上的位置，`Ω₁⁺` 的目标层 0 闭项

**判决 (编译定理)：闭项 `T⁺ : R` 与 `Lgl zero T⁺`，没有前提。根上的行不改：链在 `Raw (tw 2)` 里，起点 `top`，下一点是这一点加上 `Φˢ` 在这一点的输出，观察 `Φ⁰`；第 0 项是上一轮的 `T₃ᵐ`。
用了两处替代行 (`topᴬ`, `topˢ`)，所以不写读法，没有值定理。** 链点都在主干片段 `Tr` 里，结点的位置都在主干上，位置对都相连 (`tr-compare`)；这是替代行的后果，不说明本该有的链。
折叠在 [YiOmFold](YiOmFold.lagda.md)，缺的行在 [YiOmFoldGap](YiOmFoldGap.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiOmFoldTop where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1; up; tw)
open import OCF.Align.YiIrrIf using (R; iterate)
open import OCF.Align.YiIrrFbRaw using (Cp-tr)
open import OCF.Align.YiLvIf using (lev; Tri)
open import OCF.Align.YiLvFoldAdd using (Pos)
open import OCF.Align.YiRawFoldTw3 using (T₃ᵐ)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; first₂; Link; compare-link)
open import OCF.Align.YiOmIf using (Ω₁⁺)
open import OCF.Align.YiOmFoldBase
open import OCF.Align.YiOmFold
```

## 1 第 C 站：`Tr` 对链封闭，其中的位置对都相连

`Tr` 含起点 `top` (定义)，对加法封闭 (`YiOmFoldBase.plus-tr`)，对 `Φˢ` 封闭 (`YiOmFold.Φˢ-tr`)。
`Tr` 里的结点都在主干的两个位置上；主干上的位置与任何位置相连，三路由 `compare-link` 给出。`Φ⁰` 与 `Φˢ` 在 `Tr` 上本来不问比较 (一律折叠，一律保留)。

```agda
Trunk : Pre K₂ω → Set
Trunk (inj₁ (inj₁ _)) = ⊤
Trunk (inj₂ (inj₁ (inj₁ _))) = ⊤
Trunk (inj₂ (inj₂ _)) = ⊥

tr-node : ∀ r c t g → Tr (G.lc r c t g) → Trunk r
tr-node (inj₁ (inj₁ _)) c t g d = tt
tr-node (inj₂ (inj₁ (inj₁ _))) c t g d = tt

trunk-link : ∀ q q′ → Trunk q → Link q q′
trunk-link (inj₁ (inj₁ _)) q′ h = tt
trunk-link (inj₂ (inj₁ (inj₁ _))) q′ h = tt

tr-compare : ∀ r c t g r′ c′ t′ g′ → Tr (G.lc r c t g) → Tr (G.lc r′ c′ t′ g′) →
  Tri (lev K₂ω r) (lev K₂ω r′)
tr-compare r c t g r′ c′ t′ g′ d d′ =
  compare-link r r′ (trunk-link r r′ (tr-node r c t g d))
```

## 2 第 D 站：链与闭项

链点带坐标与三份无关的证书 (`Tr`, 合法性, 嵌套)。`bodyᴼ` 是目标为 `tw 2` 自己的折叠，`obsᴼ` 是目标层 0 的折叠。

```agda
record Ptᴼ : Set where
  constructor ptᴼ
  field
    atᴼ : RΩ
    .trᴼ : Tr atᴼ
    .lgᴼ : Lgl K₂ω atᴼ
    .nsᴼ : Nested K₂ω atᴼ
open Ptᴼ public using (atᴼ)

bodyᴼ : Ptᴼ → RΩ
bodyᴼ (ptᴼ ξ d l nb) = Φˢ ξ d

obsᴼ : Ptᴼ → R
obsᴼ (ptᴼ ξ d l nb) = Φ⁰ ξ (tr-dom ξ d) l nb

nextᴼ : Ptᴼ → Ptᴼ
nextᴼ (ptᴼ ξ d l nb) = ptᴼ (plusΩ ξ (Φˢ ξ d))
  (plus-tr ξ (Φˢ ξ d) d (Φˢ-tr ξ d))
  (plus-lgl ξ (Φˢ ξ d) l (Φˢ-legal ξ d l))
  (plus-ns ξ (Φˢ ξ d) nb (Φˢ-nested ξ d nb))

startᴼ : Ptᴼ
startᴼ = ptᴼ G.top tt tt tt

pointsᴼ : ℕ → Ptᴼ
pointsᴼ = iterate nextᴼ startᴼ

T⁺ : R
T⁺ = G.lim (λ n → obsᴼ (pointsᴼ n))
```

合法性的证明要相关的证书，沿链另算一遍。相邻两项：这一点是下一点的第一位置 (加法弱增长)，`Φ⁰` 保持第一位置。

```agda
trᶜ : ∀ n → Tr (atᴼ (pointsᴼ n))
trᶜ zero = tt
trᶜ (suc n) = plus-tr (atᴼ (pointsᴼ n)) (bodyᴼ (pointsᴼ n)) (trᶜ n)
  (Φˢ-tr (atᴼ (pointsᴼ n)) (trᶜ n))

lgᶜ : ∀ n → Lgl K₂ω (atᴼ (pointsᴼ n))
lgᶜ zero = tt
lgᶜ (suc n) = plus-lgl (atᴼ (pointsᴼ n)) (bodyᴼ (pointsᴼ n)) (lgᶜ n)
  (Φˢ-legal (atᴼ (pointsᴼ n)) (trᶜ n) (lgᶜ n))

nsᶜ : ∀ n → Nested K₂ω (atᴼ (pointsᴼ n))
nsᶜ zero = tt
nsᶜ (suc n) = plus-ns (atᴼ (pointsᴼ n)) (bodyᴼ (pointsᴼ n)) (nsᶜ n)
  (Φˢ-nested (atᴼ (pointsᴼ n)) (trᶜ n) (nsᶜ n))

obsᴼ-step : ∀ n → Cp zero (obsᴼ (pointsᴼ n)) (obsᴼ (pointsᴼ (suc n)))
obsᴼ-step n =
  Φ⁰-cp (atᴼ (pointsᴼ (suc n)))
    (tr-dom (atᴼ (pointsᴼ n)) (trᶜ n)) (tr-dom (atᴼ (pointsᴼ (suc n))) (trᶜ (suc n)))
    (lgᶜ n) (nsᶜ n) (lgᶜ (suc n)) (nsᶜ (suc n))
    (plus-weak (atᴼ (pointsᴼ n)) (bodyᴼ (pointsᴼ n)))

T⁺-legal : Lgl zero T⁺
T⁺-legal = obsᴼ-step ,
  (λ n → Φ⁰-legal (atᴼ (pointsᴼ n)) (tr-dom (atᴼ (pointsᴼ n)) (trᶜ n)) (lgᶜ n) (nsᶜ n))
```

## 3 根上的行

都是 `refl`。`guards⁺` 说链点是 `Ω₁⁺` 的带守卫坐标，`T⁺-branch` 说第 `n` 项折的是 `Ω₁⁺` 在那个坐标上的分支 (的原像)。

```agda
branch⁺ : (ξ : RΩ) → .(Gd K₂ω G.top ξ) → LF
branch⁺ ξ e = up K₂ω ξ (proj₂ (proj₂ e))

Ω₁⁺-node : Ω₁⁺ ≡ lc K₂ω G.top tt tt (tw 3) branch⁺
Ω₁⁺-node = refl

T⁺-start : atᴼ (pointsᴼ 0) ≡ G.top
T⁺-start = refl

T⁺-feedback : ∀ n → atᴼ (pointsᴼ (suc n)) ≡ plusΩ (atᴼ (pointsᴼ n)) (bodyᴼ (pointsᴼ n))
T⁺-feedback n = refl

T⁺-body : ∀ n → bodyᴼ (pointsᴼ n) ≡ Φˢ (atᴼ (pointsᴼ n)) (trᶜ n)
T⁺-body n = refl

T⁺-term : ∀ n → obsᴼ (pointsᴼ n) ≡
  Φ⁰ (atᴼ (pointsᴼ n)) (tr-dom (atᴼ (pointsᴼ n)) (trᶜ n)) (lgᶜ n) (nsᶜ n)
T⁺-term n = refl

T⁺-grow : ∀ n → Dn K₂ω (atᴼ (pointsᴼ n)) (atᴼ (pointsᴼ (suc n)))
T⁺-grow n = plus-grow (atᴼ (pointsᴼ n)) (bodyᴼ (pointsᴼ n))
  (Φˢ-pos (atᴼ (pointsᴼ n)) (trᶜ n))

guards⁺ : ∀ n → Gd K₂ω G.top (atᴼ (pointsᴼ n))
guards⁺ zero = inj₁ refl , tt , tt
guards⁺ (suc n) =
  Cp-tr K₂ω (proj₁ (guards⁺ n)) (inj₂ (T⁺-grow n)) , lgᶜ (suc n) , nsᶜ (suc n)

T⁺-branch : ∀ n → branch⁺ (atᴼ (pointsᴼ n)) (guards⁺ n) ≡ up K₂ω (atᴼ (pointsᴼ n)) (nsᶜ n)
T⁺-branch n = refl
```

第 0 项是 `tw 3` 的闭项，所以它是 `T⁺` 的第一位置。第 1 个链点展开：`top` 加上 `top` 的替代行，是根槽位上的结点。

```agda
T⁺-term₀ : obsᴼ (pointsᴼ 0) ≡ T₃ᵐ
T⁺-term₀ = refl

T₃ᵐ-first : Dn zero T₃ᵐ T⁺
T₃ᵐ-first = zero , inj₁ refl

T⁺-point₁ : atᴼ (pointsᴼ 1) ≡
  G.lc root₂ raw1 (plusΩ G.top t₀) (λ η e → plusΩ G.top (plusΩ t₀ (F₀ η)))
T⁺-point₁ = refl
```
