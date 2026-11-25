# YiIrrNeg 第 4 项：新块上 `Legal` 对 Ω̂ 封闭

否定路对 "块本身" 的检查。任务是在无关证据块 ([RR5IrrCore](RR5IrrCore.lagda.md)) 上，
用 [YiIrrIf](YiIrrIf.lagda.md) 的 `Legal`，找一棵 `Legal x` 而 `Ω̂ x` 不 `Legal` 的树，或证明封闭。

**结论（编译定理）。** 没有这样的树：`Legal-Ω̂ : ∀ x → Legal x → Legal (Ω̂ x)` 对一切 `x` 成立，
一步，不按阶段。同时得到读回的合法性 `lgl→Legal`（块里合法的值读成合法的层号）、
`Ω̂` 保持第一位置 `Ω̂-CP`、全塔与 Λ 的合法性。证明是旧块 `LevelFixVal` §4、§5 的逐行搬运，
多出来的只是把坐标的嵌套证据传到读回的无关参数上；没有一处把无关的证据当数据用。

**本篇没有的。** 折叠、序数值、`Only0` 的封闭（`Ω̂` 会造出层号不为 0 的结点，`Only0` 本来就不封闭）。
这里的 `Legal` 只说层号的形状合法。

这是构造路与下一步都要的引理；已在这里证明，不必重复。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrNegLegal where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck
open import OCF.Align.YiIrrIf
```

## 1 块里的位置读到层号上

`fstN`：读回的 Ω 结点以它的第一支为第一位置。`cp→CP`：块里的第一位置读成层号上的第一位置。
两条的嵌套证据都是无关参数，自反情形因此仍是 `self`。

```agda
fstN : ∀ y r c .(l : LglLow y r c) .(b : NestedLow y r c) t
  (g : (η : Low y r) → .(GdL y r c η) → LF) {a} →
  CP a t → CP a (upN y r c l b t g)
fstN (suc k) (inj₁ _) c l b t g p = fst p
fstN (suc k) (inj₂ r) c l b t g p = fstN k r c l b t g p
fstN (lim f) (n , r) c l b t g p = fstN (f n) r c l b t g p
fstN (lc k c₀ w₀ b₀ t₀ g₀) (inj₁ (inj₁ _)) c l b t g p = fst p
fstN (lc k c₀ w₀ b₀ t₀ g₀) (inj₁ (inj₂ r)) c l b t g p = fstN k r c l b t g p
fstN (lc k c₀ w₀ b₀ t₀ g₀) (inj₂ (inj₁ r)) c l b t g p = fstN t₀ r c l b t g p
fstN (lc k c₀ w₀ b₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c l b t g p =
  fstN (g₀ η e) r c l b t g p

cp→CP : ∀ y {a b} .(na : Nested y a) .(nb : Nested y b) →
  Cp y a b → CP (up y a na) (up y b nb)
dn→CP : ∀ y {a} b .(na : Nested y a) .(nb : Nested y b) →
  Dn y a b → CP (up y a na) (up y b nb)
dnk→CP : ∀ y i i′ {a b} .(na : NestedKid y i a) .(nb : NestedKid y i′ b) →
  DnK y i i′ a b → CP (upK y i a na) (upK y i′ b nb)

cp→CP y na nb (inj₁ refl) = self
cp→CP y {b = b} na nb (inj₂ p) = dn→CP y b na nb p

dn→CP y (G.suc b) na nb p = suc (cp→CP y na nb p)
dn→CP y (G.lim f) na nb (n , p) = lim n (cp→CP y na (nb n) p)
dn→CP y (G.lc r c t g) na nb p =
  fstN y r c (proj₁ nb) (proj₁ (proj₂ nb))
    (up y t (proj₁ (proj₂ (proj₂ nb))))
    (λ η e → up y (g η e) (proj₂ (proj₂ (proj₂ nb)) η e))
    (cp→CP y na (proj₁ (proj₂ (proj₂ nb))) p)
dn→CP y {a = G.em i′ _} (G.em i T) na nb p = dnk→CP y i′ i na nb p
dn→CP (suc k) {G.em _ _} G.top na nb p = fst (cp→CP k na tt p)
dn→CP (lc k c w b t g) {G.em (inj₂ (inj₁ _)) _} G.top na nb p =
  fst (cp→CP t na tt p)

dnk→CP (suc k) _ _ {b = b} na nb p = dn→CP k b na nb p
dnk→CP (lim f) n .n {b = b} na nb (refl , p) = dn→CP (f n) b na nb p
dnk→CP (lc k c w₀ b₀ t g) (inj₁ _) (inj₁ _) {b = b} na nb p = dn→CP k b na nb p
dnk→CP (lc k c w₀ b₀ t g) (inj₂ (inj₁ _)) (inj₂ (inj₁ _)) {b = b} na nb p =
  dn→CP t b na nb p
dnk→CP (lc k c w₀ b₀ t g) (inj₂ (inj₂ (η , e))) (inj₂ (inj₂ .(η , e))) {b = b}
  na nb (refl , p) = dn→CP (g η e) b na nb p

legalN : ∀ y r c .(l : LglLow y r c) .(b : NestedLow y r c) t
  (g : (η : Low y r) → .(GdL y r c η) → LF) → Legal y →
  (∀ η (e : GdL y r c η) → CP t (g η e)) →
  (∀ η (e : GdL y r c η) η′ (e′ : GdL y r c η′) →
     GdL y r η η′ → CP (g η e) (g η′ e′)) →
  (∀ η (e e′ : GdL y r c η) → g η e ≡ g η e′) →
  Legal t → (∀ η (e : GdL y r c η) → Legal (g η e)) →
  Legal (upN y r c l b t g)
legalN (suc k) (inj₁ _) c l b t g L p q i u v = L , p , q , i , u , v
legalN (suc k) (inj₂ r) c l b t g L p q i u v = legalN k r c l b t g L p q i u v
legalN (lim f) (n , r) c l b t g L p q i u v =
  legalN (f n) r c l b t g (proj₂ L n) p q i u v
legalN (lc k c₀ w₀ b₀ t₀ g₀) (inj₁ (inj₁ _)) c l b t g L p q i u v =
  proj₁ L , p , q , i , u , v
legalN (lc k c₀ w₀ b₀ t₀ g₀) (inj₁ (inj₂ r)) c l b t g L p q i u v =
  legalN k r c l b t g (proj₁ L) p q i u v
legalN (lc k c₀ w₀ b₀ t₀ g₀) (inj₂ (inj₁ r)) c l b t g
  (_ , _ , _ , _ , lt , _) p q i u v = legalN t₀ r c l b t g lt p q i u v
legalN (lc k c₀ w₀ b₀ t₀ g₀) (inj₂ (inj₂ (η , e , r))) c l b t g
  (_ , _ , _ , _ , _ , lg) p q i u v =
  legalN (g₀ η e) r c l b t g (lg η e) p q i u v
```

## 2 闭包定理

`Ω̂-CP`：Ω̂ 保持第一位置。`Legal-Ω̂` 与 `lgl→Legal` 互递归：读到 `top` 时要的正是 `Legal-Ω̂` 自己。
`irr` 一项在两处都是 `refl`（守卫是无关参数）。

```agda
cO-CP : ∀ k {η} .(nb : Nested k η) → Cp k (cO k) η → CP (Ω̂ k) (up k η nb)
cO-CP zero nb p = cp→CP zero tt nb p
cO-CP (suc k) nb p = cp→CP (suc k) tt nb p
cO-CP (lim f) nb p = cp→CP (lim f) tt nb p
cO-CP (lc k c w b t g) nb p = cp→CP (lc k c w b t g) tt nb p

Ω̂-CP : ∀ {a b} → CP a b → CP (Ω̂ a) (Ω̂ b)
Ω̂-CP self = self
Ω̂-CP (suc p) = fst (Ω̂-CP p)
Ω̂-CP (lim n p) = lim n (Ω̂-CP p)
Ω̂-CP (fst p) = fst (Ω̂-CP p)

Legal-Ω̂ : ∀ x → Legal x → Legal (Ω̂ x)
lgl→Legal : ∀ y → Legal y → ∀ T .(nb : Nested y T) → Lgl y T → Legal (up y T nb)
lglK→Legal : ∀ y → Legal y → ∀ i T .(nb : NestedKid y i T) →
  LglK y i T → Legal (upK y i T nb)

Legal-Ω̂ zero L = tt
Legal-Ω̂ (suc k) L =
  L ,
  (λ η e → cO-CP k (proj₂ (proj₂ e)) (proj₁ e)) ,
  (λ η e η′ e′ d → cp→CP k (proj₂ (proj₂ e)) (proj₂ (proj₂ e′)) (proj₁ d)) ,
  (λ η e e′ → refl) ,
  Legal-Ω̂ k L ,
  (λ η e → lgl→Legal k L η (proj₂ (proj₂ e)) (proj₁ (proj₂ e)))
Legal-Ω̂ (lim f) (st , L) =
  (λ n → Ω̂-CP (st n)) , (λ n → Legal-Ω̂ (f n) (L n))
Legal-Ω̂ (lc k c w b t g) (Lk , tg , dir , irr , Lt , Lg) =
  Lk ,
  (λ η e → Ω̂-CP (tg η e)) ,
  (λ η e η′ e′ d → Ω̂-CP (dir η e η′ e′ d)) ,
  (λ η e e′ → refl) ,
  Legal-Ω̂ t Lt ,
  (λ η e → Legal-Ω̂ (g η e) (Lg η e))

lgl→Legal y L G.zero nb l = tt
lgl→Legal y L (G.suc a) nb l = lgl→Legal y L a nb l
lgl→Legal y L (G.lim f) nb (st , l) =
  (λ n → cp→CP y (nb n) (nb (suc n)) (st n)) ,
  (λ n → lgl→Legal y L (f n) (nb n) (l n))
lgl→Legal y L (G.lc r c t g) nb (tg , dir , irr , lt , lg) =
  legalN y r c (proj₁ nb) (proj₁ (proj₂ nb))
    (up y t (proj₁ (proj₂ (proj₂ nb))))
    (λ η e → up y (g η e) (proj₂ (proj₂ (proj₂ nb)) η e)) L
    (λ η e → cp→CP y (proj₁ (proj₂ (proj₂ nb)))
      (proj₂ (proj₂ (proj₂ nb)) η e) (tg η e))
    (λ η e η′ e′ d → cp→CP y (proj₂ (proj₂ (proj₂ nb)) η e)
      (proj₂ (proj₂ (proj₂ nb)) η′ e′) (dir η e η′ e′ d))
    (λ η e e′ → refl)
    (lgl→Legal y L t (proj₁ (proj₂ (proj₂ nb))) lt)
    (λ η e → lgl→Legal y L (g η e) (proj₂ (proj₂ (proj₂ nb)) η e) (lg η e))
lgl→Legal y L (G.em i T) nb l = lglK→Legal y L i T nb l
lgl→Legal y L G.top nb l = Legal-Ω̂ y L

lglK→Legal (suc k) L _ T nb l = lgl→Legal k L T nb l
lglK→Legal (lim f) L n T nb l = lgl→Legal (f n) (proj₂ L n) T nb l
lglK→Legal (lc k c w b t g) L (inj₁ _) T nb l = lgl→Legal k (proj₁ L) T nb l
lglK→Legal (lc k c w b t g) (_ , _ , _ , _ , Lt , _) (inj₂ (inj₁ _)) T nb l =
  lgl→Legal t Lt T nb l
lglK→Legal (lc k c w b t g) (_ , _ , _ , _ , _ , Lg) (inj₂ (inj₂ (η , e))) T nb l =
  lgl→Legal (g η e) (Lg η e) T nb l
```

## 3 推论：塔与 Λ

```agda
tw-step : ∀ n → CP (tw n) (tw (suc n))
tw-step zero = suc self
tw-step (suc n) = Ω̂-CP (tw-step n)

Legal-tw : ∀ n → Legal (tw n)
Legal-tw zero = tt
Legal-tw (suc n) = Legal-Ω̂ (tw n) (Legal-tw n)

Legal-Λ : Legal Λ
Legal-Λ = tw-step , Legal-tw

Legal-ΩΛ : Legal (Ω̂ Λ)
Legal-ΩΛ = Legal-Ω̂ Λ Legal-Λ

-- 与接口文件里手写的实例一致: 规范 Ω₁ 的合法性也可由闭包定理得到.
Ω₁-legal′ : Legal (tw 2)
Ω₁-legal′ = Legal-tw 2
```

## 结论与范围

| 档 | 结果 |
|---|---|
| 编译定理 | `Legal-Ω̂`：新块上 `Legal x → Legal (Ω̂ x)`，对一切 `x` |
| 编译定理 | `lgl→Legal`：`Legal y`、`Lgl y T` 推出 `Legal (up y T nb)`，对一切层号 `y` 与一切嵌套证据 |
| 编译定理 | `Ω̂-CP`、`cp→CP`：Ω̂ 与读回保持第一位置 |
| 编译定理 | `Legal-tw`、`Legal-Λ`、`Legal-ΩΛ`：全塔、Λ、Ω_Λ 合法 |
| 未找到 | `Legal x` 而 `Ω̂ x` 不 `Legal` 的树：由 `Legal-Ω̂` 可知不存在 |

前提可满足：`Legal x` 有闭实例（`Legal-tw n`）。没有 Funext，没有公设，没有洞。
翻译账：只搬运旧块的树侧引理，没有新构造子、新字段，没有记号；强度没有变化。
