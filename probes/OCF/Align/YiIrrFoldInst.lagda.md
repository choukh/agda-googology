# YiIrrFold 规范实例：加法封闭，Ω₁·n 及其极限，Ω₁²

构造路的第三件，交付 (b)。折叠是 [YiIrrFold](YiIrrFold.lagda.md) 的同一个 `ψ`，本篇不另写折叠；
只把树放进定义域 `Dom`，再把接口的行在这些树上读出来。

- `_+ᴸ_`：层号的加法，照 `LevelFixVal._+ᴸ_` 搬到新块 (结点里的两份无关证明原样带过去)。
- `add-dom`：`Dom` 对加法封闭。于是 Ω₁+Ω₁，Ω₁·(n+1)，以及它们的极限都在 `Dom` 里。
- `Ω₁²`：分支是 `η ↦ Ω₁·η`，分支里 Ω 结点的嵌套深度随坐标变化。它也在 `Dom` 里。

本篇没有值；值在 [YiIrrFoldValue](YiIrrFoldValue.lagda.md)，只覆盖 Ω₁，Ω₁·(n+1) 与极限，不覆盖 Ω₁²。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiIrrFoldInst where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (tw)
open import OCF.Align.YiIrrIf
open import OCF.Align.YiIrrFoldBase
open import OCF.Align.YiIrrFold
```

## 1 层号的加法，`Dom` 对它封闭

```agda
infixl 6 _+ᴸ_
_+ᴸ_ : LF → LF → LF
a +ᴸ zero = a
a +ᴸ suc x = suc (a +ᴸ x)
a +ᴸ lim f = lim (λ n → a +ᴸ f n)
a +ᴸ lc k c w b t g = lc k c w b (a +ᴸ t) (λ η e → a +ᴸ g η e)

add-CP : ∀ a {x y} → CP x y → CP (a +ᴸ x) (a +ᴸ y)
add-CP a self = self
add-CP a (suc p) = suc (add-CP a p)
add-CP a (lim n p) = lim n (add-CP a p)
add-CP a (fst p) = fst (add-CP a p)

add-Legal : ∀ a x → Legal a → Legal x → Legal (a +ᴸ x)
add-Legal a zero la lx = la
add-Legal a (suc x) la lx = add-Legal a x la lx
add-Legal a (lim f) la (st , lf) =
  (λ n → add-CP a (st n)) , (λ n → add-Legal a (f n) la (lf n))
add-Legal a (lc k c w b t g) la (lk , tg , dir , irr , lt , lg) =
  lk ,
  (λ η e → add-CP a (tg η e)) ,
  (λ η e η′ e′ q → add-CP a (dir η e η′ e′ q)) ,
  (λ η e e′ → refl) ,
  add-Legal a t la lt ,
  (λ η e → add-Legal a (g η e) la (lg η e))

add-Only0 : ∀ a x → Only0 a → Only0 x → Only0 (a +ᴸ x)
add-Only0 a zero oa ox = oa
add-Only0 a (suc x) oa ox = add-Only0 a x oa ox
add-Only0 a (lim f) oa ox = λ n → add-Only0 a (f n) oa (ox n)
add-Only0 a (lc zero c w b t g) oa (ot , og) =
  add-Only0 a t oa ot , (λ η e → add-Only0 a (g η e) oa (og η e))
add-Only0 a (lc (suc k) c w b t g) oa ()
add-Only0 a (lc (lim f) c w b t g) oa ()
add-Only0 a (lc (lc k c₀ w₀ b₀ t₀ g₀) c w b t g) oa ()

add-Seed : ∀ a x → Seed a → Seed x → Seed (a +ᴸ x)
add-Seed a zero sa sx = sa
add-Seed a (suc x) sa sx = add-Seed a x sa sx
add-Seed a (lim f) sa sx = λ n → add-Seed a (f n) sa (sx n)
add-Seed a (lc k c w b t g) sa (s , sg) =
  s , (λ η e → add-Seed a (g η e) sa (sg η e))

add-dom : ∀ a x → Dom a → Dom x → Dom (a +ᴸ x)
add-dom a x (oa , la , sa) (ox , lx , sx) =
  add-Only0 a x oa ox , add-Legal a x la lx , add-Seed a x sa sx
```

## 2 Ω₁·(n+1) 与它们的极限

```agda
Ω₁ : LF
Ω₁ = tw 2

sum : ℕ → LF
sum zero = Ω₁
sum (suc n) = sum n +ᴸ Ω₁

sum-dom : ∀ n → Dom (sum n)
sum-dom zero = dom-Ω₁
sum-dom (suc n) = add-dom (sum n) Ω₁ (sum-dom n) dom-Ω₁

-- 相邻两项: 前一项是后一项的字面第一位置 (后一项的第一支是前一项加一).
sum-step : ∀ n → CP (sum n) (sum (suc n))
sum-step n = fst (suc self)

limit : LF
limit = lim sum

limit-dom : Dom limit
limit-dom =
  (λ n → proj₁ (sum-dom n)) ,
  (sum-step , (λ n → proj₁ (proj₂ (sum-dom n)))) ,
  (λ n → proj₂ (proj₂ (sum-dom n)))

-- Ω₁+Ω₁ 的形状: 外层是层号 0 的 Ω 结点, 每个分支是 Ω₁ 加一个读回, 里面仍有 Ω 结点.
nested-form : sum 1 ≡
  lc zero one tt tt (suc Ω₁) (λ η e → Ω₁ +ᴸ read0 η)
nested-form = refl
```

## 3 四行在这些树上读出来

接口的行对 `Dom` 里的一切树成立，下面只是把它们用在实例上，都由 `fold-rows` 的字段或 `refl` 给出。
`append-row`：对任何前缀 `x`，`x + Ω₁` 的折叠是加法链上 "前缀加读回" 的折叠的极限。
`tail-*`：前缀加读回 `x + read0 a` 的折叠对 `a` 逐构造子展开，零处回到 `ψ x`。

```agda
module F = FoldRows fold-rows

append-row : ∀ x (d : Dom (x +ᴸ Ω₁)) → ψ (x +ᴸ Ω₁) d ≡
  G.lim (λ n → F.out one tt tt (suc x) (λ η e → x +ᴸ read0 η) d
    (iterate (F.next one tt tt (suc x) (λ η e → x +ᴸ read0 η) d)
      (start one tt tt) n))
append-row x d = F.gt-row one tt tt (suc x) (λ η e → x +ᴸ read0 η) d

append-additive : ∀ x (d : Dom (x +ᴸ Ω₁)) (η : R) .(e : Gd zero one η) →
  coordinate (F.next one tt tt (suc x) (λ η e → x +ᴸ read0 η) d (point η e)) ≡
  η +ʳ ψ (x +ᴸ read0 η) (dom-branch one tt tt (suc x) (λ η e → x +ᴸ read0 η) d η e)
append-additive x d η e = refl

tail-zero : ∀ x (d : Dom x) → ψ (x +ᴸ read0 G.zero) d ≡ ψ x d
tail-zero x d = refl

tail-suc : ∀ x a (d : Dom (x +ᴸ read0 (G.suc a))) →
  ψ (x +ᴸ read0 (G.suc a)) d ≡ successor (ψ (x +ᴸ read0 a) d)
tail-suc x a d = refl

tail-lim : ∀ x f (d : Dom (x +ᴸ read0 (G.lim f))) →
  ψ (x +ᴸ read0 (G.lim f)) d ≡
  G.lim (λ n → ψ (x +ᴸ read0 (f n)) (dom-at (λ n → x +ᴸ read0 (f n)) d n))
tail-lim x f d = refl

tail-top : ∀ x (d : Dom x) → ψ (x +ᴸ read0 G.top) d ≡ successor (ψ x d)
tail-top x d = refl

Ω₁-row : ψ Ω₁ dom-Ω₁ ≡
  G.lim (λ n → F.out one tt tt (suc zero) (λ η e → read0 η) dom-Ω₁
    (iterate (F.next one tt tt (suc zero) (λ η e → read0 η) dom-Ω₁)
      (start one tt tt) n))
Ω₁-row = F.gt-row one tt tt (suc zero) (λ η e → read0 η) dom-Ω₁

sum-row : ∀ n → ψ (sum (suc n)) (sum-dom (suc n)) ≡
  G.lim (λ m → F.out one tt tt (suc (sum n)) (λ η e → sum n +ᴸ read0 η)
    (sum-dom (suc n))
    (iterate (F.next one tt tt (suc (sum n)) (λ η e → sum n +ᴸ read0 η)
      (sum-dom (suc n))) (start one tt tt) m))
sum-row n = append-row (sum n) (sum-dom (suc n))

limit-row : ψ limit limit-dom ≡ G.lim (λ n → ψ (sum n) (sum-dom n))
limit-row = refl

sum-legal : ∀ n → Lgl zero (ψ (sum n) (sum-dom n))
sum-legal n = ψ-legal (sum n) (sum-dom n)

sum-position : ∀ n →
  Cp zero (ψ (sum n) (sum-dom n)) (ψ (sum (suc n)) (sum-dom (suc n)))
sum-position n =
  ψ-position (sum n) (sum (suc n)) (sum-dom n) (sum-dom (suc n)) (sum-step n)

limit-legal : Lgl zero (ψ limit limit-dom)
limit-legal = ψ-legal limit limit-dom

limit-positive : Dn zero G.zero (ψ limit limit-dom)
limit-positive = ψ-positive limit limit-dom
```

## 4 Ω₁²：分支里的嵌套随坐标加深

`mul η` 是 Ω₁·η：对坐标递归，后继处再加一个 Ω₁，极限逐项。`Ω₁²` 的分支就是 `mul`。
它不是 "固定前缀加读回" 的族；同一个 `ψ` 照样给出合法的正输出。这里没有值定理。

```agda
mul : R → LF
mul G.zero = zero
mul (G.suc a) = mul a +ᴸ Ω₁
mul (G.lim f) = lim (λ n → mul (f n))
mul (G.lc () c t g)
mul (G.em () a)
mul G.top = zero +ᴸ Ω₁

mul-cp : ∀ {a} b → Cp zero a b → CP (mul a) (mul b)
mul-dn : ∀ {a} b → Dn zero a b → CP (mul a) (mul b)
mul-cp b (inj₁ refl) = self
mul-cp b (inj₂ p) = mul-dn b p
mul-dn (G.suc b) p = fst (suc (mul-cp b p))
mul-dn (G.lim f) (n , p) = lim n (mul-cp (f n) p)
mul-dn (G.lc () c t g) p
mul-dn (G.em () a) p
mul-dn G.top ()

mul-only : ∀ a → Only0 (mul a)
mul-only G.zero = tt
mul-only (G.suc a) = add-Only0 (mul a) Ω₁ (mul-only a) Ω₁-only
mul-only (G.lim f) = λ n → mul-only (f n)
mul-only (G.lc () c t g)
mul-only (G.em () a)
mul-only G.top = add-Only0 zero Ω₁ tt Ω₁-only

mul-seed : ∀ a → Seed (mul a)
mul-seed G.zero = tt
mul-seed (G.suc a) = add-Seed (mul a) Ω₁ (mul-seed a) Ω₁-seed
mul-seed (G.lim f) = λ n → mul-seed (f n)
mul-seed (G.lc () c t g)
mul-seed (G.em () a)
mul-seed G.top = add-Seed zero Ω₁ tt Ω₁-seed

mul-legal : ∀ a → Lgl zero a → Legal (mul a)
mul-legal G.zero l = tt
mul-legal (G.suc a) l = add-Legal (mul a) Ω₁ (mul-legal a l) Ω₁-legal
mul-legal (G.lim f) (st , lf) =
  (λ n → mul-cp (f (suc n)) (st n)) , (λ n → mul-legal (f n) (lf n))
mul-legal (G.lc () c t g) l
mul-legal (G.em () a) l
mul-legal G.top l = add-Legal zero Ω₁ tt Ω₁-legal

Ω₁² : LF
Ω₁² = lc zero one tt tt (mul one) (λ η e → mul η)

dom-Ω₁² : Dom Ω₁²
dom-Ω₁² =
  (mul-only one , (λ η e → mul-only η)) ,
  (tt ,
   (λ η e → mul-cp η (proj₁ e)) ,
   (λ η e η′ e′ q → mul-cp η′ (proj₁ q)) ,
   (λ η e e′ → refl) ,
   mul-legal one tt ,
   (λ η e → mul-legal η (proj₁ (proj₂ e)))) ,
  ((tt , tt) , (λ η e → mul-seed η))

Ω₁²-legal : Lgl zero (ψ Ω₁² dom-Ω₁²)
Ω₁²-legal = ψ-legal Ω₁² dom-Ω₁²

Ω₁²-positive : Dn zero G.zero (ψ Ω₁² dom-Ω₁²)
Ω₁²-positive = ψ-positive Ω₁² dom-Ω₁²

-- 分支在后继坐标处: 前一支再加一个 Ω₁, 折叠在那里又走一条加法链.
Ω₁²-branch-suc : ∀ a → mul (G.suc a) ≡
  lc zero one tt tt (suc (mul a)) (λ η e → mul a +ᴸ read0 η)
Ω₁²-branch-suc a = refl
```
