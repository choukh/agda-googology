# YiRawFold 第 C 站：`tw 3` 的根

**判决 (编译定理)：闭项 `T₃ᵐ : R` 与 `Lgl zero T₃ᵐ`，没有前提。根上的行不改：起点是下界 1，链点 `η` 处的值是第 `η` 支的折叠 `Φᵐ (read0 η) … base top`，下一点是 `η` 加上它；
链点带相关的 `Lgl zero η` (读成 `Legal (read0 η)`，派发要读它)。`Φᵐ` 在极限层号的 `top` 上取部分和。** 另两种放法：`T₃ᶜ` (各支用 `Φ`，部分和放到根的坐标上，无前提)；
`Plain3.T₃ᴿ` (各支用 `Φ`，根不改，条件于 `OutCoh`，没有证)。没有值定理，读法不写成定理。折叠在 [YiRawFold](YiRawFold.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiRawFoldTw3 where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; cong; cong₂; trans)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw0-Nested; raw1; up; tw)
open import OCF.Align.YiIrrIf
  using (R; one; _+ʳ_; CP; Legal; iterate; read0; read0-cp; read0-dn; read0-legal)
open import OCF.Align.YiIrrFbRaw using (Cp-tr)
open import OCF.Align.YiIrrFoldBase using (add-legal; add-cp; lgl-cp₀; lgl-dn₀)
open import OCF.Align.YiLvIf using (Plain; up0-plain)
open import OCF.Align.YiLvNegCompare using (branch₃)
open import OCF.Align.YiLvNegRestrict
  using (restrict; restrict-add; restrict-add-weak; Coh; add-coh; restrictL; restrictL-read0)
  renaming (add-weak to add-weak⁰)
open import OCF.Align.YiLvNegCum
  using (cum; weak; cum-legal; cum-add-weak; norm-guard)
  renaming (psum to psum⁰; psum-legal to psum⁰-legal)
open import OCF.Align.YiRawIf
open import OCF.Align.YiRawFoldBase
open import OCF.Align.YiRawFold
open import OCF.Align.YiRawFoldUp using (Zp; Φᵐ-below)
```

## 1 读回的层号：`Plain` 与 `Legal` 的限制，一致

第 `η` 支的公共上界是 `read0 η`。它的 `Legal` 由 `η` 的合法性读出 (`read0-legal`)，路径数据就是那份证书里的路径，所以要相关的证书。
`read0-cohP`：一致的证书 (`YiLvNegRestrict.Coh`) 读成 `CohP`。

```agda
rplain : ∀ a → Plain (read0 a)
rplain a = up0-plain a (raw0-Nested a)

plainR-read0 : ∀ {a} b (p : Cp zero a b) →
  plainR (read0 b) (read0-cp b p) (rplain b) ≡ rplain a
plainR-read0-dn : ∀ {a} b (p : Dn zero a b) →
  plainR (read0 b) (read0-dn b p) (rplain b) ≡ rplain a
plainR-read0 b (inj₁ refl) = refl
plainR-read0 b (inj₂ p) = plainR-read0-dn b p
plainR-read0-dn (G.suc b) p = plainR-read0 b p
plainR-read0-dn (G.lim f) (n , p) = plainR-read0 (f n) p

-- 两份限制合成一对.
pair-read0 : ∀ {a} b (p : Cp zero a b) (l : Lgl zero b) →
  _≡_ {A = Plain (read0 a) × Legal (read0 a)}
    (plainR (read0 b) (read0-cp b p) (rplain b) ,
     restrictL (read0 b) (read0-cp b p) (read0-legal b l))
    (rplain a , read0-legal a (restrict p l))
pair-read0 b p l = cong₂ _,_ (plainR-read0 b p) (restrictL-read0 b p l)

read0-cohP : ∀ a (l : Lgl zero a) → Coh a l → CohP (read0 a) (rplain a) (read0-legal a l)
read0-cohP G.zero l ch = tt
read0-cohP (G.suc a) l ch = read0-cohP a l ch
read0-cohP (G.lim f) (st , lf) (cs , cf) =
  (λ n → trans (pair-read0 (f (suc n)) (st n) (lf (suc n)))
    (cong (λ z → rplain (f n) , read0-legal (f n) z) (cs n))) ,
  (λ n → read0-cohP (f n) (lf n) (cf n))
read0-cohP G.top l ch = tt
```

## 2 闭项 `T₃ᵐ`：根上的行不改

第 `η` 支是 `top` 在 `read0 η` 上的读回 (`YiRawIf.branch-is-top`)，它的折叠取接口实例 `Φᵐ` 在 `top` 处的值，合法性没有前提。
链点带坐标与它相关的合法性；下一点的合法性由加法给出。相邻两项的第一位置：`η ⊲ η + y` 读回的路径在极限处只取第 0 支 (`zp-weak`)，
`Φᵐ` 沿这样的路径保持第一位置 (`YiRawFoldUp.Φᵐ-below`)，加法的证书沿它限制回原来的 (`restrict-add-weak`)。不用一致性。

```agda
foldᵐ₃ : ∀ η → Lgl zero η → R
foldᵐ₃ η l = Φᵐ (read0 η) (rplain η) (read0-legal η l) base G.top tt tt

foldᵐ₃-legal : ∀ η (l : Lgl zero η) → Lgl zero (foldᵐ₃ η l)
foldᵐ₃-legal η l =
  RawFold.legal rawFold (read0 η) (rplain η) (read0-legal η l) base G.top tt tt

zp-weak : ∀ x y → Zp (read0-cp (x +ʳ y) (add-weak⁰ x y))
zp-weak x G.zero = tt
zp-weak x (G.suc y) = zp-weak x y
zp-weak x (G.lim f) = zp-weak x (f zero)
zp-weak x G.top = tt

foldᵐ₃-up : ∀ {η} η′ (p : Cp zero η η′) → Zp (read0-cp η′ p) → (l′ : Lgl zero η′) →
  Cp zero (foldᵐ₃ η (restrict p l′)) (foldᵐ₃ η′ l′)
foldᵐ₃-up {η} η′ p z l′ =
  subst (λ w → Cp zero (Φᵐ (read0 η) (proj₁ w) (proj₂ w) base G.top tt tt) (foldᵐ₃ η′ l′))
    (pair-read0 η′ p l′)
    (Φᵐ-below (read0 η′) (read0-cp η′ p) z (rplain η′) (read0-legal η′ l′))

record Ptᵐ : Set where
  constructor ptᵐ
  field
    coordᵐ : R
    lawfulᵐ : Lgl zero coordᵐ
open Ptᵐ

obsᵐ : Ptᵐ → R
obsᵐ p = foldᵐ₃ (coordᵐ p) (lawfulᵐ p)

obsᵐ-legal : ∀ p → Lgl zero (obsᵐ p)
obsᵐ-legal p = foldᵐ₃-legal (coordᵐ p) (lawfulᵐ p)

nextᵐ : Ptᵐ → Ptᵐ
nextᵐ p = ptᵐ (coordᵐ p +ʳ obsᵐ p)
  (add-legal (coordᵐ p) (obsᵐ p) (lawfulᵐ p) (obsᵐ-legal p))

startᵐ : Ptᵐ
startᵐ = ptᵐ one tt

pointsᵐ : ℕ → Ptᵐ
pointsᵐ = iterate nextᵐ startᵐ

T₃ᵐ : R
T₃ᵐ = G.lim (λ n → obsᵐ (pointsᵐ n))

obsᵐ-step : ∀ p → Cp zero (obsᵐ p) (obsᵐ (nextᵐ p))
obsᵐ-step p =
  subst (λ z → Cp zero (foldᵐ₃ (coordᵐ p) z) (obsᵐ (nextᵐ p)))
    (restrict-add-weak (coordᵐ p) (obsᵐ p) (lawfulᵐ p) (obsᵐ-legal p))
    (foldᵐ₃-up (coordᵐ (nextᵐ p)) (add-weak⁰ (coordᵐ p) (obsᵐ p))
      (zp-weak (coordᵐ p) (obsᵐ p)) (lawfulᵐ (nextᵐ p)))

T₃ᵐ-legal : Lgl zero T₃ᵐ
T₃ᵐ-legal = (λ n → obsᵐ-step (pointsᵐ n)) , (λ n → obsᵐ-legal (pointsᵐ n))

T₃ᵐ-nested : Nested zero T₃ᵐ
T₃ᵐ-nested = raw0-Nested T₃ᵐ
```

行，都是 `refl`；`guardsᵐ` 说链点是 `tw 3` 的带守卫坐标，`T₃ᵐ-branch` 说第 `n` 项折的是 `tw 3` 在那个坐标上的分支 (的原像 `top`)。

```agda
T₃ᵐ-start : coordᵐ (pointsᵐ 0) ≡ one
T₃ᵐ-start = refl

T₃ᵐ-term : ∀ n → obsᵐ (pointsᵐ n) ≡
  Φᵐ (read0 (coordᵐ (pointsᵐ n))) (rplain (coordᵐ (pointsᵐ n)))
    (read0-legal (coordᵐ (pointsᵐ n)) (lawfulᵐ (pointsᵐ n))) base G.top tt tt
T₃ᵐ-term n = refl

T₃ᵐ-feedback : ∀ n → coordᵐ (pointsᵐ (suc n)) ≡
  coordᵐ (pointsᵐ n) +ʳ foldᵐ₃ (coordᵐ (pointsᵐ n)) (lawfulᵐ (pointsᵐ n))
T₃ᵐ-feedback n = refl

guardsᵐ : ∀ n → Gd zero raw1 (coordᵐ (pointsᵐ n))
guardsᵐ zero = inj₁ refl , tt , tt
guardsᵐ (suc n) =
  Cp-tr zero (proj₁ (guardsᵐ n)) (add-weak⁰ (coordᵐ (pointsᵐ n)) (obsᵐ (pointsᵐ n))) ,
  lawfulᵐ (pointsᵐ (suc n)) , raw0-Nested (coordᵐ (pointsᵐ (suc n)))

T₃ᵐ-branch : ∀ n → branch₃ (coordᵐ (pointsᵐ n)) (guardsᵐ n) ≡
  up (read0 (coordᵐ (pointsᵐ n))) G.top tt
T₃ᵐ-branch n = branch-is-top (coordᵐ (pointsᵐ n)) (guardsᵐ n)

-- 第 0 项是公共上界 1 上的闭项 (读法 ψ₀(Ω_1)).
T₃ᵐ-term₀ : obsᵐ (pointsᵐ 0) ≡ Φᵐ (suc zero) tt tt base G.top tt tt
T₃ᵐ-term₀ = refl
```

## 3 各支用 `Φ`：极限层号上 `top` 取各支的极限

`fold₃ η l`：同一支用 `Φ` 折。合法性要 `CohP`，由一致的证书读出。
`fold₃-up`：`η` 是 `η′` 的第一位置，`η` 的证书是 `η′` 的证书的限制，则折叠也是第一位置 (第 B 站的 `Φ-below` 加两份限制)。

```agda
fold₃ : ∀ η → Lgl zero η → R
fold₃ η l = Φ (read0 η) (rplain η) (read0-legal η l) base G.top tt tt

fold₃-branch : ∀ η .(e : Gd zero raw1 η) →
  branch₃ η e ≡ up (read0 η) G.top tt
fold₃-branch η e = branch-is-top η e

fold₃-legal : ∀ η (l : Lgl zero η) → Coh η l → Lgl zero (fold₃ η l)
fold₃-legal η l ch =
  Φ-legal (read0 η) (rplain η) (read0-legal η l) base (read0-cohP η l ch) G.top tt tt

fold₃-up : ∀ {η} η′ (p : Cp zero η η′) (l′ : Lgl zero η′) →
  Cp zero (fold₃ η (restrict p l′)) (fold₃ η′ l′)
fold₃-up {η} η′ p l′ =
  subst (λ z → Cp zero (Φ (read0 η) (proj₁ z) (proj₂ z) base G.top tt tt) (fold₃ η′ l′))
    (pair-read0 η′ p l′)
    (below zero (read0 η′) (read0-cp η′ p) (rplain η′) (read0-legal η′ l′))
```

## 4 累加归一的证书：由树算出，一致，沿链的一步是限制

`cum-legal` 不读证书 (`YiLvNegCum`)。这里补三条：它一致；`x ⊲ x + y` 这条路径上加法的证书限制回 `x` 的；
`cum v ⊲ cum (v + y)` 这条路径上 `cum-legal` 限制回 `cum-legal v`。

```agda
restrict-weak : ∀ x y (lx : Lgl zero x) (ly : Lgl zero y) →
  restrict (weak x y) (add-legal x y lx ly) ≡ lx
restrict-weak x G.zero lx ly = refl
restrict-weak x (G.suc y) lx ly = restrict-weak x y lx ly
restrict-weak x (G.lim f) lx (st , lf) = restrict-weak x (f zero) lx (lf zero)
restrict-weak x G.top lx ly = refl

psum⁰-coh : ∀ (g : ℕ → R) (lg : ∀ n → Lgl zero (g n)) → (∀ n → Coh (g n) (lg n)) →
  ∀ n → Coh (psum⁰ g n) (psum⁰-legal g lg n)
psum⁰-coh g lg cg zero = cg zero
psum⁰-coh g lg cg (suc n) =
  add-coh (psum⁰ g n) (G.suc (g (suc n))) (psum⁰-legal g lg n) (lg (suc n))
    (psum⁰-coh g lg cg n) (cg (suc n))

cum-coh : ∀ a → Coh (cum a) (cum-legal a)
cum-coh G.zero = tt
cum-coh (G.suc a) = cum-coh a
cum-coh (G.lim f) =
  (λ n → restrict-weak (psum⁰ (λ k → cum (f k)) n) (G.suc (cum (f (suc n))))
    (psum⁰-legal (λ k → cum (f k)) (λ k → cum-legal (f k)) n) (cum-legal (f (suc n)))) ,
  psum⁰-coh (λ k → cum (f k)) (λ k → cum-legal (f k)) (λ k → cum-coh (f k))
cum-coh G.top = tt

cum-restrict : ∀ v y → restrict (cum-add-weak v y) (cum-legal (v +ʳ y)) ≡ cum-legal v
cum-restrict v G.zero = refl
cum-restrict v (G.suc y) = cum-restrict v y
cum-restrict v (G.lim f) = cum-restrict v (f zero)
cum-restrict v G.top = refl
```

## 5 闭项 `T₃ᶜ`：链点只带累计 `v`

链点的数据是累计 `v : R` 一个值，没有证书。访问的坐标 `κ v = 1 + cum v`，它是 `tw 3` 的带守卫坐标 (`YiLvNegCum.norm-guard`)；
合法性 `κ-lgl v` 由树算出。观察 `y v` 是第 `κ v` 支的折叠，下一个累计是 `v + y v`。
**这改了链的行**：不改行的链访问 `1 + v` (§6)。`cum` 把极限换成部分和；`κ v` 与 `1 + v` 的值的关系没有定理。

```agda
κ : R → R
κ v = one +ʳ cum v

κ-lgl : ∀ v → Lgl zero (κ v)
κ-lgl v = add-legal one (cum v) tt (cum-legal v)

κ-coh : ∀ v → Coh (κ v) (κ-lgl v)
κ-coh v = add-coh one (cum v) tt (cum-legal v) tt (cum-coh v)

κ-guard : ∀ v → Gd zero raw1 (κ v)
κ-guard v = norm-guard one tt v

y : R → R
y v = fold₃ (κ v) (κ-lgl v)

y-legal : ∀ v → Lgl zero (y v)
y-legal v = fold₃-legal (κ v) (κ-lgl v) (κ-coh v)

y-branch : ∀ v → branch₃ (κ v) (κ-guard v) ≡ up (read0 (κ v)) G.top tt
y-branch v = fold₃-branch (κ v) (κ-guard v)

κ-step : ∀ v a → Cp zero (κ v) (κ (v +ʳ a))
κ-step v a = add-cp one (cum-add-weak v a)

κ-restrict : ∀ v a → restrict (κ-step v a) (κ-lgl (v +ʳ a)) ≡ κ-lgl v
κ-restrict v a =
  trans (restrict-add one (cum (v +ʳ a)) (cum-add-weak v a) tt (cum-legal (v +ʳ a)))
    (cong (add-legal one (cum v) tt) (cum-restrict v a))

y-step : ∀ v a → Cp zero (y v) (y (v +ʳ a))
y-step v a =
  subst (λ z → Cp zero (fold₃ (κ v) z) (y (v +ʳ a))) (κ-restrict v a)
    (fold₃-up (κ (v +ʳ a)) (κ-step v a) (κ-lgl (v +ʳ a)))

nextᶜ : R → R
nextᶜ v = v +ʳ y v

accum : ℕ → R
accum = iterate nextᶜ G.zero

T₃ᶜ : R
T₃ᶜ = G.lim (λ n → y (accum n))

T₃ᶜ-legal : Lgl zero T₃ᶜ
T₃ᶜ-legal = (λ n → y-step (accum n) (y (accum n))) , (λ n → y-legal (accum n))

T₃ᶜ-nested : Nested zero T₃ᶜ
T₃ᶜ-nested = raw0-Nested T₃ᶜ

-- 行: 起点的坐标是下界 1; 第 n 项是第 κ (accum n) 支的折叠; 累计加上它.
T₃ᶜ-start : κ (accum 0) ≡ one
T₃ᶜ-start = refl

T₃ᶜ-term : ∀ n → y (accum n) ≡
  Φ (read0 (κ (accum n))) (rplain (κ (accum n))) (read0-legal (κ (accum n)) (κ-lgl (accum n)))
    base G.top tt tt
T₃ᶜ-term n = refl

T₃ᶜ-feedback : ∀ n → accum (suc n) ≡ accum n +ʳ y (accum n)
T₃ᶜ-feedback n = refl

-- 第 0 项是公共上界 1 上的闭项 (读法 ψ₀(Ω_1)).
T₃ᶜ-term₀ : y (accum 0) ≡ Φ (suc zero) tt tt base G.top tt tt
T₃ᶜ-term₀ = refl
```

## 6 各支用 `Φ` 而根不改：条件于输出证书一致

链点带坐标 `η`、相关的合法性 `l`、它一致的证明。下一点是 `η + fold₃ η l`，证书由加法给出；相邻两项的第一位置只用加法的限制引理 (`restrict-add-weak`)，不用前提。
前提 `OutCoh` 只用在一处：下一点的证书要一致 (极限层号上 `top` 那一行的合法性要 `CohP`)，这要折叠的输出证书一致。
`OutCoh` 没有证，也没有否定；上一轮否定路对旧的目标层 0 折叠证过同形的 `YiLvNegRestrict.ψ-legal-coh`。

```agda
OutCoh : Set
OutCoh = ∀ η (l : Lgl zero η) (ch : Coh η l) → Coh (fold₃ η l) (fold₃-legal η l ch)

record Pt₃ : Set where
  constructor pt₃
  field
    coord : R
    lawful : Lgl zero coord
    coherent : Coh coord lawful
open Pt₃

module Plain3 (out-coh : OutCoh) where

  obs₃ : Pt₃ → R
  obs₃ p = fold₃ (coord p) (lawful p)

  obs₃-legal : ∀ p → Lgl zero (obs₃ p)
  obs₃-legal p = fold₃-legal (coord p) (lawful p) (coherent p)

  next₃ : Pt₃ → Pt₃
  next₃ p = pt₃ (coord p +ʳ obs₃ p)
    (add-legal (coord p) (obs₃ p) (lawful p) (obs₃-legal p))
    (add-coh (coord p) (obs₃ p) (lawful p) (obs₃-legal p) (coherent p)
      (out-coh (coord p) (lawful p) (coherent p)))

  start₃ : Pt₃
  start₃ = pt₃ one tt tt

  points₃ : ℕ → Pt₃
  points₃ = iterate next₃ start₃

  T₃ᴿ : R
  T₃ᴿ = G.lim (λ n → obs₃ (points₃ n))

  obs₃-step : ∀ p → Cp zero (obs₃ p) (obs₃ (next₃ p))
  obs₃-step p =
    subst (λ z → Cp zero (fold₃ (coord p) z) (obs₃ (next₃ p)))
      (restrict-add-weak (coord p) (obs₃ p) (lawful p) (obs₃-legal p))
      (fold₃-up (coord (next₃ p)) (add-weak⁰ (coord p) (obs₃ p)) (lawful (next₃ p)))

  T₃ᴿ-legal : Lgl zero T₃ᴿ
  T₃ᴿ-legal = (λ n → obs₃-step (points₃ n)) , (λ n → obs₃-legal (points₃ n))

  T₃ᴿ-start : coord (points₃ 0) ≡ one
  T₃ᴿ-start = refl

  T₃ᴿ-feedback : ∀ n → coord (points₃ (suc n)) ≡
    coord (points₃ n) +ʳ fold₃ (coord (points₃ n)) (lawful (points₃ n))
  T₃ᴿ-feedback n = refl
```
