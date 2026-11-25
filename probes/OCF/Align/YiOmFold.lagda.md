# YiOmFold：公共上界 `tw 2` 上的两个折叠 (第 A、B 站)

**判决 (编译定理)：目标层 0 的折叠 `Φ⁰` 在 `Dom⁰` 上逐行写出并合法，行不改：`top` 给上一轮的 `T₃ᵐ`，主干槽位上的结点走加法链，三种孩子进各自的层。
目标是 `tw 2` 自己的折叠 `Φˢ` 在主干片段 `Tr` 上写出并合法，对 `Tr` 封闭；它在 `top` 上的行是替代行 (`topˢ`)：根槽位上的结点保留，分支不是第 `η` 支的保留折叠。**
`Φ⁰` 在分支槽位结点上的行没有 (条件形式在 [YiOmFoldGap](YiOmFoldGap.lagda.md))；目标为 `tw 2` 自己时这些结点与分支的孩子的行在 [YiOmFoldChain](YiOmFoldChain.lagda.md) 的 `Φˢ⁺` 里。没有值定理。
底座 [YiOmFoldBase](YiOmFoldBase.lagda.md)，闭项 [YiOmFoldTop](YiOmFoldTop.lagda.md)。

```agda
{-# OPTIONS --safe --without-K --lossy-unification #-}
module OCF.Align.YiOmFold where

open import Data.Nat.Base using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim-irr)
open import Data.Unit.Base using (⊤; tt)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (Σ; _,_; proj₁; proj₂; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import OCF.Align.RR5IrrCore
open import OCF.Align.RR5IrrCheck using (raw1; raw0-Nested)
open import OCF.Align.YiIrrIf using (R; one; read0; read0-legal; iterate)
open import OCF.Align.YiIrrFbIf using (Pt; pt) renaming (at to atᵖ)
open import OCF.Align.YiIrrFbRaw using (Cp-tr)
open import OCF.Align.YiLvIf using (lev; Kept)
open import OCF.Align.YiLvFoldAdd
open import OCF.Align.YiLvFoldBase using (fold)
open import OCF.Align.YiRawIf using (base; IsLim; RawFold)
open import OCF.Align.YiRawFoldBase using (NdR; nd; NdLgl; Ψn; Ψn-legal; Ψn-dn)
open import OCF.Align.YiRawFold
  using (Ψ-pos; Ψ-cp; Ψ-dn; Φᵐ; rawFold; startᴿ; nextᴿ; obsᴿ; bodyᴿ)
open import OCF.Align.YiRawFoldTw3 using (T₃ᵐ; T₃ᵐ-legal)
open import OCF.Align.YiRawNegOmega using (K₂ω; root₂; first₂)
open import OCF.Align.YiOmFoldBase
```

## 1 主干上的两种孩子折进 `tw 2`

目标是 `tw 2` 自己时每个位置都是槽位，一律保留，没有链。`F₀`：层号 0 的孩子 (第 0 层的值)；`F₁`：第一支 `suc zero` 的孩子，结点落在主干的第二个槽位。
零给 `top`，后继给 ω 倍，与 `YiRawFold.Ψ` 的行相同；`F₁ top` 展开成结点，与 `ndT` 相同。

```agda
F₀ : R → RΩ
F₀ G.zero = G.top
F₀ (G.suc a) = successorΩ (F₀ a)
F₀ (G.lim f) = G.lim (λ n → F₀ (f n))
F₀ G.top = successorΩ G.top

F₁ : Raw (suc zero) → RΩ
F₁ G.zero = G.top
F₁ (G.suc a) = successorΩ (F₁ a)
F₁ (G.lim f) = G.lim (λ n → F₁ (f n))
F₁ (G.lc (inj₁ _) c t g) = G.lc first₂ c (F₁ t) (λ η e → F₁ (g η e))
F₁ (G.em _ a) = F₀ a
F₁ G.top = G.lc first₂ raw1 (F₀ raw1) (λ η e → F₀ η)

F₀-cp : ∀ {a b} → Cp zero a b → Cp K₂ω (F₀ a) (F₀ b)
F₀-dn : ∀ {a} b → Dn zero a b → Dn K₂ω (F₀ a) (F₀ b)
F₀-cp (inj₁ refl) = inj₁ refl
F₀-cp {b = b} (inj₂ p) = inj₂ (F₀-dn b p)
F₀-dn (G.suc b) p = zero , F₀-cp p
F₀-dn (G.lim f) (n , p) = n , F₀-cp p

F₀-legal : ∀ a → Lgl zero a → Lgl K₂ω (F₀ a)
F₀-legal G.zero l = tt
F₀-legal (G.suc a) l = copiesΩ-step (F₀ a) , copiesΩ-legal (F₀ a) (F₀-legal a l)
F₀-legal (G.lim f) (st , lf) = (λ n → F₀-cp (st n)) , (λ n → F₀-legal (f n) (lf n))
F₀-legal G.top l = copiesΩ-step G.top , copiesΩ-legal G.top tt

F₀-nested : ∀ a → Nested K₂ω (F₀ a)
F₀-nested G.zero = tt
F₀-nested (G.suc a) = copiesΩ-nested (F₀ a) (F₀-nested a)
F₀-nested (G.lim f) = λ n → F₀-nested (f n)
F₀-nested G.top = copiesΩ-nested G.top tt

F₀-tr : ∀ a → Tr (F₀ a)
F₀-tr G.zero = tt
F₀-tr (G.suc a) = copiesΩ-tr (F₀ a) (F₀-tr a)
F₀-tr (G.lim f) = λ n → F₀-tr (f n)
F₀-tr G.top = copiesΩ-tr G.top tt

F₀-pos : ∀ a → Pos K₂ω (F₀ a)
F₀-pos G.zero = tt
F₀-pos (G.suc a) = tt
F₀-pos (G.lim f) = tt
F₀-pos G.top = tt

F₁-cp : ∀ {a b} → Cp (suc zero) a b → Cp K₂ω (F₁ a) (F₁ b)
F₁-dn : ∀ {a} b → Dn (suc zero) a b → Dn K₂ω (F₁ a) (F₁ b)
F₁-cp (inj₁ refl) = inj₁ refl
F₁-cp {b = b} (inj₂ p) = inj₂ (F₁-dn b p)
F₁-dn (G.suc b) p = zero , F₁-cp p
F₁-dn (G.lim f) (n , p) = n , F₁-cp p
F₁-dn (G.lc (inj₁ _) c t g) p = F₁-cp p
F₁-dn {G.em _ a} (G.em _ T) p = F₀-dn T p
F₁-dn {G.em _ a} G.top (inj₁ refl) = inj₁ refl

F₁-legal : ∀ a → Lgl (suc zero) a → Lgl K₂ω (F₁ a)
F₁-legal G.zero l = tt
F₁-legal (G.suc a) l = copiesΩ-step (F₁ a) , copiesΩ-legal (F₁ a) (F₁-legal a l)
F₁-legal (G.lim f) (st , lf) = (λ n → F₁-cp (st n)) , (λ n → F₁-legal (f n) (lf n))
F₁-legal (G.lc (inj₁ _) c t g) (tg , dir , irr , lt , lg) =
  (λ η e → F₁-cp (tg η e)) , (λ η e η′ e′ q → F₁-cp (dir η e η′ e′ q)) ,
  (λ η e e′ → refl) , F₁-legal t lt , (λ η e → F₁-legal (g η e) (lg η e))
F₁-legal (G.em _ a) l = F₀-legal a l
F₁-legal G.top l =
  (λ η e → F₀-cp (proj₁ e)) , (λ η e η′ e′ q → F₀-cp (proj₁ q)) ,
  (λ η e e′ → refl) , F₀-legal raw1 tt , (λ η e → F₀-legal η (proj₁ (proj₂ e)))

F₁-nested : ∀ a → Nested (suc zero) a → Nested K₂ω (F₁ a)
F₁-nested G.zero nb = tt
F₁-nested (G.suc a) nb = copiesΩ-nested (F₁ a) (F₁-nested a nb)
F₁-nested (G.lim f) nb = λ n → F₁-nested (f n) (nb n)
F₁-nested (G.lc (inj₁ _) c t g) (l , nl , nt , ng) =
  l , nl , F₁-nested t nt , (λ η e → F₁-nested (g η e) (ng η e))
F₁-nested (G.em _ a) nb = F₀-nested a
F₁-nested G.top nb = tt , tt , F₀-nested raw1 , (λ η e → F₀-nested η)

F₁-tr : ∀ a → Tr (F₁ a)
F₁-tr G.zero = tt
F₁-tr (G.suc a) = copiesΩ-tr (F₁ a) (F₁-tr a)
F₁-tr (G.lim f) = λ n → F₁-tr (f n)
F₁-tr (G.lc (inj₁ _) c t g) = F₁-tr t , (λ η e → F₁-tr (g η e))
F₁-tr (G.em _ a) = F₀-tr a
F₁-tr G.top = F₀-tr raw1 , (λ η e → F₀-tr η)

F₁-pos : ∀ a → Pos K₂ω (F₁ a)
F₁-pos G.zero = tt
F₁-pos (G.suc a) = tt
F₁-pos (G.lim f) = tt
F₁-pos (G.lc (inj₁ _) c t g) = tt
F₁-pos (G.em _ a) = F₀-pos a
F₁-pos G.top = tt
```

## 2 目标是 `tw 2` 自己：`Φˢ`

主干槽位上的结点原样保留在自己的位置上。`top` 的行 (**替代行**) `topˢ`：根 (层号 0) 保留在根槽位，下界 1，第一支是第一支的 `top` 的保留折叠 `t₀`；
第 `η` 支取 `t₀` 加上坐标 `η` 的折叠。本该有的第 `η` 支是第 `η` 支的 `top` 的保留折叠，它的结点在第 `η` 支的槽位上。

```agda
t₀ : RΩ
t₀ = F₁ G.top

topˢ : RΩ
topˢ = G.lc root₂ raw1 t₀ (λ η e → plusΩ t₀ (F₀ η))

Φˢ : (ξ : RΩ) → .(Tr ξ) → RΩ
Φˢ G.zero d = G.top
Φˢ (G.suc a) d = successorΩ (Φˢ a d)
Φˢ (G.lim f) d = G.lim (λ n → Φˢ (f n) (d n))
Φˢ (G.lc (inj₁ (inj₁ _)) c t g) d =
  G.lc root₂ c (Φˢ t (proj₁ d)) (λ η e → Φˢ (g η e) (proj₂ d η e))
Φˢ (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) d =
  G.lc first₂ c (Φˢ t (proj₁ d)) (λ η e → Φˢ (g η e) (proj₂ d η e))
Φˢ (G.lc (inj₂ (inj₂ _)) c t g) d = ⊥-elim-irr d
Φˢ (G.em (inj₁ _) a) d = F₀ a
Φˢ (G.em (inj₂ (inj₁ _)) a) d = F₁ a
Φˢ (G.em (inj₂ (inj₂ _)) a) d = ⊥-elim-irr d
Φˢ G.top d = topˢ

Φˢ-pos : ∀ ξ .(d : Tr ξ) → Pos K₂ω (Φˢ ξ d)
Φˢ-pos G.zero d = tt
Φˢ-pos (G.suc a) d = tt
Φˢ-pos (G.lim f) d = tt
Φˢ-pos (G.lc (inj₁ (inj₁ _)) c t g) d = tt
Φˢ-pos (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) d = tt
Φˢ-pos (G.lc (inj₂ (inj₂ _)) c t g) d = ⊥-elim-irr d
Φˢ-pos (G.em (inj₁ _) a) d = F₀-pos a
Φˢ-pos (G.em (inj₂ (inj₁ _)) a) d = F₁-pos a
Φˢ-pos (G.em (inj₂ (inj₂ _)) a) d = ⊥-elim-irr d
Φˢ-pos G.top d = tt

Φˢ-tr : ∀ ξ (d : Tr ξ) → Tr (Φˢ ξ d)
Φˢ-tr G.zero d = tt
Φˢ-tr (G.suc a) d = copiesΩ-tr (Φˢ a d) (Φˢ-tr a d)
Φˢ-tr (G.lim f) d = λ n → Φˢ-tr (f n) (d n)
Φˢ-tr (G.lc (inj₁ (inj₁ _)) c t g) (dt , dg) = Φˢ-tr t dt , (λ η e → Φˢ-tr (g η e) (dg η e))
Φˢ-tr (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) (dt , dg) =
  Φˢ-tr t dt , (λ η e → Φˢ-tr (g η e) (dg η e))
Φˢ-tr (G.em (inj₁ _) a) d = F₀-tr a
Φˢ-tr (G.em (inj₂ (inj₁ _)) a) d = F₁-tr a
Φˢ-tr G.top d = F₁-tr G.top , (λ η e → plus-tr t₀ (F₀ η) (F₁-tr G.top) (F₀-tr η))

Φˢ-cp : ∀ {ξ} ξ′ (d : Tr ξ) (d′ : Tr ξ′) → Cp K₂ω ξ ξ′ → Cp K₂ω (Φˢ ξ d) (Φˢ ξ′ d′)
Φˢ-dn : ∀ {ξ} ξ′ (d : Tr ξ) (d′ : Tr ξ′) → Dn K₂ω ξ ξ′ → Dn K₂ω (Φˢ ξ d) (Φˢ ξ′ d′)
Φˢ-cp ξ′ d d′ (inj₁ refl) = inj₁ refl
Φˢ-cp ξ′ d d′ (inj₂ p) = inj₂ (Φˢ-dn ξ′ d d′ p)
Φˢ-dn (G.suc b) d d′ p = zero , Φˢ-cp b d d′ p
Φˢ-dn (G.lim f) d d′ (n , p) = n , Φˢ-cp (f n) d (d′ n) p
Φˢ-dn (G.lc (inj₁ (inj₁ _)) c t g) d (dt , dg) p = Φˢ-cp t d dt p
Φˢ-dn (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) d (dt , dg) p = Φˢ-cp t d dt p
Φˢ-dn {G.em (inj₁ _) a} (G.em (inj₁ _) T) d d′ p = F₀-dn T p
Φˢ-dn {G.em (inj₂ (inj₁ _)) a} (G.em (inj₂ (inj₁ _)) T) d d′ p = F₁-dn T p
Φˢ-dn {G.em (inj₂ (inj₁ _)) a} G.top d d′ p = F₁-cp p

Φˢ-legal : ∀ ξ (d : Tr ξ) → Lgl K₂ω ξ → Lgl K₂ω (Φˢ ξ d)
Φˢ-legal G.zero d l = tt
Φˢ-legal (G.suc a) d l =
  copiesΩ-step (Φˢ a d) , copiesΩ-legal (Φˢ a d) (Φˢ-legal a d l)
Φˢ-legal (G.lim f) d (st , lf) =
  (λ n → Φˢ-cp (f (suc n)) (d n) (d (suc n)) (st n)) ,
  (λ n → Φˢ-legal (f n) (d n) (lf n))
Φˢ-legal (G.lc (inj₁ (inj₁ _)) c t g) (dt , dg) (tg , dir , irr , lt , lg) =
  (λ η e → Φˢ-cp (g η e) dt (dg η e) (tg η e)) ,
  (λ η e η′ e′ q → Φˢ-cp (g η′ e′) (dg η e) (dg η′ e′) (dir η e η′ e′ q)) ,
  (λ η e e′ → refl) , Φˢ-legal t dt lt , (λ η e → Φˢ-legal (g η e) (dg η e) (lg η e))
Φˢ-legal (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) (dt , dg) (tg , dir , irr , lt , lg) =
  (λ η e → Φˢ-cp (g η e) dt (dg η e) (tg η e)) ,
  (λ η e η′ e′ q → Φˢ-cp (g η′ e′) (dg η e) (dg η′ e′) (dir η e η′ e′ q)) ,
  (λ η e e′ → refl) , Φˢ-legal t dt lt , (λ η e → Φˢ-legal (g η e) (dg η e) (lg η e))
Φˢ-legal (G.em (inj₁ _) a) d l = F₀-legal a l
Φˢ-legal (G.em (inj₂ (inj₁ _)) a) d l = F₁-legal a l
Φˢ-legal G.top d l =
  (λ η e → plus-weak t₀ (F₀ η)) ,
  (λ η e η′ e′ q → plus-cp t₀ (F₀-cp (proj₁ q))) ,
  (λ η e e′ → refl) , F₁-legal G.top tt ,
  (λ η e → plus-lgl t₀ (F₀ η) (F₁-legal G.top tt) (F₀-legal η (proj₁ (proj₂ e))))

Φˢ-nested : ∀ ξ (d : Tr ξ) → Nested K₂ω ξ → Nested K₂ω (Φˢ ξ d)
Φˢ-nested G.zero d nb = tt
Φˢ-nested (G.suc a) d nb = copiesΩ-nested (Φˢ a d) (Φˢ-nested a d nb)
Φˢ-nested (G.lim f) d nb = λ n → Φˢ-nested (f n) (d n) (nb n)
Φˢ-nested (G.lc (inj₁ (inj₁ _)) c t g) (dt , dg) (l , nl , nt , ng) =
  l , nl , Φˢ-nested t dt nt , (λ η e → Φˢ-nested (g η e) (dg η e) (ng η e))
Φˢ-nested (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) (dt , dg) (l , nl , nt , ng) =
  l , nl , Φˢ-nested t dt nt , (λ η e → Φˢ-nested (g η e) (dg η e) (ng η e))
Φˢ-nested (G.em (inj₁ _) a) d nb = F₀-nested a
Φˢ-nested (G.em (inj₂ (inj₁ _)) a) d nb = F₁-nested a nb
Φˢ-nested G.top d nb =
  tt , tt , F₁-nested G.top tt ,
  (λ η e → plus-ns t₀ (F₀ η) (F₁-nested G.top tt) (F₀-nested η))
```

## 3 目标层 0：`Φ⁰`

`Dom⁰` 比 `Tr` 多容许分支的孩子：`em (η , e) T` 带相关的守卫，读出 `Legal (read0 η)`，在第 `η` 支自己的层里折 (上一轮的 `Φᵐ`)。
主干槽位上的结点层号是 0，它自己那一层的折叠就是 `Φ⁰`，所以链由 `Φ⁰` 推进；链取 `YiRawFoldBase.Ψn` 的折叠行，层号 0。
分支槽位上的结点不在 `Dom⁰` 里：它的链要用目标在那一支里的折叠去折各支，见 [YiOmFoldGap](YiOmFoldGap.lagda.md)。

```agda
Dom⁰ : RΩ → Set
Dom⁰ G.zero = ⊤
Dom⁰ (G.suc a) = Dom⁰ a
Dom⁰ (G.lim f) = ∀ n → Dom⁰ (f n)
Dom⁰ (G.lc (inj₁ (inj₁ _)) c t g) = Dom⁰ t × (∀ η (e : Gd zero c η) → Dom⁰ (g η e))
Dom⁰ (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) = Dom⁰ t × (∀ η (e : Gd zero c η) → Dom⁰ (g η e))
Dom⁰ (G.lc (inj₂ (inj₂ _)) c t g) = ⊥
Dom⁰ (G.em i a) = ⊤
Dom⁰ G.top = ⊤

tr-dom : ∀ ξ → Tr ξ → Dom⁰ ξ
tr-dom G.zero d = tt
tr-dom (G.suc a) d = tr-dom a d
tr-dom (G.lim f) d = λ n → tr-dom (f n) (d n)
tr-dom (G.lc (inj₁ (inj₁ _)) c t g) (dt , dg) = tr-dom t dt , (λ η e → tr-dom (g η e) (dg η e))
tr-dom (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) (dt , dg) =
  tr-dom t dt , (λ η e → tr-dom (g η e) (dg η e))
tr-dom (G.em i a) d = tt
tr-dom G.top d = tt

Φ⁰ : (ξ : RΩ) → .(Dom⁰ ξ) → .(Lgl K₂ω ξ) → .(Nested K₂ω ξ) → R
nd⁰ : (c : R) → .(Lgl zero c) → .(Nested zero c) → R →
  (g : (η : R) → .(Gd zero c η) → RΩ) →
  .(∀ η (e : Gd zero c η) → Dom⁰ (g η e)) →
  .(∀ η (e : Gd zero c η) → Lgl K₂ω (g η e)) →
  .(∀ η (e : Gd zero c η) → Nested K₂ω (g η e)) → NdR zero zero
Φ⁰-pos : ∀ ξ .(d : Dom⁰ ξ) .(l : Lgl K₂ω ξ) .(nb : Nested K₂ω ξ) → Pos zero (Φ⁰ ξ d l nb)
Φ⁰-legal : ∀ ξ (d : Dom⁰ ξ) (l : Lgl K₂ω ξ) (nb : Nested K₂ω ξ) → Lgl zero (Φ⁰ ξ d l nb)
Φ⁰-cp : ∀ {ξ} ξ′ (d : Dom⁰ ξ) (d′ : Dom⁰ ξ′) (l : Lgl K₂ω ξ) (nb : Nested K₂ω ξ)
  (l′ : Lgl K₂ω ξ′) (nb′ : Nested K₂ω ξ′) → Cp K₂ω ξ ξ′ →
  Cp zero (Φ⁰ ξ d l nb) (Φ⁰ ξ′ d′ l′ nb′)
Φ⁰-dn : ∀ {ξ} ξ′ (d : Dom⁰ ξ) (d′ : Dom⁰ ξ′) (l : Lgl K₂ω ξ) (nb : Nested K₂ω ξ)
  (l′ : Lgl K₂ω ξ′) (nb′ : Nested K₂ω ξ′) → Dn K₂ω ξ ξ′ →
  Dn zero (Φ⁰ ξ d l nb) (Φ⁰ ξ′ d′ l′ nb′)

Φ⁰ G.zero d l nb = one
Φ⁰ (G.suc a) d l nb = successor zero (Φ⁰ a d l nb)
Φ⁰ (G.lim f) d l nb = G.lim (λ n → Φ⁰ (f n) (d n) (proj₂ l n) (nb n))
Φ⁰ (G.lc (inj₁ (inj₁ _)) c t g) d l nb =
  Ψn zero zero tt fold (nd⁰ c (proj₁ nb) (proj₁ (proj₂ nb))
    (Φ⁰ t (proj₁ d) (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
    g (proj₂ d) (proj₂ (proj₂ (proj₂ (proj₂ l)))) (proj₂ (proj₂ (proj₂ nb))))
Φ⁰ (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) d l nb =
  Ψn zero zero tt fold (nd⁰ c (proj₁ nb) (proj₁ (proj₂ nb))
    (Φ⁰ t (proj₁ d) (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
    g (proj₂ d) (proj₂ (proj₂ (proj₂ (proj₂ l)))) (proj₂ (proj₂ (proj₂ nb))))
Φ⁰ (G.lc (inj₂ (inj₂ _)) c t g) d l nb = ⊥-elim-irr d
Φ⁰ (G.em (inj₁ _) T) d l nb = Φᵐ zero tt tt base T l nb
Φ⁰ (G.em (inj₂ (inj₁ _)) T) d l nb = Φᵐ (suc zero) tt tt base T l nb
Φ⁰ (G.em (inj₂ (inj₂ (η , e))) T) d l nb =
  Φᵐ (read0 η) (rplain η) (read0-legal η (proj₁ (proj₂ e))) base T l nb
Φ⁰ G.top d l nb = T₃ᵐ

nd⁰ c lw nw t g dg lg ng = nd c lw nw t
  (λ η e → Φ⁰ (g η e) (dg η e) (lg η e) (ng η e))
  (λ η e → Φ⁰ (g η e) (dg η e) (lg η e) (ng η e))
  (λ η e → Φ⁰-legal (g η e) (dg η e) (lg η e) (ng η e))
  (λ η e → raw0-Nested (Φ⁰ (g η e) (dg η e) (lg η e) (ng η e)))
  (λ η e → Φ⁰-pos (g η e) (dg η e) (lg η e) (ng η e))

Φ⁰-pos G.zero d l nb = tt
Φ⁰-pos (G.suc a) d l nb = tt
Φ⁰-pos (G.lim f) d l nb = tt
Φ⁰-pos (G.lc (inj₁ (inj₁ _)) c t g) d l nb = tt
Φ⁰-pos (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) d l nb = tt
Φ⁰-pos (G.lc (inj₂ (inj₂ _)) c t g) d l nb = ⊥-elim-irr d
Φ⁰-pos (G.em (inj₁ _) T) d l nb =
  Ψ-pos zero zero tt tt _ T l nb
Φ⁰-pos (G.em (inj₂ (inj₁ _)) T) d l nb =
  Ψ-pos zero (suc zero) tt tt _ T l nb
Φ⁰-pos (G.em (inj₂ (inj₂ (η , e))) T) d l nb =
  Ψ-pos zero (read0 η) (rplain η) (read0-legal η (proj₁ (proj₂ e))) _ T l nb
Φ⁰-pos G.top d l nb = tt

Φ⁰-legal G.zero d l nb = tt
Φ⁰-legal (G.suc a) d l nb =
  copies-step zero tt (Φ⁰ a d l nb) ,
  copies-legal zero tt (Φ⁰ a d l nb) (Φ⁰-legal a d l nb)
Φ⁰-legal (G.lim f) d (st , lf) nb =
  (λ n → Φ⁰-cp (f (suc n)) (d n) (d (suc n)) (lf n) (nb n) (lf (suc n)) (nb (suc n)) (st n)) ,
  (λ n → Φ⁰-legal (f n) (d n) (lf n) (nb n))
Φ⁰-legal (G.lc (inj₁ (inj₁ _)) c t g) (dt , dg) (tg , dir , irr , lt , lg) (lw , nw , nt , ng) =
  Ψn-legal zero zero tt fold (nd⁰ c lw nw (Φ⁰ t dt lt nt) g dg lg ng)
    (record
      { seed = inj₁ refl , lw , nw
      ; tg = λ η e → Φ⁰-cp (g η e) dt (dg η e) lt nt (lg η e) (ng η e) (tg η e)
      ; dir = λ η e η′ e′ q → Φ⁰-cp (g η′ e′) (dg η e) (dg η′ e′)
          (lg η e) (ng η e) (lg η′ e′) (ng η′ e′) (dir η e η′ e′ q)
      ; lt = Φ⁰-legal t dt lt nt
      ; lg = λ η e → Φ⁰-legal (g η e) (dg η e) (lg η e) (ng η e)
      ; lkʳ = λ η e → Φ⁰-legal (g η e) (dg η e) (lg η e) (ng η e)
      ; nkʳ = λ η e → raw0-Nested (Φ⁰ (g η e) (dg η e) (lg η e) (ng η e)) })
Φ⁰-legal (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) (dt , dg) (tg , dir , irr , lt , lg)
  (lw , nw , nt , ng) =
  Ψn-legal zero zero tt fold (nd⁰ c lw nw (Φ⁰ t dt lt nt) g dg lg ng)
    (record
      { seed = inj₁ refl , lw , nw
      ; tg = λ η e → Φ⁰-cp (g η e) dt (dg η e) lt nt (lg η e) (ng η e) (tg η e)
      ; dir = λ η e η′ e′ q → Φ⁰-cp (g η′ e′) (dg η e) (dg η′ e′)
          (lg η e) (ng η e) (lg η′ e′) (ng η′ e′) (dir η e η′ e′ q)
      ; lt = Φ⁰-legal t dt lt nt
      ; lg = λ η e → Φ⁰-legal (g η e) (dg η e) (lg η e) (ng η e)
      ; lkʳ = λ η e → Φ⁰-legal (g η e) (dg η e) (lg η e) (ng η e)
      ; nkʳ = λ η e → raw0-Nested (Φ⁰ (g η e) (dg η e) (lg η e) (ng η e)) })
Φ⁰-legal (G.em (inj₁ _) T) d l nb = RawFold.legal rawFold zero tt tt base T l nb
Φ⁰-legal (G.em (inj₂ (inj₁ _)) T) d l nb = RawFold.legal rawFold (suc zero) tt tt base T l nb
Φ⁰-legal (G.em (inj₂ (inj₂ (η , e))) T) d l nb =
  RawFold.legal rawFold (read0 η) (rplain η) (read0-legal η (proj₁ (proj₂ e))) base T l nb
Φ⁰-legal G.top d l nb = T₃ᵐ-legal

Φ⁰-cp ξ′ d d′ l nb l′ nb′ (inj₁ refl) = inj₁ refl
Φ⁰-cp ξ′ d d′ l nb l′ nb′ (inj₂ p) = inj₂ (Φ⁰-dn ξ′ d d′ l nb l′ nb′ p)

Φ⁰-dn (G.suc b) d d′ l nb l′ nb′ p = zero , Φ⁰-cp b d d′ l nb l′ nb′ p
Φ⁰-dn (G.lim f) d d′ l nb (st , lf) nb′ (n , p) =
  n , Φ⁰-cp (f n) d (d′ n) l nb (lf n) (nb′ n) p
Φ⁰-dn (G.lc (inj₁ (inj₁ _)) c t g) d (dt , dg) l nb (tg , dir , irr , lt , lg)
  (lw , nw , nt , ng) p =
  Ψn-dn zero zero tt fold (nd⁰ c lw nw (Φ⁰ t dt lt nt) g dg lg ng)
    (Φ⁰-cp t d dt l nb lt nt p)
    (inj₁ refl , lw , nw)
    (Φ⁰-cp (g c (inj₁ refl , lw , nw)) d (dg c (inj₁ refl , lw , nw)) l nb
      (lg c (inj₁ refl , lw , nw)) (ng c (inj₁ refl , lw , nw))
      (Cp-tr K₂ω p (tg c (inj₁ refl , lw , nw))))
Φ⁰-dn (G.lc (inj₂ (inj₁ (inj₁ _))) c t g) d (dt , dg) l nb (tg , dir , irr , lt , lg)
  (lw , nw , nt , ng) p =
  Ψn-dn zero zero tt fold (nd⁰ c lw nw (Φ⁰ t dt lt nt) g dg lg ng)
    (Φ⁰-cp t d dt l nb lt nt p)
    (inj₁ refl , lw , nw)
    (Φ⁰-cp (g c (inj₁ refl , lw , nw)) d (dg c (inj₁ refl , lw , nw)) l nb
      (lg c (inj₁ refl , lw , nw)) (ng c (inj₁ refl , lw , nw))
      (Cp-tr K₂ω p (tg c (inj₁ refl , lw , nw))))
Φ⁰-dn {G.em (inj₁ _) a} (G.em (inj₁ _) T) d d′ l nb l′ nb′ p =
  Ψ-dn zero zero tt tt _ T l nb l′ nb′ p
Φ⁰-dn {G.em (inj₂ (inj₁ _)) a} (G.em (inj₂ (inj₁ _)) T) d d′ l nb l′ nb′ p =
  Ψ-dn zero (suc zero) tt tt _ T l nb l′ nb′ p
Φ⁰-dn {G.em (inj₂ (inj₂ (η , e))) a} (G.em (inj₂ (inj₂ .(η , e))) T) d d′ l nb l′ nb′
  (refl , p) =
  Ψ-dn zero (read0 η) (rplain η) (read0-legal η (proj₁ (proj₂ e))) _ T l nb l′ nb′ p
Φ⁰-dn {G.em (inj₂ (inj₁ _)) a} G.top d d′ l nb l′ nb′ p =
  zero , Ψ-cp zero (suc zero) tt tt _ G.top l nb tt tt p
```

## 4 行

都是 `refl`。结点行的链四件取 `YiRawFold` 的 `startᴿ`, `nextᴿ`, `bodyᴿ`, `obsᴿ`：下一点是这一点加上 `Φ⁰` 在这一点的分支上的输出，观察同一个 `Φ⁰`。

```agda
Φ⁰-top : Φ⁰ G.top tt tt tt ≡ T₃ᵐ
Φ⁰-top = refl

Φ⁰-kid : ∀ η (e : Gd zero raw1 η) T (l : Lgl (read0 η) T) (nb : Nested (read0 η) T) →
  Φ⁰ (G.em (inj₂ (inj₂ (η , e))) T) tt l nb ≡
  Φᵐ (read0 η) (rplain η) (read0-legal η (proj₁ (proj₂ e))) base T l nb
Φ⁰-kid η e T l nb = refl

module NodeRow (c : R) (t : RΩ) (g : (η : R) → .(Gd zero c η) → RΩ)
  (d : Dom⁰ (G.lc root₂ c t g)) (l : Lgl K₂ω (G.lc root₂ c t g))
  (nb : Nested K₂ω (G.lc root₂ c t g)) where

  N : NdR zero zero
  N = nd⁰ c (proj₁ nb) (proj₁ (proj₂ nb))
    (Φ⁰ t (proj₁ d) (proj₁ (proj₂ (proj₂ (proj₂ l)))) (proj₁ (proj₂ (proj₂ nb))))
    g (proj₂ d) (proj₂ (proj₂ (proj₂ (proj₂ l)))) (proj₂ (proj₂ (proj₂ nb)))

  chain-row : Φ⁰ (G.lc root₂ c t g) d l nb ≡
    G.lim (λ n → obsᴿ N (iterate (nextᴿ tt N) (startᴿ N) n))
  chain-row = refl

  start-row : atᵖ (startᴿ N) ≡ c
  start-row = refl

  next-row : ∀ p → atᵖ (nextᴿ tt N p) ≡ plus zero (atᵖ p) (bodyᴿ N p)
  next-row p = refl

  body-row : ∀ η (e : Gd zero c η) →
    bodyᴿ N (pt η e) ≡ Φ⁰ (g η e) (proj₂ d η e) (proj₂ (proj₂ (proj₂ (proj₂ l))) η e)
      (proj₂ (proj₂ (proj₂ nb)) η e)
  body-row η e = refl

  obs-row : ∀ η (e : Gd zero c η) → obsᴿ N (pt η e) ≡ bodyᴿ N (pt η e)
  obs-row η e = refl

Φˢ-top : Φˢ G.top tt ≡ G.lc root₂ raw1 t₀ (λ η e → plusΩ t₀ (F₀ η))
Φˢ-top = refl

Φˢ-node : ∀ c t g (d : Tr (G.lc root₂ c t g)) →
  Φˢ (G.lc root₂ c t g) d ≡
  G.lc root₂ c (Φˢ t (proj₁ d)) (λ η e → Φˢ (g η e) (proj₂ d η e))
Φˢ-node c t g d = refl
```

## 5 派发在这两个目标上是完全的

目标层 0 之下没有位置，折叠的输出是 ℕ 极限；目标是 `tw 2` 自己时结点的位置就是槽位，输出是那个槽位上的保留结点。
`top` 的根 (层号 0) 在 `Φˢ` 下保留在根槽位；它的分支是替代行，不在这条律里。

```agda
Φ⁰-fold-root : ∀ c t g .(d : Dom⁰ (G.lc root₂ c t g)) .(l : Lgl K₂ω (G.lc root₂ c t g))
  .(nb : Nested K₂ω (G.lc root₂ c t g)) → IsLim (Φ⁰ (G.lc root₂ c t g) d l nb)
Φ⁰-fold-root c t g d l nb = tt

Φ⁰-fold-first : ∀ c t g .(d : Dom⁰ (G.lc first₂ c t g)) .(l : Lgl K₂ω (G.lc first₂ c t g))
  .(nb : Nested K₂ω (G.lc first₂ c t g)) → IsLim (Φ⁰ (G.lc first₂ c t g) d l nb)
Φ⁰-fold-first c t g d l nb = tt

Φˢ-keep-root : ∀ c t g .(d : Tr (G.lc root₂ c t g)) →
  Kept K₂ω (lev K₂ω root₂) (Φˢ (G.lc root₂ c t g) d)
Φˢ-keep-root c t g d = root₂ , refl , c , _ , _ , refl

Φˢ-keep-first : ∀ c t g .(d : Tr (G.lc first₂ c t g)) →
  Kept K₂ω (lev K₂ω first₂) (Φˢ (G.lc first₂ c t g) d)
Φˢ-keep-first c t g d = first₂ , refl , c , _ , _ , refl

Φˢ-keep-top : Kept K₂ω zero (Φˢ G.top tt)
Φˢ-keep-top = root₂ , refl , raw1 , _ , _ , refl
```
